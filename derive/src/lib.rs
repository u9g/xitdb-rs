//! The derive macro for [xitdb](https://docs.rs/xitdb)'s `Record` trait.
//! Don't depend on this crate directly: enable xitdb's `derive` feature and
//! use `xitdb::Record`, which documents what the macro generates.

use proc_macro::TokenStream;
use proc_macro2::TokenStream as TokenStream2;
use quote::{quote, quote_spanned};
use syn::spanned::Spanned;
use syn::{Data, DeriveInput, Fields, GenericArgument, Ident, LitStr, PathArguments, Type};

/// Implements `xitdb::Record` and `xitdb::ValueCodec` for a struct with
/// named fields, so it's stored as a nested hash map of its fields.
///
/// Field attributes, in `#[xitdb(...)]`:
///
/// * `rename = "name"`: the key the field is stored under, instead of the
///   field's name.
/// * `codec = Type`: the field's `ValueCodec`, such as `Json<T>`, instead
///   of the field's type. For an `Option<T>` field, it's the codec of `T`.
/// * `required`: a missing field is an error, instead of reading as
///   `Default::default()`. Not allowed on `Option` fields.
#[proc_macro_derive(Record, attributes(xitdb))]
pub fn derive_record(input: TokenStream) -> TokenStream {
    let input = syn::parse_macro_input!(input as DeriveInput);
    expand(&input).unwrap_or_else(syn::Error::into_compile_error).into()
}

/// A field of the struct, with its attributes.
struct Field<'a> {
    ident: &'a Ident,
    /// The key it's stored under.
    name: LitStr,
    /// The codec of the value (of `T`, for an `Option<T>` field).
    codec: Type,
    /// The type of the value (`T`, for an `Option<T>` field).
    value_type: &'a Type,
    /// Whether the field is an `Option`, so `None` is a missing field.
    optional: bool,
    required: bool,
}

fn expand(input: &DeriveInput) -> syn::Result<TokenStream2> {
    let ident = &input.ident;
    if !input.generics.params.is_empty() {
        return Err(syn::Error::new(
            input.generics.span(),
            "#[derive(Record)] doesn't support generic structs; implement xitdb::Record and xitdb::ValueCodec by hand",
        ));
    }
    let fields = match &input.data {
        Data::Struct(data) => match &data.fields {
            Fields::Named(fields) => &fields.named,
            _ => {
                return Err(syn::Error::new(
                    ident.span(),
                    "#[derive(Record)] needs a struct with named fields, since they're the keys it's stored under",
                ));
            }
        },
        Data::Enum(_) | Data::Union(_) => {
            return Err(syn::Error::new(ident.span(), "#[derive(Record)] only supports structs with named fields"));
        }
    };
    for attr in &input.attrs {
        if attr.path().is_ident("xitdb") {
            return Err(syn::Error::new(attr.span(), "#[xitdb(...)] attributes go on the fields of a Record"));
        }
    }

    let fields = fields.iter().map(parse_field).collect::<syn::Result<Vec<_>>>()?;
    let mut names = std::collections::HashSet::new();
    for field in &fields {
        if !names.insert(field.name.value()) {
            return Err(syn::Error::new(field.name.span(), "two fields are stored under this name"));
        }
    }

    let names: Vec<_> = fields.iter().map(|field| &field.name).collect();
    let reads = fields.iter().map(read_field);
    let writes: Vec<_> = fields.iter().map(write_field).collect();
    let idents: Vec<_> = fields.iter().map(|field| field.ident).collect();

    Ok(quote! {
        impl ::xitdb::Record for #ident {
            const FIELDS: &'static [&'static str] = &[#(#names),*];

            fn read_fields<C: ::xitdb::Core>(map: &::xitdb::ReadHashMap<'_, C>) -> ::xitdb::Result<Self> {
                ::core::result::Result::Ok(#ident { #(#reads,)* })
            }

            fn write_fields<C: ::xitdb::Core>(&self, map: &mut ::xitdb::WriteHashMap<'_, C>) -> ::xitdb::Result<()> {
                #(#writes)*
                ::core::result::Result::Ok(())
            }

            fn changed_fields(&self, old: &Self) -> ::std::vec::Vec<&'static str> {
                let mut changed = ::std::vec::Vec::new();
                #(
                    if self.#idents != old.#idents {
                        changed.push(#names);
                    }
                )*
                changed
            }

            fn write_changed_fields<C: ::xitdb::Core>(
                &self,
                old: &Self,
                map: &mut ::xitdb::WriteHashMap<'_, C>,
            ) -> ::xitdb::Result<()> {
                #(
                    if self.#idents != old.#idents {
                        #writes
                    }
                )*
                ::core::result::Result::Ok(())
            }
        }

        impl ::xitdb::ValueCodec for #ident {
            type Owned = Self;
            type Borrowed = Self;

            fn read<C: ::xitdb::Core>(cursor: &::xitdb::ReadCursor<'_, C>) -> ::xitdb::Result<Self> {
                ::xitdb::__private::read_record(cursor)
            }

            fn write<C: ::xitdb::Core>(value: &Self, cursor: &mut ::xitdb::WriteCursor<'_, C>) -> ::xitdb::Result<()> {
                ::xitdb::__private::write_record(value, cursor)
            }
        }
    })
}

fn parse_field(field: &syn::Field) -> syn::Result<Field<'_>> {
    let ident = field.ident.as_ref().expect("named fields have idents");
    let mut name = None;
    let mut codec = None;
    let mut required = false;
    for attr in field.attrs.iter().filter(|attr| attr.path().is_ident("xitdb")) {
        attr.parse_nested_meta(|meta| {
            if meta.path.is_ident("rename") {
                name = Some(meta.value()?.parse::<LitStr>()?);
            } else if meta.path.is_ident("codec") {
                codec = Some(meta.value()?.parse::<Type>()?);
            } else if meta.path.is_ident("required") {
                required = true;
            } else {
                return Err(meta.error("expected `rename = \"...\"`, `codec = Type` or `required`"));
            }
            Ok(())
        })?;
    }

    let option = option_inner(&field.ty);
    if required && option.is_some() {
        let message = "an Option field can't be required, since None is a missing field";
        return Err(syn::Error::new(field.ty.span(), message));
    }
    let value_type = option.unwrap_or(&field.ty);
    Ok(Field {
        ident,
        name: name.unwrap_or_else(|| LitStr::new(&ident.to_string(), ident.span())),
        codec: codec.unwrap_or_else(|| value_type.clone()),
        value_type,
        optional: option.is_some(),
        required,
    })
}

/// `T`, if `ty` is written as `Option<T>` (or with a path, like
/// `std::option::Option<T>`).
fn option_inner(ty: &Type) -> Option<&Type> {
    let Type::Path(path) = ty else { return None };
    if path.qself.is_some() {
        return None;
    }
    let segment = path.path.segments.last()?;
    if segment.ident != "Option" {
        return None;
    }
    let PathArguments::AngleBracketed(args) = &segment.arguments else { return None };
    match args.args.iter().collect::<Vec<_>>()[..] {
        [GenericArgument::Type(inner)] => Some(inner),
        _ => None,
    }
}

/// `ident: value`, reading the field from `map`.
fn read_field(field: &Field<'_>) -> TokenStream2 {
    let Field { ident, name, codec, value_type, .. } = field;
    // the span makes a codec whose Owned isn't the field's type point at it
    let read = quote_spanned! {codec.span()=>
        ::xitdb::__private::read_field::<C, #codec, #value_type>(map, #name)?
    };
    if field.optional {
        quote! { #ident: #read }
    } else if field.required {
        quote! {
            #ident: match #read {
                ::core::option::Option::Some(value) => value,
                ::core::option::Option::None => {
                    return ::core::result::Result::Err(::xitdb::__private::missing_field(#name));
                }
            }
        }
    } else {
        quote! { #ident: #read.unwrap_or_default() }
    }
}

/// Writes the field to `map`, or removes it if it's an `Option` that's
/// `None`.
fn write_field(field: &Field<'_>) -> TokenStream2 {
    let Field { ident, name, codec, .. } = field;
    if field.optional {
        quote! {
            match &self.#ident {
                ::core::option::Option::Some(value) => {
                    ::xitdb::__private::write_field::<C, #codec, _>(map, #name, value)?
                }
                ::core::option::Option::None => ::xitdb::__private::remove_field(map, #name)?,
            }
        }
    } else {
        quote! { ::xitdb::__private::write_field::<C, #codec, _>(map, #name, &self.#ident)?; }
    }
}
