//! The derive macro for [xitdb](https://docs.rs/xitdb)'s `Record` trait.
//! Don't depend on this crate directly: enable xitdb's `derive` feature and
//! use `xitdb::Record`, which documents what the macro generates.

use proc_macro::TokenStream;
use proc_macro2::TokenStream as TokenStream2;
use quote::{quote, quote_spanned};
use syn::ext::IdentExt;
use syn::meta::ParseNestedMeta;
use syn::spanned::Spanned;
use syn::{Data, DeriveInput, Fields, GenericArgument, Ident, LitStr, Path, PathArguments, Type};

/// Implements `xitdb::Record` and `xitdb::ValueCodec` for a struct with
/// named fields, so it's stored as a nested hash map of its fields.
///
/// Field attributes, in `#[xitdb(...)]`:
///
/// * `rename = "name"`: the key the field is stored under, instead of the
///   field's name.
/// * `codec = Type`: the field's `ValueCodec`, such as `Json<T>`, instead
///   of the field's type. For an `Option<T>` field, it's the codec of the
///   whole field, such as `Option<Json<T>>`.
/// * `required`: a missing field is an error, instead of reading as
///   `Default::default()`.
///
/// Struct attribute: `#[xitdb(crate = "path")]`, the path to the `xitdb`
/// crate, if it's not `::xitdb` (for example, when it's re-exported).
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
    /// The codec of the value.
    codec: Type,
    ty: &'a Type,
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
    let krate = parse_crate(input)?;

    let fields = fields.iter().map(parse_field).collect::<syn::Result<Vec<_>>>()?;
    let mut names = std::collections::HashSet::new();
    for field in &fields {
        if !names.insert(field.name.value()) {
            return Err(syn::Error::new(field.name.span(), "two fields are stored under this name"));
        }
    }

    // every name the generated code introduces starts with __xitdb, so it
    // can't shadow, or be shadowed by, the user's types and constants
    let names: Vec<_> = fields.iter().map(|field| &field.name).collect();
    let idents: Vec<_> = fields.iter().map(|field| field.ident).collect();
    let codecs: Vec<_> = fields.iter().map(|field| &field.codec).collect();
    let reads = fields.iter().map(|field| read_field(&krate, field));
    let private = quote! { #krate::__private };

    Ok(quote! {
        impl #krate::Record for #ident {
            const FIELDS: &'static [&'static str] = &[#(#names),*];

            fn read_fields<__XitdbCore: #krate::Core>(
                __xitdb_map: &#krate::ReadHashMap<'_, __XitdbCore>,
            ) -> #krate::Result<Self> {
                ::core::result::Result::Ok(#ident { #(#reads,)* })
            }

            fn write_fields<__XitdbCore: #krate::Core>(
                &self,
                __xitdb_map: &mut #krate::WriteHashMap<'_, __XitdbCore>,
            ) -> #krate::Result<()> {
                #(
                    #private::write_field::<__XitdbCore, #codecs, _>(__xitdb_map, #names, &self.#idents)?;
                )*
                ::core::result::Result::Ok(())
            }

            fn changed_fields(&self, __xitdb_old: &Self) -> ::std::vec::Vec<&'static str> {
                let mut __xitdb_changed = ::std::vec::Vec::new();
                #(
                    if #private::field_changed::<#codecs>(&__xitdb_old.#idents, &self.#idents) {
                        __xitdb_changed.push(#names);
                    }
                )*
                __xitdb_changed
            }

            fn write_changed_fields<'__xitdb, __XitdbCore, __XitdbOpen>(
                &self,
                __xitdb_old: &Self,
                __xitdb_map: &mut #krate::LazyMap<'__xitdb, __XitdbCore, __XitdbOpen>,
            ) -> #krate::Result<bool>
            where
                __XitdbCore: #krate::Core,
                __XitdbOpen: ::core::ops::FnOnce() -> #krate::Result<#krate::WriteHashMap<'__xitdb, __XitdbCore>>,
            {
                let mut __xitdb_wrote = false;
                #(
                    if #private::field_changed::<#codecs>(&__xitdb_old.#idents, &self.#idents) {
                        #private::write_changed_field::<__XitdbCore, #codecs, _>(
                            __xitdb_map.get()?,
                            #names,
                            &__xitdb_old.#idents,
                            &self.#idents,
                        )?;
                        __xitdb_wrote = true;
                    }
                )*
                ::core::result::Result::Ok(__xitdb_wrote)
            }
        }

        impl #krate::ValueCodec for #ident {
            type Owned = Self;
            type Borrowed = Self;

            fn read<__XitdbCore: #krate::Core>(
                __xitdb_cursor: &#krate::ReadCursor<'_, __XitdbCore>,
            ) -> #krate::Result<Self> {
                #private::read_record(__xitdb_cursor)
            }

            fn write<__XitdbCore: #krate::Core>(
                __xitdb_value: &Self,
                __xitdb_cursor: &mut #krate::WriteCursor<'_, __XitdbCore>,
            ) -> #krate::Result<()> {
                #private::write_record(__xitdb_value, __xitdb_cursor)
            }

            fn changed(__xitdb_old: &Self, __xitdb_new: &Self) -> ::core::option::Option<bool> {
                ::core::option::Option::Some(!#krate::Record::changed_fields(__xitdb_new, __xitdb_old).is_empty())
            }

            fn write_changed<__XitdbCore: #krate::Core>(
                __xitdb_old: &Self,
                __xitdb_new: &Self,
                __xitdb_cursor: &mut #krate::WriteCursor<'_, __XitdbCore>,
            ) -> #krate::Result<()> {
                #private::write_record_changed(__xitdb_old, __xitdb_new, __xitdb_cursor)
            }
        }
    })
}

/// The path to the xitdb crate: `::xitdb`, or the struct's
/// `#[xitdb(crate = "...")]`.
fn parse_crate(input: &DeriveInput) -> syn::Result<Path> {
    let mut krate = None;
    for attr in input.attrs.iter().filter(|attr| attr.path().is_ident("xitdb")) {
        attr.parse_nested_meta(|meta| {
            if meta.path.is_ident("crate") {
                set_once(&meta, &mut krate, meta.value()?.parse::<LitStr>()?.parse::<Path>()?)
            } else {
                Err(meta.error("expected `crate = \"...\"`; the other attributes go on fields"))
            }
        })?;
    }
    Ok(krate.unwrap_or_else(|| syn::parse_quote!(::xitdb)))
}

fn parse_field(field: &syn::Field) -> syn::Result<Field<'_>> {
    let ident = field.ident.as_ref().expect("named fields have idents");
    let mut name = None;
    let mut codec = None;
    let mut required = None;
    for attr in field.attrs.iter().filter(|attr| attr.path().is_ident("xitdb")) {
        attr.parse_nested_meta(|meta| {
            if meta.path.is_ident("rename") {
                set_once(&meta, &mut name, meta.value()?.parse::<LitStr>()?)
            } else if meta.path.is_ident("codec") {
                set_once(&meta, &mut codec, meta.value()?.parse::<Type>()?)
            } else if meta.path.is_ident("required") {
                set_once(&meta, &mut required, ())
            } else {
                Err(meta.error("expected `rename = \"...\"`, `codec = Type` or `required`"))
            }
        })?;
    }

    // whatever the spelling, an Option field reads and writes None as a
    // missing field, through its codec; this only catches the obvious
    // mistake
    if required.is_some() && is_option(&field.ty) {
        let message = "an Option field can't be required, since None is a missing field";
        return Err(syn::Error::new(field.ty.span(), message));
    }
    Ok(Field {
        ident,
        name: name.unwrap_or_else(|| LitStr::new(&ident.unraw().to_string(), ident.span())),
        codec: codec.unwrap_or_else(|| field.ty.clone()),
        ty: &field.ty,
        required: required.is_some(),
    })
}

/// Sets an attribute's value, or fails if it's already set.
fn set_once<T>(meta: &ParseNestedMeta<'_>, slot: &mut Option<T>, value: T) -> syn::Result<()> {
    if slot.is_some() {
        let name = meta.path.get_ident().map(ToString::to_string).unwrap_or_default();
        return Err(meta.error(format!("`{name}` is given more than once")));
    }
    *slot = Some(value);
    Ok(())
}

/// Whether `ty` is written as `Option<T>` (or with a path, like
/// `std::option::Option<T>`).
fn is_option(ty: &Type) -> bool {
    let Type::Path(path) = ty else { return false };
    let Some(segment) = path.path.segments.last() else { return false };
    let PathArguments::AngleBracketed(args) = &segment.arguments else { return false };
    path.qself.is_none()
        && segment.ident == "Option"
        && matches!(args.args.iter().collect::<Vec<_>>()[..], [GenericArgument::Type(_)])
}

/// `ident: value`, reading the field from `__xitdb_map`.
fn read_field(krate: &Path, field: &Field<'_>) -> TokenStream2 {
    let Field { ident, name, codec, ty, .. } = field;
    // the span makes a codec whose Owned isn't the field's type point at it
    let read = quote_spanned! {codec.span()=>
        #krate::__private::read_field::<__XitdbCore, #codec, #ty>(__xitdb_map, #name)?
    };
    if field.required {
        quote! {
            #ident: match #read {
                ::core::option::Option::Some(__xitdb_value) => __xitdb_value,
                ::core::option::Option::None => {
                    return ::core::result::Result::Err(#krate::__private::missing_field(#name));
                }
            }
        }
    } else {
        quote! { #ident: #read.unwrap_or_default() }
    }
}
