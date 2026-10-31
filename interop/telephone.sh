#!/bin/sh
# Plays telephone with one database between this crate and the Go, Java and
# TypeScript implementations (see examples/telephone.rs). They take turns
# appending a moment of random edits, the next one in line checks every
# moment against a model, and at the end they must all read the file, and a
# compacted copy, identically.
#
#   interop/telephone.sh [rounds] [seed]
#
# Rounds default to 10 and the seed to a random one, which is printed so a
# failure can be replayed. Each implementation whose toolchain is missing is
# skipped: Go needs go (1.23+), Java needs java, javac and curl, and
# TypeScript needs node and pnpm or npm. On failure, the database, the edits
# each hop made and the dumps that disagree are kept in a directory it
# prints.
set -eu

cd "$(dirname "$0")"
rounds=${1:-10}
seed=${2:-$(od -An -N4 -tu4 /dev/urandom | tr -d ' ')}
dir=$(mktemp -d)

# native windows programs need windows paths
native() {
    if command -v cygpath >/dev/null; then cygpath -w "$1"; else echo "$1"; fi
}
case "$(uname -s)" in
    MINGW* | MSYS* | CYGWIN*) sep=';' ;;
    *) sep=':' ;;
esac

hops=rust
skip() {
    echo "telephone: skipping $1 ($2 not found)"
}

if command -v go >/dev/null; then
    go build -o "$dir/go-hop.exe" ./telephone/go
    hops="$hops go"
else
    skip go go
fi

java_version=0.46.0
java_sha1=604e8db5eb74f925447c8fbabbf93b08e877ffc2
if command -v java >/dev/null && command -v javac >/dev/null && command -v curl >/dev/null; then
    jar=${XDG_CACHE_HOME:-$HOME/.cache}/xitdb-telephone/xitdb-$java_version.jar
    if [ ! -f "$jar" ]; then
        mkdir -p "$(dirname "$jar")"
        curl -fsSL -o "$jar.part" "https://repo.clojars.org/io/github/radarroark/xitdb/$java_version/xitdb-$java_version.jar"
        if [ "$(sha1sum "$jar.part" | cut -d' ' -f1)" != "$java_sha1" ]; then
            echo "telephone: xitdb-$java_version.jar from clojars has the wrong checksum" >&2
            exit 1
        fi
        mv "$jar.part" "$jar"
    fi
    javac -d "$dir/java" -cp "$jar" telephone/java/Hop.java
    hops="$hops java"
else
    skip java "java, javac or curl"
fi

if command -v node >/dev/null; then
    if command -v pnpm >/dev/null; then
        (cd telephone/ts && pnpm install --silent)
    else
        (cd telephone/ts && npm install --silent --no-audit --no-fund)
    fi
    hops="$hops ts"
else
    skip ts node
fi

set -- rust
for hop in $hops; do
    case $hop in
        go) set -- "$@" "go=$(native "$dir/go-hop.exe")" ;;
        java) set -- "$@" "java=java -cp $(native "$jar")$sep$(native "$dir/java") Hop" ;;
        ts) set -- "$@" "ts=node $(native "$PWD/telephone/ts/hop.mjs")" ;;
    esac
done

if cargo run --quiet --example telephone -- run "$(native "$dir")" "$rounds" "$seed" "$@"; then
    rm -rf "$dir"
else
    echo "telephone: failed with seed $seed, see $dir" >&2
    exit 1
fi
