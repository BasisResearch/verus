#!/bin/bash -eu

# Downloads the pinned Basis cvc5 build into the current directory. The pin
# (release tag, per-platform asset, sha256) lives in tools/common/solvers.toml,
# the single source of truth shared with rust_verify, vargo and verus-tools-mcp.

manifest="$(cd "$(dirname "${BASH_SOURCE[0]}")/../.." && pwd)/tools/common/solvers.toml"
pin() { sed -n "/^\[$1\]/,/^\[/{s/^$2 *= *\"\([^\"]*\)\".*/\1/p}" "$manifest"; }

cvc5_repo="$(pin cvc5 repo)"
cvc5_tag="$(pin cvc5 tag)"

case "$(uname -s)/$(uname -m)" in
    Darwin/arm64)
        filename="$(pin cvc5 asset_arm64_macos)"
        sha256="$(pin cvc5 sha256_arm64_macos)"
        ;;
    Linux/x86_64)
        filename="$(pin cvc5 asset_x86_linux)"
        sha256="$(pin cvc5 sha256_x86_linux)"
        ;;
    *)
        echo "The pinned Basis cvc5 build supports macOS arm64 and Linux x86_64 only." >&2
        exit 1
        ;;
esac

if [ -z "$cvc5_repo" ] || [ -z "$cvc5_tag" ] || [ -z "$filename" ] || [ -z "$sha256" ]; then
    echo "could not read the cvc5 pin from $manifest" >&2
    exit 1
fi

url="https://github.com/$cvc5_repo/releases/download/$cvc5_tag/$filename"
tmp="cvc5.download"
trap 'rm -f "$tmp"' EXIT

echo "Downloading: $url"
curl -fL -o "$tmp" "$url"
echo "$sha256  $tmp" | shasum -a 256 -c -
chmod +x "$tmp"
mv "$tmp" cvc5
trap - EXIT
