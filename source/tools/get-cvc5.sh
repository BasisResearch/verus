#!/bin/bash -eu

cvc5_tag="basis-4a42bee406"

case "$(uname -s)/$(uname -m)" in
    Darwin/arm64)
        filename="cvc5-arm64-macos"
        sha256="b5ccae10ca03785ed3cec9794f134b991f5bb0b51f139f8b434a3478c5953c76"
        ;;
    Linux/x86_64)
        filename="cvc5-x86-linux"
        sha256="2d8b6cd70545061b9574c2d39ede246f4560e49635ef6028654bcb4a23783907"
        ;;
    *)
        echo "The pinned Basis cvc5 build supports macOS arm64 and Linux x86_64 only." >&2
        exit 1
        ;;
esac

url="https://github.com/BasisResearch/cvc5/releases/download/$cvc5_tag/$filename"
tmp="cvc5.download"
trap 'rm -f "$tmp"' EXIT

echo "Downloading: $url"
curl -fL -o "$tmp" "$url"
echo "$sha256  $tmp" | shasum -a 256 -c -
chmod +x "$tmp"
mv "$tmp" cvc5
trap - EXIT
