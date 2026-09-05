#!/bin/bash -eu

cvc5_tag="basis-4a9afc6b35"

case "$(uname -s)/$(uname -m)" in
    Darwin/arm64)
        filename="cvc5-arm64-macos"
        sha256="705452a629e7f521cd7677f3ff6cf25d853e31b60b78f3ba64b17616795b73b5"
        ;;
    Linux/x86_64)
        filename="cvc5-x86-linux"
        sha256="5a72ef96293db50421449da7f037d1bb0489697844fae657d5a2b7fa357d91fd"
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
