#! /bin/bash -eu

# Downloads the Basis cvc5 fork that Verus verifies with into the current
# directory. The fork answers the `get-info` keys behind the failure
# diagnostics (matching loops, instantiation pressure, nonlinear frontier,
# why a check gave up, e-graph equalities). Its version string is
# CVC5_VERSION in source/cargo-verus-toolchains/src/external_deps.rs; bump
# both together.

cvc5_repo="BasisResearch/cvc5"
cvc5_tag="basis-e68dc63e37"

case "$(uname -s)/$(uname -m)" in
    Darwin/arm64)
        filename="cvc5-arm64-macos"
        sha256="12a465c5f684e8b3a7170580047f6a66a517e86c10ea7dc484e74d0a3f78adc3"
        ;;
    Linux/x86_64)
        filename="cvc5-x86-linux"
        sha256="66aa2969667607a4852377cb39b1561b315aecd4045ab554f06e576fa95e3920"
        ;;
    *)
        echo "The Basis cvc5 build is published for macOS arm64 and Linux x86_64 only." >&2
        exit 1
        ;;
esac

url="https://github.com/$cvc5_repo/releases/download/$cvc5_tag/$filename"
tmp="cvc5.download"
trap 'rm -f "$tmp"' EXIT

echo "Downloading: $url"
curl -fL -o "$tmp" "$url"
echo "$sha256  $tmp" | shasum -a 256 -c -
chmod +x "$tmp"
# delete the existing cvc5 because of caching issue on macs
rm -f cvc5
mv "$tmp" cvc5
trap - EXIT
