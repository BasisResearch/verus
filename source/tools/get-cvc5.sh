#! /bin/bash -eu

# Downloads the Basis cvc5 fork that Verus verifies with into the current
# directory. The fork answers the `get-info` keys behind the failure
# diagnostics (matching loops, instantiation pressure, nonlinear frontier,
# why a check gave up, e-graph equalities). Its version string is
# CVC5_VERSION in source/cargo-verus-toolchains/src/external_deps.rs; bump
# both together.

cvc5_repo="BasisResearch/cvc5"
cvc5_tag="basis-6c96b55f6c"

case "$(uname -s)/$(uname -m)" in
    Darwin/arm64)
        filename="cvc5-arm64-macos"
        sha256="11adb95c90e72c1f65785dfd835c856c4519870da6608f90fab8ff41706b8ba7"
        ;;
    Linux/x86_64)
        filename="cvc5-x86-linux"
        sha256="4803479d4124b52943e3f0d65bbfa35bb00d208d9c0ad91b3d7b00a7cac33968"
        ;;
    Linux/aarch64 | Linux/arm64)
        filename="cvc5-arm64-linux"
        sha256="39ba75c3f4990a1277d1e9a208bb3a92650b736c89b690f2482002751c381025"
        ;;
    *)
        echo "The Basis cvc5 build is published for macOS arm64, Linux x86_64 and Linux arm64 only." >&2
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
