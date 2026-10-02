# Verus verifies with the Basis cvc5 fork (see get-cvc5.sh), which is
# published for macOS arm64, Linux x86_64 and Linux arm64 only. On Windows, build that fork
# yourself and point VERUS_CVC5_PATH at it, or verify with z3 (`-V z3`).
Write-Error "The Basis cvc5 build is published for macOS arm64, Linux x86_64 and Linux arm64 only. Build BasisResearch/cvc5 (tag basis-6c96b55f6c) and set VERUS_CVC5_PATH, or pass -V z3 to verify with z3."
exit 1
