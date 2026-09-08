# The z3 version is pinned in tools/common/solvers.toml (single source of truth).
$manifest = Join-Path $PSScriptRoot "..\..\tools\common\solvers.toml"
$section = ""
$z3_version = $null
foreach ($line in Get-Content $manifest) {
    if ($line -match '^\[(\w+)\]') { $section = $Matches[1]; continue }
    if ($section -eq "z3" -and $line -match '^version\s*=\s*"([^"]+)"') { $z3_version = $Matches[1] }
}
if (-not $z3_version) { Write-Error "could not read the z3 version from $manifest"; exit 1 }
$filename = "z3-$z3_version-x64-win"

$download_url = "https://github.com/Z3Prover/z3/releases/download/z3-$z3_version/$filename.zip"
Invoke-WebRequest -Uri $download_url -OutFile "$filename.zip"
Expand-Archive -Path "$filename.zip" -DestinationPath "."
Copy-Item "$filename/bin/z3.exe" -Destination "."
Remove-Item -Recurse -Force "$filename"
Remove-Item "$filename.zip"
