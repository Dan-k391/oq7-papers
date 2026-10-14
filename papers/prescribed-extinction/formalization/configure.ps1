param([string]$PackagesDirectory)
$ErrorActionPreference = 'Stop'
# Restore the portable pinned manifest, optionally reusing an existing package cache.
# No dependency revision is updated by this script.
$oq7Config = Get-Content -LiteralPath (Join-Path $PSScriptRoot 'sources/pinned-lake-manifest.json') -Raw | ConvertFrom-Json
$oq7Config.name = 'oq7_prescribed_extinction'
if ($PackagesDirectory) {
    $oq7Resolved = (Resolve-Path -LiteralPath $PackagesDirectory).Path
    $oq7Config.packagesDir = $oq7Resolved.Replace('\', '/')
} else {
    $oq7Config.packagesDir = '.lake/packages'
}
$oq7Config | ConvertTo-Json -Depth 20 | Set-Content -LiteralPath (Join-Path $PSScriptRoot 'lake-manifest.json') -Encoding utf8
$oq7Lake = @"
name = "oq7_prescribed_extinction"
version = "0.1.0"
packagesDir = "$($oq7Config.packagesDir)"
defaultTargets = ["OQ7", "PrescribedExtinction"]

[[require]]
name = "mathlib"
git = "https://github.com/leanprover-community/mathlib4.git"
rev = "d13f23b723b8a846827a245b89c10fc7d3f11612"

[[lean_lib]]
name = "OQ7"

[[lean_lib]]
name = "PrescribedExtinction"
"@
$oq7Lake | Set-Content -LiteralPath (Join-Path $PSScriptRoot 'lakefile.toml') -Encoding utf8
Write-Output "Configured pinned packages directory: $($oq7Config.packagesDir)"
