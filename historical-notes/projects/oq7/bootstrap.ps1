$ErrorActionPreference = 'Stop'
Push-Location $PSScriptRoot
try {
    # An independent checkout uses the toolchain pinned in lean-toolchain.
    if (-not (Get-Command elan -ErrorAction SilentlyContinue)) {
        throw 'Install the official Lean toolchain manager elan, or use lake.ps1 on this PC.'
    }
    & elan toolchain install 'leanprover/lean4:v4.34.1'
    if ($LASTEXITCODE -ne 0) { throw 'Pinned Lean installation failed.' }
    & lake update
    if ($LASTEXITCODE -ne 0) { throw 'Dependency checkout failed.' }
    $env:MATHLIB_CACHE_DIR = Join-Path $PSScriptRoot '.lake/mathlib-cache'
    & lake exe cache get
    if ($LASTEXITCODE -ne 0) { throw 'Mathlib cache retrieval failed.' }
    & (Join-Path $PSScriptRoot 'verify.ps1') -Clean
} finally {
    Pop-Location
}
