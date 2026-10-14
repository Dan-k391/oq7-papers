$oq7WorkspaceRoot = Split-Path -Parent $PSScriptRoot
$oq7LeanBin = Join-Path $oq7WorkspaceRoot '.local\toolchains\lean-4.34.1-windows\bin'
if (-not (Test-Path -LiteralPath (Join-Path $oq7LeanBin 'lean.exe'))) {
    throw 'Restore the pinned Lean 4.34.1 distribution into .local/toolchains/lean-4.34.1-windows first; see REPRODUCE.md.'
}
$env:PATH = $oq7LeanBin + ';' + $env:PATH
Set-Location -LiteralPath $oq7WorkspaceRoot
& (Join-Path $oq7LeanBin 'lean.exe') --version
