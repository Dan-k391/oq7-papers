param([Parameter(ValueFromRemainingArguments = $true)][string[]]$LakeArguments)
$ErrorActionPreference = 'Stop'
$oq7PinnedBin = 'C:\Users\Daniel\Documents\Codex\2026-10-09\set-up-a-local-ai-mathematical\outputs\math-research-lab\tools\lean-4.34.1-windows\bin'
if (Test-Path -LiteralPath (Join-Path $oq7PinnedBin 'lake.exe')) {
    $env:PATH = $oq7PinnedBin + ';' + $env:PATH
}
Push-Location $PSScriptRoot
try {
    & lake @LakeArguments
    exit $LASTEXITCODE
} finally {
    Pop-Location
}
