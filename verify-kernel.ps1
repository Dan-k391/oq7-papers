param([string]$LeanBin)
$ErrorActionPreference = 'Stop'
$env:LEAN_NUM_THREADS = '2'
if ($LeanBin) { $env:PATH = (Resolve-Path -LiteralPath $LeanBin).Path + ';' + $env:PATH }
Push-Location $PSScriptRoot
try {
    $oq7Report = Get-Content -LiteralPath 'verification/report.json' -Raw | ConvertFrom-Json
    if (-not $oq7Report.completePhysicalTheorem11Verified -or -not $oq7Report.cleanProjectBuild) {
        throw 'Run the complete clean verifier before the fresh kernel replay.'
    }
    foreach ($oq7Source in $oq7Report.sourceHashes) {
        if ((Get-FileHash -LiteralPath $oq7Source.file -Algorithm SHA256).Hash -ne $oq7Source.sha256) {
            throw "Source changed after clean verification: $($oq7Source.file)"
        }
    }
    $oq7Started = [DateTime]::UtcNow
    & lake env leanchecker --fresh --verbose PrescribedExtinction 2>&1 |
        Set-Content -LiteralPath 'verification/leanchecker-fresh.log' -Encoding utf8
    $oq7Exit = $LASTEXITCODE
    $oq7Finished = [DateTime]::UtcNow
    Add-Content -LiteralPath 'verification/leanchecker-fresh.log' -Encoding utf8 -Value @(
        "Exit code: $oq7Exit", "Started UTC: $($oq7Started.ToString('o'))",
        "Finished UTC: $($oq7Finished.ToString('o'))",
        "Elapsed seconds: $(($oq7Finished - $oq7Started).TotalSeconds)")
    if ($oq7Exit -ne 0) { throw 'Fresh kernel replay failed; see verification/leanchecker-fresh.log.' }
    foreach ($oq7Source in $oq7Report.sourceHashes) {
        if ((Get-FileHash -LiteralPath $oq7Source.file -Algorithm SHA256).Hash -ne $oq7Source.sha256) {
            throw "Source changed during kernel replay: $($oq7Source.file)"
        }
    }
    $oq7Result = [ordered]@{
        passed = $true
        command = 'lake env leanchecker --fresh --verbose PrescribedExtinction'
        module = 'PrescribedExtinction'
        scope = 'Every constant in the complete physical aggregate import closure, replayed into an empty kernel environment'
        sameLeanKernelImplementation = $true
        independentKernelImplementationUsed = $false
        sourceHashesIdenticalToCleanCertificate = $true
        startedUTC = $oq7Started.ToString('o')
        finishedUTC = $oq7Finished.ToString('o')
        elapsedSeconds = ($oq7Finished - $oq7Started).TotalSeconds
        exitCode = $oq7Exit
        log = 'verification/leanchecker-fresh.log'
    }
    $oq7Result | ConvertTo-Json -Depth 6 | Set-Content -LiteralPath 'verification/fresh-kernel-report.json' -Encoding utf8
    $oq7Report | Add-Member -NotePropertyName freshKernelReplay -NotePropertyValue $oq7Result -Force
    $oq7Report | ConvertTo-Json -Depth 20 | Set-Content -LiteralPath 'verification/report.json' -Encoding utf8
    Write-Output 'FRESH KERNEL REPLAY PASSED: complete physical import closure checked in an empty environment.'
} finally { Pop-Location }
