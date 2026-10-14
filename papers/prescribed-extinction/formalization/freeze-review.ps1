param()
$ErrorActionPreference = 'Stop'
Push-Location $PSScriptRoot
try {
    $oq7Report = Get-Content -LiteralPath 'verification/report.json' -Raw | ConvertFrom-Json
    if (-not $oq7Report.completePhysicalTheorem11Verified -or -not $oq7Report.cleanProjectBuild -or
        -not $oq7Report.freshKernelReplay.passed) { throw 'Complete clean/audit/fresh-kernel evidence is required.' }
    $oq7Dirty = @(& git status --porcelain)
    if ($LASTEXITCODE -ne 0 -or $oq7Dirty.Count -ne 0) { throw 'Commit the exact verified repository before freezing.' }
    $oq7Commit = (& git rev-parse HEAD).Trim()
    if ($LASTEXITCODE -ne 0 -or $oq7Commit -notmatch '^[0-9a-f]{40}$') { throw 'Cannot determine frozen commit.' }
    foreach ($oq7Source in $oq7Report.sourceHashes) {
        if ((Get-FileHash -LiteralPath $oq7Source.file -Algorithm SHA256).Hash -ne $oq7Source.sha256) {
            throw "Verified source changed: $($oq7Source.file)"
        }
    }
    $oq7Parent = [IO.Directory]::GetParent($PSScriptRoot).FullName
    $oq7Destination = [IO.Path]::GetFullPath((Join-Path $oq7Parent ('oq7-physical-theorem11-review-' + $oq7Commit.Substring(0, 12))))
    if (-not $oq7Destination.StartsWith($oq7Parent + [IO.Path]::DirectorySeparatorChar, [StringComparison]::OrdinalIgnoreCase)) {
        throw 'Frozen destination is outside the repository parent.'
    }
    if (Test-Path -LiteralPath $oq7Destination) { throw "Frozen destination already exists: $oq7Destination" }
    New-Item -ItemType Directory -Path $oq7Destination | Out-Null
    $oq7Bundle = Join-Path $oq7Destination 'OQ7-complete-physical-theorem11.bundle'
    $oq7Archive = Join-Path $oq7Destination 'OQ7-complete-physical-theorem11-source.zip'
    & git bundle create $oq7Bundle --all
    if ($LASTEXITCODE -ne 0) { throw 'Git bundle creation failed.' }
    & git bundle verify $oq7Bundle 2>&1 | Set-Content -LiteralPath (Join-Path $oq7Destination 'bundle-verify.log') -Encoding utf8
    if ($LASTEXITCODE -ne 0) { throw 'Git bundle verification failed.' }
    & git archive --format=zip "--output=$oq7Archive" HEAD
    if ($LASTEXITCODE -ne 0) { throw 'Source archive creation failed.' }
    Add-Type -AssemblyName System.IO.Compression.FileSystem
    $oq7Zip = [IO.Compression.ZipFile]::OpenRead($oq7Archive)
    try {
        foreach ($oq7Source in $oq7Report.sourceHashes) {
            $oq7Entry = $oq7Zip.GetEntry($oq7Source.file.Replace([char]92, [char]47))
            if ($null -eq $oq7Entry) { throw "Certified source missing from archive: $($oq7Source.file)" }
            $oq7Stream = $oq7Entry.Open()
            $oq7Hasher = [Security.Cryptography.SHA256]::Create()
            try { $oq7Hash = [BitConverter]::ToString($oq7Hasher.ComputeHash($oq7Stream)).Replace('-', '') }
            finally { $oq7Stream.Dispose(); $oq7Hasher.Dispose() }
            if ($oq7Hash -ne $oq7Source.sha256) { throw "Archived source differs from clean certificate: $($oq7Source.file)" }
        }
    } finally { $oq7Zip.Dispose() }
    Copy-Item -LiteralPath 'verification/INDEPENDENT_REVIEW_PROMPT.md' -Destination (Join-Path $oq7Destination 'INDEPENDENT_REVIEW_PROMPT.md')
    $oq7Manifest = [ordered]@{
        status = 'FROZEN_COMPLETE_PHYSICAL_THEOREM11_KERNEL_VERIFIED'
        repository = $PSScriptRoot
        commit = $oq7Commit
        theorem = $oq7Report.finalTheoremDeclaration
        exactType = $oq7Report.targetProposition
        cleanProjectBuildPassed = $true
        allProjectConstantsAudited = $oq7Report.allProjectConstantsAudited
        allowedFoundationAxioms = $oq7Report.allowedFoundationAxioms
        freshKernelReplay = $oq7Report.freshKernelReplay
        archiveCertifiedLeanSourceHashesVerified = $true
        certifiedLeanFiles = $oq7Report.sourceHashes.Count
        gitBundleVerified = $true
        artifacts = @(
            @{ name = [IO.Path]::GetFileName($oq7Bundle); sha256 = (Get-FileHash -LiteralPath $oq7Bundle -Algorithm SHA256).Hash },
            @{ name = [IO.Path]::GetFileName($oq7Archive); sha256 = (Get-FileHash -LiteralPath $oq7Archive -Algorithm SHA256).Hash }
        )
        remainingMathematicalObligations = @()
        independentSemanticReview = 'Not yet performed for this frozen commit; prompt supplied'
        createdUTC = [DateTime]::UtcNow.ToString('o')
    }
    $oq7Manifest | ConvertTo-Json -Depth 20 | Set-Content -LiteralPath (Join-Path $oq7Destination 'manifest.json') -Encoding utf8
    Set-ItemProperty -LiteralPath $oq7Bundle -Name IsReadOnly -Value $true
    Set-ItemProperty -LiteralPath $oq7Archive -Name IsReadOnly -Value $true
    Write-Output "Frozen review repository: $oq7Destination"
    Write-Output "Frozen commit: $oq7Commit"
} finally { Pop-Location }
