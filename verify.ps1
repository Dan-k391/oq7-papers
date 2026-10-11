param([string]$LeanBin, [switch]$Clean)
$ErrorActionPreference = 'Stop'
if ($LeanBin) { $env:PATH = (Resolve-Path -LiteralPath $LeanBin).Path + ';' + $env:PATH }
Push-Location $PSScriptRoot
try {
    New-Item -ItemType Directory -Force -Path 'verification' | Out-Null
    $oq7Version = ((& lean --version) | Out-String).Trim()
    if ($LASTEXITCODE -ne 0 -or $oq7Version -notmatch 'version 4\.34\.1,' -or
        $oq7Version -notmatch '5045d0056413266e57c625dcd7c365b10e377c52') { throw 'Wrong pinned Lean compiler.' }
    $oq7Sources = @(@('OQ7','PrescribedExtinction') | ForEach-Object {
        Get-ChildItem -LiteralPath $_ -Filter '*.lean' -Recurse
    }) + @(Get-Item -LiteralPath 'OQ7.lean','PrescribedExtinction.lean')
    foreach ($oq7File in $oq7Sources) {
        $oq7Code = Get-Content -LiteralPath $oq7File.FullName -Raw
        $oq7Code = [regex]::Replace($oq7Code, '(?s)/-.*?-/', '')
        $oq7Code = [regex]::Replace($oq7Code, '(?m)--[^\r\n]*', '')
        if ($oq7Code -match '\b(sorry|admit|axiom|native_decide)\b|debug\.skipKernelTC|decide\s*\+native|implemented_by') {
            throw "Disallowed proof mechanism: $($oq7File.FullName)"
        }
    }
    if ($Clean) {
        $oq7CleanOutput = @(& lake clean oq7_prescribed_extinction 2>&1)
        $oq7CleanExit = $LASTEXITCODE
        @('lake clean oq7_prescribed_extinction', "Exit code: $oq7CleanExit") + $oq7CleanOutput |
            Set-Content -LiteralPath 'verification/clean.log' -Encoding utf8
        if ($oq7CleanExit -ne 0) { throw 'Project clean failed.' }
    }
    & lake build 2>&1 | Set-Content -LiteralPath 'verification/build.log' -Encoding utf8
    if ($LASTEXITCODE -ne 0) { throw 'Build failed; see verification/build.log.' }
    & lake env lean verification/Inventory.lean 2>&1 | Set-Content -LiteralPath 'verification/inventory.log' -Encoding utf8
    if ($LASTEXITCODE -ne 0) { throw 'Kernel inventory failed.' }
    $oq7Inventory = Get-Content -LiteralPath 'verification/inventory.log' -Raw
    if ($oq7Inventory -match 'AUDIT-CUSTOM-AXIOM') { throw 'Custom axiom in project namespace.' }
    $oq7Constants = @([regex]::Matches($oq7Inventory, 'AUDIT-CONSTANT\s+(\S+)') | ForEach-Object { $_.Groups[1].Value } | Sort-Object -Unique)
    $oq7Theorems = @([regex]::Matches($oq7Inventory, 'AUDIT-THEOREM\s+(\S+)') | ForEach-Object { $_.Groups[1].Value } | Sort-Object -Unique)
    $oq7NewKernelTheorems = @($oq7Theorems | Where-Object { $_.StartsWith('OQ7Prescribed.') })
    $oq7NewTheorems = @(Get-ChildItem -LiteralPath 'PrescribedExtinction' -Filter '*.lean' | ForEach-Object {
        $oq7NewCode = Get-Content -LiteralPath $_.FullName -Raw
        [regex]::Matches($oq7NewCode, '(?m)^theorem\s+([^\s:({\[]+)') | ForEach-Object {
            'OQ7Prescribed.' + $_.Groups[1].Value
        }
    } | Sort-Object -Unique)
    foreach ($oq7NewName in $oq7NewTheorems) {
        if ($oq7NewName -notin $oq7NewKernelTheorems) { throw "Named theorem missing from kernel inventory: $oq7NewName" }
    }
    if ($oq7NewTheorems.Count -eq 0) { throw 'Missing new theorem inventory.' }
    if ('OQ7Prescribed.theorem11' -in $oq7Constants) { throw 'Update verification status before adding a final theorem.' }
    $oq7Audit = @('import OQ7', 'import PrescribedExtinction', '') + @($oq7Constants | ForEach-Object { '#print axioms ' + $_ })
    $oq7Audit | Set-Content -LiteralPath 'verification/Audit.lean' -Encoding utf8
    & lake env lean verification/Audit.lean 2>&1 | Set-Content -LiteralPath 'verification/axioms.log' -Encoding utf8
    if ($LASTEXITCODE -ne 0) { throw 'Axiom export failed.' }
    $oq7AxiomsLog = Get-Content -LiteralPath 'verification/axioms.log' -Raw
    $oq7Allowed = @('propext','Classical.choice','Quot.sound')
    foreach ($oq7Name in $oq7Constants) {
        $oq7Match = [regex]::Match($oq7AxiomsLog, "'" + [regex]::Escape($oq7Name) + "' depends on axioms: \[([^\]]*)\]")
        if ($oq7Match.Success) {
            foreach ($oq7Axiom in $oq7Match.Groups[1].Value.Split(',')) {
                if ($oq7Axiom.Trim() -notin $oq7Allowed) { throw "Unexpected axiom for ${oq7Name}: $oq7Axiom" }
            }
        } elseif ($oq7AxiomsLog -notmatch ("'" + [regex]::Escape($oq7Name) + "' does not depend on any axioms")) {
            throw "Missing axiom report: $oq7Name"
        }
    }
    $oq7Statements = @('import PrescribedExtinction','', '#print OQ7Prescribed.Theorem11Statement',
        '#print axioms OQ7Prescribed.Theorem11Statement', '') + @($oq7NewTheorems | ForEach-Object { '#check @' + $_ })
    $oq7Statements | Set-Content -LiteralPath 'verification/Statements.lean' -Encoding utf8
    & lake env lean verification/Statements.lean 2>&1 | Set-Content -LiteralPath 'verification/statements.log' -Encoding utf8
    if ($LASTEXITCODE -ne 0) { throw 'Statement export failed.' }
    $oq7Pins = Get-Content -LiteralPath 'lake-manifest.json' -Raw | ConvertFrom-Json
    $oq7Dependencies = @()
    foreach ($oq7Package in $oq7Pins.packages) {
        $oq7PackagePath = Join-Path $oq7Pins.packagesDir $oq7Package.name
        $oq7Rev = (& git -C $oq7PackagePath rev-parse HEAD).Trim()
        if ($LASTEXITCODE -ne 0 -or $oq7Rev -ne $oq7Package.rev) { throw "Incorrect dependency revision: $($oq7Package.name)" }
        $oq7Dirty = @(& git -C $oq7PackagePath status --porcelain --untracked-files=no)
        if ($LASTEXITCODE -ne 0 -or $oq7Dirty.Count -ne 0) { throw "Modified tracked dependency: $($oq7Package.name)" }
        $oq7Dependencies += @{ name = $oq7Package.name; revision = $oq7Rev; trackedSourceClean = $true }
    }
    $oq7LegacyHashes = Get-Content -LiteralPath 'sources/legacy-source-hashes.json' -Raw | ConvertFrom-Json
    foreach ($oq7Saved in $oq7LegacyHashes) {
        if ((Get-FileHash -LiteralPath $oq7Saved.file -Algorithm SHA256).Hash -ne $oq7Saved.sha256) {
            throw "Preserved legacy source differs: $($oq7Saved.file)"
        }
    }
    $oq7PdfHash = (Get-FileHash -LiteralPath 'sources/OQ7_prescribed_extinction_2026-10-11.pdf' -Algorithm SHA256).Hash
    if ($oq7PdfHash -ne '3D9775D849234E828370D7C96D8BDCDD574BEB6831A7906EA6B7706579868710') { throw 'Manuscript hash differs.' }
    $oq7TargetHash = (Get-FileHash -LiteralPath 'PrescribedExtinction/Maxwell.lean' -Algorithm SHA256).Hash
    if ($oq7TargetHash -ne '071C04ED9417A1D9AC842D61B545183627E6F997C7C1899F908871608859ABF6') {
        throw 'Existing physical target source changed. Review quantifiers before continuing.'
    }
    $oq7Hashes = @($oq7Sources | ForEach-Object {
        @{ file = [IO.Path]::GetRelativePath($PSScriptRoot, $_.FullName); sha256 = (Get-FileHash -LiteralPath $_.FullName -Algorithm SHA256).Hash }
    })
    if ($Clean) {
        Copy-Item -LiteralPath 'verification/build.log' -Destination 'verification/clean-build.log' -Force
        $oq7Hashes | ConvertTo-Json -Depth 5 | Set-Content -LiteralPath 'verification/clean-build-source-hashes.json' -Encoding utf8
    }
    $oq7SameCleanSources = $false
    if (Test-Path -LiteralPath 'verification/clean-build-source-hashes.json') {
        $oq7CleanHashes = @(Get-Content -LiteralPath 'verification/clean-build-source-hashes.json' -Raw | ConvertFrom-Json)
        $oq7SameCleanSources = ($oq7CleanHashes.Count -eq $oq7Hashes.Count)
        foreach ($oq7CurrentHash in $oq7Hashes) {
            $oq7SavedHash = @($oq7CleanHashes | Where-Object { $_.file -eq $oq7CurrentHash.file })
            if ($oq7SavedHash.Count -ne 1 -or $oq7SavedHash[0].sha256 -ne $oq7CurrentHash.sha256) {
                $oq7SameCleanSources = $false
            }
        }
    }
    [ordered]@{
        status = 'PARTIAL'
        theorem11Verified = $false
        finalTheoremDeclaration = $null
        targetProposition = 'OQ7Prescribed.Theorem11Statement'
        targetIsAProof = $false
        existingPhysicalTargetSourceUnchanged = $true
        targetSourceSHA256 = $oq7TargetHash
        verifiedAtUTC = [DateTime]::UtcNow.ToString('o')
        lean = $oq7Version
        lakeBuildPassed = $true
        cleanProjectBuild = [bool]$Clean
        savedCleanBuildHasIdenticalLeanSources = $oq7SameCleanSources
        cleanBuildLog = 'verification/clean-build.log'
        allowedFoundationAxioms = $oq7Allowed
        allProjectConstantsAudited = $oq7Constants.Count
        newTheoremCount = $oq7NewTheorems.Count
        newKernelTheoremConstantCount = $oq7NewKernelTheorems.Count
        newTheorems = $oq7NewTheorems
        legacyTheorem51Present = ('OQ7.theorem51' -in $oq7Theorems)
        legacySourcesPreserved = $true
        manuscriptSHA256 = $oq7PdfHash
        dependencyRevisions = $oq7Dependencies
        sourceHashes = $oq7Hashes
        foundationalMilestones = @(
            @{ module = 'PrescribedExtinction.GreenKernel'; scope = 'Actual scalar kernel local L1/L2 integrability and distributional dyadic test formula'; physicalContactCoefficientVerified = $false },
            @{ module = 'PrescribedExtinction.VolumePotential'; scope = 'Actual convolution exists for every compact vector L2 current; finite local bound; locally integrable potential; distributional volume formula and additivity'; boundedDyadicL2OperatorVerified = $false },
            @{ module = 'PrescribedExtinction.StaticFourier'; scope = 'Explicit static Fourier multiplier is an L2 contraction and has zero imaginary quadratic form'; identificationWithNewtonVolumePotentialVerified = $false }
        )
        unverifiedDependencies = @('3D outgoing Maxwell existence and uniqueness',
            'Scalar distributional Helmholtz fundamental-solution identity and explicit Hessian principal-value/contact formula',
            'Identification of the static Fourier operator with the distributional Newton volume operator',
            'Dynamic remainder kernel, Schur bound and bounded L2 realization/restriction of the full dyadic operator',
            'Volume representation equivalence to weak Maxwell, regularity and Silver-Muller radiation',
            'Full radiation identity, optical theorem, reciprocity and power balance',
            'Uniform inverse and sin-squared response factorization',
            'Uniform aperture localization including grazing singularities and all angular channels',
            'Planar construction and normalized zero-angle / zero-plate-loss limits',
            'First exact-extinction bracket and physical continuity',
            'Positive-loss perturbation of solutions and second exact-extinction bracket',
            'Order of limits, constant dependencies, strict nonattainment and final assembly')
    } | ConvertTo-Json -Depth 12 | Set-Content -LiteralPath 'verification/report.json' -Encoding utf8
    Write-Output 'PARTIAL: supporting source compilation and axiom audit passed. Theorem 1.1 remains unproved.'
} finally { Pop-Location }
