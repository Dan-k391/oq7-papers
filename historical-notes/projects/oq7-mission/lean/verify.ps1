param(
    [switch]$Clean,
    [string]$PinnedBin = 'C:\Users\Daniel\Documents\Codex\2026-10-09\set-up-a-local-ai-mathematical\outputs\math-research-lab\tools\lean-4.34.1-windows\bin',
    [string]$ExistingProject = (Join-Path $PSScriptRoot '..\..\oq7'),
    [string]$PythonExecutable = 'C:\Users\Daniel\.cache\codex-runtimes\codex-primary-runtime\dependencies\python\python.exe'
)
$ErrorActionPreference = 'Stop'
$PSNativeCommandUseErrorActionPreference = $false
$missionOldPath = $env:PATH
$missionAllowed = @('propext', 'Classical.choice', 'Quot.sound')
$ExistingProject = (Resolve-Path -LiteralPath $ExistingProject).Path
$missionOriginalReportPath = Join-Path $ExistingProject 'verification/report.json'
$missionOriginalReport = Get-Content -LiteralPath $missionOriginalReportPath -Raw | ConvertFrom-Json
$missionOriginalHashes = @($missionOriginalReport.sourceHashes) + @($missionOriginalReport.configurationHashes)

function Assert-OriginalPreserved {
    foreach ($record in $missionOriginalHashes) {
        $path = Join-Path $ExistingProject $record.file
        if ((Get-FileHash -LiteralPath $path -Algorithm SHA256).Hash -ne $record.sha256) {
            throw "Original source/configuration differs from its saved successful report: $($record.file)"
        }
    }
}

Push-Location $PSScriptRoot
try {
    Assert-OriginalPreserved
    New-Item -ItemType Directory -Force -Path 'verification' | Out-Null
    $env:PATH = $PinnedBin + ';' + $env:PATH
    $missionVersion = ((& lean --version) | Out-String).Trim()
    if ($LASTEXITCODE -ne 0 -or $missionVersion -notmatch 'version 4\.34\.1,' -or
        $missionVersion -notmatch 'commit 5045d0056413266e57c625dcd7c365b10e377c52') {
        throw 'Compiler differs from the exact pinned Lean release.'
    }
    $missionSources = @(Get-ChildItem -LiteralPath 'OQ7Mission' -Filter '*.lean' | Sort-Object Name)
    $missionDeclarations = [System.Collections.Generic.List[object]]::new()
    $missionTheoremNames = [System.Collections.Generic.List[string]]::new()
    foreach ($source in $missionSources) {
        $text = Get-Content -LiteralPath $source.FullName -Raw
        # Conservative lexical screen, complemented by the actual kernel census/axiom audit.
        $code = [regex]::Replace([regex]::Replace($text, '(?s)/-.*?-/', ''), '(?m)--[^\r\n]*', '')
        if ($code -match '\b(sorry|admit|axiom|native_decide)\b|debug\.skipKernelTC|decide\s*\+native|implemented_by') {
            throw "Disallowed proof mechanism in $($source.Name)"
        }
        $namespaces = [regex]::Matches($code, '(?m)^namespace\s+([A-Za-z0-9_.]+)\s*$')
        if ($namespaces.Count -ne 1) { throw "Update the scanner for nested namespaces in $($source.Name)" }
        $namespace = $namespaces[0].Groups[1].Value
        if ($namespace -ne 'OQ7Mission' -and -not $namespace.StartsWith('OQ7Mission.')) {
            throw "Wrong project namespace in $($source.Name)"
        }
        foreach ($declaration in [regex]::Matches($code, '(?m)^\s*(?:@\[[^\]\r\n]*\]\s*)*(private\s+)?(theorem|lemma|def|abbrev|structure|inductive)\s+([^\s:({\[]+)')) {
            $kind = $declaration.Groups[2].Value
            $name = $namespace + '.' + $declaration.Groups[3].Value
            $isPrivate = $declaration.Groups[1].Success
            $missionDeclarations.Add(@{ name = $name; kind = $kind; private = $isPrivate; file = 'OQ7Mission/' + $source.Name })
            if (-not $isPrivate -and $kind -in @('theorem', 'lemma')) { $missionTheoremNames.Add($name) }
        }
    }
    if ($missionTheoremNames.Count -eq 0) { throw 'No authored theorem declarations found.' }
    $missionSourceHashesBefore = @($missionSources | ForEach-Object {
        @{ file = 'OQ7Mission/' + $_.Name; sha256 = (Get-FileHash -LiteralPath $_.FullName -Algorithm SHA256).Hash }
    })
    if ($Clean) {
        # Only the new root package is cleaned; all dependency/source checkouts are reused.
        $missionCleanOutput = @(& lake clean oq7Mission 2>&1)
        $missionCleanExit = $LASTEXITCODE
        Set-Content -LiteralPath 'verification/clean.log' -Value ($missionCleanOutput -join [Environment]::NewLine) -Encoding utf8
        if ($missionCleanExit -ne 0) { throw 'Root-project clean failed.' }
    }
    & lake build 2>&1 | Set-Content -LiteralPath 'verification/build.log' -Encoding utf8
    if ($LASTEXITCODE -ne 0) { throw 'New project build failed; see verification/build.log.' }
    & lake env lean 'verification/Inventory.lean' 2>&1 | Set-Content -LiteralPath 'verification/inventory.log' -Encoding utf8
    if ($LASTEXITCODE -ne 0) { throw 'Actual kernel census/dependency export failed.' }
    $missionInventory = Get-Content -LiteralPath 'verification/inventory.log' -Raw
    $missionKernelNames = @([regex]::Matches($missionInventory, 'OQ7MISSION-NODE\s+\S+\s+(\S+)') |
        ForEach-Object { $_.Groups[1].Value } | Sort-Object -Unique)
    $missionKernelTheorems = @([regex]::Matches($missionInventory, 'OQ7MISSION-NODE\s+theorem\s+(\S+)') |
        ForEach-Object { $_.Groups[1].Value } | Sort-Object -Unique)
    if ($missionInventory -match 'OQ7MISSION-NODE\s+axiom\s+') { throw 'New project declares an axiom.' }
    foreach ($declaration in $missionDeclarations) {
        if ($declaration.private) {
            $candidates = @($missionKernelNames | Where-Object {
                $_.StartsWith('_private.OQ7Mission.') -and $_.EndsWith('.' + $declaration.name)
            })
            if ($candidates.Count -ne 1) { throw "Private source name did not resolve uniquely: $($declaration.name)" }
            $declaration.name = $candidates[0]
        }
        if ($declaration.name -notin $missionKernelNames) { throw "Source declaration absent from kernel: $($declaration.name)" }
    }
    foreach ($name in $missionTheoremNames) {
        if ($name -notin $missionKernelTheorems) { throw "Source theorem is not a kernel theorem: $name" }
    }
    & lake env lean 'verification/Statements.lean' 2>&1 | Set-Content -LiteralPath 'verification/statements.log' -Encoding utf8
    if ($LASTEXITCODE -ne 0) { throw 'Complete exact declaration type export failed.' }
    $missionStatementLog = Get-Content -LiteralPath 'verification/statements.log' -Raw
    foreach ($name in $missionKernelNames) {
        if ($missionStatementLog -notmatch ('OQ7MISSION-TYPE ' + [regex]::Escape($name) + ' :')) {
            throw "Missing exact kernel declaration type: $name"
        }
    }
    & lake env lean 'verification/Audit.lean' 2>&1 | Set-Content -LiteralPath 'verification/axioms.log' -Encoding utf8
    if ($LASTEXITCODE -ne 0) { throw 'Transitive axiom audit failed.' }
    $missionAxiomLog = Get-Content -LiteralPath 'verification/axioms.log' -Raw
    foreach ($name in $missionKernelNames) {
        $pattern = "'" + [regex]::Escape($name) + "' depends on axioms: \[([^\]]*)\]"
        $match = [regex]::Match($missionAxiomLog, $pattern)
        if (-not $match.Success) {
            $emptyPattern = "'" + [regex]::Escape($name) + "' does not depend on any axioms"
            if ($missionAxiomLog -notmatch $emptyPattern) { throw "Missing transitive axiom report: $name" }
        } else {
            foreach ($axiomName in $match.Groups[1].Value.Split(',')) {
                if ($axiomName.Trim() -notin $missionAllowed) { throw "Unexpected transitive axiom for ${name}: $axiomName" }
            }
        }
    }
    & lake env lean 'verification/FullDependencies.lean' 2>&1 |
        Set-Content -LiteralPath 'verification/full-dependencies.log' -Encoding utf8
    if ($LASTEXITCODE -ne 0) { throw 'Full new-result proof/type dependency traversal failed.' }
    # Import the preserved original build only to read theorem51's actual proof dependencies.
    $missionExistingGraphSource = Join-Path $PSScriptRoot 'verification/ExistingDependencies.lean'
    $missionExistingGraphLog = Join-Path $PSScriptRoot 'verification/existing-dependencies.log'
    Push-Location $ExistingProject
    try {
        & lake env lean $missionExistingGraphSource 2>&1 | Set-Content -LiteralPath $missionExistingGraphLog -Encoding utf8
        if ($LASTEXITCODE -ne 0) { throw 'Existing theorem51 dependency traversal failed.' }
        & lake env lean (Join-Path $PSScriptRoot 'verification/FullExistingDependencies.lean') 2>&1 |
            Set-Content -LiteralPath (Join-Path $PSScriptRoot 'verification/full-existing-dependencies.log') -Encoding utf8
        if ($LASTEXITCODE -ne 0) { throw 'Full existing theorem51 dependency traversal failed.' }
    } finally { Pop-Location }
    & $PythonExecutable 'verification/export-dependencies.py' 2>&1 |
        Set-Content -LiteralPath 'verification/dependency-export.log' -Encoding utf8
    if ($LASTEXITCODE -ne 0) { throw 'Dependency graph JSON export failed.' }
    $missionPins = Get-Content -LiteralPath 'lake-manifest.json' -Raw | ConvertFrom-Json
    $missionDependencies = @()
    foreach ($package in $missionPins.packages) {
        $packagePath = Join-Path '.lake/packages' $package.name
        $actualRev = (& git --no-optional-locks -C $packagePath rev-parse HEAD).Trim()
        if ($LASTEXITCODE -ne 0 -or $actualRev -ne $package.rev) { throw "Pinned dependency differs: $($package.name)" }
        $dirty = @(& git --no-optional-locks -C $packagePath status --porcelain --untracked-files=no)
        if ($LASTEXITCODE -ne 0 -or $dirty.Count -ne 0) { throw "Tracked dependency source modified: $($package.name)" }
        $missionDependencies += @{ name = $package.name; revision = $actualRev; trackedSourceClean = $true }
    }
    Assert-OriginalPreserved
    foreach ($record in $missionSourceHashesBefore) {
        if ((Get-FileHash -LiteralPath $record.file -Algorithm SHA256).Hash -ne $record.sha256) {
            throw "New source changed during final verification: $($record.file)"
        }
    }
    $missionConfigFiles = @('OQ7Mission.lean', 'lakefile.toml', 'lake-manifest.json', 'lean-toolchain',
        'verify.ps1', 'bootstrap-cache.ps1', 'verification/Inventory.lean',
        'verification/ExistingDependencies.lean', 'verification/export-dependencies.py',
        'verification/Statements.lean', 'verification/Audit.lean',
        'verification/FullDependencies.lean', 'verification/FullExistingDependencies.lean')
    $missionEvidenceFiles = @('build.log', 'inventory.log', 'statements.log', 'axioms.log',
        'Audit.lean', 'Statements.lean', 'existing-dependencies.log', 'dependencies.json',
        'theorem51-dependencies.json', 'dependency-export.log')
    $missionEvidenceFiles += @('full-dependencies.log', 'full-existing-dependencies.log',
        'full-dependencies.json', 'full-theorem51-dependencies.json')
    if ($Clean) { $missionEvidenceFiles += 'clean.log' }
    [ordered]@{
        verifiedAtUTC = [DateTime]::UtcNow.ToString('o')
        lean = $missionVersion
        mathlibCommit = ($missionDependencies | Where-Object { $_.name -eq 'mathlib' }).revision
        lakeBuildPassed = $true
        cleanProjectBuild = [bool]$Clean
        authoredTheoremCount = $missionTheoremNames.Count
        authoredTheoremNames = @($missionTheoremNames)
        privateAuthoredTheoremCount = @($missionDeclarations | Where-Object { $_.private -and $_.kind -in @('theorem', 'lemma') }).Count
        sourceDeclarationCount = $missionDeclarations.Count
        sourceDeclarations = @($missionDeclarations)
        kernelTheoremConstantCount = $missionKernelTheorems.Count
        kernelTheoremNames = $missionKernelTheorems
        kernelConstantCount = $missionKernelNames.Count
        kernelConstantNames = $missionKernelNames
        exactStatements = 'verification/statements.log'
        proofAndTypeDependencies = 'verification/dependencies.json'
        originalTheorem51Dependencies = 'verification/theorem51-dependencies.json'
        fullMainResultDependencies = 'verification/full-dependencies.json'
        fullOriginalTheorem51Dependencies = 'verification/full-theorem51-dependencies.json'
        dependencyClosureScope = 'All own-namespace/private constants have namespace closures; the eight generic results, rational certificate/SDP upper bound/attainment/square corollary and original theorem51 additionally have full recursive kernel type/proof expression closures including Mathlib/Lean.'
        transitiveAxiomCoverage = 'Every actual OQ7Mission kernel constant, including private helpers, definitions and generated constants.'
        declaredMathematicalAxiomCount = 0
        allowedFoundationAxioms = $missionAllowed
        dependencyRevisions = $missionDependencies
        sourceHashes = $missionSourceHashesBefore
        configurationHashes = @($missionConfigFiles | ForEach-Object {
            @{ file = $_; sha256 = (Get-FileHash -LiteralPath $_ -Algorithm SHA256).Hash }
        })
        evidenceHashes = @($missionEvidenceFiles | ForEach-Object {
            @{ file = 'verification/' + $_; sha256 = (Get-FileHash -LiteralPath (Join-Path 'verification' $_) -Algorithm SHA256).Hash }
        })
        originalProjectSourceAndConfigurationHashCount = $missionOriginalHashes.Count
        originalProjectSourceAndConfigurationUnchanged = $true
        originalSuccessfulReportSHA256 = (Get-FileHash -LiteralPath $missionOriginalReportPath -Algorithm SHA256).Hash
        manuscriptStatus = 'PARTIALLY FORMALIZED: algebraic localization/work components and exact finite-dimensional rational certificate only; physical Maxwell operator estimates, global A7.1 and compact cross-section theorems are not proved here.'
    } | ConvertTo-Json -Depth 10 | Set-Content -LiteralPath 'verification/report.json' -Encoding utf8
    Write-Output "PASS: $($missionTheoremNames.Count) authored theorems, $($missionKernelTheorems.Count) kernel theorem constants, $($missionKernelNames.Count) total own-namespace constants; full axiom/type coverage; original hashes preserved."
} finally {
    $env:PATH = $missionOldPath
    Pop-Location
}
