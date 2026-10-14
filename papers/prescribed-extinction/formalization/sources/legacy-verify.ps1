param([switch]$Clean, [string]$Milestone)
$ErrorActionPreference = 'Stop'
$oq7PinnedBin = 'C:\Users\Daniel\Documents\Codex\2026-10-09\set-up-a-local-ai-mathematical\outputs\math-research-lab\tools\lean-4.34.1-windows\bin'
if (Test-Path -LiteralPath (Join-Path $oq7PinnedBin 'lake.exe')) {
    $env:PATH = $oq7PinnedBin + ';' + $env:PATH
}
Push-Location $PSScriptRoot
try {
    New-Item -ItemType Directory -Force -Path 'verification' | Out-Null
    $oq7Version = ((& lean --version) | Out-String).Trim()
    if ($LASTEXITCODE -ne 0 -or $oq7Version -notmatch 'version 4\.34\.1,' -or
        $oq7Version -notmatch 'commit 5045d0056413266e57c625dcd7c365b10e377c52') {
        throw 'Compiler differs from the pinned Lean release.'
    }
    $oq7Sources = @(Get-ChildItem -LiteralPath 'OQ7' -Filter '*.lean' | Sort-Object Name)
    $oq7Names = [System.Collections.Generic.List[string]]::new()
    foreach ($oq7Source in $oq7Sources) {
        $oq7Text = Get-Content -LiteralPath $oq7Source.FullName -Raw
        $oq7Code = [regex]::Replace($oq7Text, '(?s)/-.*?-/', '')
        $oq7Code = [regex]::Replace($oq7Code, '(?m)--[^\r\n]*', '')
        # A conservative source gate, complemented by actual transitive axiom reports.
        if ($oq7Code -match '\b(sorry|admit|axiom|native_decide)\b|debug\.skipKernelTC|decide\s*\+native|implemented_by') {
            throw "Disallowed proof mechanism in $($oq7Source.Name)"
        }
        $oq7NamespaceMatches = [regex]::Matches($oq7Code, '(?m)^namespace\s+([A-Za-z0-9_.]+)\s*$')
        if ($oq7NamespaceMatches.Count -ne 1) {
            throw "Update the audit enumerator for nested namespaces in $($oq7Source.Name)"
        }
        $oq7Namespace = $oq7NamespaceMatches[0].Groups[1].Value
        # Preserve Unicode Lean identifiers (including subscripts), and include attributed theorems.
        foreach ($oq7Declaration in [regex]::Matches($oq7Code, '(?m)^\s*(?:@\[[^\]\r\n]*\]\s*)*(?:theorem|lemma)\s+([^\s:({\[]+)')) {
            $oq7Names.Add($oq7Namespace + '.' + $oq7Declaration.Groups[1].Value)
        }
    }
    if ($oq7Names.Count -eq 0) { throw 'No theorem declarations found.' }
    if ($Clean) {
        # Lake cleans only this project library; inherited package caches remain reusable.
        & lake clean oq7 2>&1 | Set-Content -LiteralPath 'verification/clean.log' -Encoding utf8
        if ($LASTEXITCODE -ne 0) { throw 'Lake clean failed.' }
    }
    & lake build 2>&1 | Set-Content -LiteralPath 'verification/build.log' -Encoding utf8
    if ($LASTEXITCODE -ne 0) { throw 'Lake build failed; see verification/build.log.' }
    # Enumerate actual kernel theorem constants independently of the source declaration scanner.
    & lake env lean 'verification/Inventory.lean' 2>&1 | Set-Content -LiteralPath 'verification/inventory.log' -Encoding utf8
    if ($LASTEXITCODE -ne 0) { throw 'Kernel declaration inventory failed.' }
    $oq7InventoryLog = Get-Content -LiteralPath 'verification/inventory.log' -Raw
    if ($oq7InventoryLog -match 'OQ7-AUDIT-AXIOM') { throw 'A mathematical axiom was declared in OQ7.' }
    $oq7KernelNames = @([regex]::Matches($oq7InventoryLog, 'OQ7-AUDIT-THEOREM\s+(\S+)') |
        ForEach-Object { $_.Groups[1].Value } | Sort-Object -Unique)
    foreach ($oq7Name in $oq7Names) {
        if ($oq7Name -notin $oq7KernelNames) { throw "Source declaration missing from imported kernel environment: $oq7Name" }
    }
    $oq7Statements = @('import OQ7', 'set_option pp.universes true', 'set_option pp.explicit true',
        'set_option pp.coercions true', 'set_option pp.notation false', '') +
        @($oq7Names | ForEach-Object { '#check @' + $_ })
    $oq7Statements | Set-Content -LiteralPath 'verification/Statements.lean' -Encoding utf8
    & lake env lean 'verification/Statements.lean' 2>&1 | Set-Content -LiteralPath 'verification/statements.log' -Encoding utf8
    if ($LASTEXITCODE -ne 0) { throw 'Exact theorem statement export failed.' }
    $oq7Audit = @('import OQ7', '') + @($oq7KernelNames | ForEach-Object { '#print axioms ' + $_ })
    $oq7Audit += @('', '#print OQ7.Theorem51Statement')
    $oq7Theorem51Proof = $null
    if ('OQ7.theorem51' -in $oq7KernelNames) {
        # Check the final proof against the exact saved proposition, without extra hypotheses.
        $oq7Audit += @('', 'example (p : OQ7.PhysicalParameters) : OQ7.Theorem51Statement p := OQ7.theorem51 p')
        $oq7Theorem51Proof = 'OQ7.theorem51'
    }
    $oq7Audit | Set-Content -LiteralPath 'verification/Audit.lean' -Encoding utf8
    & lake env lean 'verification/Audit.lean' 2>&1 | Set-Content -LiteralPath 'verification/axioms.log' -Encoding utf8
    if ($LASTEXITCODE -ne 0) { throw 'Axiom audit failed; see verification/axioms.log.' }
    $oq7Log = Get-Content -LiteralPath 'verification/axioms.log' -Raw
    $oq7Allowed = @('propext', 'Classical.choice', 'Quot.sound')
    foreach ($oq7Name in $oq7KernelNames) {
        $oq7Pattern = "'" + [regex]::Escape($oq7Name) + "' depends on axioms: \[([^\]]*)\]"
        $oq7Match = [regex]::Match($oq7Log, $oq7Pattern)
        if (-not $oq7Match.Success) {
            $oq7EmptyPattern = "'" + [regex]::Escape($oq7Name) + "' does not depend on any axioms"
            if ($oq7Log -notmatch $oq7EmptyPattern) { throw "Missing axiom report: $oq7Name" }
        } else {
            foreach ($oq7Axiom in $oq7Match.Groups[1].Value.Split(',')) {
                if ($oq7Axiom.Trim() -notin $oq7Allowed) { throw "Unexpected axiom for ${oq7Name}: $oq7Axiom" }
            }
        }
    }
    $oq7Pins = Get-Content -LiteralPath 'lake-manifest.json' -Raw | ConvertFrom-Json
    $oq7Mathlib = $oq7Pins.packages | Where-Object { $_.name -eq 'mathlib' }
    $oq7ActualRev = (& git -C '.lake/packages/mathlib' rev-parse HEAD).Trim()
    if ($LASTEXITCODE -ne 0 -or $oq7ActualRev -ne $oq7Mathlib.rev) { throw 'Mathlib revision differs from manifest.' }
    $oq7Dependencies = @()
    foreach ($oq7Package in $oq7Pins.packages) {
        $oq7PackagePath = Join-Path '.lake/packages' $oq7Package.name
        $oq7PackageRev = (& git -C $oq7PackagePath rev-parse HEAD).Trim()
        if ($LASTEXITCODE -ne 0 -or $oq7PackageRev -ne $oq7Package.rev) {
            throw "Dependency revision differs from manifest: $($oq7Package.name)"
        }
        $oq7PackageDirty = @(& git -C $oq7PackagePath status --porcelain --untracked-files=no)
        if ($LASTEXITCODE -ne 0 -or $oq7PackageDirty.Count -ne 0) {
            throw "Tracked dependency source is modified: $($oq7Package.name)"
        }
        $oq7Dependencies += @{ name = $oq7Package.name; revision = $oq7PackageRev; trackedSourceClean = $true }
    }
    $oq7Hashes = @($oq7Sources | ForEach-Object {
        @{ file = 'OQ7/' + $_.Name; sha256 = (Get-FileHash -LiteralPath $_.FullName -Algorithm SHA256).Hash }
    })
    [ordered]@{
        verifiedAtUTC = [DateTime]::UtcNow.ToString('o')
        lean = $oq7Version
        mathlibCommit = $oq7ActualRev
        lakeBuildPassed = $true
        cleanProjectBuild = [bool]$Clean
        theoremCount = $oq7Names.Count
        theoremNames = @($oq7Names)
        kernelTheoremConstantCount = $oq7KernelNames.Count
        kernelTheoremNames = $oq7KernelNames
        exactStatements = 'verification/statements.log'
        dependencyRevisions = $oq7Dependencies
        configurationHashes = @(@('OQ7.lean', 'lakefile.toml', 'lake-manifest.json', 'lean-toolchain', 'verify.ps1',
            'verification/Inventory.lean') | ForEach-Object {
                @{ file = $_; sha256 = (Get-FileHash -LiteralPath $_ -Algorithm SHA256).Hash }
            })
        allowedFoundationAxioms = $oq7Allowed
        sourceHashes = $oq7Hashes
        theorem51Status = $(if ($oq7Theorem51Proof) { 'Kernel verified for every original PhysicalParameters value.' } else { 'Statement defined; no proof of Theorem51Statement is claimed.' })
        theorem51Proof = $oq7Theorem51Proof
    } | ConvertTo-Json -Depth 8 | Set-Content -LiteralPath 'verification/report.json' -Encoding utf8
    if ($Milestone) {
        if ($Milestone -notmatch '^[a-z0-9-]+$') { throw 'Milestone must use lowercase letters, digits, and hyphens.' }
        $oq7Snapshot = Join-Path 'verification/milestones' $Milestone
        New-Item -ItemType Directory -Force -Path $oq7Snapshot | Out-Null
        foreach ($oq7File in @('report.json','build.log','axioms.log','Audit.lean','inventory.log','Inventory.lean',
            'statements.log','Statements.lean','clean.log')) {
            $oq7SourceLog = Join-Path 'verification' $oq7File
            if (Test-Path -LiteralPath $oq7SourceLog) {
                Copy-Item -LiteralPath $oq7SourceLog -Destination (Join-Path $oq7Snapshot $oq7File) -Force
            }
        }
    }
    Write-Output "PASS: lake build and axiom audit for $($oq7Names.Count) theorems."
} finally {
    Pop-Location
}
