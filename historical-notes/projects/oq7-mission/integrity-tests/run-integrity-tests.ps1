param(
    [string]$ProjectRoot = (Join-Path $PSScriptRoot '..\..\oq7'),
    [string]$LeanExecutable = 'C:\Users\Daniel\Documents\Codex\2026-10-09\set-up-a-local-ai-mathematical\outputs\math-research-lab\tools\lean-4.34.1-windows\bin\lean.exe'
)
$ErrorActionPreference = 'Stop'
$PSNativeCommandUseErrorActionPreference = $false
$ProjectRoot = (Resolve-Path -LiteralPath $ProjectRoot).Path
$oq7IntegrityOldLeanPath = $env:LEAN_PATH
$oq7IntegrityResults = [System.Collections.Generic.List[object]]::new()
$oq7IntegrityAllowed = @('propext', 'Classical.choice', 'Quot.sound')
$oq7IntegrityCensus = @'

run_cmd do
  let env ← Lean.getEnv
  for (name, info) in env.constants.toList do
    if name.toString.startsWith "OQ7IntegrityScratch." then
      match info with
      | .thmInfo _ =>
          Lean.logInfo m!"INTEGRITY-THEOREM {name}"
          let axioms ← Lean.collectAxioms name
          for ax in axioms do
            Lean.logInfo m!"INTEGRITY-DEPENDENCY {name} {ax}"
          Lean.logInfo m!"INTEGRITY-CENSUS-DONE {name}"
      | .axiomInfo _ => Lean.logInfo m!"INTEGRITY-AXIOM {name}"
      | _ => pure ()
'@
$oq7IntegrityCases = @(
    @{ name = 'ValidControl'; compile = $true; accepted = $true; required = @() },
    @{ name = 'InvalidProof'; compile = $false; accepted = $false; required = @('CompilerRejected') },
    @{ name = 'SorryAdmission'; compile = $true; accepted = $false; required = @('DisallowedSourceSyntax', 'ForbiddenTransitiveAxiom') },
    @{ name = 'AdmitAdmission'; compile = $true; accepted = $false; required = @('DisallowedSourceSyntax', 'ForbiddenTransitiveAxiom') },
    @{ name = 'TransitiveAxiom'; compile = $true; accepted = $false; required = @('DeclaredMathematicalAxiom', 'ForbiddenTransitiveAxiom') },
    @{ name = 'UnusedAxiom'; compile = $true; accepted = $false; required = @('DeclaredMathematicalAxiom') }
)

try {
    $oq7IntegrityVersion = ((& $LeanExecutable --version) | Out-String).Trim()
    if ($LASTEXITCODE -ne 0 -or $oq7IntegrityVersion -notmatch 'version 4\.34\.1,' -or
        $oq7IntegrityVersion -notmatch 'commit 5045d0056413266e57c625dcd7c365b10e377c52') {
        throw 'This harness requires the pinned Lean 4.34.1 compiler and exact release commit.'
    }
    $oq7IntegrityReport = Get-Content -LiteralPath (Join-Path $ProjectRoot 'verification/report.json') -Raw | ConvertFrom-Json
    $oq7IntegrityOriginalHashRecords = @($oq7IntegrityReport.sourceHashes) + @($oq7IntegrityReport.configurationHashes)
    foreach ($oq7IntegrityRecord in $oq7IntegrityOriginalHashRecords) {
        if ((Get-FileHash -LiteralPath (Join-Path $ProjectRoot $oq7IntegrityRecord.file) -Algorithm SHA256).Hash -ne $oq7IntegrityRecord.sha256) {
            throw "Existing verified source/configuration changed before tests: $($oq7IntegrityRecord.file)"
        }
    }
    $oq7IntegrityManifest = Get-Content -LiteralPath (Join-Path $ProjectRoot 'lake-manifest.json') -Raw | ConvertFrom-Json
    $oq7IntegrityPaths = @((Join-Path $ProjectRoot '.lake/build/lib/lean'))
    foreach ($oq7IntegrityPackage in $oq7IntegrityManifest.packages) {
        $oq7IntegrityPaths += Join-Path $ProjectRoot ('.lake/packages/' + $oq7IntegrityPackage.name + '/.lake/build/lib/lean')
    }
    # Some manifest entries are Lake-only packages and need no compiled import library.
    # Require the actual target and Mathlib libraries; no missing library is built here.
    foreach ($oq7IntegrityPath in @($oq7IntegrityPaths[0],
        (Join-Path $ProjectRoot '.lake/packages/mathlib/.lake/build/lib/lean'))) {
        if (-not (Test-Path -LiteralPath $oq7IntegrityPath -PathType Container)) {
            throw "Read-only required compiled library is unavailable: $oq7IntegrityPath"
        }
    }
    $oq7IntegrityAbsentLibraries = @($oq7IntegrityPaths | Where-Object {
        -not (Test-Path -LiteralPath $_ -PathType Container)
    })
    $env:LEAN_PATH = $oq7IntegrityPaths -join [IO.Path]::PathSeparator
    New-Item -ItemType Directory -Force -Path (Join-Path $PSScriptRoot 'generated'), (Join-Path $PSScriptRoot 'logs') | Out-Null
    Push-Location $PSScriptRoot
    try {
        foreach ($oq7IntegrityCase in $oq7IntegrityCases) {
            $oq7IntegrityFixture = Join-Path $PSScriptRoot ('fixtures/' + $oq7IntegrityCase.name + '.lean')
            $oq7IntegritySource = Get-Content -LiteralPath $oq7IntegrityFixture -Raw
            $oq7IntegrityScratch = Join-Path $PSScriptRoot ('generated/' + $oq7IntegrityCase.name + '.lean')
            [IO.File]::WriteAllText($oq7IntegrityScratch, $oq7IntegritySource + $oq7IntegrityCensus, [Text.UTF8Encoding]::new($false))
            $oq7IntegrityOutput = ((& $LeanExecutable ('--root=' + $PSScriptRoot) $oq7IntegrityScratch 2>&1) | Out-String)
            $oq7IntegrityExit = $LASTEXITCODE
            [IO.File]::WriteAllText((Join-Path $PSScriptRoot ('logs/' + $oq7IntegrityCase.name + '.log')), $oq7IntegrityOutput, [Text.UTF8Encoding]::new($false))
            $oq7IntegrityReasons = [System.Collections.Generic.List[string]]::new()
            if ($oq7IntegrityExit -ne 0) { $oq7IntegrityReasons.Add('CompilerRejected') }
            # This supplemental syntax gate matches the preserved project's conservative gate.
            # The kernel census and transitive whitelist remain independent of this regex.
            $oq7IntegrityCode = [regex]::Replace($oq7IntegritySource, '(?s)/-.*?-/', '')
            $oq7IntegrityCode = [regex]::Replace($oq7IntegrityCode, '(?m)--[^\r\n]*', '')
            if ($oq7IntegrityCode -match '\b(sorry|admit|axiom|native_decide)\b|debug\.skipKernelTC|decide\s*\+native|implemented_by') {
                $oq7IntegrityReasons.Add('DisallowedSourceSyntax')
            }
            $oq7IntegrityDeclaredAxioms = @([regex]::Matches($oq7IntegrityOutput, 'INTEGRITY-AXIOM\s+(\S+)') | ForEach-Object { $_.Groups[1].Value } | Sort-Object -Unique)
            if ($oq7IntegrityDeclaredAxioms.Count -gt 0) { $oq7IntegrityReasons.Add('DeclaredMathematicalAxiom') }
            $oq7IntegrityDependencies = @([regex]::Matches($oq7IntegrityOutput, 'INTEGRITY-DEPENDENCY\s+(\S+)\s+(\S+)') | ForEach-Object { $_.Groups[2].Value } | Sort-Object -Unique)
            $oq7IntegrityForbidden = @($oq7IntegrityDependencies | Where-Object { $_ -notin $oq7IntegrityAllowed })
            if ($oq7IntegrityForbidden.Count -gt 0) { $oq7IntegrityReasons.Add('ForbiddenTransitiveAxiom') }
            $oq7IntegrityTheorems = @([regex]::Matches($oq7IntegrityOutput, 'INTEGRITY-THEOREM\s+(\S+)') | ForEach-Object { $_.Groups[1].Value } | Sort-Object -Unique)
            $oq7IntegrityCompleted = @([regex]::Matches($oq7IntegrityOutput, 'INTEGRITY-CENSUS-DONE\s+(\S+)') | ForEach-Object { $_.Groups[1].Value } | Sort-Object -Unique)
            if ($oq7IntegrityExit -eq 0 -and ($oq7IntegrityTheorems.Count -eq 0 -or
                @($oq7IntegrityTheorems | Where-Object { $_ -notin $oq7IntegrityCompleted }).Count -gt 0)) {
                $oq7IntegrityReasons.Add('MissingKernelCensus')
            }
            $oq7IntegrityAccepted = $oq7IntegrityReasons.Count -eq 0
            $oq7IntegrityPassed = (($oq7IntegrityExit -eq 0) -eq $oq7IntegrityCase.compile) -and
                ($oq7IntegrityAccepted -eq $oq7IntegrityCase.accepted) -and
                (@($oq7IntegrityCase.required | Where-Object { $_ -notin $oq7IntegrityReasons }).Count -eq 0)
            $oq7IntegrityResults.Add([ordered]@{
                case = $oq7IntegrityCase.name; compilerExitCode = $oq7IntegrityExit
                compilerSuccessExpected = $oq7IntegrityCase.compile; expectedAuditAcceptance = $oq7IntegrityCase.accepted
                actualAuditAcceptance = $oq7IntegrityAccepted; detectedReasons = @($oq7IntegrityReasons)
                declaredAxioms = $oq7IntegrityDeclaredAxioms; transitiveAxioms = $oq7IntegrityDependencies
                forbiddenTransitiveAxioms = $oq7IntegrityForbidden; kernelTheorems = $oq7IntegrityTheorems
                expectationMet = $oq7IntegrityPassed
                fixtureSHA256 = (Get-FileHash -LiteralPath $oq7IntegrityFixture -Algorithm SHA256).Hash
                generatedSHA256 = (Get-FileHash -LiteralPath $oq7IntegrityScratch -Algorithm SHA256).Hash
                log = 'logs/' + $oq7IntegrityCase.name + '.log'
            })
        }
    } finally { Pop-Location }
    $oq7IntegrityChanged = @($oq7IntegrityOriginalHashRecords | Where-Object {
        (Get-FileHash -LiteralPath (Join-Path $ProjectRoot $_.file) -Algorithm SHA256).Hash -ne $_.sha256
    } | ForEach-Object { $_.file })
    $oq7IntegritySuccess = @($oq7IntegrityResults | Where-Object { -not $_.expectationMet }).Count -eq 0 -and $oq7IntegrityChanged.Count -eq 0
    [ordered]@{
        testedAtUTC = [DateTime]::UtcNow.ToString('o'); lean = $oq7IntegrityVersion
        projectRootReadOnly = $ProjectRoot; dependencyMode = 'Existing compiled libraries on LEAN_PATH; no lake build and no output .olean files'
        absentUnusedManifestLibraryPaths = $oq7IntegrityAbsentLibraries
        allowedFoundationAxioms = $oq7IntegrityAllowed; originalHashCount = $oq7IntegrityOriginalHashRecords.Count
        changedOriginalFiles = $oq7IntegrityChanged; allExpectedOutcomesObserved = $oq7IntegritySuccess
        tests = @($oq7IntegrityResults)
    } | ConvertTo-Json -Depth 10 | Set-Content -LiteralPath (Join-Path $PSScriptRoot 'results.json') -Encoding utf8
    $oq7IntegrityResults | ForEach-Object { Write-Output ($_.case + ': expectationMet=' + $_.expectationMet + ', accepted=' + $_.actualAuditAcceptance + ', compilerExit=' + $_.compilerExitCode) }
    if (-not $oq7IntegritySuccess) { throw 'Integrity test expectations failed; inspect results.json and logs.' }
} finally { $env:LEAN_PATH = $oq7IntegrityOldLeanPath }
