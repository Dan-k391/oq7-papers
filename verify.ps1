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
    & lake env lean verification/FourierInventory.lean 2>&1 | Set-Content -LiteralPath 'verification/inventory.log' -Encoding utf8
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
    $oq7PublicConstants = @($oq7Constants | Where-Object { -not $_.StartsWith('_private.') })
    $oq7Audit = @('import OQ7', 'import PrescribedExtinction', '') + @($oq7PublicConstants | ForEach-Object { '#print axioms ' + $_ })
    # Private canonical names contain numeric Name components and are not Lean identifiers.
    # Use the identical transitive collector invoked by Lean's #print axioms command.
    $oq7Audit += @'

run_cmd do
  let env ← Lean.getEnv
  for (name, _) in env.constants.toList do
    let s := name.toString
    if s.startsWith "_private.OQ7." || s.startsWith "_private.PrescribedExtinction." then
      let axioms ← Lean.collectAxioms name
      if axioms.isEmpty then
        Lean.logInfo m!"'{s}' does not depend on any axioms"
      else
        Lean.logInfo m!"'{s}' depends on axioms: {axioms.qsort Lean.Name.lt |>.map Lean.MessageData.ofConstName |>.toList}"
'@
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
    # The sole target correction changes analytic tests to all smooth tests.
    # Check exact bytes against the archived original, then permit only that
    # correction in earlier immutable-source comparisons. No quantifier changes.
    $oq7OriginalTargetPath = 'verification/physical-target-before-test-correction.txt'
    $oq7OriginalTargetHash = (Get-FileHash -LiteralPath $oq7OriginalTargetPath -Algorithm SHA256).Hash
    if ($oq7OriginalTargetHash -ne '071C04ED9417A1D9AC842D61B545183627E6F997C7C1899F908871608859ABF6') {
        throw 'Original physical target snapshot changed.'
    }
    $oq7OriginalTarget = [IO.File]::ReadAllText((Join-Path $PSScriptRoot $oq7OriginalTargetPath))
    $oq7CorrectedTarget = $oq7OriginalTarget.Replace('ContDiff ℝ ⊤ φ', 'ContDiff ℝ (⊤ : ℕ∞) φ')
    if ([IO.File]::ReadAllText((Join-Path $PSScriptRoot 'PrescribedExtinction/Maxwell.lean')) -cne $oq7CorrectedTarget) {
        throw 'Physical target changes exceed the documented smooth-test correction.'
    }
    function Get-OQ7PreservedSourceHash([string]$oq7SourcePath) {
        if ($oq7SourcePath.Replace('\','/') -eq 'PrescribedExtinction/Maxwell.lean') {
            return $oq7OriginalTargetHash
        }
        return (Get-FileHash -LiteralPath $oq7SourcePath -Algorithm SHA256).Hash
    }
    $oq7LegacyHashes = Get-Content -LiteralPath 'sources/legacy-source-hashes.json' -Raw | ConvertFrom-Json
    foreach ($oq7Saved in $oq7LegacyHashes) {
        if ((Get-OQ7PreservedSourceHash $oq7Saved.file) -ne $oq7Saved.sha256) {
            throw "Preserved legacy source differs: $($oq7Saved.file)"
        }
    }
    $oq7PdfHash = (Get-FileHash -LiteralPath 'sources/OQ7_prescribed_extinction_2026-10-11.pdf' -Algorithm SHA256).Hash
    $oq7PreDyadicHashes = Get-Content -LiteralPath 'sources/pre-dyadic-source-hashes.json' -Raw | ConvertFrom-Json
    foreach ($oq7Saved in $oq7PreDyadicHashes) {
        if ((Get-OQ7PreservedSourceHash $oq7Saved.file) -ne $oq7Saved.sha256) {
            throw "Preserved pre-dyadic source differs: $($oq7Saved.file)"
        }
    }
    $oq7PreviousReport = Get-Content 'verification/milestones/pre-dyadic/report.json' -Raw | ConvertFrom-Json
    $oq7PreviousRootHash = @($oq7PreviousReport.sourceHashes | Where-Object { $_.file -eq 'PrescribedExtinction.lean' })[0].sha256
    if ((Get-FileHash 'sources/pre-dyadic-PrescribedExtinction.lean' -Algorithm SHA256).Hash -ne $oq7PreviousRootHash) {
        throw 'Previous aggregate source snapshot differs.'
    }
    $oq7PreviousRoot = [IO.File]::ReadAllBytes((Join-Path $PSScriptRoot 'sources/pre-dyadic-PrescribedExtinction.lean'))
    $oq7CurrentRoot = [IO.File]::ReadAllBytes((Join-Path $PSScriptRoot 'PrescribedExtinction.lean'))
    if ($oq7CurrentRoot.Length -lt $oq7PreviousRoot.Length) { throw 'Aggregate source was truncated.' }
    for ($oq7ByteIndex = 0; $oq7ByteIndex -lt $oq7PreviousRoot.Length; $oq7ByteIndex++) {
        if ($oq7CurrentRoot[$oq7ByteIndex] -ne $oq7PreviousRoot[$oq7ByteIndex]) { throw 'Previous aggregate imports changed.' }
    }
    $oq7ContactBaseline = Get-Content 'sources/pre-contact-source-hashes.json' -Raw | ConvertFrom-Json
    foreach ($oq7Saved in $oq7ContactBaseline) {
        if ((Get-OQ7PreservedSourceHash $oq7Saved.file) -ne $oq7Saved.sha256) {
            throw "Preserved dyadic milestone source differs: $($oq7Saved.file)"
        }
    }
    $oq7ContactReport = Get-Content 'verification/milestones/pre-contact/report.json' -Raw | ConvertFrom-Json
    $oq7ContactRootHash = @($oq7ContactReport.sourceHashes | Where-Object { $_.file -eq 'PrescribedExtinction.lean' })[0].sha256
    if ((Get-FileHash 'sources/pre-contact-PrescribedExtinction.lean' -Algorithm SHA256).Hash -ne $oq7ContactRootHash) {
        throw 'Dyadic milestone aggregate snapshot differs.'
    }
    $oq7ContactRoot = [IO.File]::ReadAllBytes((Join-Path $PSScriptRoot 'sources/pre-contact-PrescribedExtinction.lean'))
    if ($oq7CurrentRoot.Length -lt $oq7ContactRoot.Length) { throw 'Aggregate source was truncated.' }
    for ($oq7ByteIndex = 0; $oq7ByteIndex -lt $oq7ContactRoot.Length; $oq7ByteIndex++) {
        if ($oq7CurrentRoot[$oq7ByteIndex] -ne $oq7ContactRoot[$oq7ByteIndex]) { throw 'Dyadic milestone imports changed.' }
    }
    $oq7PuncturedBaseline = Get-Content 'sources/pre-punctured-source-hashes.json' -Raw | ConvertFrom-Json
    foreach ($oq7Saved in $oq7PuncturedBaseline) {
        if ((Get-OQ7PreservedSourceHash $oq7Saved.file) -ne $oq7Saved.sha256) {
            throw "Preserved contact-progress module differs: $($oq7Saved.file)"
        }
    }
    $oq7PuncturedReport = Get-Content 'verification/milestones/pre-punctured/report.json' -Raw | ConvertFrom-Json
    $oq7PuncturedRootHash = @($oq7PuncturedReport.sourceHashes | Where-Object { $_.file -eq 'PrescribedExtinction.lean' })[0].sha256
    if ((Get-FileHash 'sources/pre-punctured-PrescribedExtinction.lean' -Algorithm SHA256).Hash -ne $oq7PuncturedRootHash) {
        throw 'Contact-progress aggregate snapshot differs.'
    }
    $oq7PuncturedRoot = [IO.File]::ReadAllBytes((Join-Path $PSScriptRoot 'sources/pre-punctured-PrescribedExtinction.lean'))
    if ($oq7CurrentRoot.Length -lt $oq7PuncturedRoot.Length) { throw 'Aggregate source was truncated.' }
    for ($oq7ByteIndex = 0; $oq7ByteIndex -lt $oq7PuncturedRoot.Length; $oq7ByteIndex++) {
        if ($oq7CurrentRoot[$oq7ByteIndex] -ne $oq7PuncturedRoot[$oq7ByteIndex]) { throw 'Contact-progress imports changed.' }
    }
    $oq7FourierBaseline = Get-Content 'sources/pre-fourier-source-hashes.json' -Raw | ConvertFrom-Json
    foreach ($oq7Saved in $oq7FourierBaseline) {
        if ((Get-OQ7PreservedSourceHash $oq7Saved.file) -ne $oq7Saved.sha256) {
            throw "Preserved module from commit 6874b49 differs: $($oq7Saved.file)"
        }
    }
    $oq7FourierReport = Get-Content 'verification/milestones/pre-fourier/report.json' -Raw | ConvertFrom-Json
    $oq7FourierRootHash = @($oq7FourierReport.sourceHashes | Where-Object { $_.file -eq 'PrescribedExtinction.lean' })[0].sha256
    if ((Get-FileHash 'sources/pre-fourier-PrescribedExtinction.lean' -Algorithm SHA256).Hash -ne $oq7FourierRootHash) {
        throw 'Contact-identity aggregate snapshot differs.'
    }
    $oq7FourierRoot = [IO.File]::ReadAllBytes((Join-Path $PSScriptRoot 'sources/pre-fourier-PrescribedExtinction.lean'))
    if ($oq7CurrentRoot.Length -lt $oq7FourierRoot.Length) { throw 'Aggregate source was truncated.' }
    for ($oq7ByteIndex = 0; $oq7ByteIndex -lt $oq7FourierRoot.Length; $oq7ByteIndex++) {
        if ($oq7CurrentRoot[$oq7ByteIndex] -ne $oq7FourierRoot[$oq7ByteIndex]) { throw 'Contact-identity imports changed.' }
    }
    foreach ($oq7RequiredFourier in @('OQ7Prescribed.newton_hessian_trace_distribution',
        'OQ7Prescribed.newtonTemperedHessian_scalarTest', 'OQ7Prescribed.newtonTemperedHessian_contact_apply',
        'OQ7Prescribed.newton_heat_representation', 'OQ7Prescribed.newtonHeatKernel_not_integrable_at_origin',
        'OQ7Prescribed.newton_heat_pairing_joint_integrable', 'OQ7Prescribed.newtonHeatKernel_fourier',
        'OQ7Prescribed.newton_frequency_heat_joint_integrable', 'OQ7Prescribed.newtonTempered_fourier_eq',
        'OQ7Prescribed.newtonTemperedHessian_fourier_integral',
        'OQ7Prescribed.staticMultiplierWithOriginLp_eq', 'OQ7Prescribed.newtonTemperedHessian_fourier_eq')) {
        if ($oq7RequiredFourier -notin $oq7NewKernelTheorems) { throw "Missing completed Fourier dependency: $oq7RequiredFourier" }
    }
    foreach ($oq7Required in @('OQ7Prescribed.newton_punctured_double_ibp',
        'OQ7Prescribed.newton_inner_contact_normal', 'OQ7Prescribed.newton_inner_derivative_normal',
        'OQ7Prescribed.newton_outer_boundary_vanishes', 'OQ7Prescribed.newton_contact_identity_real',
        'OQ7Prescribed.newton_hessian_contact_apply', 'OQ7Prescribed.newtonPVDistribution_apply',
        'OQ7Prescribed.newtonPVValue_continuous', 'OQ7Prescribed.newton_hessian_contact_distribution')) {
        if ($oq7Required -notin $oq7NewKernelTheorems) { throw "Missing completed contact obligation: $oq7Required" }
    }
    foreach ($oq7Saved in (Get-Content 'sources/pre-static-source-hashes.json' -Raw | ConvertFrom-Json)) {
        if ((Get-OQ7PreservedSourceHash $oq7Saved.file) -ne $oq7Saved.sha256) {
            throw "Preserved Fourier milestone source differs: $($oq7Saved.file)"
        }
    }
    $oq7StaticRoot = [IO.File]::ReadAllBytes((Join-Path $PSScriptRoot 'sources/pre-static-PrescribedExtinction.lean'))
    if ($oq7CurrentRoot.Length -lt $oq7StaticRoot.Length) { throw 'Fourier aggregate source truncated.' }
    for ($oq7ByteIndex = 0; $oq7ByteIndex -lt $oq7StaticRoot.Length; $oq7ByteIndex++) {
        if ($oq7CurrentRoot[$oq7ByteIndex] -ne $oq7StaticRoot[$oq7ByteIndex]) { throw 'Fourier aggregate imports changed.' }
    }
    foreach ($oq7Required in @('OQ7Prescribed.outgoingVolumeDistribution_zero_eq_staticFourier',
        'OQ7Prescribed.outgoingVolumeDistribution_zero_bounded_L2_realization',
        'OQ7Prescribed.fourierIntegral_L1L2_ae')) {
        if ($oq7Required -notin $oq7NewKernelTheorems) { throw "Missing physical static obligation: $oq7Required" }
    }
    foreach ($oq7Required in @('OQ7Prescribed.outgoing_dyadic_contact_identity',
        'OQ7Prescribed.outgoingVolumeDistribution_eq_staticFourier_add_remainder',
        'OQ7Prescribed.outgoingVolumeDistribution_on_ball_bounded_L2_realization',
        'OQ7Prescribed.outgoing_helmholtz_fundamental_distribution',
        'OQ7Prescribed.potentialComponent_helmholtz_L2_distribution',
        'OQ7Prescribed.outgoingVolumeDistribution_maxwell_source_L2',
        'OQ7Prescribed.outgoingVolumeDistribution_first_curl',
        'OQ7Prescribed.outgoingMagneticDistribution_second_curl',
        'OQ7Prescribed.scalarVectorConvolution_memLp_two',
        'OQ7Prescribed.outgoingGreen_first_distribution',
        'OQ7Prescribed.gradientPotential_ae_integrable_on_compact',
        'OQ7Prescribed.gradientPotential_memLp_on_compact',
        'OQ7Prescribed.potentialComponent_first_distribution',
        'OQ7Prescribed.electricVolumeField_locallySquareIntegrable',
        'OQ7Prescribed.magneticVolumeField_locallySquareIntegrable',
        'OQ7Prescribed.electricVolumeField_distribution',
        'OQ7Prescribed.magneticVolumeField_distribution',
        'OQ7Prescribed.physicalSourceFields_first_curl',
        'OQ7Prescribed.physicalSourceFields_second_curl',
        'OQ7Prescribed.HasWeakCurl.implies_analyticTestWeakCurl',
        'OQ7Prescribed.weakCurlTest_all_finite_orders',
        'OQ7Prescribed.distributionCurl_eq_implies_hasWeakCurl',
        'OQ7Prescribed.physicalSourceFields_first_weakCurl',
        'OQ7Prescribed.physicalSourceFields_second_weakCurl',
        'OQ7Prescribed.kernelMagnetic_gradient',
        'OQ7Prescribed.kernel_radiation_defect',
        'OQ7Prescribed.kernel_radiation_defect_norm_le',
        'OQ7Prescribed.displaced_kernel_radiation_norm_le',
        'OQ7Prescribed.exteriorElectric_integrable_far',
        'OQ7Prescribed.exteriorMagnetic_integrable_far',
        'OQ7Prescribed.exterior_radiation_integral_norm_le',
        'OQ7Prescribed.exteriorCurrentFields_outgoing',
        'OQ7Prescribed.dyadicGreenDistribution_apply_of_zero',
        'OQ7Prescribed.outgoingVolumeDistribution_current_dyadic_pairing',
        'OQ7Prescribed.currentDyadicTestPairing_exterior_integrable',
        'OQ7Prescribed.currentDyadicTestPairing_exterior_integral',
        'OQ7Prescribed.exteriorElectric_test_pairing',
        'OQ7Prescribed.electricExterior_component_distribution',
        'OQ7Prescribed.electricExterior_eq_ae',
        'OQ7Prescribed.magneticExterior_eq_pointwise_far',
        'OQ7Prescribed.outgoingPhysicalSourceFields',
        'OQ7Prescribed.smoothField_hasWeakCurl',
        'OQ7Prescribed.incidentElectric_first_weakCurl',
        'OQ7Prescribed.incidentMagnetic_second_weakCurl',
        'OQ7Prescribed.incidentElectric_locallySquareIntegrable',
        'OQ7Prescribed.incidentMagnetic_locallySquareIntegrable',
        'OQ7Prescribed.physicalPolarization_memLp',
        'OQ7Prescribed.physicalPolarization_vanish',
        'OQ7Prescribed.volumeTotalFields_weakMaxwell',
        'OQ7Prescribed.complex_imaginary_coercive_bijective',
        'OQ7Prescribed.complexImaginaryCoerciveEquiv_inverse_norm_le',
        'OQ7Prescribed.complexImaginaryCoerciveEquiv_inverse_imaginary_bound',
        'OQ7Prescribed.admissible_susceptibility_bounded_inverse',
        'OQ7Prescribed.compactPolarization_smooth_approximation',
        'OQ7Prescribed.outgoingPotential_contDiff',
        'OQ7Prescribed.smoothElectricSource_eq_ae',
        'OQ7Prescribed.smoothMagneticSource_eq_ae',
        'OQ7Prescribed.smoothElectricSource_curl',
        'OQ7Prescribed.smoothMagneticSource_curl',
        'OQ7Prescribed.smoothPhysicalSource_cutoff_energy',
        'OQ7Prescribed.smoothPhysicalSource_radial_energy',
        'OQ7Prescribed.exteriorMagnetic_norm_decay',
        'OQ7Prescribed.smoothPhysicalSource_work_nonneg',
        'OQ7Prescribed.physicalOutgoingVolume_work_nonneg',
        'OQ7Prescribed.compactOutgoingOperator_im_nonneg',
        'OQ7Prescribed.setSupportedL2_isClosed',
        'OQ7Prescribed.twoPieceSupportedOperator_negative_imaginary_bound',
        'OQ7Prescribed.bodyOutgoingOperator_coe',
        'OQ7Prescribed.bodyOutgoingOperator_im_nonneg',
        'OQ7Prescribed.materialBodyOperator_imaginary_coercive',
        'OQ7Prescribed.materialBodyEquiv_inverse_norm_le',
        'OQ7Prescribed.materialBodySolution_physicalVolumeEquation',
        'OQ7Prescribed.materialVolumeEquation_exists',
        'OQ7Prescribed.physicalScatteringState_exists',
        'OQ7Prescribed.materialVolumeCurrent_operator_equation',
        'OQ7Prescribed.materialVolumeEquation_unique_current',
        'OQ7Prescribed.activeInjection_inner',
        'OQ7Prescribed.activeInjection_norm',
        'OQ7Prescribed.activeMaterialOperator_imaginary_coercive',
        'OQ7Prescribed.activeMaterialEquiv_inverse_norm_le',
        'OQ7Prescribed.activePhysicalSolution_physicalVolumeEquation',
        'OQ7Prescribed.rankOnePhysicalScatteringState_exists',
        'OQ7Prescribed.activeProjectedIncident_sine_factorization',
        'OQ7Prescribed.activePhysicalSolution_sine_factorization',
        'OQ7Prescribed.normalizedActiveResponse_norm_le',
        'OQ7Prescribed.activePhysicalExtinction_work',
        'OQ7Prescribed.physicalExtinction_sine_squared_factorization',
        'OQ7Prescribed.physicalAbsorption_current_inner',
        'OQ7Prescribed.physicalVolume_work_balance',
        'OQ7Prescribed.physicalVolume_absorption_le_extinction',
        'OQ7Prescribed.activePhysicalAbsorption_work',
        'OQ7Prescribed.activeInverseMaterial_loss_integral',
        'OQ7Prescribed.physicalAbsorption_sine_squared_factorization',
        'OQ7Prescribed.displaced_dyadic_farField_error',
        'OQ7Prescribed.exteriorElectric_uniform_farField_error',
        'OQ7Prescribed.compactCurrentFarField_continuous',
        'OQ7Prescribed.volumePhysicalFarField_eq',
        'OQ7Prescribed.outgoingElectric_uniform_physical_farField_error',
        'OQ7Prescribed.exterior_poynting_farField_error',
        'OQ7Prescribed.sourceEnergyWeight_direction_integral',
        'OQ7Prescribed.smoothPhysicalSource_farField_work',
        'OQ7Prescribed.supportedFarFieldPower_continuous',
        'OQ7Prescribed.physicalOutgoingVolume_farField_work',
        'OQ7Prescribed.bodyOutgoingOperator_farField_work',
        'OQ7Prescribed.physicalVolume_Haar_energy_balance',
        'OQ7Prescribed.sphericalPoint_hasFDerivAt',
        'OQ7Prescribed.sphericalDerivative_det',
        'OQ7Prescribed.sphericalPoint_injOn',
        'OQ7Prescribed.sphericalPoint_image_ae_eq_univ',
        'OQ7Prescribed.integral_spherical_actual',
        'OQ7Prescribed.sphericalTripleEquiv_measurePreserving',
        'OQ7Prescribed.sphereArea_integral_original_angles',
        'OQ7Prescribed.physicalVolume_scattering_eq_Haar',
        'OQ7Prescribed.physicalVolume_energy_balance',
        'OQ7Prescribed.physicalVolume_scattering_nonneg',
        'OQ7Prescribed.smooth_sources_cutoff_Lorentz',
        'OQ7Prescribed.smoothPhysicalSources_radial_Lorentz',
        'OQ7Prescribed.exteriorElectric_norm_decay',
        'OQ7Prescribed.exterior_Lorentz_flux_norm_bound',
        'OQ7Prescribed.smoothPhysicalSources_Lorentz_boundary_error',
        'OQ7Prescribed.smoothPhysicalSources_reciprocity',
        'OQ7Prescribed.compactCurrents_bilinear_volume_integrable',
        'OQ7Prescribed.physicalOutgoingVolume_reciprocity',
        'OQ7Prescribed.tensor_bilinear_reciprocity',
        'OQ7Prescribed.bodySusceptibility_reciprocal',
        'OQ7Prescribed.reciprocalMaterialVolume_incident_work',
        'OQ7Prescribed.physicalVolume_extinction_reciprocity',
        'OQ7Prescribed.normalizedActiveResponse_continuous',
        'OQ7Prescribed.normalizedAbsorption_continuous',
        'OQ7Prescribed.normalizedExtinction_continuous',
        'OQ7Prescribed.normalizedExtinction_reciprocity',
        'OQ7Prescribed.normalizedAbsorption_pos',
        'OQ7Prescribed.normalizedExtinction_work_balance',
        'OQ7Prescribed.normalizedExtinction_pos',
        'OQ7Prescribed.physicalScattering_sine_squared_factorization',
        'OQ7Prescribed.normalizedExtinction_compact_lower_bound',
        'OQ7Prescribed.normalizedRotationAsymmetry_continuous',
        'OQ7Prescribed.normalizedRotationAsymmetry_lt_one',
        'OQ7Prescribed.physicalAsymmetry_normalized_factorization',
        'OQ7Prescribed.slabGreen_locallyIntegrable',
        'OQ7Prescribed.apertureOscillation_two_ibp',
        'OQ7Prescribed.apertureCircleJet_hasDerivAt',
        'OQ7Prescribed.apertureRadialLiftSecond_norm_le',
        'OQ7Prescribed.slabRadial_change_variables',
        'OQ7Prescribed.horizontalSlabPotential_radialWindow',
        'OQ7Prescribed.horizontalSlabPotential_error',
        'OQ7Prescribed.scaledApertureWindow_iteratedFDeriv',
        'OQ7Prescribed.horizontalSlabPotential_scaled_error',
        'OQ7Prescribed.horizontalSlabPotential_uniform_aperture_error',
        'OQ7Prescribed.scalarOutgoingPotential_partial',
        'OQ7Prescribed.horizontalSlabPotential_second_partial',
        'OQ7Prescribed.horizontalSlabTransverseKernel_uniform_error',
        'OQ7Prescribed.slabCoordinateEquiv_measurePreserving',
        'OQ7Prescribed.scalarOutgoingPotential_slab_separation',
        'OQ7Prescribed.scalarOutgoingSlabTransverse_separation',
        'OQ7Prescribed.scalarOutgoingSlabTransverse_uniform_aperture_error',
        'OQ7Prescribed.smoothDyadicField_eq_electricVolumeField',
        'OQ7Prescribed.smoothDyadicField_axis_source_projection',
        'OQ7Prescribed.electricVolumeField_slab_uniform_aperture_error',
        'OQ7Prescribed.normalizedActiveResponse_residual_bound',
        'OQ7Prescribed.normalizedActiveResponse_angle_difference_bound')) {
        if ($oq7Required -notin $oq7NewKernelTheorems) { throw "Missing outgoing operator obligation: $oq7Required" }
    }
    if ('OQ7Prescribed.scatteringStateOfVolumeEquation' -notin $oq7Constants) {
        throw 'Missing proved physical volume-equation scattering-state constructor.'
    }
    if ($oq7PdfHash -ne '3D9775D849234E828370D7C96D8BDCDD574BEB6831A7906EA6B7706579868710') { throw 'Manuscript hash differs.' }
    $oq7TargetHash = (Get-FileHash -LiteralPath 'PrescribedExtinction/Maxwell.lean' -Algorithm SHA256).Hash
    if ($oq7TargetHash -ne 'A9950F0F1C9EA4A20FF2C480A71CC4FABDC4AB84F8173851C37A4BD56E0D231B') {
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
        existingPhysicalTargetSourceUnchanged = $false
        physicalTargetOnlySmoothTestAnnotationChanged = $true
        originalPhysicalTargetSnapshotSHA256 = $oq7OriginalTargetHash
        allPreDyadicLeanModulesUnchanged = $false
        allEarlierLeanModulesExceptSmoothTestAnnotationUnchanged = $true
        existingAggregateImportPrefixUnchanged = $true
        dyadicGreenMilestoneComplete = $true
        positiveFrequencyOutgoingContactIdentityVerified = $true
        scalarHelmholtzFundamentalSolutionVerified = $true
        compactCurrentHelmholtzEquationVerified = $true
        dyadicMaxwellSourceDistributionVerified = $true
        bothMaxwellCurlSourceDistributionEquationsVerified = $true
        L1KernelL2CurrentConvolutionBoundVerified = $true
        outgoingGreenFirstDistributionalDerivativeVerified = $true
        actualGradientCurrentLocalL2Verified = $true
        actualGradientCurrentDistributionalIdentificationVerified = $true
        actualElectricAndMagneticSourceFieldsLocalL2Verified = $true
        actualSourceFieldDistributionalCurlsVerified = $true
        outgoingPhysicalVolumeDistributionVerified = $true
        outgoingPhysicalCompactDomainL2OperatorVerified = $true
        actualSourceFieldsBothPhysicalWeakCurlsVerified = $true
        physicalWeakCurlsUseAllSmoothCompactComplexVectorTests = $true
        actualDyadicKernelRadiationDefectVerified = $true
        allDirectionDisplacedSourceRadiationBoundVerified = $true
        actualExteriorGreenCurrentUniformSilverMullerVerified = $true
        exteriorFieldFarZoneIntegrabilityVerified = $true
        physicalExteriorElectricL2RepresentativeIdentificationVerified = $true
        physicalGlobalOutgoingWeakMaxwellSourceFieldsVerified = $true
        physicalExteriorMagneticPointwiseIdentificationVerified = $true
        physicalIncidentPlaneWaveWeakMaxwellVerified = $true
        classicalSmoothCurlToPhysicalWeakCurlVerified = $true
        physicalFiniteBodyPolarizationCompactL2Verified = $true
        materialVolumeEquationToOriginalScatteringStateVerified = $true
        materialVolumeEquationSolvabilityVerified = $true
        materialVolumeEquationUniqueCurrentVerified = $true
        actualBodyDomainOutgoingCompressionVerified = $true
        materialBodyInverseBoundDependsOnlyOnTensorLossData = $true
        physicalRankOneActiveCurrentEmbeddingVerified = $true
        rankOneInverseBoundIndependentOfApertureAndAxesVerified = $true
        intermediateRankOnePhysicalScatteringExistenceVerified = $true
        physicalCurrentSineFactorizationVerified = $true
        originalPhysicalExtinctionSineSquaredFactorizationVerified = $true
        normalizedResponseDefinedAtZeroRotationVerified = $true
        physicalAbsorptionEqualsCurrentWorkVerified = $true
        actualElectricUniformFullVectorFarFieldVerified = $true
        originalPhysicalFarFieldIdentificationVerified = $true
        actualFullVectorHaarRadiationWorkIdentityVerified = $true
        physicalHaarRadiationEnergyBalanceVerified = $true
        originalThetaPhiSurfaceMeasureConversionVerified = $true
        originalPhysicalOpticalWorkIdentityVerified = $true
        actualPhysicalOutgoingVolumeReciprocityVerified = $true
        originalPhysicalExtinctionReciprocityVerified = $true
        normalizedRotationResponseAndPowersContinuousAtZeroVerified = $true
        normalizedAllAngleCommonExtinctionVerified = $true
        normalizedPhysicalExtinctionStrictlyPositiveVerified = $true
        physicalFullAngularScatteringSineSquaredFactorizationVerified = $true
        normalizedPhysicalAsymmetryContinuousAndStrictlyBelowOneVerified = $true
        actualOutgoingScalarHorizontalConvolutionVerified = $true
        actualScalarGreenUniformApertureErrorVerified = $true
        scalarApertureErrorIncludesCoincidentHeightsVerified = $true
        smoothDyadicRepresentativeOfActualElectricVolumeFieldVerified = $true
        actualThreeDimensionalSeparatedSourceConvolutionVerified = $true
        physicalSmoothSlabTransverseApertureErrorUniformInAxesVerified = $true
        physicalSlabApertureErrorForAllL2HeightProfilesVerified = $false
        physicalVectorUniformApertureLocalizationVerified = $false
        physicalVolumeWorkBalanceVerified = $true
        originalPhysicalAbsorptionSineSquaredFactorizationVerified = $true
        normalizedPhysicalResponseUniformResidualBoundVerified = $true
        complexHilbertImaginaryCoerciveInverseVerified = $true
        physicalAdmissibleConstitutiveSusceptibilityInverseVerified = $true
        compactL2CurrentFixedSupportSmoothDensityVerified = $true
        smoothCurrentClassicalPhysicalSourceFieldsVerified = $true
        physicalSmoothSourceCutoffPoyntingIdentityVerified = $true
        actualOutgoingVolumeDissipativityVerified = $true
        outgoingDissipativityForAllCompactL2CurrentsVerified = $true
        physicalDyadicDistributionExteriorTestIdentificationVerified = $true
        outgoingWeakMaxwellRepresentationVerified = $false
        scatteringStateExistenceVerified = $true
        allPreContactLeanModulesUnchanged = $false
        allPrePuncturedLeanModulesUnchanged = $false
        allLeanModulesFromCommit6874b49Unchanged = $false
        baselineCommit = '6874b492e8d49d2303bb25aa12248b489c9ad13a'
        allLeanModulesFromCommit8301ddaUnchanged = $false
        staticContinuationBaselineCommit = '8301dda82eaf84611a4a40982f77dc2787b16861'
        newtonScalarTemperedFourierVerified = $true
        newtonHessianTemperedFourierVerified = $true
        zeroFrequencySymbolNullSetVerified = $true
        staticPhysicalVolumeOperatorOnSmoothCurrentsVerified = $true
        staticPhysicalVolumeOperatorOnCompactL2CurrentsVerified = $true
        newtonPuncturedDoubleIntegrationByPartsVerified = $true
        newtonInnerNormalSignsVerified = $true
        newtonOuterBoundaryVanishesVerified = $true
        newtonContactIdentityVerified = $true
        newtonDistributionalContactEqualityVerified = $true
        sphericalSecondMomentsVerified = $true
        newtonAngularBoundaryLimitsVerified = $true
        newtonPrincipalValueConvergenceVerified = $true
        newtonPrincipalValueIsBundledDistribution = $true
        staticNewtonIdentificationVerified = $true
        targetSourceSHA256 = $oq7TargetHash
        verifiedAtUTC = [DateTime]::UtcNow.ToString('o')
        lean = $oq7Version
        lakeBuildPassed = $true
        cleanProjectBuild = $oq7SameCleanSources
        cleanProjectBuildRequestedThisRun = [bool]$Clean
        savedCleanBuildHasIdenticalLeanSources = $oq7SameCleanSources
        cleanBuildLog = 'verification/clean-build.log'
        allowedFoundationAxioms = $oq7Allowed
        allProjectConstantsAudited = $oq7Constants.Count
        privateProjectConstantsAudited = @($oq7Constants | Where-Object { $_.StartsWith('_private.') }).Count
        newTheoremCount = $oq7NewTheorems.Count
        newKernelTheoremConstantCount = $oq7NewKernelTheorems.Count
        newTheorems = $oq7NewTheorems
        legacyTheorem51Present = ('OQ7.theorem51' -in $oq7Theorems)
        legacySourcesPreserved = $true
        manuscriptSHA256 = $oq7PdfHash
        dependencyRevisions = $oq7Dependencies
        sourceHashes = $oq7Hashes
        foundationalMilestones = @(
            @{ module = 'PrescribedExtinction.GreenKernel'; scope = 'Actual scalar kernel local L1/L2 integrability and distributional dyadic test formula; Newton contact identified in NewtonContact'; physicalContactCoefficientVerified = $true; positiveFrequencyOutgoingContactIdentityVerified = $true },
            @{ module = 'PrescribedExtinction.VolumePotential'; scope = 'Actual convolution exists for every compact vector L2 current; finite local bound; locally integrable potential; distributional volume formula and additivity'; boundedDyadicL2OperatorVerified = $true },
            @{ module = 'PrescribedExtinction.StaticFourier'; scope = 'Explicit static Fourier multiplier is an L2 contraction and has zero imaginary quadratic form; physical identity proved in NewtonStaticIdentification'; identificationWithNewtonVolumePotentialVerified = $true },
            @{ module = 'PrescribedExtinction.OutgoingRadial'; scope = 'Actual Newton and outgoing radial derivatives and classical Hessian away from origin; Newton distributional contact identified in NewtonContact'; physicalContactCoefficientVerified = $true; positiveFrequencyOutgoingContactIdentityVerified = $true },
            @{ module = 'PrescribedExtinction.RemainderConvolution'; scope = 'Actual classical dyadic dynamic-minus-static cancellation; explicit inverse-distance norm estimate; cutoff L2 kernel; actual convolution, compact-domain L2 bound, ae invariance and complex linearity'; identificationWithDistributionalDifferenceVerified = $true; fullPhysicalDyadicOperatorVerified = $true },
            @{ module = 'PrescribedExtinction.SphereMoments'; scope = 'Actual polar angular measure, orthogonal invariance, area 4pi and exact second moments'; actualSphereMomentsVerified = $true },
            @{ module = 'PrescribedExtinction.NewtonBoundary'; scope = 'Actual angular contact boundary tends to minus delta_ij phi(0)/3; derivative boundary tends to zero; connected to punctured integral in NewtonPunctured'; puncturedIntegrationByPartsVerified = $true },
            @{ module = 'PrescribedExtinction.NewtonPrincipalValue'; scope = 'Actual spherical principal value converges for every original test function; compensated integral and every positive-radius truncated integral are proved integrable; bundled in NewtonContact'; fullDistributionalHessianIdentityVerified = $true },
            @{ module = 'PrescribedExtinction.NewtonCutoffIBP'; scope = 'Actual smooth radial cutoff, exact derivative mass and whole-space Newton/gradient integration by parts for original test functions'; cutoffIntegrationByPartsVerified = $true },
            @{ module = 'PrescribedExtinction.NewtonShell'; scope = 'Actual exterior cutoff convergence, integrable polar conversion, radial shell rescaling and normalized shell limit'; radialShellLimitVerified = $true },
            @{ module = 'PrescribedExtinction.NewtonContact'; scope = 'Exact finite-radius punctured double integration by parts, inward-normal signs and vanishing outer boundaries; full Newton Hessian principal-value/contact identity; actual integral-valued principal value is a continuous distribution'; fullDistributionalHessianIdentityVerified = $true; staticFourierIdentificationVerified = $true },
            @{ module = 'PrescribedExtinction.NewtonTransform'; scope = 'Actual scalar Newton and full contact Hessian Fourier correspondence on all Schwartz tests; both heat interchanges absolutely integrable; zero-frequency handled globally'; kernelFourierCorrespondenceVerified = $true },
            @{ module = 'PrescribedExtinction.NewtonStaticIdentification'; scope = 'Actual original Newton volume distribution equals staticFourierOperator on every compactly supported vector L2 current; genuine current/test Fubini, smooth correlation, Fourier L1-L2 compatibility, and bounded physical L2 realization'; compactCurrentConvolutionIdentificationVerified = $true; physicalStaticOperatorVerified = $true }
        )
        unverifiedDependencies = @('Uniqueness of arbitrary physical outgoing Maxwell states',
            'Converse outgoing volume representation',
            'Uniform aperture localization including grazing singularities and all angular channels',
            'Planar construction and normalized zero-angle / zero-plate-loss limits',
            'First exact-extinction bracket and physical continuity',
            'Positive-loss perturbation of solutions and second exact-extinction bracket',
            'Order of limits, constant dependencies, strict nonattainment and final assembly')
    } | ConvertTo-Json -Depth 12 | Set-Content -LiteralPath 'verification/report.json' -Encoding utf8
    Write-Output 'PARTIAL: supporting source compilation and axiom audit passed. Theorem 1.1 remains unproved.'
} finally { Pop-Location }
