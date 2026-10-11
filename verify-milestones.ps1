param([string]$LeanBin, [string[]]$Only)
$ErrorActionPreference = 'Stop'
if ($LeanBin) { $env:PATH = (Resolve-Path -LiteralPath $LeanBin).Path + ';' + $env:PATH }
Push-Location $PSScriptRoot
try {
    $oq7Milestones = @(
        @{ name = 'green-kernel'; module = 'PrescribedExtinction.GreenKernel' },
        @{ name = 'volume-potential'; module = 'PrescribedExtinction.VolumePotential' },
        @{ name = 'static-fourier'; module = 'PrescribedExtinction.StaticFourier' },
        @{ name = 'radial-hessian'; module = 'PrescribedExtinction.OutgoingRadial' },
        @{ name = 'dyadic-remainder'; module = 'PrescribedExtinction.RemainderConvolution' },
        @{ name = 'spherical-moments'; module = 'PrescribedExtinction.SphereMoments' },
        @{ name = 'newton-boundary'; module = 'PrescribedExtinction.NewtonBoundary' },
        @{ name = 'newton-principal-value'; module = 'PrescribedExtinction.NewtonPrincipalValue' },
        @{ name = 'newton-cutoff'; module = 'PrescribedExtinction.NewtonCutoffIBP' },
        @{ name = 'newton-shell'; module = 'PrescribedExtinction.NewtonShell' },
        @{ name = 'newton-contact'; module = 'PrescribedExtinction.NewtonContact' },
        @{ name = 'newton-fundamental'; module = 'PrescribedExtinction.NewtonFundamental' },
        @{ name = 'newton-tempered'; module = 'PrescribedExtinction.NewtonTempered' },
        @{ name = 'static-symbol-coordinates'; module = 'PrescribedExtinction.StaticSymbolCoordinates' },
        @{ name = 'newton-schwartz'; module = 'PrescribedExtinction.NewtonSchwartz' },
        @{ name = 'newton-heat'; module = 'PrescribedExtinction.NewtonHeat' },
        @{ name = 'newton-fourier-normalization'; module = 'PrescribedExtinction.NewtonFourier' },
        @{ name = 'newton-frequency'; module = 'PrescribedExtinction.NewtonFrequency' },
        @{ name = 'newton-heat-pairing'; module = 'PrescribedExtinction.NewtonHeatPairing' },
        @{ name = 'newton-heat-fourier'; module = 'PrescribedExtinction.NewtonHeatFourier' },
        @{ name = 'newton-frequency-heat'; module = 'PrescribedExtinction.NewtonFrequencyHeat' },
        @{ name = 'newton-transform'; module = 'PrescribedExtinction.NewtonTransform' },
        @{ name = 'newton-symbol'; module = 'PrescribedExtinction.NewtonSymbol' },
        @{ name = 'newton-current-pairing'; module = 'PrescribedExtinction.NewtonCurrentPairing' },
        @{ name = 'newton-current-correlation'; module = 'PrescribedExtinction.NewtonCurrentCorrelation' },
        @{ name = 'fourier-l1-l2'; module = 'PrescribedExtinction.FourierL1L2' },
        @{ name = 'static-operator-distribution'; module = 'PrescribedExtinction.StaticOperatorDistribution' },
        @{ name = 'newton-current-fourier'; module = 'PrescribedExtinction.NewtonCurrentFourier' },
        @{ name = 'newton-static-identification'; module = 'PrescribedExtinction.NewtonStaticIdentification' },
        @{ name = 'outgoing-dynamic-identity'; module = 'PrescribedExtinction.OutgoingDynamicIdentity' },
        @{ name = 'outgoing-volume-identification'; module = 'PrescribedExtinction.OutgoingVolumeIdentification' },
        @{ name = 'compact-outgoing-operator'; module = 'PrescribedExtinction.CompactOutgoingIdentification' },
        @{ name = 'outgoing-fundamental'; module = 'PrescribedExtinction.OutgoingFundamental' },
        @{ name = 'volume-fundamental'; module = 'PrescribedExtinction.VolumeFundamental' },
        @{ name = 'dyadic-maxwell-source'; module = 'PrescribedExtinction.DyadicMaxwellSource' },
        @{ name = 'young-convolution'; module = 'PrescribedExtinction.YoungConvolution' },
        @{ name = 'green-gradient-current'; module = 'PrescribedExtinction.GradientCurrentPairing' },
        @{ name = 'physical-source-fields'; module = 'PrescribedExtinction.PhysicalSourceFields' },
        @{ name = 'smooth-test-correction'; module = 'PrescribedExtinction.TestRegularity' },
        @{ name = 'physical-weak-curls'; module = 'PrescribedExtinction.WeakCurlBridge' },
        @{ name = 'radiation-kernel'; module = 'PrescribedExtinction.RadiationKernel' },
        @{ name = 'exterior-current-radiation'; module = 'PrescribedExtinction.ExteriorOutgoing' },
        @{ name = 'exterior-kernel-tests'; module = 'PrescribedExtinction.ExteriorKernelTests' },
        @{ name = 'exterior-electric-identification'; module = 'PrescribedExtinction.ExteriorCurrentIdentification' }
    )
    if ($Only) {
        foreach ($oq7Name in $Only) {
            if ($oq7Name -notin $oq7Milestones.name) { throw "Unknown milestone: $oq7Name" }
        }
        $oq7Milestones = @($oq7Milestones | Where-Object { $_.name -in $Only })
    }
    foreach ($oq7Milestone in $oq7Milestones) {
        $oq7Directory = Join-Path 'verification/milestones' $oq7Milestone.name
        & lake build $oq7Milestone.module 2>&1 | Set-Content -LiteralPath (Join-Path $oq7Directory 'build.log') -Encoding utf8
        if ($LASTEXITCODE -ne 0) { throw "Milestone failed: $($oq7Milestone.name)" }
        & lake env lean (Join-Path $oq7Directory 'Audit.lean') 2>&1 |
            Set-Content -LiteralPath (Join-Path $oq7Directory 'axioms.log') -Encoding utf8
        if ($LASTEXITCODE -ne 0) { throw "Milestone axiom export failed: $($oq7Milestone.name)" }
        Write-Output "Checked stated supporting milestone: $($oq7Milestone.name). Final theorem remains PARTIAL."
    }
} finally { Pop-Location }
