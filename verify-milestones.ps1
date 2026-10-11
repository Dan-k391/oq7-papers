param([string]$LeanBin)
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
        @{ name = 'newton-principal-value'; module = 'PrescribedExtinction.NewtonPrincipalValue' }
    )
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
