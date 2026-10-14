param([string]$ExistingProject = (Join-Path $PSScriptRoot '..\..\oq7'))
$ErrorActionPreference = 'Stop'
$missionCacheSource = (Resolve-Path -LiteralPath (Join-Path $ExistingProject '.lake/packages')).Path
$missionCacheParent = Join-Path $PSScriptRoot '.lake'
$missionCacheDestination = Join-Path $missionCacheParent 'packages'
if (Test-Path -LiteralPath $missionCacheDestination) {
    Write-Output 'Dependency cache already present; no change made.'
    exit 0
}
New-Item -ItemType Directory -Force -Path $missionCacheParent | Out-Null
New-Item -ItemType Junction -Path $missionCacheDestination -Target $missionCacheSource | Out-Null
Write-Output 'New project now uses the preserved pinned dependency cache.'

