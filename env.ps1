# Dot-source after activating Lean 4.34.1; Lake supplies the import path.
$ErrorActionPreference = 'Stop'
if (-not (Get-Command lake -ErrorAction SilentlyContinue)) { throw 'Activate Lean 4.34.1 first.' }
function Invoke-OQ7Lean { & lake env lean @args }
function Invoke-OQ7Checker { & lake env leanchecker @args }
