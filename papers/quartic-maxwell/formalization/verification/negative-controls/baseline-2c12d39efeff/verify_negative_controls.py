"""Isolated expected failures for the quartic verifier's trust-boundary checks.

Control Lean files are deliberately invalid/axiomatic and are written only to
an explicitly supplied ignored scratch directory. They are never imported by
the paper's proof project. Their failures are recorded separately from success.
"""
from __future__ import annotations
import argparse
import hashlib
import importlib.util
import json
import os
from pathlib import Path
import re
import subprocess
import sys
from datetime import datetime, timezone


def main() -> int:
    sys.stdout.reconfigure(encoding="utf-8")
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--project", required=True, type=Path)
    parser.add_argument("--scratch", required=True, type=Path)
    args = parser.parse_args()
    project = args.project.resolve()
    scratch = args.scratch.resolve()
    if ".local" not in scratch.parts:
        raise SystemExit("Negative controls require a .local scratch directory")
    scratch.mkdir(parents=True, exist_ok=True)
    output = project / "verification/negative-controls"
    output.mkdir(parents=True, exist_ok=True)
    specification = importlib.util.spec_from_file_location("quartic_control_verifier", project / "verify.py")
    verifier = importlib.util.module_from_spec(specification)
    specification.loader.exec_module(verifier)
    verifier_hash = verifier.sha(project / "verify.py")
    lean = verifier.REPO / ".local/toolchains/lean-4.34.1-windows/bin/lean.exe"
    results = []

    for label, payload in [
        ("sorry_preflight", "namespace Control\ntheorem escaped : False := by sorry\nend Control\n"),
        ("axiom_preflight", "namespace Control\naxiom escaped : False\nend Control\n"),
    ]:
        source = scratch / (label + ".lean")
        source.write_text(payload, encoding="utf-8")
        try:
            verifier.exported_declarations(source)
        except SystemExit as error:
            message = str(error)
            passed = "Prohibited proof escape" in message
        else:
            passed, message = False, "ERROR: expected preflight rejection did not occur"
        (output / (label + ".log")).write_text(message + "\n", encoding="utf-8")
        results.append({"control": label, "expected": "preflight rejection", "passed": passed,
                        "source": payload, "sourceSHA256": verifier.sha(source), "diagnostic": message})

    payload = "namespace Control\ntheorem falseEquality : (1 : Nat) = 2 := by rfl\nend Control\n"
    source = scratch / "FalseProof.lean"
    source.write_text(payload, encoding="utf-8")
    result = subprocess.run([str(lean), str(source)], cwd=scratch, stdout=subprocess.PIPE,
                            stderr=subprocess.STDOUT, text=True, encoding="utf-8")
    (output / "false_proof_compiler.log").write_text(result.stdout, encoding="utf-8")
    results.append({"control": "false_proof_compiler", "expected": "Lean compilation failure",
                    "passed": result.returncode != 0 and "error:" in result.stdout,
                    "compilerExitCode": result.returncode, "source": payload,
                    "sourceSHA256": verifier.sha(source)})

    payload = ("set_option pp.fullNames true\nnamespace Control\naxiom untrusted : False\n"
               "theorem escaped : False := untrusted\n#print axioms escaped\nend Control\n")
    source = scratch / "AxiomDependency.lean"
    source.write_text(payload, encoding="utf-8")
    result = subprocess.run([str(lean), str(source)], cwd=scratch, stdout=subprocess.PIPE,
                            stderr=subprocess.STDOUT, text=True, encoding="utf-8")
    (output / "axiom_allowlist.log").write_text(result.stdout, encoding="utf-8")
    printed = re.findall(r"'([^']+)' depends on axioms: \[([^]]*)\]", result.stdout)
    unexpected = set()
    for _, names in printed:
        actual = {re.sub(r"\.\{[^}]*\}", "", name.strip()) for name in names.split(",") if name.strip()}
        unexpected |= actual - verifier.ALLOW_AXIOMS
    results.append({"control": "axiom_allowlist", "expected": "compiled axiom dependency rejected by allowlist",
                    "passed": result.returncode == 0 and "Control.untrusted" in unexpected,
                    "compilerExitCode": result.returncode, "unexpectedAxioms": sorted(unexpected),
                    "source": payload, "sourceSHA256": verifier.sha(source)})

    package = scratch / "census-package"
    modules = package / "QuarticMaxwell"
    modules.mkdir(parents=True, exist_ok=True)
    (modules / "Known.lean").write_text("namespace Control\ndef known : Nat := 1\nend Control\n", encoding="utf-8")
    (modules / "Orphan.lean").write_text("namespace Control\ndef orphan : Nat := 2\nend Control\n", encoding="utf-8")
    original_root, original_modules, original_argv = verifier.ROOT, verifier.MODULES, sys.argv
    verifier.ROOT = package
    verifier.MODULES = ["QuarticMaxwell.Known", "QuarticMaxwell"]
    sys.argv = ["negative-census-control"]
    try:
        verifier.main()
    except SystemExit as error:
        message = str(error)
        passed = "Module census differs from verifier" in message and "QuarticMaxwell.Orphan" in message
    else:
        passed, message = False, "ERROR: expected module census rejection did not occur"
    finally:
        verifier.ROOT, verifier.MODULES, sys.argv = original_root, original_modules, original_argv
    (output / "missing_module_census.log").write_text(message + "\n", encoding="utf-8")
    results.append({"control": "missing_module_census", "expected": "unregistered module rejected",
                    "passed": passed, "diagnostic": message,
                    "registered": ["QuarticMaxwell.Known"], "discovered": ["QuarticMaxwell.Known", "QuarticMaxwell.Orphan"]})
    if verifier_hash != verifier.sha(project / "verify.py"):
        raise SystemExit("Verifier changed while negative controls ran")
    report = {"timestampUTC": datetime.now(timezone.utc).isoformat(), "expectedFailureControlsOnly": True,
              "notPartOfSuccessfulProofProject": True, "verifierSHA256": verifier_hash,
              "runnerSHA256": hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
              "allControlsPassed": all(item["passed"] for item in results), "controls": results}
    (output / "report.json").write_text(json.dumps(report, indent=2) + "\n", encoding="utf-8")
    for item in results:
        print(item["control"], "PASS" if item["passed"] else "FAIL", flush=True)
    return 0 if report["allControlsPassed"] else 1


if __name__ == "__main__":
    raise SystemExit(main())
