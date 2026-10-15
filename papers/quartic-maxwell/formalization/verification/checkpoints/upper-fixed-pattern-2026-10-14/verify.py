"""Compile and audit the current quartic modules with the repository's pinned Lean.

This reports kernel verification of the implemented lemmas. It deliberately does
not report complete verification of the original physical manuscript theorems.
"""
from __future__ import annotations

import argparse
import hashlib
import json
import os
from pathlib import Path
import re
import subprocess
import sys
from datetime import datetime, timezone

ROOT = Path(__file__).resolve().parent
REPO = ROOT.parents[2]
EXPECTED_LEAN = "4.34.1"
EXPECTED_MATHLIB = "d13f23b723b8a846827a245b89c10fc7d3f11612"
ALLOW_AXIOMS = {"propext", "Classical.choice", "Quot.sound"}
MODULES = [
    "QuarticMaxwell.Certificates", "QuarticMaxwell.Operator",
    "QuarticMaxwell.Asymptotics", "QuarticMaxwell.GreenEigenvalues",
    "QuarticMaxwell.MaterialInverse", "QuarticMaxwell.Rearrangement",
    "QuarticMaxwell.SharpVolume", "QuarticMaxwell.Schur",
    "QuarticMaxwell.ProjectionGeometry", "QuarticMaxwell.ProjectionKernel",
    "QuarticMaxwell.MaskedRemainder", "QuarticMaxwell.RadiationMoment",
    "QuarticMaxwell.SquareIntegral", "QuarticMaxwell.RadiationOperator",
    "QuarticMaxwell.RadiationPhysical", "QuarticMaxwell.IncidentSources",
    "QuarticMaxwell.RadiationIdentity", "QuarticMaxwell.Reciprocity",
    "QuarticMaxwell.SupportedOperators", "QuarticMaxwell.TensorMultiplier",
    "QuarticMaxwell.VolumeInverse", "QuarticMaxwell.UniformBound",
    "QuarticMaxwell.BallBound", "QuarticMaxwell.PlaneWaves",
    "QuarticMaxwell.WeakMaterial", "QuarticMaxwell.PhysicalPowers",
    "QuarticMaxwell.StaticInverse", "QuarticMaxwell.SourceTaylor",
    "QuarticMaxwell.RadiationGram", "QuarticMaxwell.RadiationTaylor",
    "QuarticMaxwell.GramEstimates", "QuarticMaxwell.StaticReciprocity",
    "QuarticMaxwell.FixedPatternWork", "QuarticMaxwell.FixedPatternScattering",
    "QuarticMaxwell.FixedPatternContrast", "QuarticMaxwell.LocalTensorClass",
    "QuarticMaxwell.StaticHessian",
    "QuarticMaxwell.PhysicalDilation", "QuarticMaxwell.FixedPatternDilation",
    "QuarticMaxwell",
]


def lean_code(text: str) -> str:
    """Remove nested Lean comments before checking prohibited proof escapes."""
    result = []
    index = 0
    depth = 0
    while index < len(text):
        if text.startswith("/-", index):
            depth += 1
            result.append("  ")
            index += 2
        elif depth and text.startswith("-/", index):
            depth -= 1
            result.append("  ")
            index += 2
        elif not depth and text.startswith("--", index):
            end = text.find("\n", index)
            if end < 0:
                break
            result.append("\n")
            index = end + 1
        else:
            char = text[index]
            result.append(char if not depth or char == "\n" else " ")
            index += 1
    if depth:
        raise SystemExit("Unclosed Lean comment")
    return "".join(result)


def exported_declarations(source: Path) -> list[str]:
    code = lean_code(source.read_text(encoding="utf-8"))
    if re.search(r"\b(?:sorry|admit|axiom|native_decide)\b", code):
        raise SystemExit(f"Prohibited proof escape in {source}")
    # Track actual nested namespace/section scopes. Reject private declarations
    # because their generated kernel names need a separate inventory mechanism.
    scopes = []
    names = []
    for line in code.splitlines():
        # Attributes may share the declaration line (for example @[simp]).
        line = re.sub(r"^\s*(?:@\[[^\]]*\]\s*)+", "", line)
        opened = re.match(r"^\s*(?:noncomputable\s+)?(namespace|section)(?:\s+(\S+))?\s*$", line)
        if opened:
            kind, name = opened.groups()
            if kind == "namespace" and not name:
                raise SystemExit(f"Anonymous namespace in {source}")
            scopes.append((kind, name))
            continue
        ended = re.match(r"^\s*end(?:\s+(\S+))?\s*$", line)
        if ended:
            if not scopes:
                raise SystemExit(f"Unmatched scope end in {source}")
            _, name = scopes.pop()
            if ended.group(1) and ended.group(1) != name:
                raise SystemExit(f"Mismatched scope end in {source}: {line}")
            continue
        declaration = re.match(r"^\s*(?P<modifiers>(?:(?:private|protected|noncomputable)\s+)*)"
                               r"(?:theorem|lemma|def|abbrev)\s+([^\s(:]+)", line)
        if declaration:
            if "private" in declaration.group("modifiers").split():
                raise SystemExit(f"Private declaration needs explicit kernel-name audit in {source}")
            prefix = ".".join(name for kind, name in scopes if kind == "namespace")
            if not prefix:
                raise SystemExit(f"Declaration outside namespace in {source}")
            names.append(prefix + "." + declaration.group(2))
    declared_count = len(re.findall(r"\b(?:theorem|lemma|def|abbrev)\s+[^\s(:]+", code))
    if len(names) != declared_count:
        raise SystemExit(f"Public declaration parser missed a declaration in {source}")
    return names


def sha(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def main() -> int:
    sys.stdout.reconfigure(encoding="utf-8")
    sys.stderr.reconfigure(encoding="utf-8")
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--lean-bin", type=Path,
                        default=REPO / ".local/toolchains/lean-4.34.1-windows/bin")
    parser.add_argument("--fresh-kernel", action="store_true")
    args = parser.parse_args()
    lean = args.lean_bin / ("lean.exe" if os.name == "nt" else "lean")
    checker = args.lean_bin / ("leanchecker.exe" if os.name == "nt" else "leanchecker")
    dependencies = REPO / "papers/prescribed-extinction/formalization/.lake/packages"
    mathlib = dependencies / "mathlib"
    pin = subprocess.check_output(["git", "rev-parse", "HEAD"], cwd=mathlib, text=True).strip()
    version = subprocess.check_output([str(lean), "--version"], text=True).strip()
    if EXPECTED_LEAN not in version or pin != EXPECTED_MATHLIB:
        raise SystemExit(f"Pinned environment mismatch: {version}, Mathlib {pin}")
    output = ROOT / ".lake/build/lib/lean"
    logs = ROOT / "verification/logs"
    output.mkdir(parents=True, exist_ok=True)
    logs.mkdir(parents=True, exist_ok=True)
    imports = [output] + [p / ".lake/build/lib/lean" for p in dependencies.iterdir() if p.is_dir()]
    imports.append(REPO / "papers/prescribed-extinction/formalization/.lake/build/lib/lean")
    env = os.environ.copy()
    env["LEAN_PATH"] = os.pathsep.join(str(p) for p in imports)
    env["LEAN_NUM_THREADS"] = "2"
    source_paths = [ROOT / (module.replace(".", "/") + ".lean") for module in MODULES]
    discovered = {"QuarticMaxwell." + p.stem for p in (ROOT / "QuarticMaxwell").glob("*.lean")}
    if discovered != set(MODULES[:-1]):
        raise SystemExit(f"Module census differs from verifier: {discovered.symmetric_difference(MODULES[:-1])}")
    source_paths.append(ROOT / "Audit.lean")
    for source in source_paths:
        if re.search(r"\b(?:sorry|admit|axiom|native_decide)\b", lean_code(source.read_text(encoding="utf-8"))):
            raise SystemExit(f"Prohibited proof escape in {source}")
    for source in source_paths[-2:]:
        if re.search(r"\b(?:theorem|lemma|def|abbrev|structure|inductive)\s+", lean_code(source.read_text(encoding="utf-8"))):
            raise SystemExit(f"Aggregate/inspection file cannot contain unaudited declarations: {source}")
    before = {str(p.relative_to(ROOT)): sha(p) for p in source_paths}
    declarations = [name for p in source_paths[:-2] for name in exported_declarations(p)]
    if len(declarations) != len(set(declarations)):
        raise SystemExit("Duplicate exported declaration names")
    manifest_path = ROOT / "verification/public-roots.json"
    manifest = json.loads(manifest_path.read_text(encoding="utf-8"))
    missing_roots = set(manifest["requiredCompleteClaimExports"]) - set(declarations)
    if missing_roots:
        raise SystemExit(f"Required public theorem roots missing: {sorted(missing_roots)}")
    original_pdf = REPO / "papers/quartic-maxwell/manuscript/OQ7_quartic_Maxwell_2026-10-10.pdf"
    if sha(original_pdf) != manifest["originalPDFSHA256"]:
        raise SystemExit("Dated original manuscript does not match the public root manifest")
    results = []
    started = datetime.now(timezone.utc).isoformat()
    for module, source in zip(MODULES, source_paths):
        olean = output / (module.replace(".", "/") + ".olean")
        olean.parent.mkdir(parents=True, exist_ok=True)
        cmd = [str(lean), "-o", str(olean), str(source)]
        result = subprocess.run(cmd, cwd=ROOT, env=env, stdout=subprocess.PIPE,
                                stderr=subprocess.STDOUT, text=True, encoding="utf-8")
        (logs / f"{module}.log").write_text(result.stdout, encoding="utf-8")
        print(f"{module}: exit {result.returncode}", flush=True)
        results.append({"module": module, "exitCode": result.returncode,
                        "log": f"verification/logs/{module}.log"})
        if result.returncode:
            print(result.stdout[:20000])
            raise SystemExit(result.returncode)
    inventory = ROOT / "verification/Inventory.lean"
    inventory.write_text("import QuarticMaxwell\nset_option pp.fullNames true\n"
                         "set_option pp.explicit false\nset_option pp.universes true\n"
                         "set_option format.width 120\nset_option pp.deepTerms true\n"
                         "set_option pp.maxSteps 1000000\n" +
                         "\n".join(f"#check @{name}\n#print axioms {name}" for name in declarations) + "\n",
                         encoding="utf-8")
    audit = subprocess.run([str(lean), str(inventory)], cwd=ROOT, env=env,
                           stdout=subprocess.PIPE, stderr=subprocess.STDOUT, text=True, encoding="utf-8")
    (logs / "Audit.log").write_text(audit.stdout, encoding="utf-8")
    if audit.returncode:
        print(audit.stdout[:20000])
        raise SystemExit(audit.returncode)
    printed = re.findall(r"'([^']+)' depends on axioms: \[([^]]*)\]", audit.stdout)
    printed += [(name, "") for name in re.findall(r"'([^']+)' does not depend on any axioms", audit.stdout)]
    if not printed:
        raise SystemExit("No theorem axiom inventories found")
    if {name for name, _ in printed} != set(declarations):
        raise SystemExit("Axiom inventory does not cover every exported declaration")
    inventories = []
    for name, axiom_string in printed:
        axioms = [re.sub(r"\.\{[^}]*\}", "", a.strip())
                  for a in axiom_string.split(",") if a.strip()]
        if not set(axioms).issubset(ALLOW_AXIOMS):
            raise SystemExit(f"Unexpected axioms in {name}: {axioms}")
        inventories.append({"theorem": name, "axioms": axioms})
    replay = None
    if args.fresh_kernel:
        command = [str(checker), "--fresh", "--verbose", "QuarticMaxwell"]
        with (logs / "fresh-kernel.log").open("w", encoding="utf-8") as replay_log:
            replay_result = subprocess.run(command, cwd=ROOT, env=env, stdout=replay_log,
                                           stderr=subprocess.STDOUT, text=True, encoding="utf-8")
        replay = {"exitCode": replay_result.returncode, "sameKernelImplementation": True,
                  "log": "verification/logs/fresh-kernel.log"}
        if replay_result.returncode:
            raise SystemExit(replay_result.returncode)
    after = {str(p.relative_to(ROOT)): sha(p) for p in source_paths}
    if before != after:
        raise SystemExit("Sources changed during verification")
    report = {"leanVersion": version, "mathlibCommit": pin, "startedUTC": started,
              "finishedUTC": datetime.now(timezone.utc).isoformat(),
              "implementedLemmasKernelVerified": True,
              "completePhysicalManuscriptTheoremsVerified": False,
              "sourceHashes": before, "moduleResults": results,
              "axiomInventories": inventories, "allExportedDeclarationsAudited": True,
              "exportedDeclarationNames": declarations,
              "exportedTypesAndAxioms": "verification/logs/Audit.log",
              "inventorySHA256": sha(inventory), "verifierSHA256": sha(Path(__file__)),
              "publicRootManifestSHA256": sha(manifest_path),
              "claimCoverageSHA256": sha(ROOT / manifest["claimCoverage"]),
              "freshKernelReplay": replay}
    (ROOT / "verification/report.json").write_text(json.dumps(report, indent=2) + "\n", encoding="utf-8")
    print("Implemented lemmas compiled; standard axiom inventories passed. Physical manuscript verification remains incomplete.")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
