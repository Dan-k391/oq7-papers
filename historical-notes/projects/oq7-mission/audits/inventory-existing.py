"""Read-only inventory of the preserved project; writes only beside this script."""
from __future__ import annotations
import hashlib
import json
from pathlib import Path
import re
import subprocess
from datetime import datetime, timezone

AUDIT_DIR = Path(__file__).resolve().parent
PROJECT = AUDIT_DIR.parent.parent / "oq7"
GIT = Path(r"C:\Users\Daniel\.cache\codex-runtimes\codex-primary-runtime\dependencies\native\git\cmd\git.exe")
REPORT_PATH = PROJECT / "verification/report.json"
REPORT = json.loads(REPORT_PATH.read_text(encoding="utf-8-sig"))

def sha(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest().upper()

def uncomment(code: str) -> str:
    # Match the existing auditor's conservative lexical gate; the independent
    # kernel census and transitive axiom whitelist are also checked below.
    return re.sub(r"(?m)--[^\r\n]*", "", re.sub(r"(?s)/-.*?-/", "", code))

sources = sorted((PROJECT / "OQ7").glob("*.lean"))
declarations = []
disallowed_sources = []
for source in sources:
    text = source.read_text(encoding="utf-8-sig")
    code = uncomment(text)
    namespace = re.findall(r"(?m)^namespace\s+([A-Za-z0-9_.]+)\s*$", code)
    if len(namespace) != 1:
        raise RuntimeError(f"Unexpected namespaces: {source.name}: {namespace}")
    if re.search(r"\b(sorry|admit|axiom|native_decide)\b|debug\.skipKernelTC|decide\s*\+native|implemented_by", code):
        disallowed_sources.append(source.name)
    for match in re.finditer(r"(?m)^\s*(?:@\[[^\]\r\n]*\]\s*)*(?:theorem|lemma)\s+([^\s:({\[]+)", code):
        name = namespace[0] + "." + match.group(1)
        # Line references are recovered from original source bytes, not comment-stripped text.
        original = re.search(r"(?m)^\s*(?:@\[[^\]\r\n]*\]\s*)*(?:theorem|lemma)\s+" + re.escape(match.group(1)) + r"(?=[\s:({\[])", text)
        line = text.count("\n", 0, original.start()) + 1 if original else None
        declarations.append({"name": name, "file": "OQ7/" + source.name, "line": line})

hash_records = REPORT["sourceHashes"] + REPORT["configurationHashes"]
hash_mismatches = [r["file"] for r in hash_records if sha(PROJECT / r["file"]) != r["sha256"]]
inventory = (PROJECT / "verification/inventory.log").read_text(encoding="utf-8-sig")
kernel_names = set(re.findall(r"OQ7-AUDIT-THEOREM\s+(\S+)", inventory))
declared_axioms = re.findall(r"OQ7-AUDIT-AXIOM\s+(\S+)", inventory)
axiom_text = (PROJECT / "verification/axioms.log").read_text(encoding="utf-8-sig")
axiom_records = {}
for match in re.finditer(r"'([^']+)' (?:depends on axioms: \[([^\]]*)\]|does not depend on any axioms)", axiom_text):
    axiom_records[match.group(1)] = [x.strip() for x in (match.group(2) or "").split(",") if x.strip()]
allowed = {"propext", "Classical.choice", "Quot.sound"}
forbidden = {name: axioms for name, axioms in axiom_records.items() if not set(axioms) <= allowed}
statement_bytes = (PROJECT / "verification/statements.log").read_bytes()
statement_text = statement_bytes.decode("utf-8-sig")
type_names = set(re.findall(r"(?m)^@?(OQ7\.[^\s:{]+?)(?:\.\{[^}]*\})?\s*:", statement_text))
type_match = re.search(br"(?m)^OQ7\.theorem51 :[^\r\n]*(?:\r\n|\n|$)", statement_bytes)
if type_match is None:
    raise RuntimeError("Missing exact exported theorem51 type")
type_file = AUDIT_DIR / "OQ7.theorem51-type.txt"
type_file.write_bytes(type_match.group())
audit_source = (PROJECT / "verification/Audit.lean").read_text(encoding="utf-8-sig")
example_found = bool(re.search(r"(?m)^example \(p : OQ7\.PhysicalParameters\) : OQ7\.Theorem51Statement p := OQ7\.theorem51 p\r?$", audit_source))

manifest = json.loads((PROJECT / "lake-manifest.json").read_text(encoding="utf-8-sig"))
dependencies = []
for package in manifest["packages"]:
    path = PROJECT / ".lake/packages" / package["name"]
    rev = subprocess.run([str(GIT), "--no-optional-locks", "-C", str(path), "rev-parse", "HEAD"], check=True, capture_output=True, text=True).stdout.strip()
    dirty = subprocess.run([str(GIT), "--no-optional-locks", "-C", str(path), "status", "--porcelain", "--untracked-files=no"], check=True, capture_output=True, text=True).stdout
    dependencies.append({"name": package["name"], "manifestRevision": package["rev"], "actualRevision": rev, "matchesPin": rev == package["rev"], "trackedSourceClean": not dirty.strip()})

build_text = (PROJECT / "verification/build.log").read_text(encoding="utf-8-sig")
clean_text = (PROJECT / "verification/clean.log").read_text(encoding="utf-8-sig")
checks = {
    "sourceConfigurationHashesMatch": not hash_mismatches,
    "sourceNamesMatchReport": {d["name"] for d in declarations} == set(REPORT["theoremNames"]),
    "sourceNamesAllImported": {d["name"] for d in declarations} <= kernel_names,
    "kernelCensusMatchesReport": kernel_names == set(REPORT["kernelTheoremNames"]),
    "kernelAxiomCoverageComplete": kernel_names <= set(axiom_records),
    "onlyAllowedFoundationAxioms": not forbidden,
    "noDeclaredMathematicalAxioms": not declared_axioms,
    "noDisallowedSourceMechanisms": not disallowed_sources,
    "allPublicExactTypesPresent": set(REPORT["theoremNames"]) <= type_names,
    "allPinnedDependenciesPresentClean": all(p["matchesPin"] and p["trackedSourceClean"] for p in dependencies),
    "arbitraryParameterExamplePresent": example_found,
    "savedCleanBuildPassed": REPORT["cleanProjectBuild"] and REPORT["lakeBuildPassed"] and "Build completed successfully (3043 jobs)." in build_text,
    "finalExactType": type_match.group().decode("utf-8").strip() == "OQ7.theorem51 : ∀ (p : OQ7.PhysicalParameters), OQ7.Theorem51Statement p",
}
evidence_paths = [
    "OQ7/SharpPhysicalConstruction.lean", "OQ7/Target.lean", "OQ7/ResourceTheorem45.lean",
    "verification/report.json", "verification/build.log", "verification/clean.log",
    "verification/statements.log", "verification/axioms.log", "verification/inventory.log",
    "sources/OQ7_verified_research_note.pdf", "sources/original-checkpoint.md",
    ".lake/build/lib/lean/OQ7/SharpPhysicalConstruction.olean",
]
summary = {
    "inventoriedAtUTC": datetime.now(timezone.utc).isoformat(),
    "mode": "Read-only inspection of existing sources, dependencies and saved successful logs; no build performed",
    "project": str(PROJECT), "savedVerifiedAtUTC": REPORT["verifiedAtUTC"],
    "lean": REPORT["lean"], "mathlibCommit": REPORT["mathlibCommit"],
    "sourceModuleCount": len(sources), "authoredPublicTheoremDeclarationCount": len(declarations),
    "kernelTheoremConstantCount": len(kernel_names), "exactTypesFound": len(type_names),
    "axiomReportsFound": len(axiom_records), "sourceConfigurationHashesChecked": len(hash_records),
    "checks": checks, "allChecksPassed": all(checks.values()),
    "hashMismatches": hash_mismatches, "forbiddenAxioms": forbidden,
    "declaredMathematicalAxioms": declared_axioms, "disallowedSources": disallowed_sources,
    "dependencyRevisions": dependencies, "theorem51ExactType": type_match.group().decode("utf-8").strip(),
    "theorem51TypeFileSHA256": sha(type_file),
    "theorem51Axioms": axiom_records.get("OQ7.theorem51"),
    "evidenceSHA256": {name: sha(PROJECT / name) for name in evidence_paths},
    "scope": "This script inventories existing proof artifacts only. Manual correspondence to the old 18-page note and, after it was located, the new Paper A Theorems 4.5/5.1 is documented separately in LEAN_INVENTORY.md. No Paper B analytical theorem follows from this census.",
}
(AUDIT_DIR / "existing-inventory.json").write_text(json.dumps(summary, indent=2, ensure_ascii=False) + "\n", encoding="utf-8")
(AUDIT_DIR / "source-declarations.tsv").write_text("name\tfile\tline\n" + "".join(f"{d['name']}\t{d['file']}\t{d['line']}\n" for d in declarations), encoding="utf-8")
print(json.dumps({"allChecksPassed": summary["allChecksPassed"], "sourceModuleCount": len(sources), "publicDeclarations": len(declarations), "kernelConstants": len(kernel_names), "hashRecords": len(hash_records), "exactTypeSHA256": sha(type_file)}, ensure_ascii=False))
if not all(checks.values()):
    raise SystemExit(1)
