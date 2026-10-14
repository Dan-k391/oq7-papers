"""Package already verified source; never rebuild or mutate old proof/reference files."""
from pathlib import Path
import hashlib
import json
import os
import zipfile
from datetime import datetime, timezone

ROOT = Path(__file__).resolve().parents[1]
OLD = ROOT.parent / "oq7"
ARCHIVE = ROOT.parent / "OQ7_Mission_Audit_2026-10-10.zip"


def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest().upper()


def load(path):
    return json.loads(path.read_text(encoding="utf-8-sig"))


def files(root):
    for folder, dirs, names in os.walk(root, followlinks=False):
        dirs[:] = [d for d in dirs if d not in {".lake", ".git", "__pycache__"}]
        for name in sorted(names):
            path = Path(folder) / name
            if path.name == "DELIVERY_CHECKS.json" or path.suffix in {".olean", ".ilean", ".pyc"}:
                continue
            yield path


def main():
    required = ["MATHEMATICAL_AUDIT.md", "MAXWELL_LOCALIZATION_AUDIT.md", "LEAN_STATUS.md",
                "NOVELTY_REVIEW.md", "VERIFICATION_REPORT.md", "README.md",
                "audits/AUDIT_A_ANALYTICAL.md", "audits/AUDIT_B_COUNTEREXAMPLES.md",
                "audits/AUDIT_C_MODEL_FIDELITY.md", "audits/LEAN_INVENTORY.md"]
    for item in required:
        assert (ROOT / item).is_file() and (ROOT / item).stat().st_size > 200, item
    old_report = load(OLD / "verification/report.json")
    assert old_report["lakeBuildPassed"] and old_report["cleanProjectBuild"]
    assert old_report["theorem51Proof"] == "OQ7.theorem51"
    new_report = load(ROOT / "lean/verification/report.json")
    assert new_report["lakeBuildPassed"] and new_report["cleanProjectBuild"]
    assert new_report["declaredMathematicalAxiomCount"] == 0
    assert new_report["originalProjectSourceAndConfigurationUnchanged"]
    assert set(new_report["allowedFoundationAxioms"]) == {"propext", "Classical.choice", "Quot.sound"}
    new_hashes = new_report["sourceHashes"] + new_report["configurationHashes"] + new_report["evidenceHashes"]
    for record in new_hashes:
        assert digest(ROOT / "lean" / record["file"]) == record["sha256"].upper(), record["file"]
    for key in ["fullMainResultDependencies", "fullOriginalTheorem51Dependencies"]:
        assert (ROOT / "lean" / new_report[key]).is_file()
    old_hashes = old_report["sourceHashes"] + old_report["configurationHashes"]
    for record in old_hashes:
        assert digest(OLD / record["file"]) == record["sha256"].upper(), record["file"]
    refs = load(ROOT / "reference_manifest.json")
    # The extraction manifest retains actual original and copied paths.
    reference_checks = []
    for key, record in (refs.items() if isinstance(refs, dict) else enumerate(refs)):
        if not isinstance(record, dict):
            continue
        paths = [record[k] for k in ["original", "copy"] if k in record]
        expected = next((v.upper() for k, v in record.items() if "sha" in k.lower()), None)
        if expected:
            existing = [Path(p) for p in paths if Path(p).is_file()]
            assert existing, key
            for path in existing:
                assert digest(path) == expected, str(path)
            reference_checks.append({"item": record.get("id", key), "checkedPaths": [str(p) for p in existing], "sha256": expected})
    assert len(reference_checks) == 3, "all three original reference hash records required"
    controls = load(ROOT / "integrity-tests/results.json")
    assert controls["allExpectedOutcomesObserved"]
    assert len(controls["tests"]) == 6 and all(x["expectationMet"] for x in controls["tests"])
    assert not controls["changedOriginalFiles"]
    numerical = load(ROOT / "numerics/audit_b_results.json")
    for record in numerical["symbolic"].values():
        if isinstance(record, dict) and "is_zero" in record:
            assert record["is_zero"]
    assert len(numerical["finite_dense_DDA"]) == 7
    assert numerical["random_symmetric_contractions"]["samples"] == 12000
    assert numerical["random_symmetric_contractions"]["largest_delta_minus_bound"] <= 0
    for entry in numerical["finite_dense_DDA"]:
        assert max(abs(x["optical_theorem_error"]) for x in entry["observables"]) < 1e-10
        assert max(abs(x["minus_Gram_scattering"]) for x in entry["sphere_checks"]) < 1e-10
    members = {}
    for prefix, directory in [("oq7-mission", ROOT), ("scalar-lean", OLD)]:
        for path in files(directory):
            name = prefix + "/" + path.relative_to(directory).as_posix()
            members[name] = path
    with zipfile.ZipFile(ARCHIVE, "w", compression=zipfile.ZIP_DEFLATED, compresslevel=6) as z:
        for name, path in sorted(members.items()):
            z.write(path, name)
    with zipfile.ZipFile(ARCHIVE) as z:
        assert z.testzip() is None
        assert set(z.namelist()) == set(members)
        for name, path in members.items():
            assert hashlib.sha256(z.read(name)).hexdigest().upper() == digest(path), name
        assert not any("/.lake/" in name for name in z.namelist())
    checks = {"checkedAtUTC": datetime.now(timezone.utc).isoformat(),
              "requiredArtifacts": required, "oldProofHashesChecked": len(old_hashes),
              "newProofAndEvidenceHashesChecked": len(new_hashes),
              "newCleanBuildVerifiedAtUTC": new_report["verifiedAtUTC"],
              "newPublicDeclarationCount": new_report["authoredTheoremCount"],
              "newKernelTheoremConstantCount": new_report["kernelTheoremConstantCount"],
              "referenceChecks": reference_checks, "negativeControlsReport": str(ROOT / "integrity-tests/results.json"),
              "negativeControlExpectedOutcomesChecked": controls["allExpectedOutcomesObserved"],
              "symbolicAllZero": True, "finiteDDARecords": 7, "randomSearchSamples": 12000,
              "archivePath": str(ARCHIVE), "archiveSHA256": digest(ARCHIVE),
              "archiveBytes": ARCHIVE.stat().st_size, "archiveFiles": len(members),
              "everyArchiveMemberHashChecked": True, "dependencyCachesExcluded": True}
    (ROOT / "DELIVERY_CHECKS.json").write_text(json.dumps(checks, indent=2), encoding="utf-8")
    print(json.dumps({k: checks[k] for k in ["oldProofHashesChecked", "archiveSHA256", "archiveBytes", "archiveFiles"]}, indent=2))


if __name__ == "__main__":
    main()
