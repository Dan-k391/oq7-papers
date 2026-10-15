"""Compile and audit the complete new generalized-paper Lean project.

This script restores no dependencies and changes no pinned or historical source.
First restore/build the repository's prescribed-extinction project as documented.
The default final run performs one fresh kernel replay; --elaborate-only is for
development and explicitly records that no fresh replay was performed.
"""

from __future__ import annotations

import argparse
import datetime as dt
import hashlib
import json
import os
from pathlib import Path
import re
import shutil
import subprocess
import sys
import time

PROJECT = Path(__file__).resolve().parent
REPO = PROJECT.parents[2]
BASE = REPO / "papers" / "prescribed-extinction" / "formalization"
EXPECTED_TOOLCHAIN = "leanprover/lean4:v4.34.1"
EXPECTED_MATHLIB = "d13f23b723b8a846827a245b89c10fc7d3f11612"


def digest(path: Path) -> str:
    value = hashlib.sha256()
    with path.open("rb") as stream:
        for block in iter(lambda: stream.read(1024 * 1024), b""):
            value.update(block)
    return value.hexdigest()


def utc_now() -> str:
    return dt.datetime.now(dt.timezone.utc).isoformat()


def lean_code(text: str) -> str:
    """Remove nested Lean comments and strings before checking escape hatches."""
    result: list[str] = []
    pos, depth = 0, 0
    while pos < len(text):
        pair = text[pos : pos + 2]
        if depth:
            if pair == "/-":
                depth += 1
                pos += 2
            elif pair == "-/":
                depth -= 1
                pos += 2
            else:
                result.append("\n" if text[pos] == "\n" else " ")
                pos += 1
        elif pair == "/-":
            depth = 1
            result.extend("  ")
            pos += 2
        elif pair == "--":
            end = text.find("\n", pos)
            if end < 0:
                end = len(text)
            result.extend(" " * (end - pos))
            pos = end
        elif text[pos] == '"':
            result.append(" ")
            pos += 1
            while pos < len(text):
                if text[pos] == "\\":
                    result.extend("  ")
                    pos += 2
                elif text[pos] == '"':
                    result.append(" ")
                    pos += 1
                    break
                else:
                    result.append("\n" if text[pos] == "\n" else " ")
                    pos += 1
        else:
            result.append(text[pos])
            pos += 1
    if depth:
        raise RuntimeError("Unterminated Lean block comment")
    return "".join(result)


def source_graph() -> tuple[dict[str, Path], dict[str, list[str]], list[str]]:
    files = {"GeneralizedResearch": PROJECT / "GeneralizedResearch.lean"}
    files.update(
        {"GeneralizedResearch." + str(path.relative_to(PROJECT / "GeneralizedResearch")).replace(os.sep, ".")[:-5]: path
         for path in sorted((PROJECT / "GeneralizedResearch").rglob("*.lean"))}
    )
    imports: dict[str, list[str]] = {}
    for module, path in files.items():
        code = lean_code(path.read_text(encoding="utf-8-sig"))
        if re.search(r"\b(?:sorry|admit|native_decide)\b|^\s*(?:unsafe\s+)?axiom\s", code, re.M):
            raise RuntimeError("Proof escape hatch in " + str(path))
        imports[module] = re.findall(r"^\s*(?:public\s+)?import\s+(GeneralizedResearch(?:\.[A-Za-z_][A-Za-z0-9_]*)*)\s*$", code, re.M)
        for dependency in imports[module]:
            if dependency not in files:
                raise RuntimeError(f"Missing new source module {dependency}, imported by {module}")
    order: list[str] = []
    visiting: set[str] = set()
    visited: set[str] = set()

    def visit(module: str) -> None:
        if module in visiting:
            raise RuntimeError("Import cycle at " + module)
        if module in visited:
            return
        visiting.add(module)
        for dependency in imports[module]:
            visit(dependency)
        visiting.remove(module)
        visited.add(module)
        order.append(module)

    visit("GeneralizedResearch")
    if visited != set(files):
        missing = sorted(set(files) - visited)
        raise RuntimeError("The aggregate omits new modules: " + ", ".join(missing))
    return files, imports, order


def check_expected_public_roots(census: str, manifest: dict) -> int:
    """An exhaustive dynamic census must also retain the explicitly named roots.

    This checks exact printed kernel types for retained public correspondence
    roots. It supplements, and never replaces, the complete transitive-axiom
    scan performed inside Audit.lean for every current theorem declaration.
    """
    entries = re.findall(r"^THEOREM (\S+)\nTYPE (.*?)\nAXIOMS \[.*?\]$", census, re.M | re.S)
    actual = {name: type_text for name, type_text in entries}
    if len(actual) != len(entries):
        raise RuntimeError("Duplicate names in exhaustive theorem census")
    count = re.search(r"^THEOREM_CENSUS_COUNT (\d+)$", census, re.M)
    if count is None or int(count[1]) != len(actual):
        raise RuntimeError("Theorem census count does not match complete type records")
    expected = manifest.get("roots", [])
    names = [root["name"] for root in expected]
    if not names or len(names) != len(set(names)):
        raise RuntimeError("Expected public-root manifest is empty or duplicated")
    if len(actual) < manifest.get("minimum_exhaustive_theorem_count", 0):
        raise RuntimeError("Exhaustive theorem count is below the retained baseline")
    for root in expected:
        name = root["name"]
        if name not in actual:
            raise RuntimeError("Required public theorem is missing: " + name)
        type_hash = hashlib.sha256(actual[name].encode("utf-8")).hexdigest()
        if type_hash != root["printed_kernel_type_sha256"]:
            raise RuntimeError("Required public theorem type changed: " + name)
    return len(expected)


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--lean-bin", type=Path, help="Directory containing the exact pinned lean and leanchecker binaries")
    parser.add_argument("--output-dir", type=Path, default=PROJECT / "verification")
    parser.add_argument("--elaborate-only", action="store_true", help="Development mode: no fresh kernel replay and no final verification claim")
    args = parser.parse_args()
    output = args.output_dir.resolve()
    output.mkdir(parents=True, exist_ok=True)
    report: dict = {
        "started_utc": utc_now(), "status": "running", "project": "oq7_generalized_research",
        "lean_toolchain": EXPECTED_TOOLCHAIN, "mathlib_revision": EXPECTED_MATHLIB,
        "fresh_kernel_requested": not args.elaborate_only, "fresh_kernel_passed": False,
        "same_kernel_implementation": True, "independent_kernel_implementation": False,
        "steps": [], "scope": "Every source module reachable from GeneralizedResearch.lean; exact theorem types and transitive axioms are recorded separately. This is not a claim that every manuscript statement has been formalized.",
    }
    manifest = output / "report.json"

    def save() -> None:
        manifest.write_text(json.dumps(report, indent=2) + "\n", encoding="utf-8")

    try:
        if (PROJECT / "lean-toolchain").read_text().strip() != EXPECTED_TOOLCHAIN:
            raise RuntimeError("New project toolchain pin changed")
        if (BASE / "lean-toolchain").read_text().strip() != EXPECTED_TOOLCHAIN:
            raise RuntimeError("Historical project toolchain pin changed")
        pins = json.loads((BASE / "lake-manifest.json").read_text(encoding="utf-8-sig"))
        mathlib = next(package for package in pins["packages"] if package["name"] == "mathlib")
        if mathlib["rev"] != EXPECTED_MATHLIB:
            raise RuntimeError("Historical Mathlib pin changed")
        packages = BASE / ".lake" / "packages"
        for package in pins["packages"]:
            path = packages / package["name"]
            actual = subprocess.check_output(["git", "-C", str(path), "rev-parse", "HEAD"], text=True).strip()
            if actual != package["rev"]:
                raise RuntimeError("Dependency checkout revision changed: " + package["name"])
            if subprocess.run(["git", "-C", str(path), "diff", "--quiet", "HEAD", "--"], check=False).returncode:
                raise RuntimeError("Pinned dependency has modified tracked source: " + package["name"])
        report["dependency_revisions"] = {p["name"]: p["rev"] for p in pins["packages"]}
        executable = "lean.exe" if os.name == "nt" else "lean"
        checker_executable = "leanchecker.exe" if os.name == "nt" else "leanchecker"
        bin_path = args.lean_bin
        if bin_path is None:
            bundled = REPO / ".local" / "toolchains" / "lean-4.34.1-windows" / "bin"
            if (bundled / executable).is_file():
                bin_path = bundled
            else:
                located = shutil.which("lean")
                if not located:
                    raise RuntimeError("Activate the pinned Lean toolchain or supply --lean-bin")
                bin_path = Path(located).parent
        lean = bin_path.resolve() / executable
        checker = bin_path.resolve() / checker_executable
        version = subprocess.check_output([str(lean), "--version"], text=True).strip()
        if not re.search(r"Lean \(version 4\.34\.1(?:,|\))", version):
            raise RuntimeError("Compiler version differs from the repository pin: " + version)
        report["compiler_version"] = version
        report["compiler_sha256"] = digest(lean)
        report["checker_sha256"] = digest(checker)
        base_lib = BASE / ".lake" / "build" / "lib" / "lean"
        if not (base_lib / "OQ7" / "SharpPhysicalConstruction.olean").is_file():
            raise RuntimeError("Build the preserved OQ7 scalar physical library first")
        build_lib = PROJECT / ".lake" / "build" / "lib" / "lean"
        build_lib.mkdir(parents=True, exist_ok=True)
        environment = os.environ.copy()
        environment["PATH"] = str(bin_path.resolve()) + os.pathsep + environment.get("PATH", "")
        environment["LEAN_PATH"] = os.pathsep.join(
            str(path) for path in [build_lib, base_lib] +
            [packages / p["name"] / ".lake" / "build" / "lib" / "lean" for p in pins["packages"]]
        )
        files, graph, order = source_graph()
        record_sources = sorted(set(files.values()) | {PROJECT / "Audit.lean", PROJECT / "lean-toolchain", PROJECT / "lakefile.toml", PROJECT / "expected-public-roots.json", PROJECT / "negative_controls.py", Path(__file__).resolve()})
        source_hashes = {str(path.relative_to(REPO)).replace(os.sep, "/"): digest(path) for path in record_sources}
        report["source_sha256"] = source_hashes
        report["compile_order"] = order
        report["import_graph"] = graph
        report["historical_library_sha256"] = {
            str(path.relative_to(REPO)).replace(os.sep, "/"): digest(path)
            for path in sorted(
                list((BASE / "OQ7").rglob("*.lean")) +
                list((BASE / "PrescribedExtinction").rglob("*.lean")) +
                [BASE / "OQ7.lean", BASE / "PrescribedExtinction.lean", BASE / "lean-toolchain", BASE / "lakefile.toml", BASE / "lake-manifest.json"]
            )
        }
        report["manuscript_inputs"] = {
            str(path.relative_to(REPO)).replace(os.sep, "/"): digest(path)
            for path in [PROJECT.parent / "manuscript" / "OQ7_generalized_research_2026-10-10.pdf", PROJECT.parent / "arxiv" / "main.tex"]
            if path.is_file()
        }
        save()

        def run(label: str, command: list[str], log_name: str) -> None:
            print("RUN " + label, flush=True)
            started = time.monotonic()
            log = output / log_name
            with log.open("wb") as stream:
                process = subprocess.Popen(command, cwd=PROJECT, env=environment, stdout=stream, stderr=subprocess.STDOUT, stdin=subprocess.DEVNULL)
                while True:
                    try:
                        code = process.wait(timeout=30)
                        break
                    except subprocess.TimeoutExpired:
                        print(f"RUNNING {label} ({int(time.monotonic() - started)} seconds)", flush=True)
            step = {"label": label, "command": command, "exit_code": code, "seconds": round(time.monotonic() - started, 3), "log": log_name, "log_sha256": digest(log)}
            report["steps"].append(step)
            save()
            if code:
                print(log.read_text(encoding="utf-8", errors="replace")[-10000:], flush=True)
                raise RuntimeError(label + " failed")
            print("PASS " + label, flush=True)

        for module in order:
            target = build_lib.joinpath(*module.split(".")).with_suffix(".olean")
            target.parent.mkdir(parents=True, exist_ok=True)
            run(module, [str(lean), "-o", str(target), str(files[module].relative_to(PROJECT))], module + ".log")
        run("exhaustive theorem type/axiom census", [str(lean), "Audit.lean"], "types-and-axioms.log")
        census = (output / "types-and-axioms.log").read_text(encoding="utf-8")
        count = re.search(r"THEOREM_CENSUS_COUNT (\d+)", census)
        if not count:
            raise RuntimeError("The exhaustive audit did not report a theorem count")
        report["theorem_declaration_count_including_generated"] = int(count[1])
        roots_manifest = json.loads((PROJECT / "expected-public-roots.json").read_text(encoding="utf-8"))
        report["required_public_root_count"] = check_expected_public_roots(census, roots_manifest)
        if not args.elaborate_only:
            run("fresh kernel replay", [str(checker), "--fresh", "--verbose", "GeneralizedResearch"], "leanchecker-fresh.log")
            report["fresh_kernel_passed"] = True
        final_files, final_graph, final_order = source_graph()
        if set(final_files) != set(files) or final_graph != graph or final_order != order:
            raise RuntimeError("New source modules or imports changed during verification")
        for relative, expected in source_hashes.items():
            if digest(REPO / relative) != expected:
                raise RuntimeError("Source changed during verification: " + relative)
        for relative, expected in report["historical_library_sha256"].items():
            if digest(REPO / relative) != expected:
                raise RuntimeError("Historical source changed during verification: " + relative)
        report["artifact_sha256"] = {
            str(path.relative_to(PROJECT)).replace(os.sep, "/"): digest(path)
            for path in sorted(build_lib.rglob("*.olean"))
        }
        report["status"] = "elaboration-and-axioms-passed" if args.elaborate_only else "fresh-kernel-passed"
        report["finished_utc"] = utc_now()
        save()
        print("VERIFICATION " + report["status"], flush=True)
        return 0
    except Exception as error:
        report["status"] = "failed"
        report["error"] = str(error)
        report["finished_utc"] = utc_now()
        save()
        print("FAILED: " + str(error), file=sys.stderr, flush=True)
        return 1


if __name__ == "__main__":
    raise SystemExit(main())
