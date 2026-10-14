"""Re-run a paper audit described by <audit-dir>/audit.json.

    python scripts/run-paper-audit.py papers/quartic-maxwell/audit-2026-10-14
    python scripts/run-paper-audit.py papers/generalized-research/audit-2026-10-14 --kernel

Steps, in order; any failure makes the exit status nonzero:
  1. Verify the SHA-256 of every audited source file.
  2. Run every check script with `python -I` and store its JSON result.
  3. Elaborate every audit Lean file in the pinned prescribed-extinction build
     environment and reject errors, `sorry` and any axiom outside
     propext / Classical.choice / Quot.sound.
  4. For each replay entry, print the declaration types and axioms from the
     compiled environment; with --kernel, also run `leanchecker --fresh`.
Logs go to <audit-dir>/logs/.  Nothing outside the audit directory is written.
The pinned toolchain is taken from .local/toolchains/lean-4.34.1-windows/bin
unless the LEAN_BIN environment variable names another directory.
"""

import argparse
import datetime as dt
import hashlib
import json
import os
import re
import shutil
import subprocess
import sys
import tempfile
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
LAKE_PROJECT = ROOT / "papers" / "prescribed-extinction" / "formalization"
STANDARD_AXIOMS = {"propext", "Classical.choice", "Quot.sound"}


def sha256(path):
    h = hashlib.sha256()
    with open(path, "rb") as fh:
        for block in iter(lambda: fh.read(1 << 20), b""):
            h.update(block)
    return h.hexdigest()


def lean_env():
    env = dict(os.environ)
    lean_bin = os.environ.get("LEAN_BIN") or str(ROOT / ".local" / "toolchains" / "lean-4.34.1-windows" / "bin")
    env["PATH"] = lean_bin + os.pathsep + env.get("PATH", "")
    lake = shutil.which("lake", path=env["PATH"])
    if lake is None:
        sys.exit(f"lake not found; restore the pinned toolchain into {lean_bin} or set LEAN_BIN")
    return env, lake


def run(cmd, cwd, env=None, log=None):
    proc = subprocess.run(cmd, cwd=cwd, env=env, capture_output=True, text=True, encoding="utf-8", errors="replace")
    out = proc.stdout + proc.stderr
    if log:
        log.write_text(out, encoding="utf-8")
    return proc.returncode, out


def axiom_problems(output):
    problems = []
    if re.search(r"(^|:)\s*error", output, re.MULTILINE):
        problems.append("elaboration error")
    if "declaration uses `sorry`" in output or "sorryAx" in output:
        problems.append("sorry")
    for decl, axioms in re.findall(r"'([^']+)' depends on axioms: \[([^\]]*)\]", output):
        extra = {a.strip() for a in axioms.split(",") if a.strip()} - STANDARD_AXIOMS
        if extra:
            problems.append(f"{decl}: {sorted(extra)}")
    return problems


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("audit_dir")
    ap.add_argument("--kernel", action="store_true", help="also run leanchecker --fresh for replay modules")
    args = ap.parse_args()
    adir = (ROOT / args.audit_dir).resolve() if not Path(args.audit_dir).is_absolute() else Path(args.audit_dir)
    cfg = json.loads((adir / "audit.json").read_text(encoding="utf-8"))
    logs = adir / "logs"
    logs.mkdir(exist_ok=True)
    summary = {"started": dt.datetime.now(dt.timezone.utc).isoformat(timespec="seconds"), "audit": cfg.get("name"),
               "steps": []}
    ok_all = True

    def record(step, ok, detail=""):
        nonlocal ok_all
        ok_all &= ok
        summary["steps"].append({"step": step, "pass": ok, "detail": detail})
        print(("PASS " if ok else "FAIL ") + step + (f"  {detail}" if detail else ""))

    for src in cfg.get("sources", []):
        got = sha256(ROOT / src["path"])
        record(f"sha256 {src['path']}", got == src["sha256"], got)

    for chk in cfg.get("checks", []):
        script = adir / chk["script"]
        out = adir / chk["output"]
        code, text = run([sys.executable, "-I", str(script), str(out)], cwd=script.parent,
                         log=logs / (Path(chk["script"]).stem + ".log"))
        record(f"check {chk['script']}", code == 0, text.strip().splitlines()[-1] if text.strip() else "")

    env, lake = lean_env()
    for lean_file in cfg.get("lean", []):
        path = adir / lean_file
        code, text = run([lake, "env", "lean", str(path)], cwd=LAKE_PROJECT, env=env,
                         log=logs / (Path(lean_file).stem + ".lean.log"))
        problems = axiom_problems(text)
        n = len(re.findall(r"depends on axioms", text))
        record(f"lean {lean_file}", code == 0 and not problems and n > 0, f"{n} axiom reports; {problems or 'clean'}")

    for rep in cfg.get("replays", []):
        lines = [f"import {rep['import']}"]
        for decl in rep["declarations"]:
            lines += [f"#check @{decl}", f"#print axioms {decl}"]
        for d in rep.get("print", []):
            lines.append(f"#print {d}")
        with tempfile.TemporaryDirectory() as tmp:
            f = Path(tmp) / "Replay.lean"
            f.write_text("\n".join(lines) + "\n", encoding="utf-8")
            code, text = run([lake, "env", "lean", str(f)], cwd=LAKE_PROJECT, env=env,
                             log=logs / f"replay-{rep['import']}.log")
        problems = axiom_problems(text)
        record(f"replay {rep['import']}", code == 0 and not problems, problems or "standard axioms only")
        if args.kernel:
            for module in rep.get("kernel_modules", []):
                code, text = run([lake, "env", "leanchecker", "--fresh", "--verbose", module], cwd=LAKE_PROJECT,
                                 env=env, log=logs / f"leanchecker-{module}.log")
                record(f"leanchecker --fresh {module}", code == 0, text.strip().splitlines()[-1] if text.strip() else "")

    summary["finished"] = dt.datetime.now(dt.timezone.utc).isoformat(timespec="seconds")
    summary["all_pass"] = ok_all
    (logs / "last-run.json").write_text(json.dumps(summary, indent=1), encoding="utf-8")
    sys.exit(0 if ok_all else 1)


if __name__ == "__main__":
    main()
