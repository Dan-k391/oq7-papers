from pathlib import Path
import csv,datetime,hashlib,json,os,re,subprocess,sys,zipfile
ROOT=Path(r"C:\Users\Daniel\.codex\.chatgpt-projects\g-p-6ac8784424248191b154eb2ed308e1f1");OUT=Path(r"C:\Users\Daniel\.codex\.chatgpt-projects\g-p-6ac8784424248191b154eb2ed308e1f1\outputs\OQ7-final-review-20261013-0c32f324");WORK=Path(r"C:\Users\Daniel\.codex\.chatgpt-projects\g-p-6ac8784424248191b154eb2ed308e1f1\work\s0c32f324");REPO=WORK/"repo";LOG=OUT/"verification"
LEANBIN=ROOT/"work/a89f0ec7/tools/lean-4.34.1-windows/bin"
GIT=Path(r"C:\Users\Daniel\.cache\codex-runtimes\codex-primary-runtime\dependencies\native\git\cmd\git.exe")
env=dict(os.environ);env.update(PATH=str(LEANBIN)+os.pathsep+str(GIT.parent)+os.pathsep+env["PATH"],LEAN_NUM_THREADS="2",GIT_CONFIG_NOSYSTEM="1",GIT_CONFIG_GLOBAL="NUL",GIT_OPTIONAL_LOCKS="0",GIT_CONFIG_COUNT="1",GIT_CONFIG_KEY_0="core.longpaths",GIT_CONFIG_VALUE_0="true",MATHLIB_CACHE_DIR=str(WORK/"cache"),XDG_CACHE_HOME=str(WORK/"cache"),PYTHONUTF8="1")
def run(label,args):
    args=[str(a) for a in args];start=datetime.datetime.now(datetime.timezone.utc).isoformat();print("START "+label,flush=True)
    with (LOG/(label+".log")).open("wb") as f:
        proc=subprocess.Popen(args,cwd=REPO,env=env,stdout=f,stderr=subprocess.STDOUT)
        (WORK/"running-check.json").write_text(json.dumps(dict(label=label,pid=proc.pid,argv=args)),encoding="utf-8")
        try:exitcode=proc.wait(timeout=2400)
        except subprocess.TimeoutExpired:
            proc.terminate();exitcode=124;f.write(b"\nINCOMPLETE: bounded run exceeded 2400 seconds.\n")
    record=dict(label=label,argv=args,windows_command_line=subprocess.list2cmdline(args),cwd=str(REPO),started_utc=start,finished_utc=datetime.datetime.now(datetime.timezone.utc).isoformat(),exit_code=exitcode,log=label+".log",environment={k:env[k] for k in ["LEAN_NUM_THREADS","MATHLIB_CACHE_DIR","GIT_CONFIG_COUNT","GIT_CONFIG_KEY_0","GIT_CONFIG_VALUE_0"]})
    with (LOG/"COMMANDS.jsonl").open("a",encoding="utf-8") as f:f.write(json.dumps(record)+"\n")
    print("END "+label+" exit="+str(exitcode),flush=True)
    if exitcode:raise RuntimeError("Failed "+label+"; full log retained")
    return (LOG/(label+".log")).read_text(encoding="utf-8",errors="replace")
head=run("portable-commit",[GIT,"rev-parse","HEAD"]).strip()
if head!="0bdf00f9b75b43194436f9536b1bf09463fd5a5d":raise RuntimeError("Portable commit mismatch")
pins=json.loads((OUT/"release/dependency-sources/PINNED_DEPENDENCIES.json").read_text(encoding="utf-8"))["packages"];pinresults=[]
for pin in pins:
    package=REPO/".lake/packages"/pin["name"]
    actual=subprocess.run([str(GIT),"-C",str(package),"rev-parse","HEAD"],env=env,capture_output=True,text=True,check=True).stdout.strip()
    clean=subprocess.run([str(GIT),"-C",str(package),"diff","--quiet","HEAD","--"],env=env).returncode==0
    if actual!=pin["rev"] or not clean:raise RuntimeError("Dependency differs: "+pin["name"])
    pinresults.append(dict(name=pin["name"],expected_revision=pin["rev"],actual_revision=actual,tracked_source_clean=clean))
source_ids=[]
with zipfile.ZipFile(OUT/"release/frozen/OQ7-complete-physical-theorem11-source.zip") as z:
    for name in z.namelist():
        if name.endswith(".lean") and (name.startswith("OQ7/") or name.startswith("PrescribedExtinction/") or name in ["OQ7.lean","PrescribedExtinction.lean"]):
            frozen=z.read(name)
            if frozen!=(REPO/name).read_bytes():raise RuntimeError("Mathematical source differs: "+name)
            source_ids.append(dict(path=name,sha256=hashlib.sha256(frozen).hexdigest()))
(LOG/"PIN_AND_SOURCE_IDENTITIES.json").write_text(json.dumps(dict(pinned_dependencies=pinresults,library_modules=len(source_ids),source_files=source_ids),indent=2),encoding="utf-8")
print("PINS_AND_MATHEMATICAL_SOURCE_IDENTITIES_PASS",len(source_ids),flush=True)
diag=REPO/"release-diagnostics";diag.mkdir()
typecode="""import PrescribedExtinction
set_option pp.all true
set_option pp.universes true
set_option pp.fullNames true
#print OQ7Prescribed.PhysicalTheorem11Statement
#print OQ7Prescribed.Theorem11Statement
#print OQ7Prescribed.FullPhysicalOpticalStatement
#print OQ7Prescribed.MaterialAdmissible
#print OQ7Prescribed.TwoLayerBody
#print OQ7Prescribed.ScatteringState
run_cmd do
  let env ← Lean.getEnv
  match env.find? BQTOQ7Prescribed.theorem11_complete with
  | some (.thmInfo info) =>
      Lean.logInfo m!"FULLY-ELABORATED-FINAL-THEOREM-TYPE: {info.type}"
  | _ => throwError "Final declaration is missing or is not a theorem"
"""
axiomcode="""import PrescribedExtinction
example : OQ7Prescribed.PhysicalTheorem11Statement := OQ7Prescribed.theorem11_complete
#print axioms OQ7Prescribed.theorem11_complete
run_cmd do
  let env ← Lean.getEnv
  match env.find? BQTOQ7Prescribed.theorem11_complete with
  | some (.thmInfo info) =>
      unless info.type == Lean.mkConst BQTOQ7Prescribed.PhysicalTheorem11Statement do
        throwError "Final theorem has an unexpected type"
      let axioms ← Lean.collectAxioms BQTOQ7Prescribed.theorem11_complete
      for name in axioms do
        unless name == BQTpropext || name == BQTClassical.choice || name == BQTQuot.sound do
          throwError "Disallowed transitive axiom: {name}"
      Lean.logInfo "STRICT-AXIOM-AND-EXACT-TYPE-PASS"
  | _ => throwError "Final declaration is not a kernel theorem"
"""
(diag/"FinalType.lean").write_text(typecode.replace("BQT",chr(96)),encoding="utf-8")
(diag/"FinalAxioms.lean").write_text(axiomcode.replace("BQT",chr(96)),encoding="utf-8")
names=set()
with (OUT/"manuscript/theorem-correspondence.csv").open(encoding="utf-8-sig",newline="") as f:
    for row in csv.DictReader(f):names.update(re.findall(r"OQ7Prescribed\.[A-Za-z0-9_']+",row["lean_declarations"]))
code="import PrescribedExtinction\nrun_cmd do\n  let env ← Lean.getEnv\n"
for name in sorted(names):
    code+=f"  unless (env.find? {chr(96)}{name}).isSome do\n    throwError \"Missing correspondence declaration: {name}\"\n"
code+=f'  Lean.logInfo "CORRESPONDENCE-DECLARATION-EXISTENCE-PASS: {len(names)} names"\n'
(diag/"CorrespondenceNames.lean").write_text(code,encoding="utf-8")
for p in diag.iterdir():(LOG/p.name).write_bytes(p.read_bytes())
version=run("LEAN_VERSION",[LEANBIN/"lean.exe","--version"])
if "4.34.1" not in version or "5045d00" not in version:raise RuntimeError("Pinned Lean version mismatch")
run("LAKE_VERSION",[LEANBIN/"lake.exe","--version"])
run("CONFIGURE",[sys.executable,"configure.py"])
build=run("REGENERATED_BUILD",[LEANBIN/"lake.exe","build","OQ7","PrescribedExtinction"])
if "Build completed successfully" not in build:raise RuntimeError("Build success marker missing")
run("FINAL_THEOREM_TYPE",[LEANBIN/"lake.exe","env","lean","release-diagnostics/FinalType.lean"])
run("FINAL_AXIOMS",[LEANBIN/"lake.exe","env","lean","release-diagnostics/FinalAxioms.lean"])
run("CORRESPONDENCE_DECLARATIONS",[LEANBIN/"lake.exe","env","lean","release-diagnostics/CorrespondenceNames.lean"])
for name in ["Audit2","AuditExperiments","AuditCone2","AuditWholeProject"]:run(name,[LEANBIN/"lake.exe","env","lean","audit/final/experiments/"+name+".lean"])
run("KERNEL_REPLAY",[LEANBIN/"lake.exe","env","leanchecker","--fresh","--verbose","PrescribedExtinction.PhysicalTheorem11"])
result=dict(status="PASS",frozen_audited_commit="686402a6c2d63820828729cc7ab02504632e3fe7",portable_commit=head,pinned_lean="4.34.1",pinned_dependencies=pinresults,library_source_modules_unchanged=len(source_ids),build_cache_scope="Previously verified compatible dependency and project build objects copied into a new isolated checkout; current Lake build is an incremental/cached validation, not a new from-source clean build.",fresh_same_kernel_replay=True,independent_kernel_implementation_used=False,new_semantic_or_mathematical_audit_commissioned=False,correspondence_names_checked=len(names))
(LOG/"CURRENT_VERIFICATION.json").write_text(json.dumps(result,indent=2),encoding="utf-8")
print("CURRENT_FINAL_VERIFICATION_PASS",flush=True)

