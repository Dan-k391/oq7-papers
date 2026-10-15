"""Positive and deliberately failing controls against the checked paper modules."""
from pathlib import Path
import argparse,os,subprocess,json,hashlib
from datetime import datetime,timezone
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
ap=argparse.ArgumentParser(description=__doc__);ap.add_argument('--repo',type=Path,default=Path(__file__).resolve().parents[1]);ap.add_argument('--output-dir',type=Path);args=ap.parse_args();repo=args.repo.resolve()
out=(args.output_dir or repo/'.local/companion-controls-2026-10-15').resolve()
assert out.is_relative_to(repo/'.local')
out.mkdir(parents=True,exist_ok=False)
deps=repo/'papers/prescribed-extinction/formalization/.lake/packages'
fixed=repo/'papers/fixed-resource-bounds/formalization'
compact=repo/'papers/compact-maxwell-cross-sections/formalization'
libs=[fixed/'.lake/companion-checks/initial-2026-10-15/lib/lean',compact/'.lake/companion-checks/initial-scoped-2026-10-15/lib/lean']
libs += [p/'.lake/build/lib/lean' for p in deps.iterdir() if p.is_dir()]
env=os.environ.copy();env['LEAN_PATH']=os.pathsep.join(map(str,libs));env['LEAN_NUM_THREADS']='2'
lean=repo/'.local/toolchains/lean-4.34.1-windows/bin/lean.exe'
cases={
 'sphere-coefficient-positive':('''import FixedResource.SphereAlgebra
open scoped Matrix
open FixedResource.SphereAlgebra
example : ((power (L *ᵥ plus) - power (L *ᵥ minus)) / 2) / ((quad L plus).im / 2) = (720 : ℝ) / 2071 :=
  normalized_coefficient.1
''',True),
 'sphere-coefficient-altered':('''import FixedResource.SphereAlgebra
open scoped Matrix
open FixedResource.SphereAlgebra
example : ((power (L *ᵥ plus) - power (L *ᵥ minus)) / 2) / ((quad L plus).im / 2) = (721 : ℝ) / 2071 := by
  rw [normalized_coefficient.1]
  norm_num
''',False),
 'physical-reciprocity-positive':('''import CompactMaxwell.SixVectorEquality
open CompactMaxwell.SixVectorEquality CompactMaxwell.SixVectorBridge
example : (A 0 1).transpose = D * A 0 1 * D := reciprocal 0 1
''',True),
 'incorrect-reciprocity-sign':('''import CompactMaxwell.SixVectorEquality
open CompactMaxwell.SixVectorEquality CompactMaxwell.SixVectorBridge
example : (A 0 1).transpose = A 0 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> norm_num [A, M]
''',False),
 'loss-defect-positive':('''import CompactMaxwell.SixVectorEquality
open scoped ComplexOrder
open CompactMaxwell.SixVectorEquality CompactMaxwell.SixVectorBridge
example : (Q (A 0 (Real.sqrt (1/2)))).PosSemidef := by
  apply passive
  rw [Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 1/2)]
  norm_num
''',True),
 'invalid-loss-defect':('''import CompactMaxwell.SixVectorEquality
open scoped ComplexOrder
open CompactMaxwell.SixVectorEquality CompactMaxwell.SixVectorBridge
example : (Q (A 0 2)).PosSemidef := by
  apply passive
  norm_num
''',False)}
rows=[]
for name,(source,expected) in cases.items():
    path=out/(name+'.lean');path.write_text(source,encoding='utf-8')
    result=subprocess.run([str(lean),str(path)],cwd=out,env=env,capture_output=True,text=True,encoding='utf-8')
    log=out/(name+'.log');log.write_text(result.stdout+result.stderr,encoding='utf-8')
    assert (result.returncode==0)==expected,(name,result.stdout,result.stderr)
    if not expected:assert 'error:' in log.read_text(encoding='utf-8') and 'unsolved goals' in log.read_text(encoding='utf-8')
    rows.append({'control':name,'expectedToCompile':expected,'exitCode':result.returncode,'sourceSHA256':sha(path),'logSHA256':sha(log)})
    print(name+': passed',flush=True)
report={'createdUTC':datetime.now(timezone.utc).isoformat(),'status':'passed','compilerSHA256':sha(lean),'cases':rows,
  'productionSourcesMutated':False,'typeGuardFilesChanged':False}
(out/'report.json').write_text(json.dumps(report,indent=2)+'\n',encoding='utf-8')
