"""Isolated rejection controls for the exact physical core-theorem type guards.

These controls mutate only in-memory copies of the pinned type record and an
inspection-log fixture. They never modify a Lean proof or the frozen records.
"""
from pathlib import Path
import argparse, copy, hashlib, importlib.util, json
from datetime import datetime, timezone

def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--project',type=Path,default=Path(__file__).resolve().parent)
    args=parser.parse_args()
    project=args.project.resolve()
    spec=importlib.util.spec_from_file_location('quartic_verifier',project/'verify.py')
    v=importlib.util.module_from_spec(spec)
    spec.loader.exec_module(v)
    guard_path=project/'verification/core-theorem-types.json'
    guard=json.loads(guard_path.read_text(encoding='utf-8'))
    public=json.loads((project/'verification/public-roots.json').read_text(encoding='utf-8'))
    roots=set(public['requiredCompleteClaimExports'])
    # Exact types come from already kernel-audited declarations. The fixture only
    # isolates parser/comparison behavior; it is not a new mathematical proof.
    fixture='\n'.join(row['type']+f"\n'{name}' depends on axioms: [propext, Classical.choice, Quot.sound]\n"
                      for name,row in guard['types'].items())
    checked=v.validate_core_types(fixture,guard,roots)
    results=[]
    def reject(name,log,data,required):
        try: v.validate_core_types(log,data,required)
        except SystemExit as error:
            results.append({'control':name,'passed':True,'rejection':str(error)})
        else: raise SystemExit(f'Negative control was unexpectedly accepted: {name}')
    key='QuarticMaxwell.HeterogeneousAttainment.fixed_wavenumber_remainder'
    changed=fixture.replace(guard['types'][key]['type'],guard['types'][key]['type'].replace('21 / 2000','22 / 2000'))
    if changed==fixture: raise SystemExit('Type mutation fixture did not change the quantitative theorem')
    reject('changed-physical-remainder-constant',changed,guard,roots)
    changed_guard=copy.deepcopy(guard)
    changed_guard['claims'].pop('Theorem 1.3')
    reject('missing-original-core-claim',fixture,changed_guard,roots)
    changed_guard=copy.deepcopy(guard)
    changed_guard['types'].pop(key)
    reject('missing-core-type-entry',fixture,changed_guard,roots)
    changed_guard=copy.deepcopy(guard)
    changed_guard['types'][key]['sha256']='0'*64
    reject('corrupted-expected-type-hash',fixture,changed_guard,roots)
    reject('missing-required-public-core-root',fixture,guard,roots-{key})
    reject('duplicate-printed-type',fixture+'\n'+guard['types'][key]['type']+f"\n'{key}' depends on axioms: []\n",guard,roots)
    key13='QuarticMaxwell.HomogeneousSharpness.theorem13'
    changed=fixture.replace(guard['types'][key13]['type'],key13+' : True')
    reject('weakened-every-resource-physical-theorem',changed,guard,roots)
    report={'schemaVersion':1,'finishedUTC':datetime.now(timezone.utc).isoformat(),
            'scope':'Isolated parser/type-guard rejection controls; mathematical compilation and kernel replay are separate.',
            'baselinePinnedTypesAccepted':len(checked),'allControlsPassed':all(row['passed'] for row in results),
            'controls':results,'typeManifestSHA256':hashlib.sha256(guard_path.read_bytes()).hexdigest(),
            'verifierSHA256':hashlib.sha256((project/'verify.py').read_bytes()).hexdigest(),
            'controlScriptSHA256':hashlib.sha256(Path(__file__).read_bytes()).hexdigest()}
    target=project/'verification/negative-controls/type-guards-report.json'
    target.write_text(json.dumps(report,indent=2)+'\n',encoding='utf-8')
    print(f'All {len(results)} exact-core-type rejection controls passed; {len(checked)} baseline root types accepted.')
if __name__=='__main__': main()
