"""Isolated expected-failure controls; never part of a successful proof project."""
from pathlib import Path
import hashlib
import json
import os
import runpy
import subprocess
import time

import argparse
parser=argparse.ArgumentParser(description=__doc__)
parser.add_argument('--project',type=Path,required=True,help='Generalized-paper formalization project containing verify.py')
parser.add_argument('--scratch',type=Path,required=True,help='Isolated output directory for expected-failure source fixtures and logs')
parser.add_argument('--lean-bin',type=Path,required=True,help='Directory containing the repository-pinned lean binary')
args=parser.parse_args()
ROOT=args.scratch.resolve()
PROJECT=args.project.resolve()
PRODUCTION=PROJECT/'verify.py'
LEAN=args.lean_bin.resolve()/('lean.exe' if os.name=='nt' else 'lean')
ROOT.mkdir(parents=True,exist_ok=True)
v=runpy.run_path(str(PRODUCTION),run_name='negative_control')
graph=v['source_graph']
record={'purpose':'Expected-failure controls, separate from successful proof verification',
        'production_verifier_sha256':hashlib.sha256(PRODUCTION.read_bytes()).hexdigest(),'checks':[]}

def preflight(label,source,imports='import GeneralizedResearch.Control\n',expected=True):
    project=ROOT/label
    (project/'GeneralizedResearch').mkdir(parents=True,exist_ok=True)
    (project/'GeneralizedResearch.lean').write_text(imports,encoding='utf-8')
    (project/'GeneralizedResearch/Control.lean').write_text(source,encoding='utf-8')
    graph.__globals__['PROJECT']=project
    try:
        graph()
        rejected=False
        diagnostic='accepted'
    except RuntimeError as error:
        rejected=True
        diagnostic=str(error)
    ok=rejected==expected
    record['checks'].append({'name':label,'guard':'production source_graph','expected_rejection':expected,
                             'rejected':rejected,'passed':ok,'diagnostic':diagnostic})
    if not ok: raise RuntimeError(label+' did not have the expected result')

preflight('valid_control','namespace GeneralizedResearch\ntheorem clean : True := True.intro\nend GeneralizedResearch\n',expected=False)
preflight('sorry_rejected','namespace GeneralizedResearch\ntheorem bad : False := by sorry\nend GeneralizedResearch\n')
preflight('local_axiom_rejected','namespace GeneralizedResearch\naxiom invented : False\ntheorem bad : False := invented\nend GeneralizedResearch\n')
preflight('missing_module_rejected','namespace GeneralizedResearch\ntheorem clean : True := True.intro\nend GeneralizedResearch\n',
          'import GeneralizedResearch.Control\nimport GeneralizedResearch.Absent\n')
preflight('omitted_module_rejected','namespace GeneralizedResearch\ntheorem clean : True := True.intro\nend GeneralizedResearch\n',imports='')

audit_tail='''
open Lean Elab Command in
run_cmd do
  let axioms ← Lean.collectAxioms `GeneralizedResearch.Control.bad
  let forbidden := axioms.filter fun n => n != `propext && n != `Classical.choice && n != `Quot.sound
  if !forbidden.isEmpty then
    throwError m!"Expected control rejection: nonstandard axioms {forbidden.toList}"
'''
sources={
 'false_proof_rejected':'theorem impossible : False := by exact True.intro\n',
 'missing_declaration_rejected':'#check GeneralizedResearch.Control.absent\n',
 'axiom_census_rejected':'import Lean\nimport Lean.Util.CollectAxioms\nnamespace GeneralizedResearch.Control\naxiom invented : False\ntheorem bad : False := invented\nend GeneralizedResearch.Control\n'+audit_tail,
 'sorry_census_rejected':'import Lean\nimport Lean.Util.CollectAxioms\nnamespace GeneralizedResearch.Control\ntheorem bad : False := by sorry\nend GeneralizedResearch.Control\n'+audit_tail,
 'required_declaration_census_rejected':'''import Lean
open Lean Elab Command in
run_cmd do
  let env ← getEnv
  if !env.contains `GeneralizedResearch.Control.absent then
    throwError "Expected control rejection: required declaration is missing"
'''
}
for label,source in sources.items():
    path=ROOT/(label+'.lean')
    path.write_text(source,encoding='utf-8')
    result=subprocess.run([str(LEAN),str(path)],cwd=ROOT,stdout=subprocess.PIPE,stderr=subprocess.STDOUT,text=True,encoding='utf-8')
    log=ROOT/(label+'.log')
    log.write_text(result.stdout,encoding='utf-8')
    marker=('nonstandard axioms' if label in ('axiom_census_rejected','sorry_census_rejected')
            else 'required declaration is missing' if label=='required_declaration_census_rejected'
            else 'Unknown identifier' if label=='missing_declaration_rejected' else 'Type mismatch')
    ok=result.returncode!=0 and marker in result.stdout
    guard=('isolated required-declaration assertion, not a production expected-roots manifest'
           if label=='required_declaration_census_rejected' else 'exact pinned Lean compiler/axiom allowlist')
    record['checks'].append({'name':label,'guard':guard,
                             'expected_exit':'nonzero','exit_code':result.returncode,'passed':ok,
                             'required_diagnostic_marker':marker,
                             'source_sha256':hashlib.sha256(path.read_bytes()).hexdigest(),
                             'log_sha256':hashlib.sha256(log.read_bytes()).hexdigest()})
    if not ok: raise RuntimeError(label+' unexpectedly passed')

# Exercise the production expected-root guard against the retained successful census.
checkpoint=PROJECT/'verification/checkpoint-main-claims'
census=(checkpoint/'types-and-axioms.log').read_text(encoding='utf-8')
manifest=json.loads((PROJECT/'expected-public-roots.json').read_text(encoding='utf-8'))
record['production_expected_roots_sha256']=hashlib.sha256((PROJECT/'expected-public-roots.json').read_bytes()).hexdigest()
retained=[r for r in manifest['roots'] if ('THEOREM '+r['name']+'\n') in census]
retained_manifest=dict(manifest,roots=retained,minimum_exhaustive_theorem_count=1007)
if not retained: raise RuntimeError('No retained checkpoint public roots to exercise')
guard=v['check_expected_public_roots']
count=guard(census,retained_manifest)
record['checks'].append({'name':'retained_expected_roots_positive_control','guard':'production check_expected_public_roots','passed':count==len(retained)})
name=retained[0]['name']
for label,changed,marker in [
 ('public_root_missing_rejected',census.replace('THEOREM '+name+'\n','THEOREM GeneralizedResearch.Control.Renamed\n',1),'Required public theorem is missing'),
 ('public_root_changed_type_rejected',census.replace('THEOREM '+name+'\nTYPE ','THEOREM '+name+'\nTYPE False ',1),'Required public theorem type changed')]:
    try:
        guard(changed,retained_manifest)
        rejected=False;diagnostic='accepted'
    except RuntimeError as error:
        rejected=True;diagnostic=str(error)
    ok=rejected and marker.lower() in diagnostic.lower()
    record['checks'].append({'name':label,'guard':'production check_expected_public_roots','expected_rejection':True,'passed':ok,'diagnostic':diagnostic})
    if not ok: raise RuntimeError(label+' did not have the expected rejection')
record['status']='all-negative-controls-passed' 
record['control_script_sha256']=hashlib.sha256(Path(__file__).read_bytes()).hexdigest()
(ROOT/'control-report.json').write_text(json.dumps(record,indent=2)+'\n',encoding='utf-8')
print(record['status'],len(record['checks']),flush=True)
