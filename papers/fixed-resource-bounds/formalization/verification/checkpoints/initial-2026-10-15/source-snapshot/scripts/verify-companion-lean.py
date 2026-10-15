"""Compile a paper project, check every exported type/axiom, and replay Lean's kernel.

The scope ledger is authoritative: a successful implemented-source checkpoint
does not promote incomplete manuscript statements to verified theorems.
"""
from __future__ import annotations
import argparse, hashlib, importlib.util, json, os, re, shutil, subprocess, sys
from pathlib import Path
from datetime import datetime, timezone

ALLOWED={'propext','Classical.choice','Quot.sound'}
MATHLIB='d13f23b723b8a846827a245b89c10fc7d3f11612'
LEAN_COMMIT='5045d0056413266e57c625dcd7c365b10e377c52'
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def load(p):return json.loads(p.read_text(encoding='utf-8-sig'))
def require(ok,msg):
    if not ok:raise ValueError(msg)
def dump(p,x):p.write_text(json.dumps(x,indent=2,ensure_ascii=False)+'\n',encoding='utf-8')
def run(cmd,cwd,env,log):
    with log.open('w',encoding='utf-8') as stream:
        result=subprocess.run(list(map(str,cmd)),cwd=cwd,env=env,stdout=stream,stderr=subprocess.STDOUT)
    require(result.returncode==0,'Command failed; see '+str(log))
    return result.returncode

def main():
    sys.stdout.reconfigure(encoding='utf-8')
    ap=argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--project',type=Path,required=True)
    ap.add_argument('--lean-bin',type=Path)
    ap.add_argument('--output-dir',type=Path,required=True)
    ap.add_argument('--rebuild-dependencies',action='store_true')
    ap.add_argument('--bootstrap-types',action='store_true',help=argparse.SUPPRESS)
    args=ap.parse_args();project=args.project.resolve();repo=project.parents[2]
    configpath=project/'verification/project.json';config=load(configpath)
    namespace=config['namespace']
    require(project.parent.name==config['paper'],'Project identity mismatch')
    bins=(args.lean_bin or repo/'.local/toolchains/lean-4.34.1-windows/bin').resolve()
    suffix='.exe' if os.name=='nt' else ''
    lean=bins/('lean'+suffix);checker=bins/('leanchecker'+suffix)
    version=subprocess.check_output([str(lean),'--version'],text=True).strip()
    require('4.34.1' in version and LEAN_COMMIT[:12] in version,'Wrong Lean version/commit: '+version)
    depdir=repo/'papers/prescribed-extinction/formalization/.lake/packages'
    pin=subprocess.check_output(['git','rev-parse','HEAD'],cwd=depdir/'mathlib',text=True).strip()
    require(pin==MATHLIB,'Mathlib revision changed')
    require(not subprocess.check_output(['git','status','--porcelain','--untracked-files=no'],cwd=depdir/'mathlib',text=True).strip(),
            'Mathlib contains tracked modifications')
    utilpath=repo/'papers/quartic-maxwell/formalization/verify.py'
    spec=importlib.util.spec_from_file_location('quartic_lean_audit_util',utilpath)
    util=importlib.util.module_from_spec(spec);spec.loader.exec_module(util)
    roots=[project]+[repo/'papers'/p/'formalization' for p in [
        'fixed-resource-bounds','quartic-maxwell','generalized-research','prescribed-extinction']
        if repo/'papers'/p/'formalization'!=project]
    seen=set();order=[];graph={}
    def visit(module):
        if module in seen:return
        seen.add(module);rel=Path(module.replace('.','/')+'.lean')
        source=next((r/rel for r in roots if (r/rel).is_file()),None)
        if source is None:return
        imports=[]
        for line in util.lean_code(source.read_text(encoding='utf-8')).splitlines():
            if line.startswith('import '):imports.extend(line[7:].split())
        graph[module]=imports
        for imp in imports:visit(imp)
        order.append((module,source))
    visit(namespace)
    local=[(m,s) for m,s in order if s.is_relative_to(project)]
    census={namespace+'.'+p.stem for p in (project/namespace).glob('*.lean')}|{namespace}
    require({m for m,s in local}==census,'An implemented module is missing from the aggregate import graph')
    declarations=[]
    for module,source in order:
        code=util.lean_code(source.read_text(encoding='utf-8'))
        require(not re.search(r'\b(?:sorry|admit|axiom|native_decide)\b',code),'Prohibited proof escape: '+str(source))
        if source.is_relative_to(project) and module!=namespace:
            declarations.extend(util.exported_declarations(source))
    require(len(declarations)==len(set(declarations)),'Duplicate declaration')
    coveragepath=project/'verification/coverage.json';coverage=load(coveragepath)
    ids=[c['id'] for c in coverage['claims']]
    require(len(ids)==len(set(ids)) and set(ids)==set(config['requiredStatementIds']),
            'The original/current statement inventory changed or has omissions')
    foreign={n for c in coverage['claims'] for n in c['exports']}-set(declarations)
    available=set()
    for module,source in order:
        if module.startswith('FixedResource.') and not source.is_relative_to(project):
            available.update(util.exported_declarations(source))
    require(foreign.issubset(available),'Unknown imported correspondence exports: '+str(foreign-available))
    declarations.extend(sorted(foreign))
    for claim in coverage['claims']:
        require(set(claim['exports']).issubset(set(declarations)), 'Unknown coverage export: '+claim['id'])
        require(claim['status']!='complete' or claim['exports'],'Complete claim needs exact exports')
    for rel,digest in coverage['manuscriptInputs'].items():require(sha(repo/rel)==digest,'Manuscript changed before verification: '+rel)
    support=[configpath,coveragepath,project/'lean-toolchain',project/'lakefile.toml',project/'verify.py',project/'Audit.lean',
             project/'README.md',project/'CLAIM_STATUS.md',utilpath,Path(__file__).resolve()]
    before={s.relative_to(repo).as_posix():sha(s) for _,s in order}
    before.update({s.relative_to(repo).as_posix():sha(s) for s in support})
    out=args.output_dir if args.output_dir.is_absolute() else project/args.output_dir
    require(out.resolve().is_relative_to(project/'verification/checkpoints'),'Output must be a new verification checkpoint')
    require(not out.exists(),'Refusing to overwrite a checkpoint: '+str(out))
    out.mkdir(parents=True);logs=out/'logs';logs.mkdir()
    build=project/'.lake/companion-checks'/out.name/'lib/lean';build.mkdir(parents=True)
    dependencies=[p/'.lake/build/lib/lean' for p in depdir.iterdir() if p.is_dir()]
    env=os.environ.copy();env['LEAN_NUM_THREADS']='2'
    env['LEAN_PATH']=os.pathsep.join(map(str,[build]+dependencies))
    # Namespace resolution in Lean picks one root. Mirror unchanged dependency
    # objects to the isolated build; never overwrite source projects or archives.
    copied={}
    for root in roots:
        libraries=[root/'.lake/build/lib/lean']
        for lib in libraries:
            if not lib.exists():continue
            for src in lib.rglob('*'):
                if src.is_file():
                    dst=build/src.relative_to(lib)
                    if not dst.exists():dst.parent.mkdir(parents=True,exist_ok=True);shutil.copy2(src,dst)
    started=datetime.now(timezone.utc).isoformat();steps=[]
    for module,source in order:
        artifact=build/(module.replace('.','/')+'.olean')
        must_build=source.is_relative_to(project) or module.startswith('FixedResource.') or module=='FixedResource' or args.rebuild_dependencies
        if not artifact.is_file():must_build=True
        if must_build:
            artifact.parent.mkdir(parents=True,exist_ok=True)
            cwd=next(root for root in roots if source.is_relative_to(root))
            run([lean,'-o',artifact,source],cwd,env,logs/(module+'.log'))
            print(module+': compiled',flush=True)
        copied[module]={'source':source.relative_to(repo).as_posix(),'sourceSHA256':sha(source),
                        'artifactSHA256':sha(artifact),'rebuiltFromSource':must_build}
        steps.append({'module':module,'rebuiltFromSource':must_build,'exitCode':0})
    audit=out/'Inventory.lean'
    audit.write_text('import '+namespace+'\nset_option pp.fullNames true\nset_option pp.universes true\n'
        'set_option format.width 120\nset_option pp.deepTerms true\nset_option pp.maxSteps 1000000\n'+
        '\n'.join('#check @'+n+'\n#print axioms '+n for n in declarations)+'\n',encoding='utf-8')
    run([lean,audit],project,env,logs/'Audit.log')
    printed=(logs/'Audit.log').read_text(encoding='utf-8')
    records=re.findall(r"'([^']+)' depends on axioms: \[([^]]*)\]",printed)
    records += [(name,'') for name in re.findall(r"'([^']+)' does not depend on any axioms",printed)]
    require({n for n,_ in records}==set(declarations),'Incomplete axiom inventory')
    for name,axioms in records:
        require(set(re.sub(r'\.\{[^}]*\}', '', a.strip()) for a in axioms.split(',') if a.strip()).issubset(ALLOWED),
                'Nonstandard axioms: '+name)
    types={name:util.exact_audited_type(printed,name) for name in declarations}
    guardpath=project/'verification/public-types.json'
    if args.bootstrap_types:
        require(not guardpath.exists(),'Refusing to overwrite public type guards')
        dump(guardpath,{'namespace':namespace,'types':types,'typeHashes':{
            n:hashlib.sha256(t.encode('utf-8')).hexdigest() for n,t in types.items()}})
        print('Bootstrap types written; no verification success recorded. Review and run again.',flush=True)
        return
    guard=load(guardpath)
    require(types==guard['types'],'An exported theorem type changed')
    require({n:hashlib.sha256(t.encode()).hexdigest() for n,t in types.items()}==guard['typeHashes'],'Type guard hash mismatch')
    before[guardpath.relative_to(repo).as_posix()]=sha(guardpath)
    run([checker,'--fresh','--verbose',namespace],project,env,logs/'fresh-kernel.log')
    print(namespace+': fresh same-kernel replay passed',flush=True)
    require(before=={rel:sha(repo/rel) for rel in before},'Source, manuscript or scope changed during verification')
    all_complete=all(c['status']=='complete' for c in coverage['claims'])
    report={'status':'fresh-kernel-passed','startedUTC':started,'finishedUTC':datetime.now(timezone.utc).isoformat(),
      'project':config['paper'],'namespace':namespace,'leanVersion':version,'mathlibRevision':pin,
      'compilerSHA256':sha(lean),'checkerSHA256':sha(checker),'sameKernelImplementation':True,
      'independentKernelImplementation':False,'freshKernelPassed':True,'allExportedDeclarationsAudited':True,
      'exportCount':len(declarations),'exports':declarations,'axioms':dict(records),'sourceHashes':before,
      'dependencyObjects':copied,'compileOrder':steps,'importGraph':graph,
      'manuscriptInputs':coverage['manuscriptInputs'],'coverageSHA256':sha(coveragepath),
      'publicTypesSHA256':sha(guardpath),'completePhysicalManuscriptTheoremsVerified':all_complete,
      'allOriginalManuscriptClaimsVerified':False,'manuscriptsUpdated':False,
      'remainingClaimIds':[c['id'] for c in coverage['claims'] if c['status']!='complete'],
      'logHashes':{p.relative_to(out).as_posix():sha(p) for p in logs.iterdir()},'inventorySHA256':sha(audit)}
    dump(out/'report.json',report)
    snapshot=out/'source-snapshot'
    for rel,digest in before.items():
        target=snapshot/rel;target.parent.mkdir(parents=True,exist_ok=True)
        shutil.copyfile(repo/rel,target)
        require(sha(target)==digest,'Source snapshot changed while copying: '+rel)
    dump(out/'manifest.json',{'paper':config['paper'],'status':report['status'],
        'files':{p.relative_to(out).as_posix():sha(p) for p in sorted(out.rglob('*')) if p.is_file()}})
    print('Checkpoint saved; complete manuscript theorem verification = '+str(all_complete),flush=True)

if __name__=='__main__':main()
