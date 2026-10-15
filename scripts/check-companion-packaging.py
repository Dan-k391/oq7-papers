from pathlib import Path
import shutil,subprocess,sys,json,uuid,runpy,argparse
parser=argparse.ArgumentParser(description='Check publication snapshot protection and working proof-project status ownership.')
parser.add_argument('--repo',type=Path,default=Path(__file__).resolve().parents[1])
args=parser.parse_args();repo=args.repo.resolve();script=repo/'scripts/sync-paper-packages.py'
fixture=repo/'.local'/('companion-package-test-'+uuid.uuid4().hex[:8])
paper='fixed-resource-bounds';root=fixture/'papers'/paper
shutil.copytree(repo/'papers'/paper,root,ignore=shutil.ignore_patterns('.lake','.local','type-bootstrap-*'))
shutil.copyfile(repo/'PACKAGE_STRUCTURE_CHANGES.md',fixture/'PACKAGE_STRUCTURE_CHANGES.md')
def run(mode):return subprocess.run([sys.executable,str(script),'--repo',str(fixture),mode,'--paper',paper],capture_output=True,text=True,encoding='utf-8')
status=root/'formalization/README.md';before=status.read_bytes()
first=run('--sync');assert first.returncode==0,first.stderr
assert status.read_bytes()==before,'Publication synchronization overwrote project status'
second=run('--sync');assert second.returncode==0 and json.loads(second.stdout)['filesWritten']==0,second.stderr
target=root/'publication/manuscript/main.tex';changed=target.read_bytes()+b'\n% intentional test-only edit\n';target.write_bytes(changed)
negative=run('--sync');assert negative.returncode!=0 and 'Refusing to overwrite' in negative.stderr,negative.stderr
assert target.read_bytes()==changed
check=run('--check');assert check.returncode!=0 and 'Managed package file changed' in check.stderr,check.stderr
config=root/'formalization/verification/project.json';data=json.loads(config.read_text(encoding='utf-8'))
data['paper']='wrong-paper';config.write_text(json.dumps(data)+'\n',encoding='utf-8')
try:
    runpy.run_path(str(script))['project_owns_status'](root,'formalization/README.md')
except ValueError as error:
    assert 'Proof project identity mismatch' in str(error)
else:
    raise AssertionError('Invalid delegated project identity was accepted')
result={'newProjectStatusPreserved':True,'fixtureSecondSyncWrites':0,'tamperedSnapshotDetected':True,
        'tamperedSnapshotNotOverwritten':True,'wrongProjectIdentityRejected':True,'productionPublicationFilesTouched':False}
(repo/'.local/companion-package-tests.json').write_text(json.dumps(result,indent=2)+'\n',encoding='utf-8')
print(json.dumps(result))
