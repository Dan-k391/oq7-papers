import datetime,hashlib,json,os,pathlib,subprocess,zipfile
work=pathlib.Path(r'C:\Users\Daniel\.codex\.chatgpt-projects\g-p-6ac8784424248191b154eb2ed308e1f1\work\r59a36c60');out=pathlib.Path(r'C:\Users\Daniel\.codex\.chatgpt-projects\g-p-6ac8784424248191b154eb2ed308e1f1\outputs\OQ7-release-20261013-final-audit-59a36c60');git=r'C:\Users\Daniel\.cache\codex-runtimes\codex-primary-runtime\dependencies\native\git\cmd\git.exe'
target=work/'restored-3'; target.mkdir()
with zipfile.ZipFile(out/'portable-source.zip') as z: z.extractall(target)
env=dict(os.environ);env.update(PATH=str(pathlib.Path(git).parent)+os.pathsep+env['PATH'],GIT_CONFIG_GLOBAL='NUL',GIT_CONFIG_NOSYSTEM='1',GIT_CONFIG_COUNT='1',GIT_CONFIG_KEY_0='core.longpaths',GIT_CONFIG_VALUE_0='true',PYTHONUTF8='1')
args=[os.sys.executable,str(target/'restore-dependencies.py'),'--archives-directory',str(out/'dependency-sources')]
start=datetime.datetime.now(datetime.timezone.utc).isoformat()
log=out/'portable-test-logs/offline-dependency-restore.log'
with log.open('wb') as f: p=subprocess.run(args,cwd=target,env=env,stdout=f,stderr=subprocess.STDOUT)
record={'argv':args,'cwd':str(target),'started_utc':start,'finished_utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'exit_code':p.returncode}
pins=json.loads((target/'lake-manifest.json').read_text(encoding='utf-8-sig'))
records=[]
if p.returncode==0:
 for package in pins['packages']:
  dep=target/'.lake/packages'/package['name']
  actual=subprocess.check_output([git,'-C',str(dep),'rev-parse','HEAD'],env=env).decode().strip()
  dirty=subprocess.check_output([git,'-C',str(dep),'status','--porcelain','--untracked-files=no'],env=env).decode().strip()
  records.append({'name':package['name'],'expected_revision':package['rev'],'actual_revision':actual,'tracked_source_clean':not bool(dirty)})
  if actual!=package['rev'] or dirty: raise RuntimeError('Offline snapshot mismatch: '+package['name'])
record['packages']=records
(out/'portable-test-logs/OFFLINE_RESTORE_RESULT.json').write_text(json.dumps(record,indent=2),encoding='utf-8')
print(json.dumps(record,indent=2))
if p.returncode: raise RuntimeError('Offline dependency restore failed')
