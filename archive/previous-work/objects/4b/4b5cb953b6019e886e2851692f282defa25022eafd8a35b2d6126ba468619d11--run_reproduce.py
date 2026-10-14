import datetime, hashlib, json, os, pathlib, shutil, stat, subprocess, sys, zipfile
work=pathlib.Path(sys.argv[1]); out=pathlib.Path(sys.argv[2]); git=sys.argv[3]
checkout=work/'checkout'; logs=out/'reproduction_logs'; logs.mkdir(exist_ok=True)
env=dict(os.environ); env.update(GIT_CONFIG_NOSYSTEM='1',GIT_CONFIG_GLOBAL='NUL',GIT_OPTIONAL_LOCKS='0',LEAN_NUM_THREADS='2',MATHLIB_CACHE_DIR=str(work/'cache'),XDG_CACHE_HOME=str(work/'cache'),GIT_CONFIG_COUNT='1',GIT_CONFIG_KEY_0='core.longpaths',GIT_CONFIG_VALUE_0='true')
commands=[]
def run(label,args,cwd=checkout,allow_failure=False):
 print('START '+label,flush=True)
 started=datetime.datetime.now(datetime.timezone.utc).isoformat()
 log=logs/(label+'.log')
 with log.open('wb') as f: result=subprocess.run([str(x) for x in args],cwd=str(cwd),env=env,stdout=f,stderr=subprocess.STDOUT)
 record={'label':label,'argv':[str(x) for x in args],'windows_command_line':subprocess.list2cmdline([str(x) for x in args]),'cwd':str(cwd),'environment_overrides':{k:env[k] for k in ['GIT_CONFIG_NOSYSTEM','GIT_CONFIG_GLOBAL','GIT_OPTIONAL_LOCKS','LEAN_NUM_THREADS']},'started_utc':started,'finished_utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'exit_code':result.returncode,'complete_log':str(log)}
 with (out/'COMMANDS.jsonl').open('a',encoding='utf-8') as f: f.write(json.dumps(record)+'\n')
 print('END '+label+' exit='+str(result.returncode),flush=True)
 if result.returncode and not allow_failure: raise RuntimeError('Command failed: '+label+'; '+str(log))
 return result.returncode
if sys.argv[4]=='prepare':
 archive=work/'tools'/'lean-4.34.1-windows.zip'
 if hashlib.sha256(archive.read_bytes()).hexdigest()!='457698d4e2132243e899ff32178d7ae63c16431d09ed9ad524d859c3581992af': raise RuntimeError('Lean release digest mismatch')
 print('Extracting hash-verified pinned Lean toolchain',flush=True)
 with zipfile.ZipFile(archive) as z:
  for e in z.infolist():
   p=pathlib.PurePosixPath(e.filename)
   if p.is_absolute() or '..' in p.parts or stat.S_ISLNK(e.external_attr>>16): raise RuntimeError('Unsafe toolchain archive member')
   z.extract(e,work/'tools')
 leanbin=work/'tools'/'lean-4.34.1-windows'/'bin'
 env['PATH']=str(leanbin)+os.pathsep+str(pathlib.Path(git).parent)+os.pathsep+env['PATH']
 (work/'leanbin.txt').write_text(str(leanbin),encoding='utf-8')
 run('lean-version',[leanbin/'lean.exe','--version'])
 v=(logs/'lean-version.log').read_text(encoding='utf-8',errors='replace')
 if 'version 4.34.1,' not in v or '5045d0056413266e57c625dcd7c365b10e377c52' not in v: raise RuntimeError('Wrong Lean compiler version')
 run('lake-version',[leanbin/'lake.exe','--version']); run('git-version',[git,'--version'])
 pins=json.loads((checkout/'sources'/'pinned-lake-manifest.json').read_text(encoding='utf-8-sig'))
 packages=checkout/'.lake'/'packages'; packages.mkdir(parents=True,exist_ok=True)
 for package in pins['packages']:
  path=packages/package['name']
  run(package['name']+'-init',[git,'-c','core.hooksPath=NUL','init',path])
  run(package['name']+'-fetch',[git,'-c','core.hooksPath=NUL','-C',path,'fetch','--depth=1',package['url'],package['rev']])
  run(package['name']+'-checkout',[git,'-c','core.hooksPath=NUL','-C',path,'checkout','--detach','FETCH_HEAD'])
  run(package['name']+'-revision',[git,'-C',path,'rev-parse','HEAD'])
  if (logs/(package['name']+'-revision.log')).read_text().strip()!=package['rev']: raise RuntimeError('Dependency pin mismatch')
 pwsh='C:/Users/Daniel/.cache/codex-runtimes/codex-primary-runtime/dependencies/native/powershell/pwsh.exe'
 run('configure-portable',[pwsh,'-NoProfile','-File',checkout/'configure.ps1'])
 (out/'PINNED_DEPENDENCIES.json').write_text(json.dumps(pins,indent=2),encoding='utf-8')
 print('PREPARATION_COMPLETE',flush=True)
elif sys.argv[4]=='cache':
 leanbin=pathlib.Path((work/'leanbin.txt').read_text())
 env['PATH']=str(leanbin)+os.pathsep+str(pathlib.Path(git).parent)+os.pathsep+env['PATH']
 run('mathlib-cache-get-scoped',[leanbin/'lake.exe','exe','cache','get'],allow_failure=True)
elif sys.argv[4]=='build':
 leanbin=pathlib.Path((work/'leanbin.txt').read_text())
 env['PATH']=str(leanbin)+os.pathsep+str(pathlib.Path(git).parent)+os.pathsep+env['PATH']
 pwsh='C:/Users/Daniel/.cache/codex-runtimes/codex-primary-runtime/dependencies/native/powershell/pwsh.exe'
 run('verify-clean',[pwsh,'-NoProfile','-File',checkout/'verify.ps1','-LeanBin',leanbin,'-Clean','-BuildThreads','2'])
 print('CLEAN_VERIFICATION_COMPLETE',flush=True)
elif sys.argv[4]=='replay':
 leanbin=pathlib.Path((work/'leanbin.txt').read_text())
 env['PATH']=str(leanbin)+os.pathsep+str(pathlib.Path(git).parent)+os.pathsep+env['PATH']
 run('leanchecker-help',[leanbin/'lake.exe','env','leanchecker','--help'],allow_failure=True)
 run('kernel-fresh-replay',[leanbin/'lake.exe','env','leanchecker','--fresh','--verbose','PrescribedExtinction'],allow_failure=True)
 print('REPLAY_ATTEMPT_COMPLETE',flush=True)
