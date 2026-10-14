import datetime,json,os,pathlib,subprocess,sys
work=pathlib.Path(sys.argv[1]); out=pathlib.Path(sys.argv[2]); leanbin=pathlib.Path(sys.argv[3]); git=sys.argv[4]
repo=work/'lean'; logs=out/'portable-test-logs'; logs.mkdir(exist_ok=True)
env=dict(os.environ); env.update(PATH=str(leanbin)+os.pathsep+str(pathlib.Path(git).parent)+os.pathsep+env['PATH'],LEAN_NUM_THREADS='2',GIT_CONFIG_NOSYSTEM='1',GIT_CONFIG_GLOBAL='NUL',GIT_OPTIONAL_LOCKS='0',GIT_CONFIG_COUNT='1',GIT_CONFIG_KEY_0='core.longpaths',GIT_CONFIG_VALUE_0='true',MATHLIB_CACHE_DIR=str(work/'cache'),XDG_CACHE_HOME=str(work/'cache'),PYTHONUTF8='1')
def run(label,args):
 print('START '+label,flush=True); started=datetime.datetime.now(datetime.timezone.utc).isoformat()
 with (logs/(label+'.log')).open('wb') as f:
  result=subprocess.run([str(x) for x in args],cwd=str(repo),env=env,stdout=f,stderr=subprocess.STDOUT)
 entry={'label':label,'argv':[str(x) for x in args],'windows_command_line':subprocess.list2cmdline([str(x) for x in args]),'cwd':str(repo),'started_utc':started,'finished_utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'exit_code':result.returncode,'complete_log':label+'.log','environment':{k:env[k] for k in ['LEAN_NUM_THREADS','MATHLIB_CACHE_DIR','GIT_CONFIG_COUNT','GIT_CONFIG_KEY_0','GIT_CONFIG_VALUE_0']}}
 with (logs/'COMMANDS.jsonl').open('a',encoding='utf-8') as f: f.write(json.dumps(entry)+'\n')
 print('END '+label+' exit='+str(result.returncode),flush=True)
 if result.returncode: raise RuntimeError('Failed '+label+'; see full log')
run('lean-version',[leanbin/'lean.exe','--version'])
run('lake-version',[leanbin/'lake.exe','--version'])
run('project-build',[leanbin/'lake.exe','build','OQ7','PrescribedExtinction'])
run('final-declaration',[leanbin/'lake.exe','env','lean','verification/FinalCompleteTheorem.lean'])
for name in ['Audit2','AuditExperiments','AuditCone2','AuditWholeProject']:
 run(name,[leanbin/'lake.exe','env','lean','audit/final/experiments/'+name+'.lean'])
print('PORTABLE_BUILD_AND_EXISTING_AUDIT_PROGRAMS_PASS',flush=True)
