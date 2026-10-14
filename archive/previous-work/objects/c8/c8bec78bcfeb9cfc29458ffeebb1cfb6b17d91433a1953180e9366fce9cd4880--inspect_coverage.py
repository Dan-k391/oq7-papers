import hashlib,json,pathlib,re
work=pathlib.Path(r'C:\Users\Daniel\.codex\.chatgpt-projects\g-p-6ac8784424248191b154eb2ed308e1f1\work\OQ7-audit-20261013-a89f0ec7-128b-4db6-ae6a-40d4bf427076'); out=pathlib.Path(r'C:\Users\Daniel\.codex\.chatgpt-projects\g-p-6ac8784424248191b154eb2ed308e1f1\outputs\OQ7-audit-20261013-a89f0ec7-128b-4db6-ae6a-40d4bf427076'); repo=work/'checkout'
sources=[*sorted((repo/'OQ7').rglob('*.lean')),*sorted((repo/'PrescribedExtinction').rglob('*.lean')),repo/'OQ7.lean',repo/'PrescribedExtinction.lean']
def erase_comments_strings(text):
 result=[]; i=0; level=0; string=False
 while i<len(text):
  if level:
   if text[i:i+2]=='/-': level+=1;i+=2
   elif text[i:i+2]=='-/': level-=1;i+=2
   else: result.append('\n' if text[i]=='\n' else ' ');i+=1
  elif string:
   if text[i]=='\\': result+=[' ',' '];i+=2
   elif text[i]=='"': string=False;result.append(' ');i+=1
   else: result.append('\n' if text[i]=='\n' else ' ');i+=1
  elif text[i:i+2]=='/-': level=1;result+=[' ',' '];i+=2
  elif text[i:i+2]=='--':
   j=text.find('\n',i);j=len(text) if j<0 else j;result+=[' ']*(j-i);i=j
  elif text[i]=='"': string=True;result.append(' ');i+=1
  else: result.append(text[i]);i+=1
 if level or string: raise ValueError('Unclosed comment/string')
 return ''.join(result)
risk=re.compile(r'\b(sorry|admit|axiom|native_decide|ofReduceBool|ofReduceNat|implemented_by|unsafe|opaque|initialize|run_cmd|macro|elab)\b|debug\.skipKernelTC|decide\s*\+native|@\[extern')
records=[]; risks=[]; modules={}
for p in sources:
 text=p.read_text(encoding='utf-8-sig'); code=erase_comments_strings(text)
 rel=p.relative_to(repo).as_posix(); mod=rel[:-5].replace('/','.')
 imports=re.findall(r'^\s*(?:public\s+|private\s+)?import\s+([\w.]+)',code,re.M)
 modules[mod]=imports
 for match in risk.finditer(code):
  risks.append({'path':rel,'line':code.count('\n',0,match.start())+1,'mechanism':match.group()})
 records.append({'path':rel,'sha256':hashlib.sha256(p.read_bytes()).hexdigest(),'imports':imports})
def closure(initial):
 seen=set(); todo=list(initial)
 while todo:
  m=todo.pop()
  if m in seen or m not in modules: continue
  seen.add(m); todo+=modules[m]
 return seen
aggregate=closure(['OQ7','PrescribedExtinction']); final=closure(['PrescribedExtinction.PhysicalTheorem11'])
data={'mathematical_source_files':len(sources),'default_targets':['OQ7','PrescribedExtinction'],'project_modules_reachable_from_default_targets':len(aggregate),'unreachable_project_modules':sorted(set(modules)-aggregate),'final_module_project_import_closure':sorted(final),'risk_scan_method':'Nested Lean block comments, line comments and strings excluded; proof/runtime/bypass syntax searched in mathematical sources only','risk_hits':risks,'sources':records,'note':'Import coverage plus a successful fresh project build is required; coverage alone is not kernel verification.'}
(out/'BUILD_COVERAGE.json').write_text(json.dumps(data,indent=2),encoding='utf-8')
print(json.dumps({k:data[k] for k in ['mathematical_source_files','project_modules_reachable_from_default_targets','unreachable_project_modules','risk_hits']},indent=2))
