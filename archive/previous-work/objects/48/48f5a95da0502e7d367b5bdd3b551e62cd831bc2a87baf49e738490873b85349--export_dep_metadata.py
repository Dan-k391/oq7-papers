import json,pathlib,stat,sys,zipfile
work=pathlib.Path(r'C:\Users\Daniel\.codex\.chatgpt-projects\g-p-6ac8784424248191b154eb2ed308e1f1\work\r59a36c60'); out=pathlib.Path(r'C:\Users\Daniel\.codex\.chatgpt-projects\g-p-6ac8784424248191b154eb2ed308e1f1\outputs\OQ7-release-20261013-final-audit-59a36c60'); repo=work/'lean'
pins=json.loads((repo/'sources/pinned-lake-manifest.json').read_text(encoding='utf-8-sig'))
for p in pins['packages']:
 base=repo/'.lake/packages'/p['name']/'.git'; dest=out/'dependency-sources'/(p['name']+'-'+p['rev']+'-git-metadata.zip')
 with zipfile.ZipFile(dest,'w',zipfile.ZIP_DEFLATED) as z:
  for f in base.rglob('*'):
   if f.is_dir():
    z.writestr(f.relative_to(base).as_posix()+'/',b'')
   if f.is_file():
    if f.is_symlink() or f.stat().st_file_attributes & stat.FILE_ATTRIBUTE_REPARSE_POINT: raise RuntimeError('Unexpected dependency metadata link')
    z.write(f,f.relative_to(base).as_posix())
print('EXPORTED_9_PINNED_GIT_METADATA_SNAPSHOTS')
