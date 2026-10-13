"""Restore included pinned dependency source and Git metadata snapshots without network."""
import argparse,json,pathlib,stat,subprocess,zipfile
root=pathlib.Path(__file__).resolve().parent
parser=argparse.ArgumentParser(description=__doc__)
parser.add_argument('--archives-directory',type=pathlib.Path,default=root.parent/'dependency-sources')
args=parser.parse_args()
pins=json.loads((root/'sources/pinned-lake-manifest.json').read_text(encoding='utf-8-sig'))
def unpack(archive,destination):
 destination.mkdir(parents=True,exist_ok=True)
 with zipfile.ZipFile(archive) as z:
  for member in z.infolist():
   path=pathlib.PurePosixPath(member.filename)
   if path.is_absolute() or '..' in path.parts or stat.S_ISLNK(member.external_attr>>16): raise RuntimeError('Unsafe archive member')
   target=destination.joinpath(*path.parts)
   if member.is_dir(): target.mkdir(parents=True,exist_ok=True);continue
   target.parent.mkdir(parents=True,exist_ok=True);target.write_bytes(z.read(member))
for package in pins['packages']:
 target=root/'.lake/packages'/package['name']
 if target.exists(): raise RuntimeError('Refusing to overwrite an existing dependency: '+str(target))
 stem=package['name']+'-'+package['rev']
 unpack(args.archives_directory/(stem+'.zip'),target)
 unpack(args.archives_directory/(stem+'-git-metadata.zip'),target/'.git')
 actual=subprocess.check_output(['git','-C',str(target),'rev-parse','HEAD'],text=True).strip()
 if actual!=package['rev']: raise RuntimeError('Dependency revision mismatch: '+package['name'])
print('Restored all nine exact pinned dependencies. Activate Lean 4.34.1 and run lake build.')
