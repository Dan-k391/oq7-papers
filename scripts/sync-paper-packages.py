"""Maintain prescribed-extinction-style publication packages without editing manuscripts.

The editable arxiv/ inputs remain canonical. --sync verifies them before writing
byte-identical publication snapshots. --check verifies snapshots, provenance,
local links and checksums. Existing checked proofs and historical files are read only.
"""
from pathlib import Path, PurePosixPath
import argparse
import csv
import hashlib
import html
from html.parser import HTMLParser
import io
import json
import re
import subprocess
import sys
from urllib.parse import unquote, urlparse
import zipfile

PAPERS = {
    'quartic-maxwell': 'Uniform Quartic Bounds for Reciprocal Absorption–Scattering Asymmetry',
    'generalized-research': 'Reciprocal Absorption Asymmetry: Sharp Channel Tradeoffs and Dielectric Thickness Asymptotics',
    'fixed-resource-bounds': 'Resource-Dependent Bounds on Reciprocal Absorption–Scattering Asymmetry',
    'compact-maxwell-cross-sections': 'Finite-Aperture Localization and Dipolar Bounds for Reciprocal Absorption Asymmetry',
}
STYLE='body{max-width:64rem;margin:3rem auto;padding:0 1rem;font:17px/1.6 system-ui,sans-serif;color:#243341}table{border-collapse:collapse;width:100%;table-layout:fixed}td,th{border:1px solid #cad3dc;padding:.6rem;text-align:left;vertical-align:top;overflow-wrap:anywhere}code{overflow-wrap:anywhere}a{color:#1f5681}'

def sha(data): return hashlib.sha256(data).hexdigest()
def load(path): return json.loads(path.read_text(encoding='utf-8-sig'))
def jbytes(value): return (json.dumps(value,indent=2,ensure_ascii=False)+'\n').encode('utf-8')
def require(test,message):
    if not test: raise ValueError(message)
def read(path):
    require(path.is_file() and not path.is_symlink(),'Missing or linked input: '+str(path))
    return path.read_bytes()
def relative(name):
    p=PurePosixPath(name)
    require(not p.is_absolute() and str(p)==name and '\\' not in name and ':' not in name and '..' not in p.parts,'Unsafe relative package path: '+name)
    return p
def document(title,body):
    return f'<!doctype html>\n<html lang="en"><head><meta charset="utf-8"><meta name="viewport" content="width=device-width, initial-scale=1"><title>{html.escape(title)}</title><style>{STYLE}</style></head><body>{body}</body></html>\n'

def preflight(repo,paper):
    from pypdf import PdfReader
    root=repo/'papers'/paper
    require(root.resolve().is_relative_to(repo.resolve()),'Paper directory escapes repository')
    src=root/'arxiv'
    tex=read(src/'main.tex').decode('utf-8')
    require(tex.index('Daniel Wang')<tex.index('Junjie Zheng'),'Author order differs: '+paper)
    for email in ['denialk391@gmail.com','zjj2785@gmail.com']:
        require('\\href{mailto:'+email+'}{\\texttt{'+email+'}}' in tex,'Contact format differs')
    build=load(src/'BUILD_VERIFICATION.json')
    require(build['unresolved_references'] is False and not build['overfull_boxes'],'Unresolved manuscript build diagnostics')
    require(sha(read(src/'paper.pdf'))==build['pdf_sha256'],'PDF/build mismatch: '+paper)
    require(sha(read(src/'arxiv-source.zip'))==build['zip_sha256'],'ZIP/build mismatch: '+paper)
    with zipfile.ZipFile(src/'arxiv-source.zip') as archive:
        require(archive.testzip() is None,'ZIP CRC failure')
        require(set(archive.namelist())=={r['path'] for r in build['inputs']},'ZIP inventory differs')
        for row in build['inputs']:
            relative(row['path'])
            require((src/row['path']).resolve().is_relative_to(repo),'Build input escapes repository')
            data=read(src/row['path'])
            require(sha(data)==row['sha256'] and archive.read(row['path'])==data,'Input/build mismatch: '+row['path'])
    pdf=PdfReader(src/'paper.pdf')
    require(str(pdf.metadata.author)=='Daniel Wang and Junjie Zheng','PDF byline differs')
    require(len(pdf.pages)==build['pages'],'Page count differs')
    status='No paper-specific Lean verification recorded'
    proof=None
    coverage=None
    if paper=='quartic-maxwell':
        proof=root/'formalization/verification/report.json'
        coverage=root/'formalization/verification/coverage.json'
        r=load(proof)
        require(r['completePhysicalManuscriptTheoremsVerified'] and r['freshKernelReplay']['exitCode']==0,'Quartic final replay incomplete')
        for name,digest in r['sourceHashes'].items(): require(sha(read(root/'formalization'/name))==digest,'Checked proof source changed: '+name)
        require(sha(read(root/'formalization/verify.py'))==r['verifierSHA256'],'Quartic verifier changed')
        for key,name in [('claimCoverageSHA256','coverage.json'),('publicRootManifestSHA256','public-roots.json'),('coreTheoremTypeManifestSHA256','core-theorem-types.json')]:
            require(sha(read(root/'formalization/verification'/name))==r[key],'Quartic guard/coverage differs')
        status='Eight original numbered statements: source-bound Lean checks and fresh same-kernel replay passed; auxiliary scope separately tracked'
    elif paper=='generalized-research':
        proof=root/'formalization/verification/final-all-numbered/report.json'
        coverage=proof.parent/'claim-coverage.json'
        r=load(proof)
        require(r['status']=='fresh-kernel-passed' and r['fresh_kernel_passed'],'Generalized final replay incomplete')
        for name,digest in {**r['source_sha256'],**r['historical_library_sha256']}.items(): require(sha(read(repo/name))==digest,'Checked proof/dependency source changed: '+name)
        require(load(coverage)['verification']['report_sha256']==sha(read(proof)),'Generalized coverage/report binding differs')
        status='Fifteen original numbered statements: source-bound Lean checks and fresh same-kernel replay passed; auxiliary scope separately tracked'
    if proof:
        binding=load(repo/'FORMALIZATION_MANUSCRIPT_BINDING.json')
        row=next(r for r in binding['manuscripts'] if r['paper']==paper)
        require(row['revisedSourceSHA256']==sha(read(src/'main.tex')),'Manuscript needs a new verification binding before package update')
        for name,digest in {**binding['verificationReports'],**binding['coverageLedgers']}.items(): require(sha(read(repo/name))==digest,'Frozen report/coverage changed')
    return root,src,tex,build,status,proof,coverage

def project_owns_status(root, name):
    """New working proof projects own their status docs, outside old PDF snapshots."""
    if name not in {'formalization/README.md', 'formalization/CLAIM_STATUS.md'}:
        return False
    config = root/'formalization/verification/project.json'
    if not config.is_file():
        return False
    metadata = load(config)
    require(metadata.get('paper') == root.name, 'Proof project identity mismatch')
    require(metadata.get('manuscriptsFrozenUntilAllVerificationComplete') is True,
            'A working proof project must preserve the manuscript update gate')
    require((root/'formalization/lean-toolchain').is_file(), 'Missing proof toolchain pin')
    return True

def plan(repo,paper):
    root,src,tex,build,status,proof,coverage=preflight(repo,paper)
    files={}; copies={}; provenance={}
    def put(name,value): files[name]=value if isinstance(value,bytes) else value.encode('utf-8')
    def copy(source,name):
        data=read(source);put(name,data)
        origin=source.relative_to(repo).as_posix()
        copies[name]={'repositorySource':origin,'sha256':sha(data)}
        provenance[origin]=sha(data)
    for row in build['inputs']:
        if not row['path'].startswith('anc/'):
            copy(src/row['path'],'publication/manuscript/'+row['path'])
    copy(src/'paper.pdf','publication/manuscript/paper.pdf')
    copy(src/'BUILD_VERIFICATION.json','publication/verification/MANUSCRIPT_BUILD.json')
    original_files=sorted((root/'manuscript').glob('*'))
    historical=original_files+sorted((root/'audits').glob('*'))+sorted((root/'audit-2026-10-14').glob('*'))+[src/'REVISION_NOTES.md']
    historical=[p for p in historical if p.is_file()]
    for p in historical:provenance[p.relative_to(repo).as_posix()]=sha(read(p))
    rows=[]
    if coverage:
        c=load(coverage)
        if paper=='quartic-maxwell':
            for r in c['coverage']:
                rows.append([r['originalId'],r.get('readingRevisionLabel') or '',r['scopeStatus'],'; '.join(r.get('checkedExports',[])),r.get('remaining') or ''])
        else:
            for r in c['claims']:
                rows.append([r['id'],'; '.join(r.get('current_arxiv_labels',[])),r['status'],'; '.join(r.get('exports',[])),r.get('remaining_obligations') or ''])
        copy(proof,'publication/manuscript/reproducibility/final-verification.json')
        copy(coverage,'publication/manuscript/reproducibility/claim-coverage.json')
        copy(repo/'FORMALIZATION_MANUSCRIPT_BINDING.json','publication/manuscript/reproducibility/manuscript-binding.json')
        copy(src/'anc/lean-supplement.zip','publication/manuscript/reproducibility/lean-source.zip')
    else:
        for match in re.finditer(r'\\begin\{(theorem|lemma|proposition|corollary)\}(?:\[([^]]*)\])?(.*?)(?=\\end\{\1\})',tex,re.S):
            label=re.search(r'\\label\{([^}]+)\}',match[3])
            rows.append([match[1]+(': '+match[2] if match[2] else ''),label[1] if label else '(unlabelled)','No paper-specific Lean correspondence recorded','','Ordinary manuscript statement; no formal declaration assigned'])
        if not project_owns_status(root, 'formalization/README.md'):
            put('formalization/README.md',f'# {PAPERS[paper]} — formalization status\n\nNo paper-specific Lean proof project or successful fresh-kernel record is supplied for this manuscript. The companion papers\' verification is not transferred to it. This directory provides the same structural entry point as the other papers, not a verification certificate.\n\nSee [claim status](CLAIM_STATUS.md), [publication correspondence](../publication/manuscript/theorem-correspondence.html) and [current manuscript](../arxiv/README.md). No dependency pins or proof code are introduced.\n')
        if not project_owns_status(root, 'formalization/CLAIM_STATUS.md'):
            put('formalization/CLAIM_STATUS.md','# Claim status\n\nEvery current labelled statement is inventoried in [the correspondence table](../publication/manuscript/theorem-correspondence.csv). No paper-specific formal declaration is assigned. The original PDF, reconstructed source and prior editorial scope record remain distinct evidence.\n')
    buf=io.StringIO(newline='');writer=csv.writer(buf,lineterminator='\n')
    headings=['Statement identity','Reading-revision label','Recorded scope status','Exact formal exports','Remaining scope / notes']
    writer.writerow(headings);writer.writerows(rows)
    put('publication/manuscript/theorem-correspondence.csv',buf.getvalue())
    table='<table><tr>'+''.join('<th>'+html.escape(h)+'</th>' for h in headings)+'</tr>'
    for row in rows:table+='<tr>'+''.join('<td>'+html.escape(str(v))+'</td>' for v in row)+'</tr>'
    put('publication/manuscript/theorem-correspondence.html',document('Statement correspondence',f'<h1>Statement correspondence</h1><p>{html.escape(PAPERS[paper])}</p><p>{html.escape(status)}. Original and reconstructed numbering are distinguished; a recorded formal scope does not certify every sentence, novelty or human peer review.</p>{table}</table><p><a href="theorem-correspondence.csv">CSV</a> · <a href="paper.pdf">PDF</a></p>'))
    author='# Author information\n\n| Order | Author | Affiliation | Enduring email |\n|---|---|---|---|\n| 1 | Daniel Wang | McMaster University | denialk391@gmail.com |\n| 2 | Junjie Zheng | Columbia University | zjj2785@gmail.com |\n\nThese are the supplied byline and contacts, retained byte-for-byte in the manuscript. No corresponding author, department, ORCID or individual contribution statement is assigned.\n'
    put('publication/AUTHOR_INFORMATION.md',author)
    put('publication/README.md',f'# {PAPERS[paper]}\n\nDaniel Wang — McMaster University; Junjie Zheng — Columbia University.\n\n| Material | Location |\n|---|---|\n| Publication manuscript snapshot | [PDF](manuscript/paper.pdf), [LaTeX](manuscript/main.tex), [BibTeX](manuscript/references.bib) |\n| Authors | [Author information](AUTHOR_INFORMATION.md) |\n| Supplements | [S1–S4 index](manuscript/reproducibility/SUPPLEMENT_INDEX.html) |\n| Statement correspondence | [HTML](manuscript/theorem-correspondence.html), [CSV](manuscript/theorem-correspondence.csv) |\n| Verification | [Document checks](verification/DOCUMENT_CHECK.json), [recorded build](verification/MANUSCRIPT_BUILD.json) |\n| Reproduction | [Instructions](REPRODUCE.md) |\n| Changes | [Change record](CHANGES.md), [file inventory](CHANGE_INVENTORY.json) |\n\nThe editable canonical manuscript remains in [arxiv/](../arxiv/README.md). This publication package is a byte-identical snapshot, not a second independently edited manuscript. The existing PDF layout, mathematical text, byline and dates are unchanged. The folder roles match prescribed-extinction; paper-specific assets and verification scope are supplied only where available. No new HTML manuscript, schematic or Git proof bundle is fabricated.\n\nVerification scope: {status}. The [review-package index](../review-package/RELEASE_INDEX.md) points to the preserved historical versions.\n')
    put('publication/REPRODUCE.md',f'# Reproduction\n\nThe current editable inputs are `../arxiv/main.tex` and its bibliography. The files in `manuscript/` are exact publication snapshots.\n\nFrom the repository root, check all package files, source identities and links:\n\n```text\npython scripts/sync-paper-packages.py --check --paper {paper}\n```\n\nTo rebuild the canonical PDF with the existing no-shell-escape TeX workflow and then refresh this package, run from `manuscript/`:\n\n```text\npython build.py --tex-dir PATH_TO_TEX_BIN\n```\n\nThe wrapper calls the repository build script, then the package synchronizer. Synchronization verifies recorded build inputs and any existing proof/manuscript bindings before it writes. Manual changes to managed snapshot files are refused. The document check records reuse of the earlier PDF build and visual review; copying does not constitute a new mathematical verification or arXiv server build.\n\n'+('For proofs, extract `manuscript/reproducibility/lean-source.zip` to an empty directory, run its `verify_supplement.py`, and follow its root README for exact dependency pins and fresh replay. Compiler/dependency caches remain external. Fresh replay uses Lean\'s own kernel implementation.\n' if proof else 'No paper-specific Lean source package is supplied. The correspondence table explicitly records that boundary; no companion proof is substituted.\n'))
    wrapper=f'''"""Rebuild canonical manuscript, then synchronize its publication snapshot."""\nfrom pathlib import Path\nimport subprocess,sys\nroot=Path(__file__).resolve().parents[4]\nsubprocess.run([sys.executable,str(root/'scripts/build-arxiv.py'),{paper!r},*sys.argv[1:]],check=True)\nsubprocess.run([sys.executable,str(root/'scripts/sync-paper-packages.py'),'--sync','--paper',{paper!r}],check=True)\n'''
    put('publication/manuscript/build.py',wrapper)
    put('publication/SOURCE_CHANGES.diff',b'')
    put('publication/CHANGES.md',f'# Package structure changes — 15 October 2026\n\nCreated the prescribed-extinction-style publication/manuscript/reproducibility and verification entry points for `{paper}`. Manuscript source, bibliography, processed bibliography and PDF are copied exactly from the verified current arXiv package. `SOURCE_CHANGES.diff` is empty because no manuscript text was changed. The byline, emails, layout, section structure, mathematical content and source archives remain unchanged.\n\nAdded author metadata, S1–S4 navigation, scope-aware correspondence, exact provenance/checksums, reproduction instructions and a historical review index. Existing source manuscripts, original audits and formalization files remain in their original paths. '+('The existing proof package and report/coverage/binding records are copied byte-for-byte as evidence, with their original path conventions retained.\n' if proof else 'Added status-only formalization documentation; it contains no Lean code and makes no verification claim.\n')+'\nSee the repository-level [complete structure change record](../../../PACKAGE_STRUCTURE_CHANGES.md).\n')
    rbase='publication/manuscript/reproducibility/'
    s2='<a href="lean-source.zip">Exact Lean source and reproduction supplement</a>' if proof else 'No paper-specific Lean supplement exists; consult the <a href="../../../formalization/README.md">formalization status</a>.'
    s3='<a href="current-verification.json">Current package verification status</a> and <a href="../../verification/MANUSCRIPT_BUILD.json">original current build record</a>'
    if proof:s3+='; <a href="final-verification.json">byte-preserved final Lean report</a> and <a href="claim-coverage.json">claim coverage</a>'
    body=f'<h1>Manuscript supplements</h1><p>{html.escape(PAPERS[paper])}</p><p>Daniel Wang — McMaster University<br>Junjie Zheng — Columbia University</p><table><tr><th>Supplement</th><th>Contents</th></tr><tr><td>S1</td><td><a href="../theorem-correspondence.html">Statement correspondence</a> and <a href="../theorem-correspondence.csv">CSV</a></td></tr><tr><td>S2</td><td>{s2}</td></tr><tr><td>S3</td><td>{s3}</td></tr><tr><td>S4</td><td><a href="AUDIT_PROVENANCE.md">Audit provenance</a>, <a href="CORRESPONDENCE_AUDIT_SCOPE.md">scope</a>, <a href="MANUSCRIPT_VERSION_CORRESPONDENCE.md">version correspondence</a> and <a href="manifest.json">evidence manifest</a></td></tr></table><p>{html.escape(status)}. No human peer review, independently implemented kernel or scientific priority is inferred.</p><p><a href="../../REPRODUCE.md">Reproduction</a> · <a href="../paper.pdf">PDF</a></p>'
    put(rbase+'SUPPLEMENT_INDEX.html',document('Manuscript supplements',body))
    put(rbase+'AUDIT_PROVENANCE.md',f'# Audit provenance\n\nCurrent recorded scope: {status}.\n\nPackage checks establish file identity, recorded build consistency and navigation integrity. They do not establish new mathematics. Earlier AI-assisted reviews, ordinary proofs, Lean checks and human review are separate categories. No human referee approval, independently implemented checker or novelty assessment is supplied by this package organization.\n\nHistorical evidence is indexed in [the review package](../../../review-package/RELEASE_INDEX.md). Copied raw evidence retains its original path conventions; those paths refer to its originating repository project or the unchanged standalone source archive.\n')
    put(rbase+'CORRESPONDENCE_AUDIT_SCOPE.md',f'# Correspondence scope\n\n{status}.\n\nThe [table](../theorem-correspondence.html) is generated from '+('the paper\'s exact-version claim ledger; original statement IDs are not silently replaced by current section counters. Remaining auxiliary obligations retain their recorded status.' if coverage else 'the labelled mathematical environments in the current TeX source. It is an inventory, not a formal or semantic correctness certificate.')+'\n')
    put(rbase+'MANUSCRIPT_VERSION_CORRESPONDENCE.md','# Manuscript version correspondence\n\n`publication/manuscript/main.tex`, the bibliography and PDF are exact copies of the current `arxiv/` versions identified in the package manifest. Historical originals remain under `manuscript/` at the paper root. Original audit paths are unchanged. The copied final proof records, where supplied, retain their original reading-version hashes; the separate manuscript binding records subsequent editorial revisions. No historic report is rewritten to claim it checked a later manuscript.\n')
    verification={'paper':paper,'scope':status,'pdfSHA256':sha(read(src/'paper.pdf')),'sourceSHA256':sha(read(src/'main.tex')),'recordedPages':build['pages'],'recordedBuildReused':True,'manuscriptBytesChanged':False,'newLeanExecution':False,'newMathematicalReview':False,'humanPeerReviewEstablished':False,'arxivServerTested':False,'canonicalDirectory':f'papers/{paper}/arxiv','formalReport':proof.relative_to(repo).as_posix() if proof else None,'formalReportSHA256':sha(read(proof)) if proof else None}
    put(rbase+'current-verification.json',jbytes(verification))
    put('publication/verification/DOCUMENT_CHECK.json',jbytes({**verification,'authorOrder':['Daniel Wang','Junjie Zheng'],'contacts':['denialk391@gmail.com','zjj2785@gmail.com'],'publicationLayoutReusedByteForByte':True,'buildInputsMatched':True,'sourceArchiveCRCAndContentsMatched':True,'newPDFRenderPerformed':False}))
    review='# Historical review-package index\n\nThis is a navigation index of this paper\'s existing evidence, not a newly sealed or independently reviewed release. The earlier paths and bytes remain unchanged.\n\n'
    for p in historical:review+=f'- [{p.relative_to(root).as_posix()}](../{p.relative_to(root).as_posix()}) — SHA-256 `{sha(read(p))}`.\n'
    review+='\nSee [version dispositions](VERSION_VERIFICATION_DISPOSITION.md) and the [publication snapshot](../publication/README.md).\n'
    put('review-package/RELEASE_INDEX.md',review)
    put('review-package/VERSION_VERIFICATION_DISPOSITION.md',f'# Version and verification dispositions\n\n- Historical manuscript: preserved at `../manuscript/`; no current verification inferred from its name or date.\n- Reconstructed editable revision: `../arxiv/`, with its own build record.\n- Publication package: byte-identical snapshot of that current revision.\n- Mathematical/formal scope: {status}.\n- Original audits, where present: retain their own dates, source identities and AI-assisted review categories.\n- This index does not designate a sealed release or a completed human review.\n')
    put('review-package/manifest.json',jbytes({'paper':paper,'indexOnly':True,'newSealedRelease':False,'preservedFiles':{p.relative_to(root).as_posix():sha(read(p)) for p in historical}}))
    evidence={name[len(rbase):]:sha(data) for name,data in files.items() if name.startswith(rbase)}
    put(rbase+'manifest.json',jbytes({'paper':paper,'role':'Evidence byte identities, not an independent verification certificate','files':evidence,'originIdentities':provenance}))
    inventory=[{'path':name,'operation':'generated snapshot/navigation','sha256':sha(data),'canonicalCopy':copies.get(name)} for name,data in sorted(files.items())]
    put('publication/CHANGE_INVENTORY.json',jbytes({'paper':paper,'scope':'Managed files; excludes this inventory, PACKAGE_MANIFEST and SHA256SUMS to avoid circular hashes','files':inventory}))
    state={'schemaVersion':1,'generator':'scripts/sync-paper-packages.py','paper':paper,'manuscriptChanged':False,'formalScope':status,'copies':copies,'provenance':provenance,'files':{name:sha(data) for name,data in sorted(files.items())}}
    put('publication/verification/PACKAGE_MANIFEST.json',jbytes(state))
    sums=''.join(sha(data)+'  '+name.removeprefix('publication/')+'\n' for name,data in sorted(files.items()) if name.startswith('publication/'))
    put('publication/SHA256SUMS',sums)
    return root,files

class Links(HTMLParser):
    def __init__(self):super().__init__();self.links=[]
    def handle_starttag(self,tag,attrs):
        if tag=='a':self.links.extend(v for k,v in attrs if k=='href')

def check(repo,paper):
    root=repo/'papers'/paper
    preflight(repo,paper)
    state=load(root/'publication/verification/PACKAGE_MANIFEST.json')
    require(state['paper']==paper,'Package identity mismatch')
    count=0
    delegated=[]
    for name,digest in state['files'].items():
        relative(name)
        require((root/name).resolve().is_relative_to(root.resolve()),'Managed path escapes paper directory')
        data=read(root/name)
        if project_owns_status(root, name):
            delegated.append(name)
        else:
            require(sha(data)==digest,'Managed package file changed: '+name)
        if name.endswith('.html'):
            parser=Links();parser.feed(data.decode('utf-8'));links=parser.links
        elif name.endswith('.md'):
            links=re.findall(r'\[[^\]]+\]\(([^)]+)\)',data.decode('utf-8'))
        else:links=[]
        for link in links:
            parsed=urlparse(link)
            if parsed.scheme or not parsed.path:continue
            target=((root/name).parent/unquote(parsed.path)).resolve()
            require(target.is_relative_to(repo) and target.is_file(),'Broken or external local link: '+name+' -> '+link)
            count+=1
    for name,row in state['copies'].items():require(read(root/name)==read(repo/row['repositorySource']),'Snapshot/canonical mismatch: '+name)
    for name,digest in state['provenance'].items():require(sha(read(repo/name))==digest,'Provenance source changed: '+name)
    for line in (root/'publication/SHA256SUMS').read_text().splitlines():
        digest,name=line.split('  ',1)
        require(sha(read(root/'publication'/name))==digest,'Publication checksum differs: '+name)
    return {'paper':paper,'managedFiles':len(state['files']),'localLinksChecked':count,'snapshotAndProvenanceHashes':'passed','formalScope':state['formalScope'],'workingProofProjectStatusDocuments':delegated}

def sync(repo,paper):
    root,files=plan(repo,paper)
    statepath=root/'publication/verification/PACKAGE_MANIFEST.json'
    if statepath.exists():
        state=load(statepath)
        for line in (root/'publication/SHA256SUMS').read_text().splitlines():
            digest,name=line.split('  ',1)
            require(sha(read(root/'publication'/name))==digest,'Refusing to overwrite a changed publication record: '+name)
        for name,digest in state['files'].items():
            if not project_owns_status(root, name):
                require(sha(read(root/name))==digest,'Refusing to overwrite a changed managed file: '+name)
        owned=set(state['files'])|{'publication/verification/PACKAGE_MANIFEST.json','publication/SHA256SUMS'}
    else:owned=set()
    for name,data in files.items():
        relative(name)
        target=root/name
        require(target.resolve().is_relative_to(root.resolve()),'Publication target escapes paper directory')
        require(not target.exists() or name in owned or read(target)==data,'Refusing to overwrite unowned file: '+name)
    # Every canonical input and recorded proof gate has passed before first write.
    changed=0
    for name,data in files.items():
        target=root/name
        if not target.exists() or read(target)!=data:
            target.parent.mkdir(parents=True,exist_ok=True);target.write_bytes(data);changed+=1
    result=check(repo,paper);result['filesWritten']=changed
    return result

def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--repo',type=Path,default=Path(__file__).resolve().parents[1])
    parser.add_argument('--paper',choices=[*PAPERS,'all'],default='all')
    mode=parser.add_mutually_exclusive_group(required=True)
    mode.add_argument('--preflight',action='store_true');mode.add_argument('--sync',action='store_true');mode.add_argument('--check',action='store_true')
    args=parser.parse_args();repo=args.repo.resolve()
    papers=list(PAPERS) if args.paper=='all' else [args.paper]
    if args.sync or args.preflight:
        for paper in papers:preflight(repo,paper)
    for paper in papers:
        result=({'paper':paper,'preflight':'passed'} if args.preflight else sync(repo,paper) if args.sync else check(repo,paper))
        print(json.dumps(result,ensure_ascii=True),flush=True)

if __name__=='__main__':main()
