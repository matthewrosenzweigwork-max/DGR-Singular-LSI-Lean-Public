import argparse,hashlib,json,subprocess
from pathlib import Path
p=argparse.ArgumentParser();p.add_argument('report',type=Path);p.add_argument('repo',type=Path);p.add_argument('commit');p.add_argument('component',choices=['periodic','whole-space','planar']);a=p.parse_args()
j=json.loads(a.report.read_text());prefix='' if a.component=='planar' else f'trials/{a.component}/project/'
expected_repo='matthewrosenzweigwork-max/'+('LSI-2D-Diffusive-Coulomb-Gas-Lean-Public' if a.component=='planar' else 'DGR-Singular-LSI-Lean-Public')
def blob(path):return subprocess.check_output(['git','-C',str(a.repo),'show',a.commit+':'+prefix+path])
def check(condition,message):
 if not condition:raise SystemExit('REPORT NOT ACCEPTED: '+message)
check(j.get('status')=='pass' and j.get('phase')=='verification' and j.get('stage')=='complete','full verification did not complete with pass')
check(j.get('errors')==[],'report contains errors')
check(j.get('source',{}).get('commit')==a.commit,'source commit mismatch')
check(j['source'].get('repository')==expected_repo,'source repository mismatch')
check(j['source'].get('project_path','')==prefix.rstrip('/'),'project path mismatch')
check(j.get('lean_toolchain')=='leanprover/lean4:v4.35.0-rc2','Lean toolchain mismatch')
check(j.get('toolchain_commit')=='11acb17ec6b07a8f9e9173e6845197929540936b','Lean source commit mismatch')
check(j.get('execution_profile')=='palomar-standard-v1','execution profile mismatch')
check(j.get('mathlib_toolchain')==[{'revision':'065356127b1dc0016f66b7283ce0ce2c4055aa55','toolchain':'leanprover/lean4:v4.35.0-rc2'}],'Mathlib pin mismatch')
config_bytes=blob('comparator.json');config=json.loads(config_bytes);actual=j.get('comparator',{})
for k in ['challenge_module','solution_module','theorem_names','definition_names','permitted_axioms']:
 check(actual.get(k,[])==config.get(k,[]),'Comparator selection mismatch: '+k)
check(actual.get('sha256')==hashlib.sha256(config_bytes).hexdigest(),'Comparator file hash mismatch')
challenge=j.get('challenge',{});check(challenge.get('sha256')==hashlib.sha256(blob('Challenge.lean')).hexdigest(),'Challenge file hash mismatch')
check(challenge.get('trust_level')=='high' and challenge.get('untrusted_sources')==[],'Challenge provenance did not receive high trust')
check({k.get('name') for k in j.get('kernels',[])}=={'nanoda','con-ron'},'independent kernel configuration mismatch')
protected_bytes=j.get('protected_config','').encode();protected=json.loads(protected_bytes)
check(hashlib.sha256(protected_bytes).hexdigest()==j.get('protected_config_sha256'),'protected configuration hash mismatch')
for k in ['theorem_names','definition_names','permitted_axioms']:
 check(protected.get(k,[])==config.get(k,[]),'protected Comparator selection mismatch: '+k)
check(set(protected.get('external_kernels',{}))=={'nanoda','con-ron'},'protected independent kernels missing')
log=j.get('comparator_log_tail','')
for message in ['con-ron kernel accepts the solution','nanoda kernel accepts the solution','Lean default kernel accepts the solution','Your solution is okay!']:
 check(message in log,'kernel acceptance evidence missing: '+message)
check(j.get('license',{}).get('declared_identifier')=='Apache-2.0' and j['license'].get('detected_identifier')=='Apache-2.0','license mismatch')
check(j['license'].get('sha256')==hashlib.sha256(subprocess.check_output(['git','-C',str(a.repo),'show',a.commit+':'+j['license']['path']])).hexdigest(),'license bytes mismatch')
index_path=a.report.parent.parent/'FULL_PREFLIGHT_EVIDENCE.json'
if index_path.is_file():
 index=json.loads(index_path.read_text());records=[r for r in index['records'] if r['component']==a.component]
 check(index['candidate_commit']==a.commit and len(records)==1,'report index candidate/component mismatch')
 check(records[0]['report_sha256']==hashlib.sha256(a.report.read_bytes()).hexdigest(),'preserved raw report hash mismatch')
print(json.dumps({'accepted':True,'component':a.component,'commit':a.commit,'theorems':len(config['theorem_names']),'definitions':len(config.get('definition_names',[])),'challenge_lines':challenge.get('lines'),'workflow_url':j.get('workflow_url'),'warnings':j.get('warnings',[])},indent=2))
