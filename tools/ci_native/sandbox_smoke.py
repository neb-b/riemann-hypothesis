import json,os,sys,tempfile
from pathlib import Path
import rpc,launch

def main():
 with tempfile.TemporaryDirectory(prefix='native-sandbox-fixture-')as tmp:
  base=Path(tmp);candidate=base/'candidate';(candidate/'.lake/build').mkdir(parents=True);archive=base/'archive';archive.mkdir();(archive/'original').write_text('immutable fixture')
  actual=Path('/home/kim/riemann-toolchain-4.36/pr66-cache-engineering/project')
  deps=(actual/'.lake/packages').resolve();(candidate/'lake-manifest.json').write_bytes((actual/'lake-manifest.json').read_bytes())
  tc=base/'toolchain';tc.mkdir();host={'id':'smoke','runner_name':'fixture-runner','runs_on':['self-hosted','Linux','X64','fixture'],'cpus':1,'memory_mib':512,'timeout_seconds':30,'archive_root':str(archive),'dependency_root':str(deps),'toolchain_root':str(tc)}
  snapshot={**rpc.read(Path(rpc.__file__).with_name('identity.json')),'fingerprint':'a'*64,'git_commit':'716d8a580091b7ebd505049e77fc300cc442f7ba'}
  trusted=Path(launch.__file__).with_name('producer.py')
  rpc.plan(snapshot,{'snapshot':'a'*64,'modules':[{'module':'Fixture.One'}]},[host],'123',1,'b'*40,rpc.digest(trusted),'c'*64,base/'plan')
  secret=base/'HOST-CREDENTIAL-FIXTURE';secret.write_text('MUST NOT BE VISIBLE')
  args=launch.command(candidate,base/'plan/smoke',base/'output',trusted,'123',1,'fixture-runner')
  code="import sys,os,json;sys.path.insert(0,"+repr(str(Path(rpc.__file__).parent))+");import rpc,producer;from pathlib import Path;assert len(producer.dependency_paths(Path("+repr(str(deps))+"),Path("+repr(str(candidate/'lake-manifest.json'))+")))==8;assert rpc.no_network();rpc.resource_limits("+repr(host)+");assert not Path("+repr(str(secret))+").exists();assert 'GITHUB_TOKEN' not in os.environ;assert rpc.readonly_mount("+repr(str(archive))+");p=Path("+repr(str(candidate/'.lake/build/writable-fixture'))+");p.write_text('ok');assert p.read_text()=='ok';print(json.dumps({'sandbox':True,'network_none':True,'credential_fixture_hidden':True,'input_readonly':True,'output_writable':True,'own_unit_cgroup_bounded':True,'proof_elaboration':False}))"
  args=args[:args.index(sys.executable)]+[sys.executable,'-c',code]
  import subprocess
  result=subprocess.run(args,env={'PATH':os.environ['PATH'],'GITHUB_TOKEN':'HOST-SECRET-MUST-NOT-PASS'},capture_output=True,text=True,timeout=20)
  print(result.stdout,end='');print(result.stderr,end='',file=sys.stderr)
  if result.returncode:raise SystemExit(result.returncode)
if __name__=='__main__':main()
