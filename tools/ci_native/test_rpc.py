import importlib.util,json,os,subprocess,tempfile,time,unittest,zipfile
from pathlib import Path
from unittest.mock import patch
P=Path(__file__).with_name('rpc.py');spec=importlib.util.spec_from_file_location('native_rpc',P);r=importlib.util.module_from_spec(spec);spec.loader.exec_module(r)
class ProtocolTests(unittest.TestCase):
 def setUp(self):
  self.tmp=tempfile.TemporaryDirectory(prefix='native-rpc-fixture-');self.addCleanup(self.tmp.cleanup);self.base=Path(self.tmp.name)
  self.snapshot={**r.read(P.with_name('identity.json')),'fingerprint':'a'*64,'git_commit':'716d8a580091b7ebd505049e77fc300cc442f7ba'}
 def hosts(self,n):return [{'id':f'w{i}','runner_name':f'registered-{i}','runs_on':['self-hosted','Linux','X64',f'unique-{i}'],'cpus':i+1,'memory_mib':4096,'timeout_seconds':60}for i in range(n)]
 def planned(self,n=1,count=1,now=None):
  missing={'snapshot':'a'*64,'modules':[{'module':f'Fixture.M{i}','bytes':i+1}for i in range(count)]}
  out=self.base/'plan';matrix=r.plan(self.snapshot,missing,self.hosts(n),'123',1,'b'*40,'c'*64,'d'*64,out,now=now)
  return out,matrix
 def test_dynamic_seventeen_workers_exactly_once(self):
  out,matrix=self.planned(17,103);names=[]
  for row in matrix['include']:names+=r.read(out/row['id']/'request-0.json')['modules']
  self.assertEqual(len(names),103);self.assertEqual(len(set(names)),103);self.assertEqual(len(matrix['include']),17)
 def test_empty_work_never_creates_request(self):
  out,matrix=self.planned(7,0);self.assertEqual(matrix,{'include':[]});self.assertFalse(list(out.glob('*/request-*.json')))
 def test_identity_config_and_source_fail_closed(self):
  for k in ['git_commit','source_tree','lakefile_sha256','manifest_sha256','toolchain']:
   x=dict(self.snapshot);x[k]='wrong'
   with self.assertRaises(ValueError):r.snapshot_identity(x)
 def test_limits_and_registered_linux_only(self):
  for key,val in [('cpus',0),('cpus',257),('memory_mib',0),('memory_mib',2097153),('timeout_seconds',0),('timeout_seconds',21601)]:
   h=self.hosts(1)[0];h[key]=val
   with self.assertRaises(ValueError):r.host(h)
  h=self.hosts(1)[0];h['runs_on']=['ubuntu-latest']
  with self.assertRaises(ValueError):r.host(h)
 def test_lease_expiry_attempt_runner_request_and_no_proof(self):
  out,_=self.planned(now=1000);lease=r.read(out/'w0/lease.json');req=r.read(out/'w0/request-0.json')
  self.assertEqual(r.check_lease(lease,req,'123',1,'registered-0',1000),['Fixture.M0'])
  for args in [('123',1,'registered-0',lease['expires_at']+1),('123',2,'registered-0',1000),('123',1,'other',1000)]:
   with self.assertRaises(ValueError):r.check_lease(lease,req,*args)
  bad={**req,'modules':['Other']}
  with self.assertRaises(ValueError):r.check_lease(lease,bad,'123',1,'registered-0',1000)
  lease['operation']='proof'
  with self.assertRaises(ValueError):r.check_lease(lease,req,'123',1,'registered-0',1000)
 def test_paths_modules_and_symlink_escape(self):
  for path in ['/tmp/a','.lake/build/../secret','../x','.lake//build/ir/A.c','.lake/build/ir/../../x','C:\\a']:
   with self.assertRaises(ValueError):r.relative(path)
  for name in ['A:olean','../A','A/B','A..B','A;true']:
   with self.assertRaises(ValueError):r.module_name(name)
  self.assertEqual(r.module_name('Development.Divisors₂.A'),'Development.Divisors₂.A')
  (self.base/'.lake').mkdir();(self.base/'.lake/build').symlink_to('/tmp',target_is_directory=True)
  with self.assertRaises(ValueError):r.regular(self.base,'.lake/build/ir/A.c',False)
 def manifest_zip(self,content=b'C runtime'):
  path='.lake/build/ir/Fixture/M0.c';file=self.base/'part';file.write_bytes(content)
  manifest={'schema':1,'snapshot':'a'*64,'modules':['Fixture.M0'],'files':[{'module':'Fixture.M0','path':path,'bytes':len(content),'sha256':r.digest(file)}]}
  archive=self.base/'parts.zip'
  with zipfile.ZipFile(archive,'w')as z:z.writestr(path,content)
  return manifest,archive,path
 def test_archive_sha_and_safe_regular_staging(self):
  manifest,archive,path=self.manifest_zip();self.assertGreater(r.verify_zip(archive,manifest,'a'*64,runtime_only=True),0)
  r.stage_zip(archive,self.base/'cache',manifest,'a'*64);self.assertEqual((self.base/'cache'/path).read_bytes(),b'C runtime')
  (self.base/'cache'/path).write_bytes(b'foreign')
  with self.assertRaises(ValueError):r.stage_zip(archive,self.base/'cache',manifest,'a'*64)
  with zipfile.ZipFile(archive,'w')as z:z.writestr(path,b'X runtime')
  with self.assertRaises(ValueError):r.verify_zip(archive,manifest,'a'*64)
 def test_archive_symlink_and_extra_file(self):
  manifest,archive,path=self.manifest_zip();link=zipfile.ZipInfo(path);link.create_system=3;link.external_attr=0o120777<<16
  with zipfile.ZipFile(archive,'w')as z:z.writestr(link,b'C runtime')
  with self.assertRaises(ValueError):r.verify_zip(archive,manifest,'a'*64)
  with zipfile.ZipFile(archive,'w')as z:z.writestr(path,b'C runtime');z.writestr('../escape',b'x')
  with self.assertRaises(ValueError):r.verify_zip(archive,manifest,'a'*64)
 def test_runtime_cannot_return_proof_interfaces(self):
  for path in ['.lake/build/lib/lean/Fixture/M0.olean','.lake/build/ir/Fixture/M0.ir','.lake/build/lib/lean/Fixture/M0.olean.private']:
   self.assertFalse(r.runtime_path(path))
  for path in ['.lake/build/ir/Fixture/M0.c','.lake/build/ir/Fixture/M0.c.o','.lake/build/lib/lean/Fixture/M0.olean.hash']:
   self.assertTrue(r.runtime_path(path))
 def test_cgroup_requires_real_bounded_cpu_memory_pids(self):
  vals={'memory.max':str(4096*1024**2),'cpu.max':'100000 100000','pids.max':'512'}
  with patch.object(r,'current_cgroup',return_value=Path('/sys/fs/cgroup')),patch.object(Path,'exists',return_value=True),patch.object(Path,'read_text',lambda p:vals[p.name]):r.resource_limits(self.hosts(1)[0])
  for name,value in [('memory.max','max'),('cpu.max','max 100000'),('pids.max','max')]:
   x=dict(vals);x[name]=value
   with patch.object(r,'current_cgroup',return_value=Path('/sys/fs/cgroup')),patch.object(Path,'exists',return_value=True),patch.object(Path,'read_text',lambda p:x[p.name]),self.assertRaises(ValueError):r.resource_limits(self.hosts(1)[0])
 def test_return_binding_and_byte_sha(self):
  manifest,archive,_=self.manifest_zip();out,_=self.planned();control=out/'w0';lease=r.read(control/'lease.json');req=r.read(control/'request-0.json');returned=self.base/'return';returned.mkdir()
  r.atomic(returned/'artifacts-0.json',manifest);(returned/'runtime-parts.zip').write_bytes(archive.read_bytes())
  response={'snapshot':'a'*64,'operation':r.OPERATION,'batch':0,'lease_id':lease['lease_id'],'request_sha256':lease['request_sha256'],'run_id':'123','run_attempt':1,'runner_name':'registered-0','result':{'ok':True,'modules':[{'module':'Fixture.M0','ok':True}]},'artifacts':{'manifest':'artifacts-0.json','sha256':r.digest(returned/'artifacts-0.json')}}
  r.atomic(returned/'response-0.json',response);provenance={'run_id':'123','run_attempt':1,'runner_name':'registered-0','workflow_sha':'b'*40,'artifact_name':f'native-123-1-{lease["lease_id"]}'}
  got=r.accept(control,returned,provenance);self.assertFalse(got['promotion_performed']);self.assertEqual(got['native_proof_check'],'NOT_PERFORMED')
  response['run_attempt']=2;r.atomic(returned/'response-0.json',response)
  with self.assertRaises(ValueError):r.accept(control,returned,provenance)
 def test_worker_fixed_backend_and_published_bytes_preserved(self):
  root=self.base/'workspace';control=self.base/'control';control.mkdir();producer=self.base/'reviewed-producer';producer.write_text('FIXTURE ONLY; NOT EXECUTED')
  module='Fixture.M0';files=[]
  (root/'src/Fixture').mkdir(parents=True);(root/'src/Fixture/M0.lean').write_text('module\n-- data fixture only\n')
  for part,suffix in [('lib/lean','.olean'),('ir','.ir')]:
   rel=f'.lake/build/{part}/Fixture/M0{suffix}';p=root/rel;p.parent.mkdir(parents=True,exist_ok=True);p.write_bytes(b'PUBLISHED FIXTURE');files.append({'module':module,'path':rel,'bytes':p.stat().st_size,'sha256':r.digest(p)})
  inputs={'schema':1,'snapshot':'a'*64,'modules':[module],'files':files};r.atomic(control/'input-manifest.json',inputs)
  planroot=self.base/'worker-plan';r.plan(self.snapshot,{'snapshot':'a'*64,'modules':[{'module':module}]},self.hosts(1),'123',1,'b'*40,r.digest(producer),r.digest(control/'input-manifest.json'),planroot)
  for n in ['lease.json','request-0.json']:(control/n).write_bytes((planroot/'w0'/n).read_bytes())
  original=subprocess.run;calls=[]
  def execute(argv,**kw):
   if str(argv[0])==str(producer):
    calls.append((argv,kw));p=root/'.lake/build/ir/Fixture/M0.c';p.write_text('/* fixture runtime */');r.atomic(Path(argv[-1]),{'ok':True,'modules':[{'module':module,'ok':True}]});return subprocess.CompletedProcess(argv,0,b'',b'')
   return original(argv,**kw)
  with patch.object(r,'verify_source'),patch.object(r,'no_network',return_value=True),patch.object(r,'resource_limits'),patch.object(r.subprocess,'run',side_effect=execute),patch.dict(os.environ,{'GITHUB_TOKEN':'DO-NOT-PASS','AWS_SECRET_ACCESS_KEY':'DO-NOT-PASS'}):
   result=r.worker(root,control,self.base/'output',producer,'123',1,'registered-0')
  self.assertEqual(len(calls),1);self.assertNotIn('GITHUB_TOKEN',calls[0][1]['env']);self.assertNotIn('AWS_SECRET_ACCESS_KEY',calls[0][1]['env']);self.assertEqual(calls[0][1]['timeout'],60)
  manifest=r.read(self.base/'output/artifacts-0.json');self.assertEqual([x['path']for x in manifest['files']],['.lake/build/ir/Fixture/M0.c']);self.assertEqual(result['operation'],r.OPERATION)
if __name__=='__main__':unittest.main(verbosity=2)
