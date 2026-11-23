import hashlib,json,subprocess,sys,tempfile,unittest
from pathlib import Path
from unittest.mock import patch
import rpc,flat_inputs,launch,producer,prepare
import test_rpc as fixtures

def receipt():
 return {'schema':1,'kind':'verified-volunteer-artifact-archive','revision':rpc.BASELINE_COMMIT,
 'archive_sha256':'c652456b1f0e35e98b9a0b809f807e729db6cfaad76c986c20fa618f1781d1fb',
 'files':1195160,'modules':149395,'unpacked_bytes':82466169920,'proof_verification':False}

class AdapterTests(unittest.TestCase):
 setUp=fixtures.ProtocolTests.setUp
 hosts=fixtures.ProtocolTests.hosts
 planned=fixtures.ProtocolTests.planned
 def flat(self,names):
  root=self.base/'archive'
  for name in names:
   stem=root/Path(*name.split('.'));stem.parent.mkdir(parents=True,exist_ok=True)
   for suffix in flat_inputs.PARTS:Path(str(stem)+suffix).write_bytes((name+suffix).encode())
  return root,flat_inputs.build(root,self.snapshot,names)
 def test_eight_actual_archive_parts_and_sha(self):
  archive,manifest=self.flat(['Fixture.M0'])
  self.assertEqual(len(manifest['files']),8)
  self.assertEqual({Path(x['path']).name for x in manifest['files']},{'M0'+x for x in flat_inputs.PARTS})
  with patch.object(rpc,'readonly_mount',return_value=True):rpc.verify_flat(archive,manifest,'a'*64,receipt())
  (archive/'Fixture/M0.ir.sig').write_bytes(b'changed')
  with patch.object(rpc,'readonly_mount',return_value=True),self.assertRaises(ValueError):rpc.verify_flat(archive,manifest,'a'*64,receipt())
 def test_archive_receipt_and_readonly_fail_closed(self):
  archive,manifest=self.flat(['Fixture.M0'])
  for key,value in [('proof_verification',True),('files',1),('archive_sha256','f'*64),('revision','0'*40)]:
   bad={**receipt(),key:value}
   with self.assertRaises(ValueError):rpc.archive_receipt(bad)
  with patch.object(rpc,'readonly_mount',return_value=False),self.assertRaises(ValueError):rpc.verify_flat(archive,manifest,'a'*64,receipt())
 def test_flat_symlink_missing_original_part(self):
  archive,manifest=self.flat(['Fixture.M0']);part=archive/'Fixture/M0.ir';part.unlink()
  with self.assertRaises(ValueError):flat_inputs.build(archive,self.snapshot,['Fixture.M0'])
  part.symlink_to(archive/'Fixture/M0.olean')
  with self.assertRaises(ValueError):flat_inputs.build(archive,self.snapshot,['Fixture.M0'])
 def test_per_host_manifests_are_disjoint_bound_subsets(self):
  out,matrix=self.planned(3,7);archive,master=self.flat([f'Fixture.M{i}'for i in range(7)])
  flat_inputs.bind(out,master,receipt());seen=[]
  for row in matrix['include']:
   c=out/row['id'];lease=rpc.read(c/'lease.json');m=rpc.read(c/'input-manifest.json')
   self.assertEqual(rpc.digest(c/'input-manifest.json'),lease['input_manifest_sha256'])
   self.assertEqual(rpc.digest(c/'verified-archive.json'),lease['worker']['archive_receipt_sha256'])
   self.assertEqual(len(m['files']),8*len(m['modules']));seen+=m['modules']
  self.assertEqual(len(seen),7);self.assertEqual(len(set(seen)),7)
 def test_prepare_refuses_unapproved_registry(self):
  with self.assertRaises(ValueError):prepare.prepare({},[],self.base/'out','1',1,'b'*40,'c'*64)
 def test_effective_own_unit_cgroup_not_host_root(self):
  unit=Path('/sys/fs/cgroup/user.slice/unit.service')
  def text(p):
   if p.name=='memory.max':return str(2048*1024**2) if p.parent==unit else 'max'
   if p.name=='cpu.max':return '100000 100000' if p.parent==unit else 'max 100000'
   return '512' if p.parent==unit else 'max'
  with patch.object(rpc,'current_cgroup',return_value=unit),patch.object(Path,'exists',return_value=True),patch.object(Path,'read_text',text):rpc.resource_limits(self.hosts(1)[0])
 def test_full_options_preserve_root_and_ground_fields_override(self):
  import tomllib
  config=tomllib.loads(Path(__file__).parents[2].joinpath('lakefile.toml').read_text())
  result=producer.options(config,'GroundTheory.GlobalFields.Example')
  self.assertEqual(result['synthInstance.maxHeartbeats'],400000)
  self.assertEqual(result['maxHeartbeats'],4000000);self.assertFalse(result['autoImplicit'])
  self.assertEqual(producer.options(config,'Main')['pp.unicode.fun'],True)
  with self.assertRaises(ValueError):producer.options(config,'NotADefaultLibrary.Example')
 def test_header_module_flag_skips_nested_comments(self):
  p=self.base/'header.lean';p.write_text('/- a /- nested -/ b -/\n-- line\nmodule\nimport Lean\n')
  self.assertTrue(producer.module_flag(p));p.write_text('-- module\nimport Lean\n');self.assertFalse(producer.module_flag(p))
 def test_native_is_one_process_per_module_partial_results_ordered(self):
  home=self.base/'bridge';package=home/'backend';binary=package/'.lake/build/bin/runtime-producer';binary.parent.mkdir(parents=True);binary.write_text('fake ELF not executed')
  (package/'RuntimeProducer.lean').write_text('fake trusted infrastructure fixture')
  source=producer.sha(package/'RuntimeProducer.lean');producer.publish(package/'binary-receipt.json',{'source_sha256':source,'elf_sha256':producer.sha(binary)})
  root=self.base/'workspace';(root/'src/Fixture').mkdir(parents=True);(root/'.lake/build').mkdir(parents=True)
  root.joinpath('lakefile.toml').write_text('name="tree"\n[[lean_lib]]\nname="Fixture"\nglobs=["Fixture.+"]\n')
  for name in ['A','B']:(root/f'src/Fixture/{name}.lean').write_text('module\n')
  deps=self.base/'deps'
  for i in range(9):(deps/f'd{i}/.lake/build/lib/lean').mkdir(parents=True)
  request=self.base/'native-request.json';result=self.base/'native-result.json';producer.publish(request,{'modules':['Fixture.A','Fixture.B']});calls=[]
  def native(argv,**kwargs):
   data=json.loads(Path(argv[2]).read_text());self.assertEqual(len(data['modules']),1);item=data['modules'][0];calls.append((data,kwargs))
   ok=item['name']=='Fixture.A'
   if ok:Path(item['output']).write_text('/* fixture generated C */')
   producer.publish(argv[4],{'complete':True,'results':[{'module':item['name'],'ok':ok,'error':'fixture failure' if not ok else '','output':item['output']}]})
   return subprocess.CompletedProcess(argv,0 if ok else 1,b'',b'')
  env={'NATIVE_ARCHIVE_ROOT':str(self.base/'archive'),'NATIVE_PACKAGE_ROOT':str(deps),'NATIVE_TOOLCHAIN_ROOT':str(self.base/'tc'),'NATIVE_PRODUCER_JOBS':'2','LEAN_NUM_THREADS':'2','GITHUB_TOKEN':'MUST-NOT-PASS'}
  with patch.object(producer,'__file__',str(home/'producer.py')),patch.object(producer,'SOURCE_SHA',source),patch.dict(producer.os.environ,env),patch.object(sys,'argv',['producer.py','--workspace',str(root),'--request',str(request),'--result',str(result)]),patch.object(producer.subprocess,'run',side_effect=native),patch.object(producer,'dependency_paths',return_value=[str(x)for x in sorted(deps.glob('*/.lake/build/lib/lean'))][:8]):
   self.assertEqual(producer.main(),0)
  rows=json.loads(result.read_text());self.assertFalse(rows['ok']);self.assertEqual([x['module'] for x in rows['modules']],['Fixture.A','Fixture.B']);self.assertEqual(len(calls),2)
  for _,kw in calls:self.assertEqual(kw['env']['LEAN_NUM_THREADS'],'1');self.assertNotIn('GITHUB_TOKEN',kw['env'])
 def test_partial_return_salvages_only_success(self):
  out,_=self.planned(1,2);control=out/'w0';lease=rpc.read(control/'lease.json');names=rpc.read(control/'request-0.json')['modules'];returned=self.base/'returned';returned.mkdir()
  path='.lake/build/ir/'+names[0].replace('.','/')+'.c';data=b'fixture C';sha=hashlib.sha256(data).hexdigest()
  manifest={'schema':1,'snapshot':'a'*64,'modules':[names[0]],'files':[{'module':names[0],'path':path,'bytes':len(data),'sha256':sha}]};rpc.atomic(returned/'artifacts-0.json',manifest)
  import zipfile
  with zipfile.ZipFile(returned/'runtime-parts.zip','w')as z:z.writestr(path,data)
  rpc.atomic(returned/'response-0.json',{'snapshot':'a'*64,'operation':rpc.OPERATION,'batch':0,'lease_id':lease['lease_id'],'request_sha256':lease['request_sha256'],'run_id':'123','run_attempt':1,'runner_name':'registered-0','result':{'ok':False,'modules':[{'module':names[0],'ok':True},{'module':names[1],'ok':False}]},'artifacts':{'manifest':'artifacts-0.json','sha256':rpc.digest(returned/'artifacts-0.json')}})
  got=rpc.accept(control,returned,{'run_id':'123','run_attempt':1,'runner_name':'registered-0','workflow_sha':'b'*40,'artifact_name':f'native-123-1-{lease["lease_id"]}'})
  self.assertEqual(got['modules'],[names[0]]);self.assertEqual(got['failed_modules'],[names[1]]);self.assertFalse(got['promotion_performed'])

 def test_launcher_empty_root_only_explicit_readonly_inputs(self):
  out,_=self.planned();control=out/'w0';lease=rpc.read(control/'lease.json')
  root=self.base/'candidate';(root/'.lake/build').mkdir(parents=True);archive=self.base/'archive';archive.mkdir();deps=self.base/'deps';tc=self.base/'tc';tc.mkdir()
  for i in range(9):(deps/f'd{i}/.lake/build/lib/lean').mkdir(parents=True)
  trusted=Path(launch.__file__).parent/'producer.py'
  lease['producer_sha256']=rpc.digest(trusted)
  lease['worker'].update(archive_root=str(archive),dependency_root=str(deps),toolchain_root=str(tc))
  rpc.atomic(control/'lease.json',lease)
  with patch.object(rpc,'resource_limits'),patch.object(launch.shutil,'which',return_value='/fake/bwrap'),patch.object(launch,'dependency_paths',return_value=[str(x)for x in sorted(deps.glob('*/.lake/build/lib/lean'))][:8]):
   args=launch.command(root,control,self.base/'output',trusted,'123',1,'registered-0')
  self.assertEqual(args[:3],['bwrap','--tmpfs','/']);self.assertIn('--unshare-net',args);self.assertIn('--unshare-pid',args);self.assertIn('--clearenv',args)
  self.assertNotIn('--ro-bind / /',' '.join(args))
  self.assertIn(str(root),args);self.assertIn(str(archive),args)
 def test_no_network_uses_process_namespace_proc(self):
  with patch.object(Path,'read_text',return_value='Inter-| header\n face | header\n lo: 0 0\n'):self.assertTrue(rpc.no_network())
  with patch.object(Path,'read_text',return_value='Inter-| header\n face | header\n lo: 0\n eth0: 1\n'):self.assertFalse(rpc.no_network())


 def test_nine_locked_sources_have_eight_caches_Cli_has_none(self):
  names=['mathlib','plausible','LeanSearchClient','importGraph','proofwidgets','aesop','Qq','batteries','Cli']
  deps=self.base/'real-layout';rows=[]
  for i,name in enumerate(names):
   (deps/name).mkdir(parents=True);rows.append({'name':name,'rev':format(i,'040x')})
   if name!='Cli':(deps/name/'.lake/build/lib/lean').mkdir(parents=True)
  manifest=self.base/'lock.json';manifest.write_text(json.dumps({'packages':rows}));pins={x['name']:x['rev']for x in rows};calls=[]
  def head(argv,**kwargs):calls.append(Path(argv[2]).name);return pins[Path(argv[2]).name]+'\n'
  with patch.object(producer.subprocess,'check_output',side_effect=head):paths=producer.dependency_paths(deps,manifest)
  self.assertEqual(len(paths),8);self.assertEqual(set(calls),set(names));self.assertNotIn(str(deps/'Cli/.lake/build/lib/lean'),paths)
  with patch.object(producer.subprocess,'check_output',return_value='wrong\n'),self.assertRaises(ValueError):producer.dependency_paths(deps,manifest)
  (deps/'Cli/.lake/build/lib/lean').mkdir(parents=True)
  with patch.object(producer.subprocess,'check_output',side_effect=head),self.assertRaises(ValueError):producer.dependency_paths(deps,manifest)

if __name__=='__main__':unittest.main(verbosity=2)
