#!/usr/bin/env python3
"""Exercise production namespace/overlays with a tiny actual Mathlib proof.

The fixture deliberately replaces the worker entrypoint with the trusted backend;
source-lease verification is tested separately. It never edits a project checkout.
"""
import argparse
import json
import os
from pathlib import Path
import subprocess
import tempfile
import rpc
import launch


def main():
    parser = argparse.ArgumentParser()
    for name in ('dependency-root', 'toolchain', 'worklist', 'project-config'):
        parser.add_argument('--' + name, required=True, type=Path)
    parser.add_argument('--receipt', type=Path)
    parser.add_argument('--sealed-base', action='store_true')
    parser.add_argument('--modules', type=int, default=1)
    parser.add_argument('--jobs', type=int, default=2)
    args = parser.parse_args()
    dependencies, toolchain = args.dependency_root.resolve(), args.toolchain.resolve()
    allowed = sorted(rpc.proof_worklist(args.worklist))
    assert 1 <= args.modules <= 64 and 1 <= args.jobs <= 64
    names = allowed[:args.modules]
    sources = [dependencies / 'mathlib/Mathlib/Logic/Relation.lean',
               dependencies / 'mathlib/.lake/build/lib/lean/Mathlib/Logic/Relation.olean']
    before = {str(path): rpc.digest(path) for path in sources}
    with tempfile.TemporaryDirectory(prefix='rh-mathlib-sandbox-') as temporary:
        base = Path(temporary)
        root, control, output = base / 'candidate', base / 'control', base / 'output'
        root.mkdir()
        for config in ('lakefile.toml', 'lake-manifest.json', 'lean-toolchain'):
            (root / config).write_bytes((args.project_config / config).read_bytes())
        for part in ('build', 'packages'):
            (root / '.lake' / part).mkdir(parents=True, exist_ok=True)
        for i, name in enumerate(names):
            source = root / 'src' / Path(*name.split('.')).with_suffix('.lean')
            source.parent.mkdir(parents=True, exist_ok=True)
            source.write_text('module\nimport Mathlib.Logic.Relation\npublic theorem donorSandboxPilot' + str(i) + ' : True := True.intro\n')
        snapshot = rpc.proof_policy()['snapshot']
        host = {'id': 'pilot', 'runner_name': 'pilot',
                'runs_on': ['self-hosted', 'Linux', 'X64', 'isolated-proof-pilot'],
                'cpus': max(16, args.jobs), 'memory_mib': 65536, 'jobs': args.jobs, 'timeout_seconds': 120}
        trusted = Path(__file__).with_name('proof_producer.py')
        manifest = {'schema': 1, 'snapshot': snapshot['fingerprint'], 'modules': [], 'files': []}
        rpc.plan(snapshot, {'snapshot': snapshot['fingerprint'], 'modules': [{'module': name} for name in names]},
                 [host], '123', 1, 'b' * 40, rpc.digest(trusted), rpc.rawsha(manifest),
                 control, mode=rpc.PROOF_OPERATION, worklist=args.worklist)
        control = control / 'pilot'
        import zipfile
        with zipfile.ZipFile(control / 'input-parts.zip', 'w'):
            pass
        rpc.atomic(control / 'input-manifest.json', manifest)
        lease = rpc.read(control / 'lease.json')
        baseline = base / 'unused-baseline'
        baseline.mkdir()
        lease['worker'].update(dependency_root=str(dependencies), toolchain_root=str(toolchain),
                               baseline_cache_root=str(baseline))
        if args.sealed_base:
            import proof_baseline
            expanded=base/'expanded'
            for part in ('lib/lean','ir'):(expanded/'.lake/build'/part).mkdir(parents=True)
            rpc.atomic(expanded/'complete.json',proof_baseline.seal_fields())
            lease['worker']['expanded_base_root']=str(expanded)
        rpc.atomic(control / 'lease.json', lease)
        argv = launch.command(root, control, output, trusted, '123', 1, 'pilot',seal_base=args.sealed_base)
        index = argv.index('--chdir')
        # Reuse the exact production isolation and dependency mounts. Only this
        # test's fixed tiny backend replaces the file-RPC/real-source checks.
        argv = argv[:index] + ['--setenv', 'LEAN_SYSROOT', str(toolchain),
                              '--setenv', 'LAKE_HOME', str(toolchain),
                              '--setenv', 'LEAN_NUM_THREADS', str(args.jobs)] + argv[index:index + 2]
        backend = Path(__file__).parent / 'backend/.lake/build/bin/proof-producer'
        result = output / 'returned/mathlib-result.json'
        # Check the same operation-specific limit again inside the namespace,
        # as production rpc.worker does, before invoking the stock backend.
        probe = ('import sys,subprocess;sys.path.insert(0,' + repr(str(Path(__file__).parent)) + ');'
                 'import rpc;rpc.resource_limits(' + repr(host) + ',rpc.PROOF_OPERATION);'
                 'raise SystemExit(subprocess.run(' + repr([str(backend.resolve()), str(control / 'request-0.json'), str(result)]) + ').returncode)')
        argv += [__import__('sys').executable, '-c', probe]
        process = subprocess.run(argv, capture_output=True, text=True)
        print(process.stdout)
        print(process.stderr)
        assert process.returncode == 0
        value = rpc.read(result)
        assert value['ok'] and len(value['modules']) == len(names) and all(row['ok'] for row in value['modules'])
        native_parts=[]
        for name in names:
          for suffix in rpc.PROOF_PARTS:
            part='ir' if suffix=='.c' else 'lib/lean'
            upper=output/'seed/.lake/build' if not args.sealed_base or '--overlay-src' in argv else output/'private-base-build'
            path=upper/part/Path(*name.split('.')).with_suffix(suffix)
            assert path.is_file(), 'successful Mathlib proof lacks '+suffix
            native_parts.append({'module':name,'suffix':suffix,'bytes':path.stat().st_size,'sha256':rpc.digest(path)})
        for path, sha in before.items():
            assert rpc.digest(path) == sha, 'original dependency bytes changed'
        upper_files = [path for path in (output / 'dependency-overlays').rglob('*') if path.is_file()]
        assert upper_files, 'pilot did not exercise writable dependency sidecars'
        receipt={'stock_mathlib_proof': 'PASS', 'original_dependency_sample_bytes_unchanged': True,
                          'private_upper_files': len(upper_files),
                          'private_sidecar_samples': [str(p.relative_to(output)) for p in upper_files[:12]],
                          'production_bwrap_overlay_namespace': True, 'live_project_modified': False,
                          'native_output_parts':native_parts,'native_output_part_count':len(native_parts),
                          'modules':len(names),'producer_jobs':args.jobs,
                          'actual_pids_max':(rpc.current_cgroup()/'pids.max').read_text().strip(),
                          'resource_checks':'launch and inside production namespace'}
        if args.receipt:rpc.atomic(args.receipt,receipt)
        print(json.dumps(receipt))

if __name__ == '__main__':
    main()
