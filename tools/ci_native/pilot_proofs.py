#!/usr/bin/env python3
"""Small real stock proof/guard integration test; no project checkout is built."""
import argparse
import hashlib
import json
import os
from pathlib import Path
import subprocess
import tempfile


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument('--toolchain', required=True, type=Path)
    parser.add_argument('--backend', required=True, type=Path)
    args = parser.parse_args()
    toolchain, backend = args.toolchain.resolve(), args.backend.resolve()
    environment = {'PATH': str(toolchain / 'bin') + ':' + os.environ['PATH'],
                   'HOME': '/tmp/native-proof-pilot', 'LEAN_SYSROOT': str(toolchain),
                   'LAKE_HOME': str(toolchain), 'LEAN_NUM_THREADS': '2', 'LAKE_NO_CACHE': 'true'}
    with tempfile.TemporaryDirectory(prefix='rh-proof-pilot-') as temporary:
        root = Path(temporary)
        source = root / 'src/Fixture'
        source.mkdir(parents=True)
        (root / 'lakefile.toml').write_text('name="proofFixture"\nsrcDir="src"\n[[lean_lib]]\nname="Fixture"\nglobs=["Fixture.+"]\n')
        (root / 'lean-toolchain').write_text('leanprover/lean4:v4.36.0\n')
        modules = {'Base': 'module\npublic theorem base : True := True.intro\n',
                   'A': 'module\nimport Fixture.Base\ntheorem proofA : True := base\n',
                   'B': 'module\nimport Fixture.Base\ntheorem proofB : True := base\n',
                   'Unbuilt': 'module\npublic theorem notBuilt : True := True.intro\n',
                   'Blocked': 'module\nimport Fixture.Unbuilt\ntheorem blocked : True := notBuilt\n'}
        for name, text in modules.items():
            (source / (name + '.lean')).write_text(text)
        subprocess.run([str(toolchain / 'bin/lake'), 'build', '+Fixture.Base'],
                       cwd=root, env=environment, check=True)
        request, result = root / 'request.json', root / 'result.json'
        request.write_text(json.dumps({'modules': ['Fixture.A', 'Fixture.B']}))
        subprocess.run([str(backend), str(request), str(result)], cwd=root,
                       env=environment, check=True)
        value = json.loads(result.read_text())
        assert value['ok'] and all(row['ok'] for row in value['modules'])
        for name in ['A', 'B']:
            for suffix in ['olean', 'olean.server', 'olean.private', 'ilean', 'ir.sig', 'ir', 'trace']:
                assert (root / '.lake/build/lib/lean/Fixture' / (name + '.' + suffix)).is_file()
            assert (root / '.lake/build/ir/Fixture' / (name + '.c')).is_file()
        request.write_text(json.dumps({'modules': ['Fixture.Blocked']}))
        blocked = subprocess.run([str(backend), str(request), str(root / 'blocked.json')],
                                 cwd=root, env=environment, capture_output=True)
        assert blocked.returncode != 0
        assert not (root / '.lake/build/lib/lean/Fixture/Unbuilt.olean').exists()
        assert not (root / '.lake/build/lib/lean/Fixture/Blocked.olean').exists()
    print(json.dumps({'stock_proof_modules_built': 2, 'complete_native_parts_verified': 16,
                      'unleased_missing_dependency_rejected': True,
                      'unleased_dependency_compiled': False, 'live_project_modified': False}))


if __name__ == '__main__':
    main()
