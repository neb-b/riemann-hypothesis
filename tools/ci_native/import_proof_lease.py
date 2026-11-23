#!/usr/bin/env python3
"""Verify one GHA proof return before completing its existing coordinator lease."""
import argparse
from pathlib import Path
import rpc


def accept(control, returned, provenance, proxy_root, proxy_round, coordinator_leases, worker_id, batch):
    control, returned, proxy_root, proxy_round = map(Path, (control, returned, proxy_root, proxy_round))
    rpc.require(rpc.IDENT.fullmatch(worker_id), 'invalid coordinator worker ID')
    rpc.require(type(batch) is int and batch >= 0, 'invalid coordinator batch')
    lease = rpc.read(control / 'lease.json')
    rpc.require(lease['operation'] == rpc.PROOF_OPERATION, 'not a proof lease')
    request = rpc.read(control / 'request-0.json')
    expected = rpc.read(proxy_round / f'request-{batch}.json')
    durable = rpc.read(coordinator_leases)
    rpc.require(durable['snapshot'] == lease['snapshot'], 'coordinator source changed')
    active = durable['workers'][worker_id]
    rpc.require(active is not None and active['batch'] == batch and
                active['modules'] == expected['modules'], 'coordinator lease mismatch')
    rpc.require(len(set(request['modules'])) == len(request['modules']) and
                set(active['modules']) == set(request['modules']), 'coordinator work scope mismatch')
    rpc.require(expected['snapshot'] == lease['snapshot']['fingerprint'], 'proxy snapshot mismatch')
    destination = proxy_round / f'response-{batch}.json'
    rpc.require(not destination.exists(), 'coordinator response already exists')
    receipt = rpc.accept(control, returned, provenance)
    manifest = rpc.read(returned / 'artifacts-0.json')
    # Existing accepted output bytes may agree; different bytes are never silently
    # replaced. The coordinator remains the sole DAG/lease authority.
    rpc.stage_zip(returned / 'runtime-parts.zip', proxy_root, manifest, expected['snapshot'])
    original = rpc.read(returned / 'response-0.json')
    manifest_path = proxy_round / f'artifacts-{batch}.json'
    rpc.atomic(manifest_path, manifest)
    # Actions may rebalance the same exact scope into a different order. Preserve
    # its original response and translate only the coordinator's ordered view.
    by_name = {row['module']: row for row in original['result']['modules']}
    result = {**original['result'], 'modules': [by_name[name] for name in active['modules']]}
    response = {'snapshot': expected['snapshot'], 'batch': batch,
                'elapsed_ms': original['elapsed_ms'], 'result': result,
                'artifacts': {'manifest': str(manifest_path), 'sha256': rpc.digest(manifest_path),
                              'files': len(manifest['files']), 'modules': len(manifest['modules']),
                              'bytes': sum(row['bytes'] for row in manifest['files'])}}
    rpc.atomic(proxy_round / f'gha-accepted-{batch}.json', receipt)
    # This final atomic write is the only completion signal observed by the
    # unchanged coordinator. Failed verification leaves its lease untouched.
    rpc.atomic(destination, response)
    return receipt


def main():
    parser = argparse.ArgumentParser()
    for name in ('control', 'returned', 'provenance', 'proxy-root', 'proxy-round',
                 'coordinator-leases', 'worker-id'):
        parser.add_argument('--' + name, required=True)
    parser.add_argument('--batch', type=int, required=True)
    values = vars(parser.parse_args())
    values['provenance'] = rpc.read(values['provenance'])
    import json
    print(json.dumps(accept(**values)))

if __name__ == '__main__':
    main()
