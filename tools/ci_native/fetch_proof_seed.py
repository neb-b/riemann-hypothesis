#!/usr/bin/env python3
"""Download SHA-addressed proof controls from the existing public cache only."""
import argparse
import hashlib
from pathlib import Path
import urllib.request
import rpc

BASE = 'https://rh-cache.taucetiproject.org/ci/proof-leases/'


def fetch(digest, kind, output, maximum):
    rpc.require(rpc.SHA.fullmatch(digest), 'invalid proof control SHA')
    rpc.require(kind in ('seed.json', 'worklist.txt', 'inputs.zip'), 'unknown proof control object')
    path = Path(output)
    path.parent.mkdir(parents=True, exist_ok=True)
    temporary = path.with_name(path.name + '.download')
    sha, size = hashlib.sha256(), 0
    try:
        request = urllib.request.Request(BASE + digest + '/' + kind, headers={'User-Agent': 'RiemannHypothesisCache/1.0'})
        with urllib.request.urlopen(request, timeout=120) as response, temporary.open('wb') as stream:
            while data := response.read(1024 * 1024):
                size += len(data)
                rpc.require(size <= maximum, 'proof control object too large')
                sha.update(data)
                stream.write(data)
        rpc.require(sha.hexdigest() == digest, 'proof control SHA mismatch')
        temporary.replace(path)
    finally:
        temporary.unlink(missing_ok=True)
    return path


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument('--seed-sha256', required=True)
    parser.add_argument('--output', required=True, type=Path)
    parser.add_argument('--inputs-only', action='store_true')
    args = parser.parse_args()
    seed = fetch(args.seed_sha256, 'seed.json', args.output / 'seed.json', 10 * 1024**2)
    value = rpc.read(seed)
    rpc.snapshot_identity(value['snapshot'], rpc.PROOF_OPERATION)
    if args.inputs_only:
        fetch(value['input_archive_sha256'], 'inputs.zip', args.output / 'input-parts.zip', rpc.MAX_BYTES)
    else:
        fetch(rpc.proof_policy()['worklist_sha256'], 'worklist.txt',
              args.output / 'proof-worklist.txt', 20 * 1024**2)
        rpc.proof_worklist(args.output / 'proof-worklist.txt')

if __name__ == '__main__':
    main()
