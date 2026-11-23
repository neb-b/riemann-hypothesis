#!/usr/bin/env python3
"""Bind an operator-reviewed, SHA-pinned data seed to this single manual workflow run."""
import argparse,json
from pathlib import Path
import rpc,flat_inputs

def prepare(seed,registry,output,run_id,attempt,workflow_sha,producer_sha):
    rpc.require(registry,'no approved registered runners; enable only after independent review')
    result=rpc.plan(seed['snapshot'],seed['missing'],registry,run_id,attempt,workflow_sha,producer_sha,
                    rpc.rawsha(seed['input_manifest']),output)
    flat_inputs.bind(output,seed['input_manifest'],seed['verified_archive'])
    return result

def main():
    p=argparse.ArgumentParser()
    for key in ['seed','seed-sha256','registry','output','run-id','workflow-sha','producer']:p.add_argument('--'+key,required=True)
    p.add_argument('--attempt',type=int,required=True);a=p.parse_args()
    rpc.require(rpc.digest(a.seed)==a.seed_sha256,'operator seed SHA mismatch')
    print(json.dumps(prepare(rpc.read(a.seed),rpc.read(a.registry),a.output,a.run_id,a.attempt,a.workflow_sha,rpc.digest(a.producer))))
if __name__=='__main__':main()
