The reviewed runtime adapter also has an explicit, separately pinned `native-proof`
mode for bounded #91 proof batches. See [PROOFS.md](PROOFS.md). Runtime mode retains
the restrictions below. The runner-group policy is unchanged; merge and dispatch
require operator review.

The runtime-only operation is a reviewable transport adapter for the exact PR66 source tree
`0ba0b4d44fa26b97a376ec10889be6b553237103`. It does not repair proofs, execute project
Lean source, call the old proof ShardWorker, promote a cache, register runners, or
dispatch a workflow. The workflow is an .example file and the approved runner roster
is empty. The independent five-host production batch is outside this adapter.

The compiled backend is the already reviewed RuntimeProducer source
`56561f3340a6002317ba7886ffc3676ff648985fa8a2af345612ae0e91fea264`.
It reads the published module/private/IR archive and emits C for existing computational
declarations, one native process per module. Its infrastructure package can be built
with `python3 build_backend.py --toolchain /absolute/stock/toolchain`.
This compiles only that trusted helper, with the stock 4.36.0/611c compiler.
The architecture-local ELF SHA is recorded separately; no Nix ELF is assumed portable.

The worker keeps the existing schema-1 native file manifests and
request-0.json / ready.json / response-0.json file-RPC identities.
`rpc.py plan` distributes an arbitrary positive number of registered Linux/X64
workers, using measured project_closure_archived_bytes when supplied, otherwise bytes.
These weights are payload sizes, not claimed RAM estimates. Resource limits remain
explicit operator policy. Leases bind the immutable source/configuration, request
SHA, trusted wrapper SHA, run/attempt, exact runner, time limit, and input manifest.

An operator prepares one data-only seed JSON:
`{snapshot,missing,input_manifest,verified_archive}`.
Snapshot contains the exact identity.json fields plus git_commit and a 64-hex source
fingerprint. The explicit candidate commit may be the metadata-only 716/2e43 head
only when its source tree and all raw configuration hashes match the pinned identity.
Missing contains `{snapshot:fingerprint,modules:[{module,bytes,...}]}`.
The master input_manifest is the existing schema-1 manifest of the eight original
published parts per requested module. Generate it read-only with:

```sh
python3 flat_inputs.py archive --archive /verified/archive/lean \
  --snapshot snapshot.json --missing missing.json --output input-manifest.json
```

The full-archive verification receipt must attest the exact published c652 archive
(149395 modules / 1195160 files / 82466169920 bytes). This receipt describes transport
integrity, not proof verification. Every requested original part is independently
rehashed by the worker before and after runtime generation, from a read-only mount.
No 83GB copy is needed. All eight actual suffixes are retained, including .ir.sig,
.cbuild-input and .cbuild-source. No synthetic .hash files are assumed in the archive.

Each approved roster entry requires id, runner_name, runs_on (self-hosted/Linux/X64
and a unique registered runner label), cpus, memory_mib, timeout_seconds, and absolute
archive_root, dependency_root, toolchain_root paths. Optional jobs is bounded by cpus.
All nine locked source repository HEADs must match the raw manifest. Exactly eight
compiled cache directories are expected: Cli has none. The dependency caches and
stock toolchain must already be verified by the operator.
No SSH access or cloud credentials are needed by a registered GHA runner.

`prepare.py` requires the operator-pinned seed SHA, uses only the committed approved
roster, assigns nonoverlapping tasks, and binds per-worker eight-part input subsets.
An empty inventory creates no request and never invokes a default Lake target.
The sample workflow accepts exactly one manual candidate run in a constant concurrency
group. Before enabling it, the owner must review the whole patch, pin the Actions
versions to reviewed immutable commits, add only actually registered runner labels,
and provide the authenticated seed artifact from an explicitly trusted run.
It is not enabled merely by copying these tools into a checkout.

The self-hosted job checks out candidate source as data with persist-credentials:false,
builds the trusted infrastructure helper separately, then invokes launch.py inside
a systemd user unit with CPUQuota, MemoryMax, MemorySwapMax=0, TasksMax=512, RuntimeMaxSec.
The launcher verifies the actual unit cgroup (including ancestor limits), mounts
source/tools/nine locked dependency source repos and their eight compiled cache directories read-only, mounts only the private output cache
writable, starts from an empty filesystem with only explicit system runtime/input
mounts (no host home/root/run/var/etc), removes inherited environment variables,
and unshares network and PID namespaces. Bubblewrap is required; there is no
unsandboxed fallback. The source checkout must be private with an existing empty
.lake/build directory. Never point the launcher at a mutable canonical proof workspace.

The backend derives canonical module setup options from the unchanged raw lakefile,
including the GroundTheoryFields synthesis override. Per-module failures remain
explicit ordered rows; successful C can be recovered without declaring the batch
or any proof checked. GitHub artifact upload occurs after leaving the sandbox.
`rpc.py accept` binds authoritative Actions provenance (not an untrusted JSON claim),
checks the lease/run/attempt/runner/manifest and every ZIP byte, forbids proof/IR
outputs, and returns a verification receipt only. The caller must obtain provenance
from the GitHub API and keeps exclusive cache-promotion authority. Failed/stale jobs
are never automatically reassigned by this adapter.

Validation is metadata/fixture-only for the adapter; no project Lean elaboration or
runtime production lease has been launched by it. The separate native-producer
100-module benchmark is evidence for the backend, not a claim that this workflow
has run in GitHub Actions. Run local protocol tests with:
`python3 -m unittest -v test_rpc.py test_adapter.py`.
