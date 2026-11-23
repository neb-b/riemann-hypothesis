# Lake cache bootstrap

Operational CI and publishing use the workflow-owned release and baseline pins in `scripts/cache-baselines.json`. Dependency state and revision maps are scoped by toolchain. Completed jobs from a previous registered release retain that release's pins when publishing; the original archive bootstrap below remains specific to Lean 4.33.1.

A release upgrade uses `scripts/run-complete-build.py` for its final stock default-target build. The wrapper binds committed inputs before and after the command to its log and output map. `scripts/stage-completed-build.py --build-receipt ...` requires that fresh receipt and stages the existing compressed artifacts plus a separate module index, without rebuilding proofs. A completed native `--cache-dir` can supply LTARs absent from the IR directory. Publish from the operator credential host with `publish-lake-cache.py --module-manifest ... --build-receipt ...`, verify the public map/index and a cold client restoration, then activate the new descriptor's revision and SHA256 pins. An unconfigured release cannot fall back to another toolchain's archive.

The proof artifacts come from [Jack McCarthy's published archive](https://huggingface.co/datasets/JackMcCarthy/riemann-hypothesis-build/tree/9036e64326acf4acfae159b96664e9708445c1d1): 175,187 `.olean`/`.ilean` pairs, 28,638,044,751 compressed bytes and 99,269,509,951 extracted bytes. `fetch-published-cache.py` verifies the archive, manifest, and every extracted file against pinned SHA256 checksums, rejecting links, duplicates, and unsafe paths.

The preferred C source is the separately published [Lake build extras](https://huggingface.co/datasets/JackMcCarthy/riemann-hypothesis-build/tree/d4a057ad21e2f699743f0ed061fa2be73edfd68b/lake-extras), pinned to revision `d4a057ad21e2f699743f0ed061fa2be73edfd68b`. These came from another build, so their C must be checked against the preserved proof artifacts before use. External traces and hash files are never installed over the build tree.

## Preserve proofs, supply C and traces

- These are legacy modules, without `module` headers. Separate `.ir`, `.ir.sig`, `.olean.server`, and `.olean.private` files are unnecessary.
- `Normalize.lean` changes the archived package metadata from `none` to `tree`, matching stock Lake. Constants and runtime IR remain unchanged; published ileans are retained. For modules without runtime code, stock Lean emits initialization-only C from import/package metadata.
- `fetch-published-extras.py` verifies both extras archives and manifests, then separately extracts C for the **20,955 runtime modules** and collects the external build's olean hashes. Resumption rechecks derived C and hash data against the pinned per-file SHA256 manifests; a completion marker cannot bypass those checks.
- `AttestExtras.lean` compares actual frozen olean bytes with the external build's Lake hash. Where necessary, it serializes a temporary copy changing only diagnostic filenames in `lintLogExt`; matching that copy certifies that the runtime/proof data is unchanged. The frozen olean is never replaced.
- The initial run attested **10,813 exact matches and 10,141 diagnostic-path-only matches**. The sole remaining module, `Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.LocModel`, already had compatibility-checked source-generated C.
- `accept-published-c.py` rehashes frozen oleans, verifies published C SHA256 values, and installs only missing C. Previously validated C is preserved because indexing or packing may already have observed it.

An unattested module uses the guarded source fallback: stock Lean elaborates it in an offline Bubblewrap sandbox, and `CheckRuntime.lean` compares every archived constant—including theorem proof values—plus native signatures, runtime IR, imports/package metadata, and initializer order. Fresh oleans/ileans are discarded after acceptance; only C is retained. Thus a cold bootstrap needs fallback compilation only for unmatched modules, rather than all 20,955 runtime modules.

Source Lean commands explicitly pass **`-j1`**. `LEAN_NUM_THREADS=1` alone does not limit the [Lean 4.33.1 shell](https://github.com/leanprover/lean4/blob/v4.33.1/src/Lean/Shell.lean#L219), whose default pool uses the hardware thread count. Independent module jobs provide parallelism.

`Trace.lean` uses the pinned Lake's hashing/import-trace operations to reconstruct source/dependency/compiler/options/module/package input hashes. It writes synthetic fetch traces and packs complete `.ltar` artifacts with stock `leantar`; only root-package mappings are published. Ordinary Lake commands retain their normal graph-processing costs. Mathematical verification is separate: see [the Comparator instructions](../README.md#checking-it).

## Produce and test

```bash
ulimit -n 65536
MATHLIB_CACHE_GET_URL=https://cache.mathlib.org/mathlib4 lake exe mathlib/cache get
python3 scripts/fetch-published-cache.py --download-dir .lake/published-cache
python3 scripts/bootstrap-cache.py --workers 16
```

The producer checks the pinned source tree, dependency manifest, and compiler configuration. Its preferred route is normalization, extras verification, attestation, C acceptance, guarded fallback for unmatched modules, then indexing/packing. State and validation records live in `.lake/bootstrap`; final artifacts and `outputs.jsonl` are staged in `.lake/cache-staging`. Re-extract the original archive before normalization, never during an already normalized resumed run.

Before packing, the producer raises its process stack soft limit to the existing hard limit. Stock `leantar` needs more than the usual 8 MiB stack to compress some deeply nested oleans; no system limits are changed. The resulting archives unpack with the default 8 MiB stack.

```bash
lake -d scripts/cache-bootstrap build trace-cache normalize-cache check-runtime hash-outputs attest-extras
python3 scripts/cache-bootstrap/test_bootstrap.py
```

Fixtures compare normalized outputs and input hashes with stock Lake builds, test compressed-cache restoration after deleting outputs, and check invalidation after source/options change. Actual samples `BuildAid.D1` and `Lemmata.CofiniteContinuousBounds.LeOfCofinite` produced byte-identical normalized oleans and C. Diagnostic-path differences are handled explicitly by attestation.

## Public cache reads

The public cache uses the direct R2 custom domain `https://rh-cache.taucetiproject.org`, backed by a dedicated `riemann-hypothesis-cache` bucket in the TauCeti Cloudflare account. Its service configuration is committed in `lakefile.toml`.

```bash
lake exe cache get
lake build --no-build
```

The project's `cache` executable delegates to Mathlib's qualified `mathlib/cache` executable, then downloads the root package with stock Lake and bulk-restores the verified archives. It internally selects the lakefile's service, uses a temporary curl configuration for 500 parallel transfers, and raises only its child process file-descriptor limit for Mathlib's unpacker. No user configuration or upload credential is needed. Bare `lake cache get` is stock Lake's separate built-in command and does not select this root-package service automatically in Lean 4.33.1.

`ci-cache-get.py` first looks for a successful public CI receipt matching the current clean Git source tree and the actual lakefile, dependency-manifest and toolchain bytes. It checks the input-fingerprint index, then a bounded set of equivalent ancestors, so documentation-only revisions can reuse a cache. A matching receipt selects immutable, SHA256-addressed map and module-manifest objects; a mutable PR revision map is never substituted. Stock Lake fetches the selected map's archives, and the existing path and per-archive SHA256 checks run before bulk restoration. Missing or nonmatching successful CI results select the original published-cache fallback; corrupt matching metadata or archives stop with an error.

These caches include outputs from **untrusted pull requests and volunteer machines**. The metadata and digest checks establish which bytes were published for which inputs; they do not verify proofs. An independent fresh build is needed when you need to trust the result. This CI cache path performs builds and cache restoration, without export or Comparator checks.

The full anonymous cold native download passed with all **175,187 archives / 4,938,217,979 bytes** in 4 minutes 47 seconds. Stock Lake spent approximately three minutes processing the index before transfers began. The default-concurrency control also ran without errors before the faster complete test superseded it.

The bulk restore checks the pinned source/configuration and every completed archive's SHA256, then calls stock `leantar` once with 24 workers. Actual HTTPS-manifest download, archive checks and restoration passed in 91 seconds; the subsequent full stock no-build/rehash check passed in 44 seconds. Its small fixture is `python3 scripts/cache-bootstrap/test_restore.py`.

For independent verification or fetching Mathlib alone, use `lake exe mathlib/cache get`, which bypasses this project's combined entry point.

## Publish a completed cache

The bootstrap is pinned to the original submission. Publish its validated staging directory from a separate host holding the upload credential:

```bash
python3 scripts/publish-lake-cache.py .lake/cache-staging \
  --rev e50d09817ad81469f737e8f637561e6ccf86c670 --check-only
python3 scripts/publish-lake-cache.py .lake/cache-staging \
  --rev e50d09817ad81469f737e8f637561e6ccf86c670
```

The publisher reads a mode-0600 account R2 token from `~/.riemann-hypothesis-tauceti-r2-token`, scoped to the dedicated bucket in the TauCeti account, and verifies the revision map through the anonymous endpoint. Never copy this credential to a proof-building machine. It rejects incomplete mappings, unexpected files, and links before upload. For a progressive upload, use `sync-cache-artifacts.py DIRECTORY --watch`; finalize with `publish-lake-cache.py DIRECTORY --rev REV --map-only-after-sync`, which checks every remote artifact's presence and size before publishing the map.

The original published olean archive and Lake-extras mirrors remain in the separate Riemann Hypothesis Cloudflare account. Production native-cache downloads use the custom domain above; the `r2.dev` development URL throttles a full 175,187-artifact download.

For future source revisions, successful community CI publishes a receipt, an immutable complete map and a matching module manifest under `ci/`. `lake exe cache get` consumes these through the matching-input lookup above. Failed CI builds can supply incremental producer caches, but the public client only restores a complete successful receipt. The original archive bootstrap remains pinned and deliberately rejects changed sources; its guard is not relaxed for dynamic CI restoration. Manual publication from a completed stock Lake build remains available through `lake cache stage` and the original publisher, including `--platform x86_64-unknown-linux-gnu` for clients predating the portable-cache setting.
