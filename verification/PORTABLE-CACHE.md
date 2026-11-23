# Reusing an existing Lean 4.36 build

Keep the exact completed source checkout, `.lake/build`, and `.lake/packages`; do not clean them. Record the original commit, `HEAD:src`, and configuration hashes before applying infrastructure changes. The native cache is produced from the final committed checkout, while this original identity remains a separate audit record.

For the immutable `Vilin97/riemann-hypothesis` snapshot `0092a8320a85932ea5a71baa0c093880a7f2a784`, the prepared metadata patch preserves every proof source, compiler option and default target. It adds portable-cache configuration and changes Mathlib's tag spelling to its already-locked commit. The dependency manifest changes only `mathlib.inputRev`; all dependency commits remain identical. This fork has no `BuildAid` source directory, so the patch does not add a `BuildAid` target.

For publication as the upstream cache, the maintainer supplies the **exact immutable merge-candidate commit**, with any infrastructure conflicts already resolved. Check it out while retaining `.lake/build` and `.lake/packages`. This may add main's `BuildAid` helpers; unchanged proofs retain their input hashes, while genuinely new or changed modules build normally. Preserve the author's original commit/source tree in the separate origin audit; never relabel a fork cache header as the merged source.

```bash
# MERGE_COMMIT is the full maintainer-supplied immutable SHA.
git fetch upstream "$MERGE_COMMIT"
git checkout --detach "$MERGE_COMMIT"
git status --short -- src lakefile.toml lake-manifest.json lean-toolchain
```

Use the supplied trusted helper scripts and fresh output paths:

```bash
python3 "$HELPERS/run-complete-build.py" \
  --release leanprover/lean4:v4.36.0 --project "$PROJECT" \
  --build-map "$PRODUCER/outputs.jsonl" --build-log "$PRODUCER/full-build.log" \
  --receipt "$PRODUCER/build-receipt.json" --jobs 8

python3 "$HELPERS/stage-completed-build.py" \
  --release leanprover/lean4:v4.36.0 --project "$PROJECT" \
  --build-map "$PRODUCER/outputs.jsonl" --build-log "$PRODUCER/full-build.log" \
  --build-receipt "$PRODUCER/build-receipt.json" \
  --output "$PRODUCER/native" --metadata "$PRODUCER/metadata"
```

The first command performs the complete stock default-target check and packs LTARs; unchanged proofs reuse their existing traces and artifacts. It binds the final source/configuration identity, command, log and map in a receipt. The second command performs no proof compilation, verifies native content hashes and SHA256, and stages the compressed cache. Add `--cache-dir /path/to/completed/native/cache` if cache hits have no local IR-directory LTAR alias. Transfer `native/` and `metadata/` to the maintainer's publishing host; no Cloudflare credential is needed on the producer.

Tiny stock 4.36 fixtures verify unchanged input hashes, artifact bytes and mtimes across these infrastructure edits, for both legacy sources and the new module system. Stock LTAR staging/restoration also preserves server/private OLean and IR parts, followed by a successful no-build check. The producer's full default-target check remains the authority for the actual project.

## Integration review

- The producer receipt names the exact final source/configuration/toolchain and complete default-target scope; its log/map hashes match the staged data. The author's original source identity remains separate.
- The operator verifies compressed artifact hashes and the receipt-bound module index, then publishes to the matching toolchain namespace. Previous-release cache data remains available.
- A fresh client downloads the published map/artifacts, restores all module parts, and passes `lake --no-build --rehash build` for that exact candidate. The retained `Challenge` module is checked as required by the migration; no Comparator/export run is implied.
- Only after that successful cold restore and final no-build check are the new revision/map/manifest pins activated in `cache-baselines.json`. Historical running jobs retain their own toolchain descriptor, and automatic full builds use heavy runners.
