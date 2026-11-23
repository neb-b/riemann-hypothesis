#!/usr/bin/env bash
# Optional environment setup; `lake exe cache get` does this itself.
if [[ "${BASH_SOURCE[0]}" == "$0" ]]; then
  echo 'Use: source scripts/cache-env.sh' >&2
  exit 1
fi

# zsh has no BASH_SOURCE; there, $0 is the path of the sourced file.
RH_CACHE_ROOT="$(cd -- "$(dirname -- "${BASH_SOURCE[0]:-$0}")/.." && pwd)"
export LAKE_CONFIG="$RH_CACHE_ROOT/lakefile.toml"
export LAKE_CACHE_DIR="${LAKE_CACHE_DIR:-$RH_CACHE_ROOT/.lake/cache}"
export LAKE_ARTIFACT_CACHE=true
export LAKE_RESTORE_ARTIFACTS=true
unset RH_CACHE_ROOT
