#!/usr/bin/env bash
set -euo pipefail

if [[ "$#" != 1 || "$1" != get ]]; then
  echo 'Usage: lake exe cache get' >&2
  exit 2
fi

RH_CACHE_ROOT="$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$RH_CACHE_ROOT"

# scripts/ci-cache-get.py needs Python 3.11 for tomllib. Say so before downloading anything.
if ! python3 -c 'import sys; sys.exit(sys.version_info < (3, 11))'; then
  RH_CACHE_PYTHON="$(command -v python3 >/dev/null && python3 --version 2>&1 || echo none)"
  echo "lake exe cache get needs Python 3.11 or newer as python3; found: $RH_CACHE_PYTHON" >&2
  exit 1
fi

# Mathlib's parallel unpacker can exceed the usual 1024-file soft limit.
RH_CACHE_FD_HARD="$(ulimit -Hn)"
if [[ "$RH_CACHE_FD_HARD" == unlimited || "$RH_CACHE_FD_HARD" -gt 65536 ]]; then
  ulimit -Sn 65536
else
  ulimit -Sn "$RH_CACHE_FD_HARD"
fi

# Qualify Mathlib's executable because this package also supplies a cache target.
printf 'Fetching Mathlib cache...\n'
MATHLIB_CACHE_GET_URL="${MATHLIB_CACHE_GET_URL:-https://cache.mathlib.org/mathlib4}" \
  lake exe mathlib/cache get

# Cache URLs live in lakefile.toml; users need no separate configuration file.
export LAKE_CACHE_DIR="$RH_CACHE_ROOT/.lake/cache"
source scripts/cache-env.sh
RH_CACHE_CURL_HOME="$(mktemp -d "$PWD/.lake/cache-curl.XXXXXX")"
trap 'rm -rf -- "$RH_CACHE_CURL_HOME"' EXIT
printf 'parallel-max = 500\n' > "$RH_CACHE_CURL_HOME/.curlrc"
if CURL_HOME="$RH_CACHE_CURL_HOME" python3 scripts/ci-cache-get.py; then
  exit 0
else
  RH_CI_CACHE_STATUS=$?
  if [[ "$RH_CI_CACHE_STATUS" != 3 ]]; then
    exit "$RH_CI_CACHE_STATUS"
  fi
fi
if [[ "$(<lean-toolchain)" != 'leanprover/lean4:v4.33.1' ]]; then
  echo 'No validated cache matches these build inputs; use lake build.' >&2
  exit 3
fi
printf 'Fetching project cache (4.94 GB; processing the index takes a few minutes)...\n'
CURL_HOME="$RH_CACHE_CURL_HOME" lake -q cache get --repo leanprover-community/riemann-hypothesis \
  --rev e50d09817ad81469f737e8f637561e6ccf86c670
python3 scripts/restore-cache.py
