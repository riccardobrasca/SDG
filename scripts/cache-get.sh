#!/usr/bin/env bash
#
# Fetch the mathlib cache for this project.
#
# Plain `lake exe cache get` does not work here.  Our mathlib is a fork branch
# (riccardobrasca/mathlib4, `less_choice`) built with a custom Lean toolchain,
# which upstream mathlib CI no longer builds, so none of its artifacts are on
# cache.mathlib.org.  They are hosted on webusers.imj-prg.fr instead, and
# `cache` reads them from there through `MATHLIB_CACHE_GET_URL`.  That endpoint
# is flat (one file per hash, no per-commit namespace), so no `--scope` is
# passed: a scope would add a commit segment to every URL.  `--repo` pins the
# URL layout, which `cache` would otherwise infer from git remotes.
#
# Usage:
#   scripts/cache-get.sh                 # same as `lake exe cache get`
#   scripts/cache-get.sh get!            # force re-download
#   scripts/cache-get.sh SDG/Basic/D.lean   # only these files and their imports
#
# Set MATHLIB_CACHE_GET_URL to read from a different endpoint.

set -euo pipefail

root=$(git rev-parse --show-toplevel)
cd "$root"

mathlib=.lake/packages/mathlib
if [ ! -d "$mathlib/.git" ]; then
  echo "error: no mathlib checkout at $mathlib -- run 'lake update' first." >&2
  exit 1
fi

# The cache keys are computed from the files in the checkout, so a checkout
# that differs from the manifest fetches files for the wrong commit.
checkout=$(git -C "$mathlib" rev-parse HEAD)

pinned=$(python3 -c '
import json, sys
for p in json.load(open("lake-manifest.json"))["packages"]:
    if p.get("name") == "mathlib":
        print(p.get("rev", ""))
        break
' 2>/dev/null || true)
if [ -n "$pinned" ] && [ "$pinned" != "$checkout" ]; then
  echo "warning: mathlib checkout ($checkout) differs from lake-manifest.json ($pinned)." >&2
  echo "         Using the checkout.  Run 'lake update' if that is not what you want." >&2
fi

# Accept an explicit subcommand as the first argument; otherwise default to `get`
# and pass everything through as file targets.
cmd=get
case "${1-}" in
  get|get!|get-|lookup) cmd=$1; shift ;;
esac

export MATHLIB_CACHE_GET_URL=${MATHLIB_CACHE_GET_URL:-https://webusers.imj-prg.fr/~riccardo.brasca/mathlib-cache}
echo "mathlib $checkout, cache from $MATHLIB_CACHE_GET_URL"
exec lake exe cache "$cmd" --repo=riccardobrasca/mathlib4 "$@"
