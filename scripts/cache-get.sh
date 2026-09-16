#!/usr/bin/env bash
#
# Fetch the mathlib cache for this project.
#
# Plain `lake exe cache get` does not work here.  Our mathlib is a fork branch
# (riccardobrasca/mathlib4, `less_choice`), so every artifact lives in the
# `forks` container, which is namespaced by commit SHA ("scope").  When `cache`
# is run from a downstream project it takes that SHA from `git rev-parse HEAD`
# in the current directory -- i.e. from *this* repository, not from the mathlib
# checkout -- and probes a namespace that was never written.  The set of hashes
# it asks for is correct (those are computed from the mathlib checkout); only
# the namespace is wrong.  Passing the mathlib checkout's HEAD as `--scope`
# fixes it.
#
# Usage:
#   scripts/cache-get.sh                 # same as `lake exe cache get`
#   scripts/cache-get.sh get!            # force re-download
#   scripts/cache-get.sh SDG/Basic/D.lean   # only these files and their imports

set -euo pipefail

root=$(git rev-parse --show-toplevel)
cd "$root"

mathlib=.lake/packages/mathlib
if [ ! -d "$mathlib/.git" ]; then
  echo "error: no mathlib checkout at $mathlib -- run 'lake update' first." >&2
  exit 1
fi

# The cache keys are computed from the files in the checkout, so the checked-out
# commit is the authoritative scope; the manifest is only a fallback.
scope=$(git -C "$mathlib" rev-parse HEAD)

pinned=$(python3 -c '
import json, sys
for p in json.load(open("lake-manifest.json"))["packages"]:
    if p.get("name") == "mathlib":
        print(p.get("rev", ""))
        break
' 2>/dev/null || true)
if [ -n "$pinned" ] && [ "$pinned" != "$scope" ]; then
  echo "warning: mathlib checkout ($scope) differs from lake-manifest.json ($pinned)." >&2
  echo "         Using the checkout.  Run 'lake update' if that is not what you want." >&2
fi

# Accept an explicit subcommand as the first argument; otherwise default to `get`
# and pass everything through as file targets.
cmd=get
case "${1-}" in
  get|get!|get-|lookup) cmd=$1; shift ;;
esac

echo "mathlib cache scope: $scope"
exec lake exe cache "$cmd" --scope="$scope" "$@"
