#!/usr/bin/env bash
# Tests for the scripts behind the PR check and Auto-merge workflows.
#
#   scripts/ci/selftest.sh             the unit tests and syntax checks; needs only python3 and bash
#   scripts/ci/selftest.sh --replay    also run scripts/ci/verdict.py on pull requests that were
#                                      merged by hand, and compare with what was decided then
#
# --replay needs lake, bwrap, this checkout's dependencies (`lake exe cache get`) and the full
# history; it builds old commits of main in scratch worktrees, which takes a while.
set -euo pipefail
cd "$(dirname "$0")/../.."
root=$PWD

for script in scripts/*.sh scripts/ci/*.sh; do bash -n "$script"; done
python3 -m py_compile scripts/ci/*.py
python3 -m unittest discover -s scripts/ci -p 'test_*.py'
[ "${1:-}" = --replay ] || exit 0

# number, the commit of main it was merged onto, its head commit, and the verdict expected
replays="
1175 37b8b5e05a7570ff4d3fc9832abc3d3a565e91e8 dd6a45bfdc25217602aa861378ff4e2d4ec8262c merge
1182 a7454ad43918164a17ca2165aeb7da7f6871b2cc e46aea289c3a9b71eb85f7c596c3dfa0da1ce2fe read
"
scratch=$(mktemp -d "${RUNNER_TEMP:-${TMPDIR:-/tmp}}/selftest.XXXXXX")
# shellcheck disable=SC2329  # called by the trap
cleanup() {
  git worktree list --porcelain | sed -n "s#^worktree \($scratch/.*\)#\1#p" | xargs -r -n1 git worktree remove --force
  git for-each-ref --format='%(refname)' refs/selftest | xargs -r -n1 git update-ref -d
  rm -rf "$scratch"
}
trap cleanup EXIT
status=0; seed=
while read -r pr base head expected; do
  [ -n "$pr" ] || continue
  git fetch -q --no-tags origin "+refs/pull/$pr/head:refs/selftest/pr-$pr"
  [ "$(git rev-parse "refs/selftest/pr-$pr")" = "$head" ]
  work=$scratch/pr-$pr
  git worktree add -q --detach "$work" "$base"
  mkdir -p "$work/.lake"
  ln -s "$(realpath .lake/packages)" "$work/.lake/packages"
  [ -z "$seed" ] || cp -a "$seed" "$work/.lake/build"   # start from the previous build
  python3 scripts/ci/verdict.py --work "$work" --base "$base" --head "$head" --pr "$pr" --out "$scratch/out-$pr" || true
  got=$(python3 -c 'import json, sys; print(json.load(open(sys.argv[1]))["verdict"])' "$scratch/out-$pr/verdict.json")
  if [ "$got" = "$expected" ]; then echo "replay #$pr: $got, as expected"
  else echo "replay #$pr: got $got, expected $expected"; cat "$scratch/out-$pr/summary.md"; status=1; fi
  seed=$work/.lake/build
done <<<"$replays"
cd "$root"
exit $status
