#!/usr/bin/env bash
# Run a command in a Lake work tree under bwrap, for building code that came from a pull request.
#
#   scripts/ci/sandbox.sh <work tree> [<read-only dir>...] -- <command> [<argument>...]
#
# Inside, there is no network, no other process to see, no home directory and no /tmp or /run
# from outside; the file system is read-only except <work tree>/.lake/build and a private /tmp.
# The environment is emptied, so no token is passed in. The command runs in <work tree>. The
# directories listed before `--` (the checkout that holds the checker, say) stay readable.
#
# The tree must have been built once outside, from code that is trusted (main's): Lake writes
# the compiled lakefiles of the dependencies to .lake/config and file hashes next to the
# dependencies' sources on the first build, and none of that is writable here.
#
# What the command prints is whatever the code it builds wants printed: treat it as data.
set -euo pipefail
work=$(realpath "${1:?usage: sandbox.sh <work tree> [<read-only dir>...] -- <command>...}"); shift
readable=()
while [ $# -gt 0 ] && [ "$1" != -- ]; do readable+=("$(realpath "$1")"); shift; done
[ "${1:-}" = -- ] && shift
[ $# -gt 0 ] || { echo "sandbox.sh: no command" >&2; exit 2; }
command -v bwrap >/dev/null || { echo "sandbox.sh: bwrap (bubblewrap) is required" >&2; exit 2; }
elan=$(realpath "${ELAN_HOME:-$HOME/.elan}")
[ -x "$elan/bin/lake" ] || { echo "sandbox.sh: no elan at $elan" >&2; exit 2; }
mkdir -p "$work/.lake/build"
# .lake/packages may be a link to a shared copy (the local worktrees do this).
packages=$(realpath "$work/.lake/packages")

args=(--unshare-all --die-with-parent --new-session --clearenv
  --ro-bind / / --dev /dev --proc /proc
  --tmpfs /tmp --tmpfs /run --tmpfs /home --tmpfs /root --tmpfs /mnt --tmpfs /var/tmp
  --ro-bind "$elan" "$elan" --ro-bind "$packages" "$packages" --ro-bind "$work" "$work")
for dir in "${readable[@]}"; do args+=(--ro-bind "$dir" "$dir"); done
args+=(--bind "$work/.lake/build" "$work/.lake/build" --chdir "$work"
  --setenv PATH "$elan/bin:/usr/local/bin:/usr/bin:/bin" --setenv HOME /tmp --setenv ELAN_HOME "$elan"
  --setenv LANG C.UTF-8 --setenv LC_ALL C.UTF-8)
exec bwrap "${args[@]}" "$@"
