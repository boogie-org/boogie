#!/usr/bin/env bash
# Run every test program under -infer:j and fail if any aborts.
#
# Abstract interpretation is off by default in Boogie and unconditionally on in Dafny, so the flag's own
# corpus coverage is thin: 21 of the test files pass -infer: on their RUN line. That is how a null-Type
# dereference in ThresholdFinder went unnoticed while crashing 60 of them.
#
# This asserts only that nothing aborts. It deliberately does not compare expectations: with inference
# forced on, output legitimately differs for many files, and a check that diffed it would be silenced
# within a week.
#
# Run by hand, not from CI: it is serial, and takes about five times as long as the whole lit suite.
# Parallelising it would close most of that gap if it is ever worth gating on.
set -u
boogie=${1:?usage: infer-crash-sweep.sh <path to BoogieDriver.dll>}
# Absolute, because of the cd below: a relative path would leave dotnet unable to find the assembly, and
# its complaint about that is not an abort, so every program would pass.
boogie=$(cd "$(dirname "$boogie")" && pwd)/$(basename "$boogie")
test -f "$boogie" || { echo "not a file: $boogie" >&2; exit 1; }
root=$(cd "$(dirname "$0")" && pwd)
# Some RUN lines write files next to the cwd (a relative /proverLog:, say), so run from a scratch
# directory and leave the tree clean.
scratch=$(mktemp -d)
trap 'rm -rf "$scratch"' EXIT
cd "$scratch"

crashed=0
total=0
for f in $(find "$root" -name '*.bpl' | sort); do
  run=$(grep -m1 '^// RUN:' "$f" 2>/dev/null | sed 's|^// RUN: ||')
  opts=$(echo "$run" | sed 's|%parallel-boogie||; s|%boogie||; s|"%s".*||; s|%diff.*||')
  case "$opts" in *%*) opts="";; esac
  # Skip a test that breaks the solver on purpose: it cannot distinguish a crash from its own subject.
  case "$run" in *PROVER_PATH*) continue;; esac
  total=$((total + 1))
  out=$(dotnet "$boogie" -useBaseNameForFileName -timeLimit:20 -processTimeLimit:60 \
          $opts -infer:j "$f" 2>&1)
  if echo "$out" | grep -q 'Unhandled exception\|Process terminated'; then
    crashed=$((crashed + 1))
    echo "CRASH under -infer:j: ${f#"$root"/}"
    echo "$out" | grep -m3 -E 'Exception|   at ' | sed 's/^/    /'
  fi
done
echo "-infer:j crash sweep: $total programs, $crashed aborted"
test "$crashed" -eq 0
