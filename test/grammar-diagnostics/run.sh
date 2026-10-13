#!/bin/sh
#
# Tests for the always-on grammar diagnostics (unreachable / unproductive /
# duplicate rules).
#
#   run.sh            check stderr against expected/
#   run.sh --update   rewrite expected/ from the current stderr
#
# Each case is run with --syntax-only so no C is generated; the diagnostics are
# written to stderr. The warnings are followed by location suffixes, so the
# comparison is done on lines with the location stripped, plus a couple of
# semantic assertions. This keeps the tests independent of the exact line
# numbers in the cases while still catching a missing or changed diagnostic.

set -e

here=$(cd "$(dirname "$0")" && pwd)
repo=$(cd "$here/../.." && pwd)
if [ -z "$COLM" ]; then
	for cand in "$repo/build/bin/colm" "$repo/src/colm/colm"; do
		if [ -x "$cand" ]; then
			COLM=$cand
			break
		fi
	done
fi
if [ -z "$COLM" ]; then
	COLM=$(command -v colm 2>/dev/null || true)
fi
export CPATH=${CPATH:-"$repo/build/src/colm/include"}
export LIBRARY_PATH=${LIBRARY_PATH:-"$repo/build/src/colm"}

update=0
[ "$1" = "--update" ] && update=1

if [ ! -x "$COLM" ]; then
	echo "grammar-diagnostics: no colm at $COLM (build it, or set COLM)" >&2
	exit 2
fi

tmp=$(mktemp -d)
trap 'rm -rf "$tmp"' EXIT
mkdir -p "$here/expected"

fail=0
pass=0

note()
{
	echo "grammar-diagnostics: $*"
}

die()
{
	echo "grammar-diagnostics: FAIL: $*" >&2
	fail=$((fail + 1))
}

# Run a case and keep only the diagnostic body, with locations removed so the
# golden does not depend on line numbers.
run_case()
{
	name=$1
	dest="$tmp/$name.out"
	( cd "$here/cases" && "$COLM" --syntax-only "$name.lm" ) >/dev/null 2>"$tmp/$name.raw"
	sed -E 's/^warning: [^:]+:[0-9]+:[0-9]+: /warning: /' "$tmp/$name.raw" >"$dest"
	echo "$dest"
}

check_golden()
{
	name=$1
	actual=$2
	expected="$here/expected/$name.out"

	if [ "$update" = 1 ]; then
		cp "$actual" "$expected"
		return
	fi

	if [ ! -f "$expected" ]; then
		die "$name has no golden file (run: run.sh --update)"
		return
	fi

	if diff -u "$expected" "$actual" >"$tmp/$name.diff"; then
		pass=$((pass + 1))
	else
		die "$name differs:"
		cat "$tmp/$name.diff" >&2
	fi
}

assert_contains()
{
	name=$1
	file=$2
	text=$3
	if grep -qF "$text" "$file"; then
		pass=$((pass + 1))
	else
		die "$name: expected to contain: $text"
	fi
}

assert_absent()
{
	name=$1
	file=$2
	if grep -qE 'is unreachable|cannot derive|duplicate production|is subsumed by|EBNF .' "$file"; then
		die "$name: expected no grammar diagnostics"
	else
		pass=$((pass + 1))
	fi
}

assert_not_contains()
{
	name=$1
	file=$2
	text=$3
	if grep -qF "$text" "$file"; then
		die "$name: expected NOT to contain: $text"
	else
		pass=$((pass + 1))
	fi
}

cases="clean unreachable unproductive duplicate subsumed ebnf library"
for name in $cases; do
	out=$(run_case "$name")
	check_golden "$name" "$out"
done

assert_contains "unreachable" "$tmp/unreachable.out" "non-terminal 'unused' is unreachable"
assert_contains "unproductive" "$tmp/unproductive.out" "non-terminal 'loop' cannot derive any terminal string"
assert_contains "duplicate" "$tmp/duplicate.out" "duplicate production for 'exp'"
assert_contains "duplicate" "$tmp/duplicate.out" "grammar: 0 unreachable, 0 unproductive, 1 duplicate"
assert_contains "subsumed" "$tmp/subsumed.out" "alternative 'a -> b' is subsumed by 'a -> c'"
assert_contains "ebnf" "$tmp/ebnf.out" "EBNF '?' on nullable 'nul'"
assert_contains "ebnf" "$tmp/ebnf.out" "EBNF '*' on nullable 'nul'"
assert_contains "ebnf" "$tmp/ebnf.out" "EBNF '+' on nullable 'nul'"
assert_contains "ebnf" "$tmp/ebnf.out" "3 ebnf-redundant"
assert_not_contains "ebnf" "$tmp/ebnf.out" "on nullable 'solid'"
assert_absent "clean" "$tmp/clean.out"
assert_absent "library" "$tmp/library.out"

# --no-warn-grammar disables the pass entirely.
( cd "$here/cases" && "$COLM" --no-warn-grammar --syntax-only unreachable.lm ) \
	>/dev/null 2>"$tmp/nowarn.out"
assert_absent "no-warn-grammar" "$tmp/nowarn.out"

# An undeclared backtick literal used as a token (pattern / production RHS /
# cons / precedence) is a plain compilation error; it must not be reported as
# an "unknown type ... in typeof expression" (L1).
( cd "$here/cases" && "$COLM" --syntax-only errliteral.lm ) \
	>/dev/null 2>"$tmp/errliteral.raw" || true
assert_contains "errliteral" "$tmp/errliteral.raw" \
	"unknown token or literal \`*"
assert_contains "errliteral" "$tmp/errliteral.raw" \
	"no matching literal, token or rl declaration in scope"
assert_not_contains "errliteral" "$tmp/errliteral.raw" "in typeof expression"

if [ "$update" = 1 ]; then
	note "updated golden files"
	exit 0
fi

if [ "$fail" != 0 ]; then
	note "$fail failing, $pass passing"
	exit 1
fi

note "$pass checks passed"
