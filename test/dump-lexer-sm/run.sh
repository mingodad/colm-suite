#!/bin/sh
#
# Tests for --dump-lexer-sm, in particular that it works with --syntax-only
# (where no code is generated). The reduced lexer machine is built during
# analysis, so the dump must not require the full codegen path.
#
#   run.sh            run the checks
#
# Uses the same COLM discovery as test/grammar-diagnostics/run.sh.

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

if [ ! -x "$COLM" ]; then
	echo "dump-lexer-sm: no colm at $COLM (build it, or set COLM)" >&2
	exit 2
fi

tmp=$(mktemp -d)
trap 'rm -rf "$tmp"; rm -f "$here/cases/calc.lex-sm.txt"' EXIT

pass=0
fail=0
die()
{
	echo "dump-lexer-sm: FAIL: $*" >&2
	fail=$((fail + 1))
}

# 1. --syntax-only with an explicit dump file produces a non-empty machine.
( cd "$here/cases" && "$COLM" --syntax-only --dump-lexer-sm="$tmp/syn.txt" calc.lm ) \
	>/dev/null 2>&1 || die "syntax-only compile failed"
if [ -s "$tmp/syn.txt" ] && grep -q "Reduced lexer FSM" "$tmp/syn.txt"; then
	pass=$((pass + 1))
else
	die "syntax-only did not produce a dump"
fi

# 2. The syntax-only dump is byte-identical to the full-compile dump.
( cd "$here/cases" && "$COLM" -c --dump-lexer-sm="$tmp/full.txt" -o "$tmp/calc.c" calc.lm ) \
	>/dev/null 2>&1 || die "full compile failed"
if diff -q "$tmp/syn.txt" "$tmp/full.txt" >/dev/null; then
	pass=$((pass + 1))
else
	die "syntax-only and full-compile dumps differ"
fi

# 3. Without the flag, --syntax-only writes nothing.
rm -f "$here/cases/calc.lex-sm.txt"
( cd "$here/cases" && "$COLM" --syntax-only calc.lm ) >/dev/null 2>&1
if [ ! -e "$here/cases/calc.lex-sm.txt" ]; then
	pass=$((pass + 1))
else
	die "dump written without --dump-lexer-sm"
fi

# 4. Without an explicit file, --syntax-only uses <input-stem>.lex-sm.txt.
( cd "$here/cases" && "$COLM" --syntax-only --dump-lexer-sm calc.lm ) >/dev/null 2>&1
if [ -s "$here/cases/calc.lex-sm.txt" ]; then
	pass=$((pass + 1))
else
	die "default-named syntax-only dump missing"
fi

if [ "$fail" != 0 ]; then
	echo "dump-lexer-sm: $fail failing, $pass passing"
	exit 1
fi

echo "dump-lexer-sm: $pass checks passed"
