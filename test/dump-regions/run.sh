#!/bin/sh
#
# Tests for the region diagnostics:
#
#   --dump-regions   (compile time) print each token region with its
#                    declaration site and tokens.
#
#   --dump-lexer     (run time) a generated program always parses this
#                    option and dumps how it tokenizes its own input.
#                    Without the option the program runs normally.
#
#   --dump-parse     (run time) a generated program also parses this
#                    option and traces region switches, scanner region
#                    retries and the deepest parse failure. Off by default.
#
#   --dump-cst       (run time) a generated program also parses this
#                    option and dumps the concrete syntax tree it built.
#                    --dump-cst=TYPES dumps only the listed node types.
#                    Off by default.
#
#   -h, -H, -?, --help  (run time) print the generated program's options.
#
# Uses the same COLM discovery as test/dump-lexer-sm/run.sh.

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
	echo "dump-regions: no colm at $COLM (build it, or set COLM)" >&2
	exit 2
fi

tmp=$(mktemp -d)
trap 'rm -rf "$tmp"' EXIT

pass=0
fail=0
die()
{
	echo "dump-regions: FAIL: $*" >&2
	fail=$((fail + 1))
}

# 1. --dump-regions names the region and lists its tokens.
if ( cd "$here/cases" && "$COLM" --dump-regions basic.lm ) \
		>"$tmp/regions.txt" 2>&1; then
	if grep -q "regions:" "$tmp/regions.txt" &&
			grep -q "basic.lm:" "$tmp/regions.txt" &&
			grep -q "Number" "$tmp/regions.txt" &&
			grep -q "Plus" "$tmp/regions.txt"; then
		pass=$((pass + 1))
	else
		die "--dump-regions output missing regions or tokens"
	fi
else
	die "--dump-regions failed to run"
fi

# 2. Build a program. It must build without any dump flag.
if ( cd "$here/cases" && "$COLM" -o "$tmp/basic" basic.lm ) \
		>/dev/null 2>&1; then
	pass=$((pass + 1))
else
	die "compiling basic.lm failed"
fi

# 3. Without --dump-lexer, the program runs normally and is silent.
printf '1+2\n' | "$tmp/basic" >"$tmp/normal.out" 2>"$tmp/normal.err" || true
if grep -q "ok" "$tmp/normal.out" && [ ! -s "$tmp/normal.err" ]; then
	pass=$((pass + 1))
else
	die "normal run printed a trace or did not parse"
fi

# 4. With --dump-lexer, the program dumps its input lexing.
printf '1+2\n' | "$tmp/basic" --dump-lexer >/dev/null 2>"$tmp/dump.err" || true
if grep -q "Number" "$tmp/dump.err" &&
		grep -q "basic.lm:" "$tmp/dump.err"; then
	pass=$((pass + 1))
else
	die "--dump-lexer did not dump tokens"
fi

# 5. The dump option is not passed through to the program: removing it
#    leaves the same normal output.
printf '1+2\n' | "$tmp/basic" --dump-lexer >"$tmp/dump.out" 2>/dev/null || true
if grep -q "ok" "$tmp/dump.out"; then
	pass=$((pass + 1))
else
	die "program did not run with --dump-lexer"
fi

# 6. Build the two-region grammar.
if ( cd "$here/cases" && "$COLM" -o "$tmp/two" two.lm ) \
		>/dev/null 2>&1; then
	pass=$((pass + 1))
else
	die "compiling two.lm failed"
fi

# 7. --dump-parse traces region switches, naming both regions, and the
#    program still parses normally.
printf 'alpha = beta\n' | "$tmp/two" --dump-parse \
		>"$tmp/parse.out" 2>"$tmp/parse.err" || true
if grep -q "parse: region .*two.lm:3 -> two.lm:9" "$tmp/parse.err" &&
		grep -q "parse: region .*two.lm:9 -> two.lm:3" "$tmp/parse.err" &&
		grep -q "ok" "$tmp/parse.out"; then
	pass=$((pass + 1))
else
	die "--dump-parse did not trace region switches"
fi

# 8. --dump-parse reports the deepest parse failure with its region,
#    while the program's own output is unchanged.
printf '1++2\n' | "$tmp/basic" --dump-parse \
		>"$tmp/fail.out" 2>"$tmp/fail.err" || true
if grep -q "parse: deepest failure at" "$tmp/fail.err" &&
		grep -q "in region basic.lm:" "$tmp/fail.err" &&
		grep -q "fail" "$tmp/fail.out"; then
	pass=$((pass + 1))
else
	die "--dump-parse did not report the parse failure"
fi

# 9. --dump-cst dumps the concrete syntax tree of the parsed input,
#    while the program still parses normally.
printf '1+2\n' | "$tmp/basic" --dump-cst \
		>"$tmp/cst.out" 2>"$tmp/cst.err" || true
if grep -q "Number: 1" "$tmp/cst.err" &&
		grep -q "Plus: +" "$tmp/cst.err" &&
		grep -q "ok" "$tmp/cst.out"; then
	pass=$((pass + 1))
else
	die "--dump-cst did not dump the CST"
fi

# 10. The dump option is not passed through to the program either.
printf '1+2\n' | "$tmp/basic" --dump-cst >"$tmp/cst.out" 2>/dev/null || true
if grep -q "ok" "$tmp/cst.out"; then
	pass=$((pass + 1))
else
	die "program did not run with --dump-cst"
fi

# 11. --dump-cst=TYPES keeps only the named node types, while the
#     program still parses normally. Token nodes are elided.
printf '1+2\n' | "$tmp/basic" --dump-cst=e \
		>"$tmp/cstf.out" 2>"$tmp/cstf.err" || true
if grep -q "^e$" "$tmp/cstf.err" &&
		! grep -q "Number" "$tmp/cstf.err" &&
		! grep -q "Plus" "$tmp/cstf.err" &&
		grep -q "ok" "$tmp/cstf.out"; then
	pass=$((pass + 1))
else
	die "--dump-cst=e did not filter to type e"
fi

# 12. -h prints the generated program's options and exits 0 without
#     running the program.
if "$tmp/basic" -h >"$tmp/help.out" 2>/dev/null; then
	if grep -q "usage:" "$tmp/help.out" &&
			grep -q -- "--dump-cst" "$tmp/help.out"; then
		pass=$((pass + 1))
	else
		die "-h did not list the options"
	fi
else
	die "-h did not exit 0"
fi

if [ "$fail" != 0 ]; then
	echo "dump-regions: $fail failing, $pass passing"
	exit 1
fi

echo "dump-regions: $pass checks passed"
