#!/bin/sh
#
# Golden tests for colm's --pda-report output.
#
#   run.sh            check the report output against expected/
#   run.sh --update   rewrite expected/ from the current output
#
# Each case in cases/ is run with --syntax-only --pda-report=clusters and
# --pda-report=json, from inside cases/ so the [file:line] locations stay
# relative and portable. A handful of semantic assertions run on top of the
# byte-for-byte comparison, so a golden update cannot silently drop the one
# property that matters (the level-only tie staying visible).
#
# The big Colm grammar is checked too, by regenerating the artifacts under
# nontrivial/ when they are present.

set -e

here=$(cd "$(dirname "$0")" && pwd)
repo=$(cd "$here/../.." && pwd)
# Find a colm to test: explicit COLM, then cmake, then autotools, then PATH.
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
	echo "pda-report: no colm at $COLM (build it, or set COLM)" >&2
	exit 2
fi

tmp=$(mktemp -d)
trap 'rm -rf "$tmp"' EXIT
mkdir -p "$here/expected"

fail=0
pass=0

note()
{
	echo "pda-report: $*"
}

die()
{
	echo "pda-report: FAIL: $*" >&2
	fail=$((fail + 1))
}

actual_for()
{
	name=$1
	mode=$2
	dest="$tmp/$name.$mode"
	( cd "$here/cases" && "$COLM" --syntax-only --pda-report="$mode" "$name.lm" ) \
		>/dev/null 2>"$dest"
	echo "$dest"
}

check_golden()
{
	name=$1
	mode=$2
	actual=$3
	expected="$here/expected/$name.$mode"

	if [ "$update" = 1 ]; then
		cp "$actual" "$expected"
		return
	fi

	if [ ! -f "$expected" ]; then
		die "$name.$mode has no golden file (run: run.sh --update)"
		return
	fi

	if diff -u "$expected" "$actual" >"$tmp/$name.$mode.diff"; then
		pass=$((pass + 1))
	else
		die "$name.$mode differs:"
		cat "$tmp/$name.$mode.diff" >&2
	fi
}

# Semantic assertions, independent of the golden bytes.
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

assert_no_state()
{
	name=$1
	file=$2
	if grep -q '^state ' "$file"; then
		die "$name: expected no conflict states"
	else
		pass=$((pass + 1))
	fi
}

# JSON schema check: stable keys and types, no surprises.
check_json_schema()
{
	name=$1
	file=$2
	if ! command -v python3 >/dev/null 2>&1; then
		return
	fi
	python3 - "$file" <<'PY' || fail=$((fail + 1))
import json, sys
d = json.load(open(sys.argv[1]))
for k in ("rawShiftReduce", "rawReduceReduce",
          "remainingShiftReduce", "remainingReduceReduce"):
    assert isinstance(d[k], int), k
assert isinstance(d["conflicts"], list)
assert isinstance(d["shapes"], list)
for c in d["conflicts"]:
    assert isinstance(c["state"], int)
    assert c["kind"] in ("shift/reduce", "reduce/reduce")
    assert c["status"] in ("resolved", "nonassoc-error", "unresolved")
    assert "tie" in c or "resolvedBy" in c or c["status"] == "nonassoc-error"
    assert isinstance(c["actions"], list) and c["actions"]
    for a in c["actions"]:
        assert a["type"] in ("shift", "reduce", "shift-reduce")
        if a["type"] == "shift":
            assert isinstance(a["target"], int)
        else:
            assert isinstance(a["production"], str)
            assert isinstance(a["prodNum"], int)
    assert isinstance(c["tokens"], list)
for s in d["shapes"]:
    assert s["kind"] in ("shift/reduce", "reduce/reduce")
    assert isinstance(s["states"], list)
    assert isinstance(s["unresolved"], bool)
PY
	pass=$((pass + 1))
}

cases="clean assoc level tie nonassoc"
modes="clusters json"

for name in $cases; do
	for mode in $modes; do
		file=$(actual_for "$name" "$mode")
		check_golden "$name" "$mode" "$file"
		[ "$mode" = json ] && check_json_schema "$name" "$file"
	done
done

# The motivated regression: a level-only tie is a *remaining* conflict.
cl="$tmp/tie.clusters"
assert_contains "tie" "$cl" "UNRESOLVED level-only tie"
assert_contains "tie" "$cl" "tie"

assert_contains "level" "$tmp/level.clusters" "resolved by level"
assert_contains "assoc" "$tmp/assoc.clusters" "resolved by assoc"
assert_contains "nonassoc" "$tmp/nonassoc.clusters" "error nonassoc"
assert_no_state "clean" "$tmp/clean.clusters"

# --pda-report=conflicts lists only conflicting states, and must include the
# tie state from the clusters report (whose number is allocation-dependent).
tie_state=$(grep -o '^state [0-9]*' "$tmp/tie.clusters" | head -1 | awk '{print $2}')
cf=$(actual_for tie conflicts)
assert_contains "conflicts-only" "$cf" "state $tie_state"

# Big grammar: regenerate in place and diff (R6). Skipped if not present.
big="$repo/nontrivial"
if [ -f "$big/prog.lm" ] && [ -f "$big/conflict-index.txt" ]; then
	mkdir -p "$tmp/big"
	( cd "$big" && "$COLM" --syntax-only --pda-report=clusters prog.lm ) \
		>/dev/null 2>"$tmp/big/conflict-index.txt"
	( cd "$big" && "$COLM" --syntax-only --pda-report=json prog.lm ) \
		>/dev/null 2>"$tmp/big/conflicts.json"
	if [ "$update" = 1 ]; then
		cp "$tmp/big/conflict-index.txt" "$big/conflict-index.txt"
		cp "$tmp/big/conflicts.json" "$big/conflicts.json"
	else
		if diff -u "$big/conflict-index.txt" "$tmp/big/conflict-index.txt" \
				>"$tmp/big/index.diff"; then
			pass=$((pass + 1))
		else
			die "nontrivial/prog.lm conflict-index differs:"
			cat "$tmp/big/index.diff" >&2
		fi
		if diff -u "$big/conflicts.json" "$tmp/big/conflicts.json" \
				>"$tmp/big/json.diff"; then
			pass=$((pass + 1))
		else
			die "nontrivial/prog.lm conflicts.json differs:"
			cat "$tmp/big/json.diff" >&2
		fi
		check_json_schema "prog" "$tmp/big/conflicts.json"
	fi
fi

if [ "$update" = 1 ]; then
	note "updated golden files"
	exit 0
fi

if [ "$fail" != 0 ]; then
	note "$fail failing, $pass passing"
	exit 1
fi

note "$pass checks passed"
