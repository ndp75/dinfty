#!/usr/bin/env bash
# Acceptance check for the Dinfty release. Run from the repository root.
# Builds Dinfty.Verify and checks that every `#print axioms` report is a
# subset of Lean's three standard axioms. Exits non-zero on any failure.
set -o pipefail
fail=0
expected=195

lake build Dinfty.Verify 2>&1 | tee build.log

grep -q "Build completed successfully" build.log \
  || { echo "FAIL: build did not complete"; fail=1; }

for pat in "^error:" "declaration uses 'sorry'"; do
  n=$(grep -c "$pat" build.log)
  [ "$n" -eq 0 ] || { echo "FAIL: $n occurrences of '$pat'"; fail=1; }
done

# One axiom result per line. Join wrapped lines first.
axioms=$(tr '\n' ' ' < build.log \
         | grep -o -e "depends on axioms: \[[^]]*\]" -e "does not depend on any axioms")

total=$(printf '%s\n' "$axioms" | grep -c .)
[ "$total" -eq "$expected" ] \
  || { echo "FAIL: $total axiom results, expected $expected"; fail=1; }

bad=$(printf '%s\n' "$axioms" | grep -e sorryAx -e "Lean.ofReduceBool")
[ -z "$bad" ] || { echo "FAIL: sorry or native_decide reached the kernel:"; echo "$bad"; fail=1; }

nonstd=$(printf '%s\n' "$axioms" | grep -v \
  -e "^depends on axioms: \[propext, Classical.choice, Quot.sound\]$" \
  -e "^depends on axioms: \[propext, Quot.sound\]$" \
  -e "^depends on axioms: \[propext\]$" \
  -e "^does not depend on any axioms$" | sort -u)
[ -z "$nonstd" ] || { echo "FAIL: non-standard axioms:"; echo "$nonstd"; fail=1; }

echo
echo "Axiom report distribution:"
printf '%s\n' "$axioms" | sort | uniq -c

[ "$fail" -eq 0 ] && echo "PASS: $total axiom results, all standard, no sorry."
exit $fail
