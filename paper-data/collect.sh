#!/bin/sh
# Collect size and tactic-surface data for the CPP writeup.
#
# Nothing is modified. Every state is materialised into a temporary directory,
# either from a git object or by copying a working tree, and measured there.
# Run from anywhere; paths default to the sibling checkouts.
#
# States of InteractionTrees
#   A   itrees-old/InteractionTrees @ master (bd356ec)  upstream, built on paco
#   A'  InteractionTrees @ 68b3568                      the same upstream content,
#                                                       merged into our fork; a
#                                                       cross-check on A
#   B   InteractionTrees @ d34881b                      ported to enhanced
#                                                       coinduction, against
#                                                       rocq-coinduction 1.21
#   C   InteractionTrees working tree                   ported to enhanced
#                                                       coinduction, against the
#                                                       rewritten library
#
# States of the coinduction library
#   D   companion-and-tower @ 3dd5df7    "Bare pous library" = rocq-coinduction 1.21
#   D'  pous-coinduction working tree    pristine upstream; a cross-check on D
#   E   companion-and-tower working tree the rewritten library
set -e

HERE=$(cd "$(dirname "$0")" && pwd)
ROOT=${ROOT:-$(cd "$HERE/../.." && pwd)}
ITREES=${ITREES:-$ROOT/InteractionTrees}
PACO=${PACO:-$ROOT/itrees-old/InteractionTrees}
COIND=${COIND:-$ROOT/companion-and-tower}
POUS=${POUS:-$ROOT/pous-coinduction}

WORK=$(mktemp -d)
trap 'rm -rf "$WORK"' EXIT

materialise () { # name repo rev subdir
  name=$1; repo=$2; rev=$3; sub=$4
  mkdir -p "$WORK/$name"
  if [ "$rev" = "WORKTREE" ]; then
    ( cd "$repo" && tar cf - "$sub" 2>/dev/null ) | ( cd "$WORK/$name" && tar xf - )
  else
    git -C "$repo" archive "$rev" "$sub" | ( cd "$WORK/$name" && tar xf - )
  fi
}

# rocq wc summed over every .v file under $1 -> "spec proof comments files"
wc_tree () {
  find "$1" -name '*.v' -print0 2>/dev/null | xargs -0 rocq wc 2>/dev/null \
  | awk '$1 ~ /^[0-9]+$/ && $4 != "total" { s+=$1; p+=$2; c+=$3; n++ } END { printf "%d %d %d %d", s, p, c, n }'
}

tactic_defs () {
  grep -rhE '^[[:space:]]*(#\[[a-z]*\][[:space:]]*)?(Ltac|Tactic Notation)[[:space:]]' \
       --include='*.v' "$1" 2>/dev/null | wc -l | tr -d ' '
}

count_re () { grep -rhE "$2" --include='*.v' "$1" 2>/dev/null | wc -l | tr -d ' '; }

emit () { # label dir
  label=$1; dir=$2
  set -- $(wc_tree "$dir")
  spec=$1; proof=$2; comm=$3; files=$4
  printf '%s,%s,%s,%s,%s,%s,%s,%s,%s\n' \
    "$label" "$files" "$spec" "$proof" "$comm" "$((spec+proof))" \
    "$(tactic_defs "$dir")" \
    "$(count_re "$dir" '\bpaco[0-9]|\bgpaco[0-9]|\bpcofix|\bgcofix')" \
    "$(count_re "$dir" 'monotone[0-9]|_mono\b|_monotone\b')"
}

echo "# table 1: InteractionTrees, per tree, per state"
echo "state,files,spec,proof,comments,spec+proof,tactic_defs,paco_tokens,monotonicity_tokens"
for t in theories extra; do
  materialise "A-$t"  "$PACO"   WORKTREE "$t"
  materialise "Ap-$t" "$ITREES" 68b3568  "$t"
  materialise "B-$t"  "$ITREES" d34881b  "$t"
  materialise "C-$t"  "$ITREES" WORKTREE "$t"
  emit "$t/A-paco(itrees-old)"   "$WORK/A-$t/$t"
  emit "$t/A'-paco(68b3568)"     "$WORK/Ap-$t/$t"
  emit "$t/B-oldcoind(d34881b)"  "$WORK/B-$t/$t"
  emit "$t/C-newcoind(worktree)" "$WORK/C-$t/$t"
done

echo
echo "# table 2: the coinduction library"
echo "state,files,spec,proof,comments,spec+proof,tactic_defs,paco_tokens,monotonicity_tokens"
materialise D  "$COIND" 3dd5df7  theories
materialise Dp "$POUS"  WORKTREE theories
materialise E  "$COIND" WORKTREE theories
emit "D-pous(3dd5df7)"        "$WORK/D/theories"
emit "D'-pous(upstream tree)" "$WORK/Dp/theories"
emit "E-rewritten(worktree)"  "$WORK/E/theories"

# the same, with the test file excluded from both ends
rm -f "$WORK/D/theories/tests.v" "$WORK/E/theories/tests.v"
emit "D-pous(3dd5df7) no tests"       "$WORK/D/theories"
emit "E-rewritten(worktree) no tests" "$WORK/E/theories"

echo
echo "# table 3: the OCaml reification plugin, deleted by the rewrite"
echo "file,lines"
git -C "$COIND" ls-tree -r --name-only 3dd5df7 | grep '^src/' | while read f; do
  printf '%s,%s\n' "$f" "$(git -C "$COIND" show "3dd5df7:$f" | wc -l | tr -d ' ')"
done
printf 'TOTAL,%s\n' "$(git -C "$COIND" ls-tree -r --name-only 3dd5df7 | grep '^src/' \
  | while read f; do git -C "$COIND" show "3dd5df7:$f"; done | wc -l | tr -d ' ')"

echo
echo "# table 4: raw line counts, for comparison with rocq wc"
echo "state,wc_l_theories,wc_l_extra"
raw () { find "$1" -name '*.v' -print0 | xargs -0 cat | wc -l | tr -d ' '; }
printf 'A-paco,%s,%s\n'     "$(raw "$WORK/A-theories/theories")" "$(raw "$WORK/A-extra/extra")"
printf 'B-oldcoind,%s,%s\n' "$(raw "$WORK/B-theories/theories")" "$(raw "$WORK/B-extra/extra")"
printf 'C-newcoind,%s,%s\n' "$(raw "$WORK/C-theories/theories")" "$(raw "$WORK/C-extra/extra")"

echo
echo "# table 5: tactic definitions per file, the ten that moved most (B -> C)"
echo "file,B,C,delta"
( cd "$WORK/B-theories/theories" && find . -name '*.v' | sed 's|^\./||' ) | sort > "$WORK/files.txt"
while read f; do
  b=$(tactic_defs "$WORK/B-theories/theories/$f" 2>/dev/null || echo 0)
  c=$(tactic_defs "$WORK/C-theories/theories/$f" 2>/dev/null || echo 0)
  [ "$b" = "$c" ] || printf '%s,%s,%s,%s\n' "$f" "$b" "$c" "$((c-b))"
done < "$WORK/files.txt" | sort -t, -k4,4n | head -10

echo
echo "# table 6: whole-system spec+proof, library excluding tests, Rocq only and with the OCaml plugin"
echo "state,itrees_theories,itrees_extra,coind_library,rocq_total,ocaml_plugin,grand_total"
sp () { set -- $(wc_tree "$1"); echo $(($1+$2)); }
# note: tests.v was removed from $WORK/D and $WORK/E above, so these library
# figures exclude the test file at both ends
b_it=$(sp "$WORK/B-theories/theories"); b_ex=$(sp "$WORK/B-extra/extra"); b_li=$(sp "$WORK/D/theories")
c_it=$(sp "$WORK/C-theories/theories"); c_ex=$(sp "$WORK/C-extra/extra"); c_li=$(sp "$WORK/E/theories")
printf 'B-oldcoind,%s,%s,%s,%s,307,%s\n' "$b_it" "$b_ex" "$b_li" "$((b_it+b_ex+b_li))" "$((b_it+b_ex+b_li+307))"
printf 'C-newcoind,%s,%s,%s,%s,0,%s\n'   "$c_it" "$c_ex" "$c_li" "$((c_it+c_ex+c_li))" "$((c_it+c_ex+c_li))"

echo
echo "# table 7: deltas, spec+proof by rocq wc, and including comments"
echo "measure,A-paco,B-oldcoind,C-newcoind,A->B,B->C,A->C"
d () { printf '%s,%s,%s,%s,%s,%s,%s\n' "$1" "$2" "$3" "$4" "$(($3-$2))" "$(($4-$3))" "$(($4-$2))"; }
set -- $(wc_tree "$WORK/A-theories/theories"); as=$1; ap=$2; ac=$3
set -- $(wc_tree "$WORK/B-theories/theories"); bs=$1; bp=$2; bc=$3
set -- $(wc_tree "$WORK/C-theories/theories"); cs=$1; cp=$2; cc=$3
set -- $(wc_tree "$WORK/A-extra/extra"); axs=$1; axp=$2; axc=$3
set -- $(wc_tree "$WORK/B-extra/extra"); bxs=$1; bxp=$2; bxc=$3
set -- $(wc_tree "$WORK/C-extra/extra"); cxs=$1; cxp=$2; cxc=$3
d "theories spec"        "$as" "$bs" "$cs"
d "theories proof"       "$ap" "$bp" "$cp"
d "theories spec+proof"  "$((as+ap))" "$((bs+bp))" "$((cs+cp))"
d "extra spec"           "$axs" "$bxs" "$cxs"
d "extra proof"          "$axp" "$bxp" "$cxp"
d "extra spec+proof"     "$((axs+axp))" "$((bxs+bxp))" "$((cxs+cxp))"
d "both proof"           "$((ap+axp))" "$((bp+bxp))" "$((cp+cxp))"
d "both spec"            "$((as+axs))" "$((bs+bxs))" "$((cs+cxs))"
d "both spec+proof"      "$((as+ap+axs+axp))" "$((bs+bp+bxs+bxp))" "$((cs+cp+cxs+cxp))"
d "both incl comments"   "$((as+ap+ac+axs+axp+axc))" "$((bs+bp+bc+bxs+bxp+bxc))" "$((cs+cp+cc+cxs+cxp+cxc))"
d "tactic defs theories" "$(tactic_defs "$WORK/A-theories/theories")" "$(tactic_defs "$WORK/B-theories/theories")" "$(tactic_defs "$WORK/C-theories/theories")"
d "tactic defs extra"    "$(tactic_defs "$WORK/A-extra/extra")" "$(tactic_defs "$WORK/B-extra/extra")" "$(tactic_defs "$WORK/C-extra/extra")"
