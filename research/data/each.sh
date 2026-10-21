# Each law of examples/data.ts without lemmas, depth 1 then 2, 25 s apiece.
for w in lengthMap mirrorMirror sizeMirror sumFlatten insertSorted insertCount insertLength bstInsert reverseReverse; do
  for d in 1 2; do echo "$w depth $d: $(perl -e 'alarm shift; exec @ARGV' 25 bun research/data/dump.ts $w $d 99 2>&1 | tail -1 | cut -c1-200)"; done
done
