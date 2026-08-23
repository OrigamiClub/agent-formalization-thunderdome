# Gilbert–Varshamov bound — agent_04

**Form chosen:** the combinatorial/existential form directly from the prompt — given
alphabet size `q ≥ 2`, length `n ≥ 1`, target minimum distance `1 ≤ d ≤ n`, and a
positive integer `M`, if `M * (∑_{i=0}^{d-2} C(n-1,i)(q-1)^i) < q^n`, then there
exists a code `C` (a `Finset (Fin n → Fin q)`) with `C.card = M` such that any two
distinct codewords differ in at least `d` coordinates.

**Encoding choices.** Codewords live in `Fin n → Fin q` (the standard `q^n`-size
ambient space). Rather than use Mathlib's `hammingDist`/`Hamming` API (whose exact
name/namespace I wasn't fully certain of), I spelled out "differ in at least `d`
coordinates" inline as `d ≤ (Finset.univ.filter (fun i => x i ≠ y i)).card`, which is
unambiguous and self-contained. The sum `∑_{i=0}^{d-2} C(n-1,i)(q-1)^i` is written as
`∑ i ∈ Finset.range (d - 1), Nat.choose (n-1) i * (q-1)^i`, using truncated natural
subtraction; `Finset.range (d-1)` has exactly `d-1` elements `{0,...,d-2}`, and when
`d = 1` it is empty, matching the convention that the sum is vacuously `0` in that
edge case. All hypotheses (`q`, `n`, `d`, `M` bounds, and the GV inequality itself)
are explicit premises, and the theorem is left as `:= by sorry`.

**Uncertain identifiers:** none load-bearing, since I avoided `hammingDist`; standard
identifiers used (`Nat.choose`, `Finset.range`, `Finset.univ.filter`, `Finset.card`)
are all core Mathlib and should be safe.
