# Gilbert–Varshamov bound — agent_11

I formalized the **combinatorial/existential form**: given alphabet size `q ≥ 2`,
length `n ≥ 1`, target minimum distance `1 ≤ d ≤ n`, and a positive integer `M`
satisfying `M * (∑_{i=0}^{d-2} C(n-1,i)(q-1)^i) < q^n`, there exists a `Finset`
`C` of `Fin n → Fin q` with `C.card = M` such that every two distinct elements
of `C` differ in at least `d` coordinates. This is the classical greedy/sphere-
packing statement (form given directly in the prompt), rather than the
rate-distance asymptotic form or the linear-code/dimension form.

The sum bound is encoded with `Finset.range (d - 1)` (Nat truncated
subtraction), which equals `{0, ..., d-2}` and correctly becomes the empty
sum (0) exactly when `d = 1`. Hamming distance is *not* pulled from a
guessed Mathlib name; instead "distance ≥ d" is spelled out inline as
`d ≤ (Finset.univ.filter (fun i => x i ≠ y i)).card`, i.e. the number of
coordinates where two codewords disagree. (Mathlib does contain a `Hamming`
type synonym with `hammingDist`, which would be an equally valid alternative
encoding, but I preferred the explicit filter/card expression to avoid
relying on an API I wasn't fully certain about.) No proof is attempted;
the theorem ends in `sorry` as requested.
