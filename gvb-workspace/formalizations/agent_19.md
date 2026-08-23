# Gilbert–Varshamov bound — agent_19

I chose the **combinatorial/existential form** (the primary form given in the
prompt): given alphabet size `q ≥ 2`, length `n ≥ 1`, minimum distance target
`1 ≤ d ≤ n`, and a positive integer `M` satisfying
`M * ∑_{i=0}^{d-2} C(n-1,i) (q-1)^i < q^n`, there exists a code `C` of
codewords of length `n` over an alphabet of size `q` with `|C| = M` and
pairwise Hamming distance at least `d`.

I did not use a dedicated Mathlib Hamming-distance function (I was unsure of
the exact name/API for `Fintype`-indexed Hamming distance, e.g. something in
`Mathlib.InformationTheory.Hamming`, and didn't want to guess wrong), and
instead defined "distance ≥ d" inline via
`d ≤ (Finset.univ.filter (fun i => x i ≠ y i)).card`, i.e. the number of
coordinates on which two codewords `x y : Fin n → Fin q` disagree. Alphabet
and codeword space are modeled as `Fin q` and `Fin n → Fin q` respectively,
and a code is a `Finset (Fin n → Fin q)`. The sum `∑_{i=0}^{d-2} C(n-1,i)
(q-1)^i` is encoded as `∑ i in Finset.range (d - 1), (n-1).choose i *
(q-1)^i`, using that `Finset.range (d-1)` enumerates `i = 0, …, d-2`. The
theorem is stated with `:= by sorry` as requested; no proof is attempted.
