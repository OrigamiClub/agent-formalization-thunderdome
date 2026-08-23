# Gilbert–Varshamov bound — agent_07

**Form chosen:** the classical combinatorial/existential form (option "as given" in the
background, essentially the same as variant (a)/(c) but stated directly with an abstract
code size `M`, matching the exact inequality quoted in the prompt). Codewords are modeled
as functions `Fin n → Fin q` (length-`n` strings over an alphabet of size `q`), and a code is
a `Finset` of such functions. This form was chosen over the rate–distance asymptotic form
because it is a finite, purely combinatorial statement that translates directly into
Mathlib-style `Finset`/`Nat.choose` arithmetic without needing limits or the binary entropy
function, and over the linear/dimension form because it avoids committing to a finite-field
vector-space structure that isn't part of the stated background.

**Nonstandard/inline definitions:** "distance at least `d`" is spelled out inline as
`d ≤ (Finset.univ.filter (fun i => x i ≠ y i)).card`, i.e. the number of coordinates where two
codewords disagree, rather than invoking Mathlib's `hammingDist` (I was not fully confident of
its exact name/namespace/typeclass requirements, so I used the manifestly correct filter-card
expression instead — this is definitionally what Hamming distance means here).

**Encoding/simplification choices:** the sum `∑_{i=0}^{d-2} C(n-1,i)(q-1)^i` is written as
`∑ i ∈ Finset.range (d - 1), (n-1).choose i * (q-1)^i`, since `Finset.range (d-1) = {0,...,d-2}`
has exactly `d-1` terms, matching the upper index `d-2` in the natural-language sum (all
arithmetic is over `ℕ`, so `d - 1` and `n - 1` use truncated subtraction, which is safe given
the hypotheses `1 ≤ d` and `1 ≤ n`). The hypotheses `2 ≤ q`, `0 < n`, `1 ≤ d ≤ n`, `0 < M` are
stated explicitly as separate premises rather than folded into the type, mirroring the
background statement.
