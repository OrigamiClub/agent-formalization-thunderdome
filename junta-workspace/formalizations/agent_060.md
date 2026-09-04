# agent_060 — formalization note

## What is stated

Statement only, three theorems, each `:= by sorry`, nothing proved:

1. `boolean_degree_d_is_junta` — the **forward** direction. `m(d)` is an existential
   `∃ m : ℕ → ℕ` inside the statement (the exact constant is not part of the essential
   claim; the problem only asserts "there is a constant m(d)").
2. `sharp_threshold_converse` — the **converse**, abstract form: for `1 ≤ k < 2d` and
   every `m`, some slice carries a Boolean degree-`d` non-`m`-junta.
3. `sharp_threshold_converse_explicit` — the converse **with the explicit witnessing
   family** `fiPoly` / `fiWitness`.

## Encoding decisions

- **Slice**: `Slice n k := {S : Finset (Fin n) // S.card = k}`. Subtype of `Finset`,
  the most direct rendering of `{S ⊆ [n] : |S| = k}`. Ambient coordinate type `Fin n`;
  `n, k, d` are explicit `ℕ` arguments.
- **Codomain**: real-valued `Slice n k → ℝ` plus a predicate `IsBooleanFn f` (`∀ S,
  f S = 0 ∨ f S = 1`). Keeping everything in `ℝ` avoids coercions, since "degree" is
  defined through real polynomials.
- **Degree ≤ d**: `HasDegreeLE f d := ∃ p : MvPolynomial (Fin n) ℝ, p.totalDegree ≤ d
  ∧ ∀ S, f S = eval (indicator S) p`, where `indicator S i = if i ∈ S then 1 else 0`.
  This is exactly "agrees on the slice with a real polynomial of total degree ≤ d
  evaluated at the indicator vector". Multilinearity is not imposed — on the slice it
  is free, and the `∃` makes it harmless.
- **m-junta**: `IsJunta f m := ∃ J : Finset (Fin n), J.card ≤ m ∧ ∀ S T, S.1 ∩ J =
  T.1 ∩ J → f S = f T`. "Value depends only on `S ∩ J`" for some `|J| ≤ m`.
- **Quantifier shape**: forward has `∃ m` outermost then `∀ d k n f`. Converse has
  `∀ d k` (with `1 ≤ k`, `k < 2*d`) then `∀ m`, then `∃ n` and `∃ f`. Constraints
  `k ≥ 2d` / `k < 2d` written `2*d ≤ k` / `k < 2*d`; `n ≥ 2k` written `2*k ≤ n`.

## The explicit family — deliberate deviation from the problem text

The problem writes the witness as `∏_{i=1}^{ℓ} (∑_{j=1}^{e} x_{(i-1)e+j})`, `e =
min(d,k)`. I encode instead the **sum of products**

    fiPoly = ∑_{i=0}^{ℓ-1} ∏_{c ∈ block i} X c ,   block i = {i·e, …, i·e+e−1},  e = min d k

(an OR of `ℓ` disjoint size-`e` ANDs). Reasons the product-of-sums cannot be the
intended witness, while the sum-of-products is:

- **Degree.** `∏_{i=1}^{ℓ}(∑ …)` has total degree `ℓ`, which is not constant in `ℓ`;
  it cannot be a degree-`d` function for large `ℓ`. `∑_{i}∏_{j}` has total degree
  `e = min(d,k) ≤ d`, independent of `ℓ`.
- **"For every m".** On `binom([n],k)`, `∏_{i=1}^{ℓ}(∑_{c∈block i} x_c) = ∏_i |S∩block i|`,
  which is identically `0` as soon as `ℓ > k` (some block is missed). So it collapses
  to a constant and cannot be a non-`m`-junta for `m ≥ k²`. The sum-of-products equals
  `#{ i < ℓ : block i ⊆ S }`, needs all `ℓe` block coordinates, and `ℓ` is free.
- **Threshold `k = 2d` matches.** `∑_i ∏_j` is Boolean on `binom([n],k)` iff at most
  one block fits in a `k`-set, i.e. `2·min(d,k) > k`, i.e. `k < 2d`. And `k ≥ 2d ⇔
  2·min(d,k) ≤ k ⇔ two disjoint blocks fit ⇔ not Boolean` — exactly the theorem's
  dividing line.

I read the problem's `∏(∑)` as a transcription swap of `∑(∏)`. This is flagged as an
uncertainty.

**"Not `ℓe`-juntas".** The OR-of-blocks function literally *is* an `ℓe`-junta (take
`J` = all block coordinates). The source phrase must mean "needs all `ℓe`
coordinates". I encode `∀ m, m < ℓ * min d k → ¬ IsJunta (fiWitness …) m`
(equivalently: not an `(ℓe−1)`-junta), which is the faithful strong reading and
directly yields "for every `m`, non-`m`-junta" by taking `ℓ` with `ℓe > m`.

**Size hypotheses for the explicit family.** Both `2*k ≤ n` and `2*ℓ*min d k ≤ n`
are assumed. The second is the problem's `n ≥ 2ℓe`; the first guarantees the `k − e`
non-block elements of `S` have room outside the blocks (needed when `d < k < 2d`).
`ℓ = 0` makes `fiWitness ≡ 0` and the non-junta clause vacuous — harmless.

## Uncertainties

- **`∏` vs `∑` swap** in the witness (discussed above) — I deviated intentionally.
- **Off-by-one** in "not `ℓe`-junta" — encoded as `m < ℓe ⇒ ¬ IsJunta … m`.
- **Mathlib identifiers** assumed: `MvPolynomial`, `MvPolynomial.totalDegree`,
  `MvPolynomial.eval` (argument order `eval (s : σ → R) p`), `MvPolynomial.X`,
  `Finset.univ.filter`, `Finset.range`, `∑ i ∈ s, …` / `∏ c ∈ s, …` BigOperators
  notation, `open scoped BigOperators`. All standard; minor API drift possible.
- I do not believe Mathlib has a native "Boolean degree on the slice" / Johnson-scheme
  eigenspace notion, so everything is defined from scratch.
- The forward theorem asks only for `n ≥ 2k` (which with `k ≥ 2d` gives `n − k ≥ k ≥
  2d`); the paper's abstract phrase "k, n−k large enough" is captured by this.
- `fiPoly` having `totalDegree = min d k` (not merely `≤`) needs the blocks nonempty,
  disjoint and in range; true under the hypotheses but not needed for the statement.
