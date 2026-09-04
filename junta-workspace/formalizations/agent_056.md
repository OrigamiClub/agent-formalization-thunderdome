# Agent 056 — formalization note

## What is stated

All three pieces, as separate `:= by sorry` theorems (no proofs):

1. `boolean_degree_junta_pos` — positive direction: `∀ d ≥ 1, ∃ M, ∀ k ≥ 2d, ∀ n ≥ 2k`,
   every Boolean degree-`d` function on `binom([n],k)` is an `M`-junta.
2. `boolean_degree_junta_neg` — negative direction, headline existential form:
   `1 ≤ k < 2d` ⇒ `∀ m, ∃ n ≥ 2k, ∃ f` Boolean degree-`d` on `binom([n],k)`, `f` not an
   `m`-junta.
3. `boolean_degree_junta_neg_explicit` — same but with the explicit witnessing family
   `tribesFun` named and its three properties (Boolean, degree `≤ d`, not an `m`-junta
   for `m < ℓe`) asserted.

## Encoding decisions

- **Slice**: `Slice n k := {S : Finset (Fin n) // S.card = k}`. The ambient coordinate
  set is `Fin n`; `n, k, d` are plain `ℕ` arguments carried by each theorem.
- **Boolean codomain**: functions are `Slice n k → ℝ` with a side predicate
  `IsBooleanF f : ∀ S, f S = 0 ∨ f S = 1`. Chosen over `Bool`/`Fin 2` so that "agrees
  with a real polynomial" is stated directly without a coercion.
- **Degree ≤ d** (`HasDegreeLE`): `∃ p : MvPolynomial (Fin n) ℝ`, `p` multilinear
  (`IsMultilinearPoly`: every exponent in `p.support` is `≤ 1`), `p.totalDegree ≤ d`,
  and `∀ S, f S = MvPolynomial.eval (ind S) p` where `ind S i = if i ∈ S then 1 else 0`.
  Multilinearity is included to match the wording "multilinear real polynomial"; on the
  slice it can be dropped without changing the class of functions (`x_i^2 = x_i` on
  `0/1` inputs, degree non-increasing), so an equivalent variant just omits that
  conjunct.
- **m-junta** (`IsJunta f m`): `∃ J : Finset (Fin n)`, `J.card ≤ m`, and for all `S T`
  in the slice, `S ∩ J = T ∩ J → f S = f T`.
- **m(d)**: existential `∃ M : ℕ` inside the positive statement (for `d` fixed), rather
  than an explicit `m : ℕ → ℕ`. The paper's explicit value is `binom(2d,d)`; I kept it
  existential to avoid pinning a constant I might state wrongly.
- **Explicit family** (`tribesFun n k e ℓ`): `∑_{i < ℓ} 1[block n e i ⊆ S]`, where
  `block n e i = { c : Fin n | i*e ≤ c < i*e + e }`. In the theorem `e` is instantiated
  to `min d k`, and `n` is required `≥ 2k` and `≥ 2ℓe`. Blocks are given by a
  decidable nat-range predicate (avoids `DecidablePred` friction from a bounded `∃`).

## Reading of the source's witness formula

The task writes the witnesses as `∏_{i=1}^{ℓ} (Σ_{j=1}^{e} x_{(i-1)e+j})`, i.e. a
**product of sums**. I formalized instead a **sum of products**,
`Σ_{i=1}^{ℓ} ∏_{j=1}^{e} x_{(i-1)e+j}` (an OR of `ℓ` disjoint `e`-variable ANDs — a
read-once DNF / tribes function). Reasons:
- A product of `ℓ` sums has total degree `ℓ`; it cannot be a fixed degree-`d` function
  while `ℓ → ∞` ("for every `m`"), and it could not fail to be an `ℓe`-junta.
- For `d = 1, k = 1, e = 1` the product reading degenerates to `∏ x_i`, which is
  identically `0` on `binom([n],1)` for `ℓ ≥ 2` — not a non-junta.
- The sum-of-products reading: degree `e = min d k ≤ d`; Boolean on the slice because
  `k < 2e` (true for `k ≤ d` and for `d < k < 2d`), so at most one block is contained
  in any `k`-set; and it depends on exactly the `ℓe` block coordinates.

This matches the tribes-style lower bound I recall from Filmus–Ihringer, so I believe
the "∏(Σ)" in the prompt is a transcription with product/sum swapped.

## Reading of "not an ℓe-junta"

`tribesFun` depends on exactly the `ℓe` block coordinates, so taking `J` = those
coordinates it *is* literally an `ℓe`-junta. The mathematically correct statement, and
what drives "for every `m`", is: it is **not** an `m`-junta for any `m < ℓe`
(equivalently, not an `(ℓe − 1)`-junta). I encoded that (`∀ m, m < ℓ * min d k → ¬
IsJunta …`) and treat the source's "ℓe-junta" as loose phrasing.

## Uncertainties

- Blanket `import Mathlib`.
- Guessed/relied-on Mathlib identifiers: `MvPolynomial`, `MvPolynomial.eval`,
  `MvPolynomial.support`, `MvPolynomial.totalDegree`, `Finset.filter` (predicate-first,
  used via dot-notation), `Finset` subset `Decidable` instance for the `if` in
  `tribesFun`. Names/signatures not machine-checked (no compiler available).
- The exact constant `m(d)` is not committed to (existential).
- Whether to require multilinearity in `HasDegreeLE` is a modelling choice; I included
  it. The positive theorem is essentially unchanged either way; the two negative
  theorems are fine since the witnesses are genuinely multilinear.
