# Agent 084 — formalization note

## What I stated

All three parts, as three `theorem … := by sorry`:

1. `filmus_ihringer_junta` — the junta upper bound: `∃ M : ℕ → ℕ`, for `d ≥ 1`,
   `k ≥ 2d`, `n ≥ 2k`, every Boolean degree-`d` function on the slice is an `M d`-junta.
2. `filmus_ihringer_tightness` — the converse: for `d ≥ 1`, `1 ≤ k < 2d`, and every `m`,
   there is `n ≥ 2k` and a Boolean degree-`d` function on the slice that is not an
   `m`-junta.
3. `filmus_ihringer_witness` — the explicit family
   `∑_{i=1}^{ℓ} ∏_{j=1}^{e} x_{(i-1)e+j}`, `e = min d k`, asserted (for `n ≥ 2ℓe`) to be
   Boolean, degree `≤ d`, and not an `m`-junta for any `m < ℓe`.

## Encoding decisions

- **Slice**: `Slice n k := {S : Finset (Fin n) // S.card = k}`. Ambient coordinate set is
  `Fin n`; `n`, `k`, `d`, `m`, `ℓ` are all explicit `ℕ` arguments/quantifiers. Chose the
  subtype-of-`Finset` form because set intersection `S ∩ J` (needed for the junta
  definition) and polynomial evaluation at an indicator are both immediate.
- **Boolean codomain**: real-valued functions `Slice n k → ℝ` together with a predicate
  `IsBoolean f : ∀ S, f S = 0 ∨ f S = 1`. Real codomain chosen so that "degree" refers
  directly to real polynomials with no coercion friction.
- **Degree ≤ d** (`HasDegreeLE`): `∃ p : MvPolynomial (Fin n) ℝ` with
  `p.totalDegree ≤ d`, `p` multilinear, and `f S = MvPolynomial.eval (indicator S) p` for
  every slice point. Multilinearity is written out as
  `∀ t ∈ p.support, ∀ i, t i ≤ 1` (every monomial uses each variable at most once)
  rather than relying on a possibly-nonexistent `MvPolynomial.IsMultilinear`.
  `indicator S i = if i ∈ S.1 then (1:ℝ) else 0`.
- **m-junta** (`IsJunta`): `∃ J : Finset (Fin n)`, `J.card ≤ m`, and
  `∀ S T, S.1 ∩ J = T.1 ∩ J → f S = f T`. Direct transcription of "depends only on
  `S ∩ J`".
- **m(d)**: existential `∃ M : ℕ → ℕ` inside theorem 1 (not an external explicit
  function).
- **Explicit family** (`witnessFn`, `block`): `block n e i` is the `Fin n`-coordinates
  with value in `[i*e, i*e+e)`; `witnessFn n k e ℓ S` is the real cast of
  `#{ i < ℓ | block n e i ⊆ S.1 }`. This equals the evaluation of
  `∑_{i<ℓ} ∏_{j<e} X_{i*e+j}` at the indicator vector (0-indexed), matching the
  displayed formula.

## Uncertainties / caveats

- **`∑ ∏` vs `∏ ∑`.** The prompt prints the family as
  `∏_{i=1}^{ℓ}(∑_{j=1}^{e} x_{(i-1)e+j})`. Read literally that is a product of linear
  forms: its value `∏_i |S ∩ B_i|` is not `{0,1}`-valued in general, its polynomial
  degree is `ℓ` (not `≤ d`), and the junta size it forces is bounded by `k·min(d,k)`,
  which cannot exceed an arbitrary `m`. The only reading consistent with "Boolean",
  "degree `d`", and "for every `m`" is the **sum of products**
  `∑_{i=1}^{ℓ} ∏_{j=1}^{e} x_{(i-1)e+j}`, which has degree `e = min(d,k) ≤ d`, is
  `{0,1}`-valued on the slice when `k < 2d` (two disjoint size-`e` blocks cannot both fit
  in an `S` of size `k`), and depends on all `ℓe` coordinates. I formalized this
  corrected reading and flag the discrepancy here.
- **"not `ℓe`-juntas".** As written this is literally false for the sum-of-products
  witness: it depends only on coordinates `1,…,ℓe`, hence *is* an `ℓe`-junta. I
  interpreted the intended claim as "needs all `ℓe` coordinates", i.e. not an
  `(ℓe−1)`-junta, and stated it as `∀ m < ℓ*e, ¬ IsJunta … m`.
- **Guessed Mathlib identifiers**: `MvPolynomial.totalDegree`, `MvPolynomial.eval`,
  `MvPolynomial.support`, `Finsupp` application `t i`, and the `DecidablePred`
  instances for `block n e i ⊆ S.1` and the `Fin`/`ℕ` comparison predicates inside
  `Finset.filter`. All are standard, but I have no compiler here; a `classical` /
  `open Classical` may be needed if a decidability instance is not found for the
  `filter` in `witnessFn` / `block`.
- I did not assume any Mathlib "Boolean function on the slice" or "junta" API exists;
  everything is defined locally.
