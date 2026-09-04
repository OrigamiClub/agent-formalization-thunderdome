# Agent 040 — formalization note

## What is stated

Two theorems, statement only (`:= by sorry`, nothing proved):

1. `filmus_ihringer` — **both directions in one statement**:
   - the existential constant `m(d)` (introduced as `∃ m : ℕ` after `d` and `1 ≤ d`,
     so it depends only on `d`);
   - **upper bound**: `k ≥ 2d`, `n ≥ 2k` ⇒ every Boolean degree-`d` function on the
     slice is an `m`-junta;
   - **converse**: `1 ≤ k < 2d` ⇒ for every `m'` there is `n ≥ 2k` and a Boolean
     degree-`d` function on the slice that is not an `m'`-junta.
   The converse conjunct does not use `m`; it is placed inside the same `∃ m` only
   to mirror the paper's "there is `m(d)` such that … . Conversely …" phrasing.

2. `filmus_ihringer_explicit_family` — the **explicit witnessing family** for the
   converse: `∏_{i<ℓ} (∑_{j<e} x_{ι(i,j)})` with `e = min d k`, asserting that for a
   suitable `ℓ` (with `ℓ·e > m`) and `n ≥ 2·ℓ·e` its restriction to the slice is
   Boolean, has degree `≤ d`, and is not an `ℓ·e`-junta.

## Encoding decisions

- **Slice**: `Slice n k := {S : Finset (Fin n) // S.card = k}`. `Fin n` stands in
  for `{1,…,n}`. Subtype chosen so functions are plain `Slice n k → ℝ`.
- **Codomain**: real-valued functions `Slice n k → ℝ` together with a separate
  `IsBoolean f := ∀ S, f S = 0 ∨ f S = 1` predicate. This keeps the "degree"
  notion (which is inherently about real polynomials) uniform with the Boolean
  constraint, rather than juggling `Bool`/`Fin 2` casts.
- **Degree ≤ d**: `DegreeLE d f` = there is `p : MvPolynomial (Fin n) ℝ` with
  `p.totalDegree ≤ d`, `∀ i, p.degreeOf i ≤ 1` (multilinear), and
  `MvPolynomial.eval (indicator S.val) p = f S` on the whole slice, where
  `indicator S i = if i ∈ S then 1 else 0`. The multilinearity clause is kept to
  match the theorem text literally; it is equivalent to dropping it since
  `x_i^2 = x_i` on `0/1` inputs (noted in the source docstring).
- **m-junta**: `IsJunta m f` = there is `J : Finset (Fin n)` with `J.card ≤ m` and
  `∀ S T, S.val ∩ J = T.val ∩ J → f S = f T` (value depends only on `S ∩ J`).
- **`m(d)`**: an existential `∃ m : ℕ` inside the statement, not a supplied
  `m : ℕ → ℕ`. Weaker/cleaner and matches "there is a constant".
- **`n, k, d` and coordinates**: carried as explicit `ℕ` arguments; the ambient
  coordinate set is `Fin n`, threaded through `MvPolynomial (Fin n) ℝ`.
- **Explicit family indexing**: the `ℓ·e` block variables `x_{(i-1)e+j}` are
  modelled by an arbitrary `ι : Fin ℓ × Fin (min d k) → Fin n` asserted
  `Function.Injective`. Only pairwise disjointness of the `ℓ` blocks of `e`
  distinct variables matters mathematically, so replacing "consecutive blocks"
  by "an injective placement" is faithful and avoids `Fin` index arithmetic.
  `witnessPoly e ℓ ι := ∏ i, ∑ j, MvPolynomial.X (ι (i,j))`.

## Uncertainties

- **Mathlib identifiers** (from memory, not compiler-checked):
  `MvPolynomial.totalDegree`, `MvPolynomial.degreeOf`, `MvPolynomial.eval`,
  `MvPolynomial.X`, `Function.Injective`, `Finset.card`, big-operator `∏`/`∑`
  notation (hence `open scoped BigOperators`). Dot-notation `p.totalDegree` /
  `p.degreeOf i` assumes the poly is the first explicit `MvPolynomial` argument.
- **`noncomputable`**: `restrict` and `witnessPoly` are marked `noncomputable`
  defensively (evaluation / `Finsupp` machinery); irrelevant to a `sorry` file.
- **Booleanness of the raw product witness**: the source theorem calls the family
  "a Boolean degree-`d` function", so `IsBoolean` is asserted of
  `restrict (witnessPoly …)` verbatim. I did not independently verify that the
  literal product `∏ (∑ x)` (as opposed to, e.g., its `0/1` support or a
  normalization) is itself `{0,1}`-valued on the slice for all `1 ≤ k < 2d`; for
  small cases the raw integer product can exceed `1`. If the intended witness is a
  Boolean function *built from* this product rather than the product itself, the
  `IsBoolean` conjunct in `filmus_ihringer_explicit_family` should be read as
  "there is such a Boolean function agreeing with it". The direction-only theorem
  `filmus_ihringer` is unaffected by this subtlety.
- **Degree collapse**: the non-obvious content of the explicit family is that this
  degree-`ℓ` polynomial has slice-degree `≤ d`; that is packaged inside
  `DegreeLE d (restrict …)` and left to `sorry`.
