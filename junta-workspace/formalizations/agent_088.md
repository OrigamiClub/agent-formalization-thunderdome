# Agent 088 — formalization note

## What is stated

All three pieces, statement only, each `:= by sorry`:

1. `filmus_ihringer_slice_junta` — the forward direction. For `d ≥ 1` there
   **exists** a bound `m : ℕ` such that for all `k ≥ 2d`, all `n ≥ 2k`, every
   Boolean degree-`≤ d` function on the slice is an `m`-junta. `m(d)` is an
   existential inside the statement (chosen over an explicit `m : ℕ → ℕ` because
   the paper's constant is not elementary and the existential is the honest
   content).

2. `filmus_ihringer_slice_converse` — the converse in pure existential form: for
   `1 ≤ k < 2d`, for every `m` there are `n ≥ 2k` and a Boolean degree-`≤ d`
   function that is not an `m`-junta.

3. `filmus_ihringer_slice_converse_explicit` — the converse with the explicit
   family `∏_{i=1}^{ℓ}(Σ_{j=1}^{e} x_{(i-1)e+j})`, `e = min d k`, asserting that
   for `n ≥ 2ℓe` (and `n ≥ 2k`) it is Boolean-valued, has slice-degree `≤ d`, and
   is not an `m`-junta for any `m < ℓe`. Since `ℓ` is a free parameter, letting it
   grow contradicts any fixed bound.

## Encoding decisions

- **Slice**: `abbrev Slice n k := {S : Finset (Fin n) // S.card = k}`. Subtype of
  `Finset`, so `S ∩ J` for the junta condition is just `Finset` intersection and
  the coordinate set `J` is a `Finset (Fin n)`. `abbrev` so instances/elaboration
  see through it.
- **Boolean codomain**: functions `Slice n k → ℝ` with a side predicate
  `IsBooleanValued f : ∀ S, f S = 0 ∨ f S = 1`. Keeping the codomain `ℝ` makes
  "agrees with a real polynomial" immediate (no coercion juggling).
- **Degree ≤ d** (`HasSliceDegreeLE`): `∃ p : MvPolynomial (Fin n) ℝ` that is
  multilinear (`∀ i, p.degreeOf i ≤ 1`), has `p.totalDegree ≤ d`, and satisfies
  `f S = eval (indicator S) p` on every slice point, where
  `indicator S i = if i ∈ S then 1 else 0`. This matches the problem's "agrees on
  the slice with a multilinear real polynomial of total degree ≤ d evaluated at
  the indicator vector." Multilinearity is kept for fidelity; it is WLOG for
  `0/1` evaluations (replace `x_i^a` by `x_i`, total degree does not increase),
  and the explicit witness `sharpPoly` is multilinear (disjoint blocks of
  distinct variables). Note the family's *polynomial* degree is `ℓ`, so the
  degree-`≤ d` witness in claim 3 is a *different* polynomial (the reduced/slice
  representation) — the existential over `p` accommodates this.
- **m-junta** (`IsJunta`): `∃ J, J.card ≤ m ∧ ∀ S T, S ∩ J = T ∩ J → f S = f T`.
- **Explicit family**: `sharpPoly h = ∏_{i:Fin ℓ} ∑_{j:Fin e} X (blockIdx h i j)`,
  where `blockIdx` maps block/offset `(i,j)` to coordinate `i*e + j : Fin n`,
  with the in-range proof discharged from the hypothesis `h : ℓ*e ≤ n` passed to
  the definition. Indexing is `0`-based (`Fin ℓ`, `Fin e`), i.e. block `i` uses
  coordinates `i*e .. i*e+e-1`; this is the `1`-based `(i-1)e+j` of the prompt.
- `n`, `k`, `d`, `ℓ`, `e`, `m` are all explicit `ℕ` arguments; the ambient
  coordinate type is `Fin n`. In claim 3 `e` is an explicit variable pinned by
  `he : e = min d k` (cleaner than a `let` in the statement, and lets `sharpPoly`
  take `e` as an implicit inferred from `hℓe : ℓ * e ≤ n`).

## Uncertainties

- Mathlib identifiers used from memory: `MvPolynomial.eval`,
  `MvPolynomial.totalDegree`, `MvPolynomial.degreeOf`, `MvPolynomial.X`,
  `mul_le_mul_right'`. I believe all exist with these names/shapes in current
  Mathlib; `degreeOf` and `totalDegree` are the ones most worth double-checking.
- The `blockIdx` bound proof (`have`/`omega`, with `mul_le_mul_right'` supplying
  the one nonlinear step) is written blind; it may need cosmetic adjustment.
- No claim that the *mathematics* of claim 3 is literally correct as transcribed
  (e.g. exact Boolean-valuedness of the raw product on every slice point, or the
  precise sense of "not an `ℓe`-junta"). The task is to formalize the *statement*;
  I transcribed the family and the three properties the prompt attributes to it,
  with "not an `m`-junta for `m < ℓe`" as my reading of "not `ℓe`-juntas"
  (i.e. all `ℓe` coordinates are relevant). If in doubt, claims 1 and 2 are the
  robust ones.
- `MvPolynomial (Fin n) ℝ` forces `noncomputable` on `sharpPoly`/`sharpFun`;
  marked as such.
