# Agent 041 — Filmus–Ihringer slice-junta theorem, statement-only

## What I stated

Three theorems, all `:= by sorry`:

1. `filmus_ihringer_junta` — the forward direction, with `m(d)` as an
   **existential** `∃ m : ℕ → ℕ` at the front of the statement (a single
   function witnessing all `d`, `k ≥ 2d`, `n ≥ 2k`).
2. `filmus_ihringer_not_junta` — the converse in clean existential form:
   for `1 ≤ k < 2d` and every `m`, some `n ≥ 2k` and some Boolean degree-`d`
   function that is not an `m`-junta.
3. `filmus_ihringer_flower_witness` — the explicit witnessing family
   `∏_{i=1}^{ℓ}(Σ_{j=1}^{e} x_{(i-1)e+j})` with `e = min d k`, asserting it is
   Boolean, degree `≤ d`, and not an `ℓe`-junta when `n ≥ 2ℓe`.

## Encoding decisions

- **Slice**: I do *not* use a subtype. Functions are `f : Finset (Fin n) → ℝ`
  defined on all of `Finset (Fin n)`, and every property is quantified over
  `S` with the side condition `S.card = k`. This keeps the "many polynomial
  representations agree on the slice" phenomenon transparent and avoids
  subtype/coercion friction.
- **Boolean codomain**: `{0,1} ⊆ ℝ`, expressed as `f S = 0 ∨ f S = 1` for
  `k`-sets. Chosen so that "degree" via real polynomials is immediate.
- **Degree ≤ d** (`HasSliceDegreeLE`): `∃ p : MvPolynomial (Fin n) ℝ` with
  `p.totalDegree ≤ d` agreeing with `f` at the indicator vector `indicator S`
  (`fun i => if i ∈ S then 1 else 0`) for every `k`-set `S`. The existential
  makes this the minimum representing degree, which is the correct slice
  notion (on the slice `Σ x_i = k` lets you lower apparent degree). I allow an
  arbitrary polynomial rather than forcing multilinearity: on `{0,1}` inputs
  multilinear reduction does not increase total degree, so the two are
  equivalent here.
- **m-junta** (`IsJuntaOnSlice`): `∃ J : Finset (Fin n)`, `J.card ≤ m`, with
  `f S = f T` whenever `S, T` are `k`-sets and `S ∩ J = T ∩ J`.
- **Carrying `n, k, d`**: all explicit `∀`-bound `ℕ`s inside each theorem;
  ambient coordinate set is `Fin n`. `m(d)` is existential (choice 1 above).
- **Explicit family**: included, `0`-indexed. `flowerFactor e i S` is the sum
  over `j ∈ range e` of the indicator of coordinate `i*e + j`; a `dite` guards
  the `Fin n` membership and returns `0` out of range (never triggered when
  `2ℓe ≤ n`, since `i < ℓ, j < e ⇒ i*e+j < ℓe ≤ n`). `flowerFn d k ℓ S` is the
  product over `i ∈ range ℓ`. Both `noncomputable` (real arithmetic).
  Non-junta bound `ℓ * min d k`, size hypothesis `2 * ℓ * min d k ≤ n`,
  matching "for `n ≥ 2ℓe` not `ℓe`-juntas".

## Uncertainties

- **Mathlib identifiers** (believed correct, not compiler-checked):
  `MvPolynomial (Fin n) ℝ`, `MvPolynomial.totalDegree`, `MvPolynomial.eval`
  (signature `eval (v : σ → R) (p) : R`), `Finset.card`, `Finset.range`,
  `∑ / ∏ … ∈ …` big-operator syntax over `Finset`, `Finset.inter` via `∩`.
  `import Mathlib` used to avoid a wrong specific import path.
- **The `BooleanOnSlice` conjunct in `filmus_ihringer_flower_witness`.** I
  transcribed the task's assertion that the flower functions are "Boolean
  degree-`d`". A raw product of block-sums is generally integer-valued and can
  exceed `1` on the slice, so I am **not confident** this conjunct is literally
  true for the naive product as I defined it; the paper's construction may
  differ in detail (e.g. an indicator wrapper, or a parameter regime I have
  not reproduced). The reliable converse statement is
  `filmus_ihringer_not_junta`; theorem 3 should be read as a good-faith
  transcription of the stated witness whose Boolean/degree conjuncts carry
  this caveat.
- **Exact slice-degree of the flower family**: I assert `HasSliceDegreeLE k d`
  (degree `≤ d`, not `≤ ℓ`), relying on the slice identity `Σ x_i = k`. This
  is the crux of the FI construction and I have not verified it.
- Forward direction uses `degree ≤ d` (not `= d`); standard reading.
