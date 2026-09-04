# Agent 022 — formalization note

## What is stated

All three pieces, statement-only, each closed by `:= by sorry`:

1. `boolean_degree_le_isJunta` — the **forward** direction: `∃ m : ℕ` (a bound
   depending on `d` only, since it is quantified *before* `k` and `n`) such that
   for `k ≥ 2d`, `n ≥ 2k`, every Boolean degree-`d` function on `binom([n],k)` is
   an `m`-junta.
2. `not_isJunta_of_lt_two_mul` — the **converse**: for `1 ≤ k < 2d` and every `m`,
   some `n ≥ 2k` carries a Boolean degree-`d` function that is not an `m`-junta.
3. `witnessFun` / `witnessFun_spec` — the **explicit family**, asserting it is
   Boolean, degree ≤ `d`, and not an `m`-junta for any `m < ℓ·e`.

## Encoding decisions

- **Slice**: `Slice n k := {S : Finset (Fin n) // S.card = k}`. Coordinates are
  `Fin n`; `n`, `k`, `d`, `ℓ` are plain `ℕ` arguments.
- **Boolean codomain**: functions are `Slice n k → ℝ`, with a separate predicate
  `IsBoolean f : ∀ S, f S = 0 ∨ f S = 1`. Real-valued is convenient for tying the
  value directly to polynomial evaluation.
- **Degree ≤ d** (`HasDegreeLE`): `∃ p : MvPolynomial (Fin n) ℝ` that is
  multilinear (`∀ i, MvPolynomial.degreeOf i p ≤ 1`), has
  `MvPolynomial.totalDegree p ≤ d`, and agrees with `f` on every slice point when
  evaluated at the `0/1` indicator vector `ind S.1` (`ind S i = if i ∈ S then 1
  else 0`). This is the standard "degree on the slice" notion. The multilinearity
  conjunct is kept for fidelity to the problem text; it is logically redundant on
  `0/1` inputs (multilinearization does not raise total degree).
- **m-junta** (`IsJunta m f`): `∃ J : Finset (Fin n), J.card ≤ m ∧ DependsOnlyOn f
  J`, where `DependsOnlyOn f J : ∀ S T, S.1 ∩ J = T.1 ∩ J → f S = f T`.
- **m(d)**: an existential `∃ m : ℕ` inside the forward statement (not an explicit
  `m : ℕ → ℕ`), matching "there is a constant m(d)".
- **Explicit family**: `block e i n := Finset.univ.filter (fun v => (v:ℕ)/e = i)`
  is `{i·e, …, i·e+e-1} ⊆ Fin n`; `witnessFun d k ℓ n S = ∑_{i<ℓ} ∏_{v ∈ block
  (min d k) i n} ind S.1 v`. The non-junta clause is stated as `∀ m < ℓ·(min d k),
  ¬ IsJunta m (…)`.

## Deviation from the prompt's literal formula (deliberate)

The prompt writes the witness as `∏_{i=1}^{ℓ} (Σ_{j=1}^{e} x_{(i-1)e+j})`. Read
literally (product of block-sums, evaluated at the indicator), that is **not**
`{0,1}`-valued on the slice (e.g. `d,k ≥ 3`, `k = 3`, `e = 3`, `S` with two
elements in one block gives value `2`), and its cube-degree is `ℓ`, not `d`. I
instead formalized `Σ_{i=1}^{ℓ} ∏_{j=1}^{e} x_{(i-1)e+j}` = "number of blocks
fully contained in `S`". This *is* `{0,1}`-valued precisely because `1 ≤ k < 2d`
forces `k < 2·min d k`, so at most one width-`e` block fits inside a `k`-set; it
is multilinear of total degree `e = min d k ≤ d`; and it depends on every one of
the `ℓ·e` block coordinates. I believe the `∏`/`Σ` were transposed in the prompt;
this reading is the one that makes every asserted property true.

Also: the phrase "not `ℓe`-juntas" is literally false for this function (it *is*
an `ℓe`-junta, taking `J` = all block coordinates). I state the intended content,
`¬ IsJunta m` for every `m < ℓe`, which is what drives the converse.

## Uncertainties / guessed identifiers

- `MvPolynomial.degreeOf`, `MvPolynomial.totalDegree`, `MvPolynomial.eval`,
  `Finset.filter`, `Finset.range`, big-operator notation `∑ … ∈ …, ` / `∏ … ∈ …, `
  — believed current Mathlib, but not compiler-checked here. `Finset.filter`'s
  argument order (`filter p s`) is assumed; `Finset.univ.filter (fun v => …)` via
  dot notation should be robust to that.
- `open scoped BigOperators` is included for cross-version safety; recent Mathlib
  makes it unnecessary but it should remain harmless.
- The `n ≥ 2ℓe` bound in `witnessFun_spec` is copied from the theorem statement;
  the exact slack needed for the non-junta argument may differ by `O(1)`, which
  does not matter for a statement-only formalization.
- No dedicated Mathlib notion of "Boolean function / degree on the slice" was
  assumed to exist; all such notions are defined locally here.
