# agent_074 — Filmus–Ihringer slice-junta theorem (statement only)

## What is stated

All three parts, as separate `:= by sorry` theorems:

1. `boolean_degree_le_d_on_slice_is_junta` — the **upper bound**: `∀ d ≥ 1, ∃ m,
   ∀ k ≥ 2d, ∀ n ≥ 2k`, every Boolean degree-`≤ d` function on `binom([n],k)` is an
   `m`-junta.
2. `boolean_degree_le_d_on_slice_not_junta` — the **abstract lower bound**: for
   `1 ≤ k < 2d` and every `m`, some `n ≥ 2k` carries a Boolean degree-`≤ d` function
   that is not an `m`-junta.
3. `fiFun_is_boolean_degree_le_d_and_not_junta` — the **explicit family**:
   `∏_{i=1}^{ℓ} (∑_{j=1}^{e} x_{(i-1)e+j})` with `e = min d k`, stated (for `ℓ ≥ 1`,
   `n ≥ 2ℓe`) to be Boolean, degree `≤ d`, and not an `ℓe`-junta.

## Encoding decisions

- **Slice**: sets `S : Finset (Fin n)` with side condition `S.card = k`. Chosen over
  a subtype so the polynomial-evaluation machinery applies without transport. A
  "function on the slice" is a total `f : Finset (Fin n) → ℝ`; every predicate only
  constrains `S` with `S.card = k`, so off-slice values are irrelevant.
- **Boolean**: `f S = 0 ∨ f S = 1` (i.e. `{0,1} ⊆ ℝ`). Keeps degree/junta in one
  ambient ring.
- **Degree ≤ d** (`DegreeLEOnSlice`): `∃ p : MvPolynomial (Fin n) ℝ` that is
  multilinear (`∀ t ∈ p.support, ∀ i, t i ≤ 1`), has `p.totalDegree ≤ d`, and agrees
  on the slice with `MvPolynomial.eval (indicator S) p`, where
  `indicator S i = if i ∈ S then 1 else 0`. The multilinearity clause is included for
  literal faithfulness to the problem's "Terms"; on `0/1` inputs it can be dropped
  without changing the notion, so it does not affect the mathematical content of
  either the hypothesis (part 1) or the conclusions (parts 2, 3).
- **m-junta** (`IsJuntaOnSlice`): `∃ J, J.card ≤ m ∧ ∀ S T` on the slice,
  `S ∩ J = T ∩ J → f S = f T`. This is the "value depends only on `S ∩ J`" reading.
- **m(d)**: an existential `∃ m : ℕ` placed under `∀ d, 1 ≤ d → …` (literal reading of
  "Let d ≥ 1. There is a constant m(d)"), rather than a global `m : ℕ → ℕ`.
- **Explicit family**: to avoid carrying an index-range proof through the statement,
  `fiLinearForm` uses `dite (i*e+j < n)` and sends out-of-range terms to `0`; the
  hypothesis `2*(ℓ*min d k) ≤ n` guarantees all used coordinates are in range. Blocks
  are consecutive coordinate intervals of length `e`, `0`-indexed.
- `n`, `k`, `d`, `ℓ` are all explicit `ℕ` binders inside each theorem; `n` also
  appears as the ambient coordinate count via `Fin n`. A section `variable {n : ℕ}`
  serves the auxiliary defs only.

## Uncertainties

- **Booleanity of the raw product family (part 3).** `MvPolynomial.eval (indicator S)
  (fiPoly e ℓ) = ∏_i |S ∩ B_i|`, which is not obviously `0/1`-valued on the slice for
  every admissible `d,k,ℓ`. I transcribed "Boolean" directly from the problem
  statement; I did not verify it holds for the literal raw product (the Filmus–
  Ihringer source may intend a normalised/reduced form). Parts 1 and 2 do not depend
  on this. If part 3's Boolean clause is in fact false as literally written, the
  intended statement is presumably about the slice-reduced representative of this
  polynomial.
- **Mathlib identifiers** (believed correct): `MvPolynomial`, `MvPolynomial.X`,
  `MvPolynomial.eval`, `MvPolynomial.totalDegree`, `MvPolynomial.support`,
  `Finset.range`, `Finset.card`. The `∑ x ∈ s, …` / `∏ x ∈ s, …` big-operator syntax
  is the current form (older Mathlib uses `in`).
- **`noncomputable`** is placed on `fiLinearForm` / `fiPoly` / `fiFun` because they
  land in / evaluate into `ℝ`; exact necessity depends on the Mathlib version.
- No Mathlib-native "Boolean degree" or "junta" notion for the slice is used; I did
  not find one and defined both from scratch.
