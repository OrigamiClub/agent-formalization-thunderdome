# Agent 089 — formalization note

## What is stated

Three `sorry`-terminated theorems (statement only, nothing proved):

1. `filmus_ihringer_forward` — the positive direction: `∀ d ≥ 1, ∃ m, ∀ k ≥ 2d, ∀ n ≥ 2k`,
   every Boolean degree-`≤ d` function on the slice is an `m`-junta.
2. `filmus_ihringer_converse` — the negative direction as a bare existential: for
   `1 ≤ k < 2d` and every `m`, some `n ≥ 2k` and some Boolean degree-`≤ d` function on
   `binom([n],k)` is not an `m`-junta.
3. `filmus_ihringer_tightness_family` — the negative direction with the explicit
   witnessing family `∏_{i<ℓ}(∑_{j<e} x_{i·e+j})`, `e = min d k`, claiming it is
   Boolean, degree `≤ d`, and not an `(ℓ·e)`-junta for `n ≥ 2ℓe`.

## Encoding decisions

- **Slice**: `Slice n k := {S : Finset (Fin n) // S.card = k}`. Subtype of `Finset`,
  the most direct rendering of "k-element subsets of {1,…,n}".
- **Codomain**: functions `Slice n k → ℝ` together with a separate `IsBoolean`
  predicate (`f S = 0 ∨ f S = 1`). Real codomain chosen so that "degree" can be
  phrased with a real polynomial without any coercion gymnastics; Boolean-ness is a
  hypothesis in the forward theorem and a conclusion in the converse ones.
- **Degree ≤ d** (`HasSliceDegreeLE`): existence of `p : MvPolynomial (Fin n) ℝ` with
  `p.totalDegree ≤ d` agreeing with `f` on every slice point, evaluated at the 0/1
  indicator vector `slicePoint S i = if i ∈ S.val then 1 else 0`. This is the
  "agrees with a multilinear real polynomial of total degree ≤ d at the indicator
  vector" definition from the problem's Terms. I did not force multilinearity
  (`totalDegree ≤ d` on an arbitrary polynomial is equivalent on the 0/1 cube, and
  the slice statement is about agreement of values).
- **m-junta** (`IsJunta`): `∃ J : Finset (Fin n), J.card ≤ m ∧ ∀ S T, S∩J = T∩J → f S = f T`.
- **m(d)**: existential `∃ m : ℕ` inside `filmus_ihringer_forward`, one per `d`
  (equivalent to an explicit `m : ℕ → ℕ` by choice).
- **Parameters** `n, k, d, ℓ` are plain `ℕ` arguments; the ambient coordinate set is
  `Fin n`. Inequalities transcribed as `2*d ≤ k`, `2*k ≤ n`, `k < 2*d`,
  `2*(ℓ*min d k) ≤ n`.
- **Explicit family** (`familyFun`): the block sum `∑_{j<e} x_{i·e+j}` is realized as
  `(S.val.filter (fun a => (a:ℕ) = i*e + j)).card`, i.e. the count of elements of `S`
  landing in block `i`; the product is over `i ∈ Finset.range ℓ`. This avoids
  constructing `Fin n` indices with side-condition proofs while giving exactly the
  intended polynomial values on the slice.

## Uncertainties

- **Guessed Mathlib identifiers**: `MvPolynomial.eval`, `MvPolynomial.totalDegree`
  (used as `p.totalDegree`), `Finset.filter` argument order (`s.filter p`),
  `Finset.range`, `∏ i ∈ s, …` / `∑ j ∈ s, …` `BigOperators` notation. These match
  current Mathlib to the best of my knowledge but were not compiler-checked.
- **Family theorem faithfulness**: I transcribed the problem's parenthetical
  literally as `¬ IsJunta (ℓ * min d k) (familyFun …)`. I could not verify from
  memory that `familyFun` is genuinely Boolean and genuinely degree `≤ d` on the
  slice for all `1 ≤ k < 2d` in this exact index regime, nor that "not an `ℓe`-junta"
  is literally correct (the natural reading of the tightness claim is that the
  *minimal* junta size grows like `ℓe`, i.e. the functions are not `(ℓe−1)`-juntas /
  admit no uniform bound as `ℓ → ∞`). Theorems 1 and 2 are the parts I am confident
  are faithful; Theorem 3 is a best-effort literal transcription of the witnessing
  family and its stated properties.
- The forward theorem's `m` is existentially bound with no explicit value; the source
  ("there is a constant `m(d)`") is matched but the bound itself is not exhibited.
