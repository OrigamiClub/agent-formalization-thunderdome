# Agent 045 — formalization note

## What I stated

**Both directions**, as two separate theorems, with the non-junta witness left
**existential** (the explicit product family is *not* encoded):

- `boolean_degree_d_is_junta` — positive direction. `d ≥ 1`, `∃ m : ℕ` (the `m(d)`),
  then `∀ k ≥ 2d, ∀ n ≥ 2k`, every `BooleanValued` `HasDegreeLE _ d` function on
  `Slice n k` satisfies `IsJunta _ m`.
- `boolean_degree_d_not_junta` — tightness direction. `d ≥ 1`, `1 ≤ k < 2d`, then
  `∀ m, ∃ n ≥ 2k, ∃ f`, with `f` Boolean, degree `≤ d`, and `¬ IsJunta f m`.

## Encoding decisions

- **Slice**: `abbrev Slice n k := {S : Finset (Fin n) // S.card = k}`. Subtype of
  `Finset (Fin n)`; `abbrev` so that `.1` / subtype defeq unfolds transparently.
  Ambient coordinate set is `Fin n`; `n, k, d` are plain `ℕ` hypotheses, inequalities
  written `2 * d ≤ k`, `2 * k ≤ n` (i.e. `k ≥ 2d`, `n ≥ 2k`).
- **Boolean codomain**: functions are `Slice n k → ℝ` with a side predicate
  `BooleanValued f : ∀ S, f S = 0 ∨ f S = 1`. Chosen (over `Bool` / `Fin 2` / `ZMod 2`)
  so the same `f` can be fed directly to the polynomial-agreement condition without
  coercions.
- **Degree ≤ d**: `HasDegreeLE f d` = `∃ p : MvPolynomial (Fin n) ℝ` with
  `p.totalDegree ≤ d`, `∀ i, MvPolynomial.degreeOf i p ≤ 1` (multilinearity), and
  `∀ S, f S = MvPolynomial.eval (sliceIndicator S) p`, where `sliceIndicator S i =
  if i ∈ S.1 then 1 else 0`. The multilinearity clause matches the problem text
  ("agrees ... with a multilinear real polynomial"); on the slice it is not a genuine
  restriction (`x_i^2 = x_i`), so dropping it would give an equivalent statement.
- **m-junta**: `IsJunta f m` = `∃ J : Finset (Fin n), J.card ≤ m ∧ ∀ S S',
  S.1 ∩ J = S'.1 ∩ J → f S = f S'`. "Depends only on `S ∩ J`" rendered as: equal
  intersections force equal values.
- **`m(d)`**: existential inside the positive statement (`∃ m : ℕ, ...`) rather than an
  explicit `m : ℕ → ℕ`, since the theorem only asserts existence of the bound.

## Uncertainties

- Guessed / relied-on Mathlib identifiers: `MvPolynomial.totalDegree`,
  `MvPolynomial.degreeOf` (argument order `degreeOf (i : σ) (p)`), `MvPolynomial.eval`
  (takes the point, then the polynomial, via a ring hom). Names and signatures are
  from memory; if `degreeOf` argument order differs the multilinearity clause needs
  swapping.
- **Explicit family deliberately omitted.** The problem's witness
  `∏_{i=1}^{ℓ}(Σ_{j=1}^{e} x_{(i-1)e+j})`, read literally as a polynomial, has total
  degree `ℓ` (a product of `ℓ` linear forms) and, on small slices, its values are not
  obviously in `{0,1}` — so under my naive reading it is neither manifestly degree `d`
  nor manifestly Boolean, and reconciling that presumably needs the slice identity
  `Σ x_i = k` plus a normalization I could not reconstruct with confidence. Rather than
  assert a possibly-false `theorem` about a concrete polynomial, I kept the non-junta
  witness existential. The mathematical content of the tightness claim ("for every `m`
  some Boolean degree-`d` non-`m`-junta exists") is fully captured.
- The hypothesis `1 ≤ d` (`hd`) is carried in both theorems though the positive one is
  also fine for `d = 0`; kept for faithfulness to "Let d ≥ 1".
