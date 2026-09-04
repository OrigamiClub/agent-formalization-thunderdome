# Agent 025 — formalization note

## What is stated

All three pieces, as separate `theorem`s (statement only, `:= by sorry`):

1. `boolean_degree_junta` — the positive direction: for each `d ≥ 1` there exists `m : ℕ`
   working for all `k ≥ 2d`, `n ≥ 2k`.
2. `boolean_degree_not_junta` — the negative direction as a pure existential (for `1 ≤ k < 2d`,
   for every `m` there is a non-`m`-junta Boolean degree-`d` function).
3. `familyFun_witness` — the explicit witnessing family
   `∏_{i=1}^{ℓ}(∑_{j=1}^{e} x_{(i-1)e+j})`, `e = min d k`, with the three claims
   (Boolean, degree `≤ d` on the slice, not an `m`-junta for any `m < ℓe`).

Theorem 2 is morally a corollary of Theorem 3, but is stated independently to match the
phrasing of the problem.

## Encoding decisions

- **Slice**: `Slice n k := {S : Finset (Fin n) // S.card = k}` — subtype of `Finset (Fin n)`.
  Ambient coordinate set is `Fin n`; `n`, `k`, `d`, `ℓ` are plain `ℕ` arguments with the
  inequalities (`1 ≤ d`, `2*d ≤ k`, `k < 2*d`, `2*k ≤ n`, `2*ℓ*min d k ≤ n`) as hypotheses.
- **Boolean codomain**: functions are `Slice n k → ℝ` together with a predicate
  `IsBoolean f := ∀ S, f S = 0 ∨ f S = 1`. Chosen over `Bool` / `Fin 2` / `ZMod 2` so that
  polynomial evaluation needs no coercion and "agrees with a real polynomial" is literal.
- **Degree ≤ d**: `HasDegreeLE f d` says there is `p : MvPolynomial (Fin n) ℝ` that is
  multilinear (`∀ i, p.degreeOf i ≤ 1`), has `p.totalDegree ≤ d`, and satisfies
  `eval (charVec S.1) p = f S` for every slice point, where
  `charVec S i = if i ∈ S then 1 else 0`. Multilinearity is included to match the phrase
  "multilinear real polynomial" in the statement; it is WLOG on the cube and does not change
  the mathematical content.
- **m-junta**: `IsJunta f m := ∃ J : Finset (Fin n), J.card ≤ m ∧ ∀ S T, S.1 ∩ J = T.1 ∩ J → f S = f T`
  ("value determined by `S ∩ J`").
- **m(d)**: existential *inside* the statement (`∃ m : ℕ, …`), one per `d`, matching
  "there is a constant m(d)". Not exposed as an explicit `m : ℕ → ℕ`.
- **Explicit family**: `familyPoly n d k ℓ` is a `Finset.range` product of `Finset.range` sums
  over `0`-based indices; the coordinate `i*e + j` is injected into `Fin n` via a `dite`
  guard (`if h : i*e+j < n then X ⟨_, h⟩ else 0`) so the definition is total and self-contained.
  The hypothesis `2*ℓ*min d k ≤ n` guarantees all used indices are in range (and the slice is
  large enough), and `2*k ≤ n` keeps the slice non-empty even when `ℓ = 0`.

## Deliberate deviation

The problem says the family members "are not `ℓe`-juntas". Taken literally that is false: a
function whose value is defined from the `ℓe` named coordinates `x_1,…,x_{ℓe}` *is* an
`ℓe`-junta (take `J = {1,…,ℓe}`). The intended and true claim is that they need *all* `ℓe`
coordinates, i.e. they are not `(ℓe − 1)`-juntas. I formalized the stronger, faithful form:
`∀ m < ℓ * min d k, ¬ IsJunta (familyFun …) m`.

## Uncertainties / guessed identifiers

- `MvPolynomial.degreeOf`, `MvPolynomial.totalDegree`, `MvPolynomial.eval`, `MvPolynomial.X`:
  believed correct current Mathlib names (high confidence). `p.degreeOf i` relies on dot
  notation placing `p` at the `MvPolynomial` argument of `degreeOf i p`.
- `open scoped BigOperators` is kept for the `∏ / ∑ … ∈ Finset.range …` notation; on recent
  Mathlib this open may be redundant/deprecated but should not be an error.
- I am not aware of a native Mathlib API for "the slice", "Boolean degree-`d` function", or
  "junta", so all four notions are defined from scratch here.
- No claim about tightness of the constants beyond what the statement asserts; `d ≥ 1` is the
  only lower bound imposed on `d`.
