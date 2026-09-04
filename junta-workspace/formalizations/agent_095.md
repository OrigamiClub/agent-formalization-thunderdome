# Agent 095 — formalization note

## What I stated

All three pieces, statement-only, each `:= by sorry`:

1. `boolean_degree_d_is_junta` — the **forward** direction (`k ≥ 2d`): a constant `m(d)`
   works for all `k, n, f`.
2. `exists_boolean_degree_d_not_junta` — the **converse** (`1 ≤ k < 2d`) in plain
   existential form.
3. `exists_boolean_degree_d_not_junta_explicit` — the converse **with the explicit
   witnessing family** `∏_{i=1}^{ℓ}(∑_{j=1}^{e} x_{(i-1)e+j})`, `e = min d k`.

## Encoding decisions

- **Slice**: `abbrev Slice n k := {S : Finset (Fin n) // S.card = k}`. Subtype of
  `Finset (Fin n)`; simple, gives `S.1 : Finset (Fin n)` for intersections and
  membership. Ambient coordinate set is `Fin n`; `n, k, d` are plain `ℕ` arguments.
- **Boolean codomain**: functions are `Slice n k → ℝ` together with a predicate
  `IsBoolean f : ∀ S, f S = 0 ∨ f S = 1`. Keeping the codomain `ℝ` makes "agrees with a
  real polynomial" statable without coercions.
- **Degree ≤ d**: `HasDegreeLE f d` := `∃ p : MvPolynomial (Fin n) ℝ`, `p.totalDegree ≤ d`
  and `f` agrees with `sliceEval p` at every slice point, where
  `sliceEval p S = MvPolynomial.eval (fun i => if i ∈ S.1 then 1 else 0) p`.
  This is the "agrees on the slice with a total-degree-≤ d polynomial at the indicator
  vector" definition from the problem text. Note it does **not** require the witnessing
  polynomial to be the obvious one — this is what lets the degree-`ℓ` product
  `blockSumPoly` still count as degree `≤ d` on the slice.
- **m-junta**: `IsJunta f m` := `∃ J : Finset (Fin n)`, `J.card ≤ m`, and
  `S.1 ∩ J = T.1 ∩ J → f S = f T`. "Value depends only on `S ∩ J`."
- **`m(d)`**: existential *inside* the forward statement (`∃ m, ∀ k n f, …`), so it is a
  constant depending only on `d`. I did not introduce an explicit `m : ℕ → ℕ`.
- **Explicit family**: `blockSumPoly e ℓ n (h : 2*(ℓ*e) ≤ n) : MvPolynomial (Fin n) ℝ`
  `:= ∏ i : Fin ℓ, ∑ j : Fin e, X (Fin.castLE _ (finProdFinEquiv (i, j)))`.
  Block `i` occupies coordinates `i*e … i*e+e-1`. The `2*(ℓ*e) ≤ n` hypothesis
  encodes the paper's `n ≥ 2ℓe`. In statement 3, `ℓ` is chosen with `m < ℓ*e`, then the
  claim is quantified over all sufficiently large `n`; non-`ℓe`-junta ⟹ non-`m`-junta.

## Uncertainties / guessed identifiers

- `finProdFinEquiv : Fin m × Fin n ≃ Fin (m * n)` — name and orientation guessed. If its
  codomain is `Fin (e * ℓ)` rather than `Fin (ℓ * e)` the `Fin.castLE` side condition is
  handled by the `first | omega | (rw [Nat.mul_comm]; omega)` fallback I wrote.
- `omega` is assumed to atomize the nonlinear term `ℓ * e` so it can derive
  `ℓ * e ≤ n` from `2 * (ℓ * e) ≤ n`.
- `MvPolynomial.eval`, `MvPolynomial.X`, `MvPolynomial.totalDegree`, `Fin.castLE`,
  `Fin.isLt` — standard Mathlib, used as-is.
- **Faithfulness of the explicit family**: I transcribed
  `∏_{i=1}^{ℓ}(∑_{j=1}^{e} x_{(i-1)e+j})` literally from the problem text and assert
  (as conjuncts) that its slice restriction is Boolean, degree `≤ d`, and not an
  `ℓe`-junta. I did not independently verify these three properties from the
  Filmus–Ihringer paper; small-case sanity checks I ran by hand were inconclusive, so
  it is possible the intended construction has a different exact form (e.g. affine
  factors `∑ x_j - 1`, or a `{-1,1}` Boolean convention). The forward theorem and the
  plain converse (statements 1 and 2) do not depend on this.
- `import Mathlib` (whole library) for simplicity; not minimized.
