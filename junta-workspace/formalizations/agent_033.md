# Agent 033 — formalization note

## What I stated

All three pieces, statement-only (`:= by sorry`, nothing proved):

1. `boolean_degree_d_on_slice_is_junta` — the **forward** direction. `m` is an
   explicit `∃ m : ℕ → ℕ` at the head of the statement (matching "there is a constant
   `m(d)`"), followed by `∀ d ≥ 1, ∀ k ≥ 2d, ∀ n ≥ 2k, ∀ f`, Boolean + degree ≤ d ⇒
   `m d`-junta.
2. `no_junta_bound_below_2d` — the **converse**, in its clean form: for `1 ≤ k < 2d`
   and every `m`, there exist `n ≥ 2k` and a Boolean degree-`d` function that is not an
   `m`-junta.
3. `witness_family_not_junta` — the **explicit family**
   `∏_{i=1}^{ℓ}(∑_{j=1}^{e} x_{(i-1)e+j})`, `e = min d k`: its slice restriction is
   Boolean, has degree ≤ d, and is not an `m`-junta for any `m < ℓ·e`.

## Encoding decisions

- **Slice**: `Slice n k := {S : Finset (Fin n) // S.card = k}`. Direct, gives easy
  access to `S ∩ J` via `Finset.inter` and to indicator vectors.
- **Boolean codomain**: functions `Slice n k → ℝ` together with a predicate
  `IsBooleanValued f := ∀ S, f S = 0 ∨ f S = 1`. Chosen over `Bool`/`Fin 2`/`ZMod 2`
  so that "degree ≤ d" can be phrased with a single real polynomial and `MvPolynomial.eval`
  with no coercion friction.
- **Degree ≤ d**: `HasSliceDegreeLE f d := ∃ p : MvPolynomial (Fin n) ℝ,
  p.totalDegree ≤ d ∧ ∀ S, f S = MvPolynomial.eval (indicator S) p`, where
  `indicator S i = if i ∈ S.1 then 1 else 0`. This is the "agrees on the slice with a
  real polynomial of total degree ≤ d evaluated at the 0/1 indicator vector"
  definition. Multilinearity is not imposed: over `{0,1}` any polynomial can be
  multilinearized without raising total degree, so the two formulations agree.
- **m-junta**: `IsJunta f m := ∃ J : Finset (Fin n), J.card ≤ m ∧
  ∀ S T, S.1 ∩ J = T.1 ∩ J → f S = f T`. "Value depends only on `S ∩ J`."
- **`m(d)`**: existential `∃ m : ℕ → ℕ` inside the forward statement.
- **n, k, d**: plain `ℕ` arguments; ambient coordinate set is `Fin n`. Hypotheses
  `1 ≤ d`, `2*d ≤ k`, `2*k ≤ n` (resp. `1 ≤ k`, `k < 2*d`) as bare inequalities.
- **Explicit family**: `witnessPoly e ℓ n : MvPolynomial (Fin n) ℝ` as
  `∏ i ∈ range ℓ, ∑ j ∈ range e, X ⟨i*e+j, _⟩`. Zero-indexed reindexing of the
  1-indexed formula in the prompt (`i-1 ↦ i ∈ range ℓ`, `j ↦ j ∈ range e`, variable
  index `i*e + j` running over `0 … ℓe-1`). Out-of-range indices are guarded by a
  `dite` returning `0` (they never fire once `ℓ*e ≤ n`, which follows from
  `2*(ℓ*e) ≤ n`). `witnessFun` is its slice restriction.

## Uncertainties

- **"not `ℓ·e`-juntas"** in the prompt is, taken literally, false: `witnessFun`
  depends only on the `ℓ·e` variables `x_0,…,x_{ℓe-1}`, hence *is* an `ℓ·e`-junta. I
  read the intended claim as "junta size exactly `ℓ·e`", i.e. **not an
  `(ℓ·e − 1)`-junta**, and stated the slightly stronger/cleaner
  `∀ m < ℓ·e, ¬ IsJunta … m`. This is also exactly what feeds the converse
  (`no_junta_bound_below_2d`) via `ℓ` chosen with `ℓ·e > m`.
- **Booleanity of the literal product-of-sums witness.** For some parameter regimes
  the raw product `∏_i (∑_j x_{i·e+j})` can take values outside `{0,1}` on the slice
  (e.g. a block meeting `S` in two elements while all `ℓ` blocks are still met). The
  paper's construction is Boolean on the slices it targets; I transcribed the formula
  as given and kept `IsBooleanValued (witnessFun …)` as a *claim* of the theorem (it is
  under `sorry`). If the precise paper witness differs by a normalization / squared
  differences `∏ (x_{2i-1} − x_{2i})²`, only `witnessPoly` would need adjusting; the
  surrounding statement shapes are unaffected.
- **Mathlib identifiers** used (from memory, not compiler-checked):
  `MvPolynomial`, `MvPolynomial.totalDegree`, `MvPolynomial.eval`, `MvPolynomial.X`,
  `Finset.card`, `Finset.range`, `∏ … ∈ …` / `∑ … ∈ …` big-operator notation,
  `Finset` intersection `∩`. `import Mathlib` (whole library) to stay self-contained.
- No claim is made that any `sorry` is provable; several would require the actual
  Filmus–Ihringer proof (forward) or the correct witness analysis (converse).
