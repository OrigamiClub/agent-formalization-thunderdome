# Agent 013 — formalization note

## What I stated

Both directions, plus the explicit witnessing family, in three declarations:

- `filmus_ihringer (d) (hd : 1 ≤ d)` — a conjunction:
  - **forward**: `∃ M : ℕ, ∀ k n, 2*d ≤ k → 2*k ≤ n → ∀ f, BooleanDegreeLE d f → IsJunta M f`;
  - **converse**: `∀ k, 1 ≤ k → k < 2*d → ∀ m, ∃ n ≥ 2*k, ∃ f, BooleanDegreeLE d f ∧ ¬ IsJunta m f`.
- `filmus_ihringer_explicit` — the family `∏_{i=1}^{ℓ} (∑_{j=1}^{e} x_{(i-1)e+j})`, `e = min d k`,
  asserted (for `1 ≤ k < 2d`, `n ≥ 2ℓe`) to be `{0,1}`-valued on the slice, of Boolean degree ≤ `d`,
  and not an `ℓe`-junta.

All bodies are `:= by sorry`. Nothing is proved.

## Encoding decisions

- **Slice**: `Slice n k := {S : Finset (Fin n) // S.card = k}`. `{1,…,n}` is `Fin n`.
  Chose the subtype of `Finset` because intersection `S ∩ J` (needed for the junta
  definition) is directly available and cheap.
- **Boolean codomain**: `Bool`. The "value in `{0,1}`" appears where it matters — inside
  `BooleanDegreeLE` as `if f S then (1:ℝ) else 0`, and in the explicit theorem as an
  explicit `eval … = 0 ∨ eval … = 1` disjunction.
- **Degree ≤ d**: `BooleanDegreeLE d f` = `∃ p : MvPolynomial (Fin n) ℝ`, `IsMultilinear p`,
  `p.totalDegree ≤ d`, and `MvPolynomial.eval (indicator S) p = (if f S then 1 else 0)` for
  every slice point. `indicator S i = if i ∈ S then 1 else 0`. I included an explicit
  multilinearity predicate `IsMultilinear p := ∀ t ∈ p.support, ∀ i, t i ≤ 1` to match the
  wording "multilinear real polynomial". (It is redundant — on `{0,1}` inputs any polynomial
  reduces to a multilinear one of no larger total degree — but harmless and faithful.)
- **m-junta**: `IsJunta m f` = `∃ J : Finset (Fin n)`, `J.card ≤ m`, and
  `∀ S T, S ∩ J = T ∩ J → f S = f T`. This is the "value depends only on `S ∩ J`" formulation.
- **m(d)**: existential *inside* the statement (`∃ M : ℕ, …`), since `d` is already fixed by
  the outer binder; matches "there is a constant `m(d)`".
- **n, k, d**: plain `ℕ` binders; ambient coordinate type `Fin n` derived from `n`. Bounds
  written `2 * d ≤ k`, `2 * k ≤ n`, `k < 2 * d`.
- **Explicit family**: to avoid `Fin`-index arithmetic side goals in a definition, block `i`
  is `blockSum n e i := ∑ c ∈ univ.filter (fun c => i*e ≤ c ∧ c < (i+1)*e), X c`, and
  `fiFamily n ℓ e := ∏ i ∈ range ℓ, blockSum n e i`. For `n ≥ 2ℓe` (the theorem hypothesis)
  every block is full with `e` coordinates and blocks are pairwise disjoint. The Boolean
  function `g` is pinned down by a hypothesis `hg : g S = decide (eval (indicator S) (fiFamily …) = 1)`
  rather than by a `let`, to keep the statement readable.

## Uncertainties

- Mathlib identifiers used from memory: `MvPolynomial`, `MvPolynomial.eval`,
  `MvPolynomial.X`, `MvPolynomial.totalDegree`, `MvPolynomial.support` (support is a
  `Finset (Fin n →₀ ℕ)`, so `t i` is the exponent of variable `i`), `Finset.filter`,
  `Finset.range`, `Finset.univ`, `∑ … ∈ …`, `∏ … ∈ …`. Names/argument order not
  compiler-checked.
- `IsMultilinear` is my own local definition (name may collide with a Mathlib notion for
  multilinear maps, but it is namespaced under `AgentO13`).
- The problem's phrasing "witnessed by functions ∏…(Σ… x)" gives the polynomial but not an
  explicit reduction showing it is `{0,1}`-valued and degree ≤ `d` on the slice; I encoded
  those as asserted conclusions of `filmus_ihringer_explicit`. If the intended family is a
  sum-of-products or otherwise differs, `fiFamily` would need adjustment; I formalized the
  formula exactly as written (1-indexed `x_{(i-1)e+j}` ↦ 0-indexed coordinate `i*e + j`).
- `decide (… = 1)` presumes `Decidable` equality on `ℝ` via `Classical`; `import Mathlib`
  brings classical instances, so this should elaborate, but I could not verify.
