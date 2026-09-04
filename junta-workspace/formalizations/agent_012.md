# Agent 012 — formalization note

## What is stated

All three components, statement-only, each `:= by sorry`:

1. `boolean_degLE_isJunta` — positive direction.
2. `exists_boolean_degLE_not_isJunta` — negative direction (pure existence, for every `m`).
3. `witnessFun_spec` — the explicit witnessing family and its properties.

## Encoding decisions

- **Ground set / coordinates.** Coordinates are `ℕ`; the ground set of `binom([n],k)`
  is `Finset.range n`. This avoids all `Fin n` bound arithmetic and lets the
  explicit polynomial be indexed by raw naturals `i * e + j` with no `< n` proof
  obligations inside the definition.
- **Slice.** `Slice n k := {S : Finset ℕ // S ⊆ Finset.range n ∧ S.card = k}`
  (subtype). Points of the slice are `k`-subsets of `range n`.
- **Boolean codomain.** Real-valued functions `Slice n k → ℝ` together with a
  predicate `IsBoolean f : ∀ S, f S = 0 ∨ f S = 1`. Chosen (over `Bool`/`Fin 2`)
  because "degree" is naturally about real polynomials and no coercion friction
  is introduced.
- **Degree `≤ d`.** `HasSliceDegreeLE d f`: there exists `p : MvPolynomial ℕ ℝ`
  that is multilinear (`IsMultilin`), has `p.totalDegree ≤ d`, and agrees with `f`
  on every slice point after evaluation at the `0/1` indicator vector
  (`MvPolynomial.eval (ind S.1) p`). This matches the problem's phrasing
  "agrees on the slice with a multilinear real polynomial of total degree `≤ d`
  evaluated at the indicator vector."
- **Multilinear.** No Mathlib predicate for "multilinear `MvPolynomial`" is known
  to me, so `IsMultilin p := ∀ μ ∈ p.support, ∀ t, μ t ≤ 1` (every monomial
  squarefree). Included for faithfulness; it is equivalent to dropping it in the
  degree definition, since on `0/1` inputs `xᵢ² = xᵢ` reduces degree.
- **`m`-junta.** `IsJunta m f`: `∃ J : Finset ℕ, J.card ≤ m ∧ ∀ S T, S.1 ∩ J = T.1 ∩ J → f S = f T`.
- **`m(d)`.** Existential *inside* the statement (`∃ m : ℕ, ...`), with `m`
  chosen before `k`, `n`, `f` so it depends only on `d` — i.e. it is the constant
  `m(d)` of the theorem.
- **Carrying `n, k, d`.** Plain `ℕ` arguments/binders; hypotheses `1 ≤ d`,
  `2*d ≤ k`, `2*k ≤ n` (positive) and `1 ≤ k`, `k < 2*d`, `2*k ≤ n` (negative).

## Explicit family

`witnessPoly d k = ∏_{i ∈ range k} ∑_{j ∈ range (min d k)} X (i * min d k + j)`,
i.e. the family `∏_{i=1}^{ℓ}(Σ_{j=1}^{e} x_{(i-1)e+j})` with `e = min d k` and the
number of blocks fixed to `ℓ = k`. `witnessFun d k n` is its restriction to the
slice. `witnessFun_spec` asserts, for `1 ≤ k < 2d` and `n ≥ 2·k·e`: Boolean,
slice-degree `≤ d`, and `¬ IsJunta (k·e − 1)`.

## Uncertainties / deviations

- **`ℓ` fixed to `k`.** With disjoint blocks on a weight-`k` slice, the block
  counts sum to `≤ k`; the product `∏` is `0/1`-valued only when `ℓ = k` (then
  every nonzero term forces one point per block). For `ℓ < k` the product is not
  Boolean and for `ℓ > k` it is identically `0`. So I hard-code `ℓ = k`, which I
  believe is the intended regime; the problem text's free `ℓ` is, I think, meant
  with `ℓ = k`.
- **`k·e − 1` vs "not `ℓe`-juntas".** Under my `IsJunta`, `witnessFun` trivially
  *is* a `(k·e)`-junta (take `J` = the `k·e` block coordinates it mentions), so I
  state the sharp true fact `¬ IsJunta (k·e − 1)` ("it really needs all `k·e`
  block coordinates"). The source's "not `ℓe`-juntas" presumably uses an
  off-by-one or a strict-inequality junta convention.
- **`for every m` and the explicit family.** With `ℓ = k` fixed and `k < 2d`, the
  explicit family has only `k·e ≤ (2d−1)·d` relevant coordinates, so on its own
  it yields non-juntas of bounded size, not "for every `m`". I still state the
  negative direction at full strength (`∀ m`), trusting the paper; the family
  theorem is the weaker concrete companion fact.
- **Slice-degree reduction.** `witnessPoly` has total degree `k > d`; that
  `witnessFun` nonetheless has slice-degree `≤ d` (when `k < 2d`) is exactly the
  paper's construction and is left to `sorry`.
- **Guessed Mathlib identifiers:** `MvPolynomial.eval`, `MvPolynomial.X`,
  `MvPolynomial.totalDegree`, `MvPolynomial.support` (for `p.support` returning
  `Finset (ℕ →₀ ℕ)`), big-operator notation `∏ i ∈ s, _` / `∑ j ∈ s, _`,
  `Finset.range`, `Finset` `∩`. These are standard; exact names/namespacing are
  my best recollection.
