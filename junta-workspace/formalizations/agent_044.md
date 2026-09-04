# Agent 044 — formalization note

## What I stated

All three of:

1. `filmus_ihringer_forward` — the junta bound for `k ≥ 2d`.
2. `filmus_ihringer_converse` — pure-existence failure of any uniform junta bound for `1 ≤ k < 2d`.
3. `filmus_ihringer_converse_witness` — the same converse, but naming the explicit
   witnessing family.

Everything is statement-only; every `theorem` ends in `:= by sorry`, and no proofs
(not even for auxiliary defs) are given.

## Encoding decisions

- **Slice**: `abbrev Slice n k := {S : Finset (Fin n) // S.card = k}`. Subtype of
  `Finset (Fin n)`; `abbrev` (not `def`) so `.val` / `.property` and defeq unfolding
  work transparently in the statements. Coordinates are `Fin n`, i.e. `{1,…,n}`.
- **Boolean codomain**: `Bool`. Cleanest "two-valued" choice; coerced to `ℝ` as
  `if f S then 1 else 0` only where a real value is needed (the polynomial-agreement
  condition).
- **Degree ≤ d**: `BooleanDegreeLE d f` = there is `p : MvPolynomial (Fin n) ℝ` with
  `p.totalDegree ≤ d` agreeing with `f` (as a `0/1` real) at the indicator vector
  `indicator S = fun i => if i ∈ S then 1 else 0`, for every slice point `S`.
  I did **not** impose multilinearity on `p`: on `0/1` inputs every polynomial agrees
  with its multilinearization, whose total degree is no larger, so the two formulations
  give the same class. This matches the "agrees on the slice with a multilinear real
  polynomial of total degree ≤ d" wording.
- **m-junta**: `IsJunta m f` = there is `J : Finset (Fin n)` with `J.card ≤ m` such that
  `S.val ∩ J = T.val ∩ J → f S = f T`. This is exactly "value depends only on `S ∩ J`".
- **m(d)**: existential *inside* the forward statement (`∃ m : ℕ, …`) rather than an
  explicit `m : ℕ → ℕ`. The theorem only asserts a constant exists; leaving it
  existential avoids committing to a particular (non-canonical) bound.
- **n, k, d, ambient set**: all carried as explicit `ℕ` arguments, universally quantified
  in each theorem; ambient coordinate type is `Fin n`. `n`, `k` are implicit in the
  defs (`BooleanDegreeLE`, `IsJunta`), inferred from the function's type.

## The explicit family — interpretation and caveat

The prompt renders the family as `∏_{i=1}^{ℓ} (Σ_{j=1}^{e} x_{(i-1)e+j})` with
`e = min(d,k)`. Taken literally (product of the `ℓ` block-sums), that expression is
**not** `{0,1}`-valued on the slice (e.g. `k=3`, `e=2`, `ℓ=2`, `S={1,2,3}` gives
`2·1 = 2`), and it is identically `0` whenever `ℓ > k`, so it could not witness
non-`m`-juntas for large `m`.

The construction that *is* Boolean, has degree `≤ d`, and fails every fixed junta bound
is the **sum of products** — the number of blocks lying entirely inside `S`:
`f(S) = Σ_{i=1}^{ℓ} ∏_{j=1}^{e} x_{(i-1)e+j}`. Its multilinear degree is
`e = min(d,k) ≤ d`. It is `{0,1}`-valued precisely because `k < 2·min(d,k)` (checked:
`k ≤ d ⇒ e = k < 2k`; `d < k ⇒ e = d`, and `k < 2d` is the hypothesis), so a `k`-set
contains at most one full block. For `n ≥ 2ℓe` it depends on all `ℓe` block coordinates,
so choosing `ℓe > m` makes it not an `m`-junta. This is what I formalized in
`filmus_ihringer_converse_witness`.

I quantified over an **arbitrary** family `B : Fin ℓ → Finset (Fin n)` of pairwise
disjoint size-`e` blocks (rather than hard-coding the consecutive blocks
`{(i-1)e+1, …, ie}`). This keeps the statement free of `Fin n` bound-arithmetic, and the
consecutive layout is one instance. The witness `f` is pinned by
`∀ S, f S = decide (∃ i, B i ⊆ S.val)`.

## Uncertainties / guessed identifiers

- `MvPolynomial`, `MvPolynomial.totalDegree`, `MvPolynomial.eval` — standard Mathlib,
  high confidence. `MvPolynomial.eval` is applied as `MvPolynomial.eval v p`.
- `Finset.card`, `Finset.inter` (`∩` on `Finset`), `Disjoint`, `decide`,
  `Fintype.decidableExistsFintype` (for `decide (∃ i : Fin ℓ, …)`) — standard; the
  `Decidable` instance for `∃ i, B i ⊆ S.val` should be found automatically.
- No claim that these `sorry`-ed statements are provable as written; in particular the
  forward direction's `m` is left existential and the witness theorem asserts the three
  properties of `f` without constructing the degree-`e` polynomial explicitly (it is
  `∑ i, ∏ j ∈ B i, MvPolynomial.X j`).
