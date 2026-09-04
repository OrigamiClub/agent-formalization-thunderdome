# Agent 024 — formalization note

## What I stated

All three of:

1. `filmus_ihringer_forward` — the forward direction: for `d ≥ 1` there **exists** a
   bound `M` such that for all `k ≥ 2d`, all `n ≥ 2k`, every Boolean degree-`d` function
   on `binom([n],k)` is an `M`-junta.
2. `filmus_ihringer_converse` — the converse as a pure existence statement: for `d ≥ 1`,
   any `k` with `1 ≤ k < 2d`, and any `m`, there exist `n ≥ 2k` and a Boolean degree-`d`
   function on `binom([n],k)` that is not an `m`-junta.
3. `filmus_ihringer_witness` — the converse **with the explicit family**
   `∏_{i=1}^{ℓ}(∑_{j=1}^{e} x_{(i-1)e+j})`, `e = min d k`, asserting (literally, as the
   source phrases it) that for `n ≥ 2ℓe` these functions are Boolean, degree `≤ d`, and
   not `ℓe`-juntas.

## Encoding decisions

- **Slice**: `abbrev Slice n k := {S : Finset (Fin n) // S.card = k}`. Subtype of
  `Finset (Fin n)`; `abbrev` keeps it reducible so `.val`/`.property` and instance
  resolution work transparently. Ambient coordinate set is `Fin n`; `n`, `k`, `d` are
  explicit `ℕ` arguments carried by each theorem.
- **Boolean codomain**: functions are `Slice n k → ℝ` together with a predicate
  `IsBoolean f : ∀ S, f S = 0 ∨ f S = 1`. Real-valued (rather than `Bool`/`Fin 2`) so
  that "agrees with a real polynomial" is stated directly without coercions.
- **Degree ≤ d** (`HasDegreeLE`): `∃ p : MvPolynomial (Fin n) ℝ` with
  `p.totalDegree ≤ d`, `p` multilinear (`∀ mono ∈ p.support, ∀ i, mono i ≤ 1`), and
  `MvPolynomial.eval (charVec S.val) p = f S` for every slice point, where
  `charVec S i = if i ∈ S then 1 else 0`. Multilinearity is included to match the
  problem statement verbatim; it is in fact WLOG on `{0,1}`-inputs (reduce `x_i^2 ↦ x_i`),
  so dropping that conjunct would give an equivalent notion.
- **m-junta** (`IsJunta f m`): `∃ J : Finset (Fin n)`, `J.card ≤ m`, and
  `S.val ∩ J = T.val ∩ J → f S = f T`. This is the "value depends only on `S ∩ J`"
  formulation.
- **m(d)**: existential *inside* the statement (`∃ M : ℕ, …`), rather than an explicit
  `m : ℕ → ℕ`. The theorem only claims existence of the bound.
- **Explicit family**: `witnessPoly n ℓ e : MvPolynomial (Fin n) ℝ` is
  `∏_{i<ℓ} ∑_{j<e} X (i*e+j)` with a dependent `if` guarding the `Fin n` bound (out-of-range
  indices contribute `0`; irrelevant once `n ≥ ℓe`). `witnessFun n k ℓ e` is its evaluation
  at `charVec`. Indexing is 0-based: block `i` (`i < ℓ`) owns coordinates
  `i*e, …, i*e+e-1`, so the used coordinates are exactly `{0, …, ℓe-1}`.

## Uncertainties / caveats

- **Mathlib identifiers** used (from memory, not compiler-checked):
  `MvPolynomial (Fin n) ℝ`, `MvPolynomial.X`, `MvPolynomial.eval`,
  `MvPolynomial.totalDegree`, `MvPolynomial.support`, `Finset.card`, `Finset.range`,
  `Finset.inter` (via `∩`), `∑`/`∏` big-operator notation over `Finset.range`. The coercion
  `mono i` for `mono : Fin n →₀ ℕ` relies on the `Finsupp` `FunLike` instance.
- **`filmus_ihringer_witness` is a literal transcription** of the source's sentence and I
  did **not** verify it. One tension: `witnessFun n k ℓ e` manifestly depends only on the
  `ℓe` "block" coordinates, so read literally it *is* an `ℓe`-junta. The source almost
  certainly means these functions depend on *all* `ℓe` coordinates (i.e. are not
  `(ℓe−1)`-juntas), which is what makes `m(d)` provably large when `k < 2d`. I kept the
  literal `¬ IsJunta … (ℓ * e)` as written; a reader may prefer `ℓ * e - 1`. The clean
  content of the converse is captured independently by `filmus_ihringer_converse`.
- I did not attempt to encode a possible extra hypothesis `n - k` large (the abstract of
  the paper mentions `k` and `n-k` large); the task's threshold `n ≥ 2k` is used as given.
