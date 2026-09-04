# Agent 079 — formalization note

## What is stated

All three pieces, statement-only, each `:= by sorry`:

1. `filmus_ihringer_forward` — positive direction: `∃ m`, for all `k ≥ 2d`, `n ≥ 2k`,
   every Boolean degree-`≤ d` function on `binom([n],k)` is an `m`-junta.
2. `filmus_ihringer_converse` — sharpness, clean existential form: for `1 ≤ k < 2d`
   and every `m`, some `n ≥ 2k` carries a Boolean degree-`≤ d` non-`m`-junta.
3. `filmus_ihringer_converse_explicit` — sharpness with the explicit family `gFamily`.

## Encoding decisions

- **Slice**: `Slice n k := {S : Finset (Fin n) // S.card = k}`. Coordinates are
  `Fin n`; a point of the slice is a `k`-element `Finset`. Straightforward, keeps
  `S ∩ J` literally as `Finset.inter`.
- **Boolean codomain**: real-valued functions with `IsBoolValued f : ∀ x, f x = 0 ∨ f x = 1`.
  Chosen over `Bool`/`Fin 2` so that "degree" can be phrased directly via real
  polynomials without a coercion layer.
- **Degree `≤ d`** (`HasDegreeLE`): `∃ p : MvPolynomial (Fin n) ℝ` with
  `p.totalDegree ≤ d` that agrees with `f` at every characteristic vector
  `charVec S.1 : Fin n → ℝ` (`0/1`-valued) over the whole slice. This is the
  "agrees on the slice with a total-degree-`≤ d` real polynomial evaluated at the
  indicator vector" definition from the problem statement. Multilinearity is not
  imposed: it is automatic up to agreement at `0/1` points, so omitting it gives
  the same predicate and a simpler statement.
- **`m`-junta** (`IsJunta`): `∃ J : Finset (Fin n)`, `J.card ≤ m`, and
  `S.1 ∩ J = T.1 ∩ J → f S = f T`. Direct reading of "value depends only on `S ∩ J`".
- **`m(d)`**: existential *inside* the statement (`∃ m : ℕ`), with `d` a theorem
  parameter. Equivalent to an explicit `m : ℕ → ℕ` but lighter.
- **Carrying `n, k, d`**: universally quantified `ℕ` with hypotheses `1 ≤ d`,
  `2*d ≤ k`, `k < 2*d`, `2*k ≤ n` as appropriate; ambient coordinate type is
  `Fin n`, threaded through `Slice n k`.
- **Explicit family** `gFamily n k d ℓ`: with `e = min d k`, block `i` (`i < ℓ`) is
  the coordinate range `{i*e, …, i*e+e-1}`, and
  `gFamily S = ∑_{i<ℓ} ∏_{j<e} [ i*e+j ∈ S ]` (indicators in `ℝ`). Membership of a
  natural number index is tested against `S.1.map Fin.valEmbedding : Finset ℕ`,
  which avoids constructing `Fin n` elements with side conditions inside the `def`.
  Non-junta claim: `∀ m < ℓ*e, ¬ IsJunta (gFamily …) m`, under `n ≥ 2·ℓ·e`.

## Uncertainties

- **Operator reading in the witnessing family.** The prompt writes the witnesses as
  `∏_{i=1}^{ℓ} (Σ_{j=1}^{e} x_{(i-1)e+j})` (outer product of inner sums). Taken as
  literal arithmetic this is *not* Boolean on the slice (e.g. `ℓ=1`, `d,k ≥ 2`:
  the value `x_1+⋯+x_e` reaches `2`), so it cannot be the intended "Boolean
  degree-`d`" family. I encoded the arithmetic **sum of products**
  `Σ_{i} ∏_{j} x_{(i-1)e+j}` (OR-of-ANDs), which *is* `0/1`-valued on the slice
  precisely because `k < 2d` with `e = min d k` forbids two disjoint `e`-blocks in a
  `k`-set, and which collapses to total degree `e ≤ d` on the slice for the same
  reason (all products of `≥ 2` block-monomials vanish there). I believe this is the
  actual Filmus–Ihringer tightness construction and that the prompt swapped `∏`/`Σ`.
- **"not `ℓe`-juntas".** As a function `gFamily` reads exactly the `ℓe` block
  coordinates, so it *is* an `ℓe`-junta; the meaningful (and, I believe, intended)
  claim is that every block coordinate is pivotal, i.e. it is not an `(ℓe−1)`-junta,
  and hence — taking `ℓ` large — not an `m`-junta for any fixed `m`. I stated
  `∀ m < ℓ*min d k, ¬ IsJunta … m`, which is this reading and is exactly what feeds
  the clean converse.
- **Mathlib identifiers** (from memory, not compiler-checked): `MvPolynomial.eval`,
  `MvPolynomial.totalDegree`, `Finset.map`, `Fin.valEmbedding : Fin n ↪ ℕ`,
  `Finset.range`, `Finset.inter` (as `∩`). `Fin.valEmbedding` is the one I am least
  sure of by exact name; if absent, `⟨Fin.val, Fin.val_injective⟩` is the drop-in
  replacement.
- No claim is made that the three theorems are provable as literally stated beyond
  faithfulness to the prompt; in particular `HasDegreeLE (gFamily …) d` relies on the
  slice-degree collapse described above.
