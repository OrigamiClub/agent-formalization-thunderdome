# agent_070 — Filmus–Ihringer, Boolean constant-degree functions on the slice are juntas

## What I stated

All three pieces, statement-only, each ending in `:= by sorry`:

1. `boolean_degree_d_on_slice_is_junta` — the **forward** direction.
2. `boolean_degree_d_on_slice_not_junta` — the **converse** direction.
3. `blockFamily` + `blockFamily_witnesses_non_junta` — the **explicit witnessing family**.

## Encoding decisions

- **Slice.** `Slice n k := {S : Finset (Fin n) // S.card = k}`. Coordinates are `Fin n`;
  a slice point is a `k`-subset. `n`, `k`, `d` are plain `ℕ` arguments carried explicitly.
- **Boolean codomain.** Functions are `Slice n k → ℝ` with a separate predicate
  `IsBooleanOnSlice f : ∀ S, f S = 0 ∨ f S = 1`. Real-valued is the natural choice because
  "degree" is defined through a *real* polynomial; keeping values in `{0,1} ⊆ ℝ` avoids
  coercions between `Bool`/`Fin 2` and `ℝ`.
- **Degree ≤ d.** `HasDegreeLE d f`: there exists `p : MvPolynomial (Fin n) ℝ` with
  `p.totalDegree ≤ d` such that for every slice point `S`,
  `f S = MvPolynomial.eval (fun i => if i ∈ S.1 then 1 else 0) p`
  (evaluation at the 0/1 indicator vector of `S`). I use "≤ d" (constant-degree), not "= d".
  I did **not** force `p` multilinear; on the slice one always can, and `totalDegree ≤ d`
  is the intended notion.
- **m-junta.** `IsJunta m f`: there is `J : Finset (Fin n)` with `J.card ≤ m` such that
  `S.1 ∩ J = T.1 ∩ J → f S = f T` for all slice points `S T`.
- **m(d).** Existential *inside* the forward statement: `∃ M : ℕ, ∀ k …`, with `M` bound
  before `k` and `n`, so it depends only on `d`.
- **Quantifier shape of the converse.** `∀ k, 1 ≤ k → k < 2*d → ∀ m, ∃ n, 2*k ≤ n ∧ ∃ f, …`,
  matching "if `1 ≤ k < 2d` then for every `m` there exist `n ≥ 2k` and a function …".
- **Explicit family.** Given combinatorially rather than via `MvPolynomial`, to avoid
  discharging `Fin n` index bounds inside the statement. With `e := min d k`, block `i` is
  `{a : Fin n | (a : ℕ) / e = i}` (the consecutive block `[i*e, i*e+e)`), and
  `blockFamily n k d ℓ S` is the number of blocks `i < ℓ` with `|S ∩ block i| = e`
  (i.e. `block i ⊆ S`). Indexed by a single natural number `ℓ`; `e = min d k` is inlined.

## Uncertainties / caveats

- **Reading of the family.** The prompt writes the witness as a *product over the `ℓ`
  blocks of a sum within each block*, `∏_{i}(Σ_{j} x_{(i-1)e+j})`. Taken literally that
  polynomial has total degree `ℓ` (a product of `ℓ` linear forms), so it cannot be
  degree `≤ d` while `ℓ` grows, and on the `k`-slice it is not `{0,1}`-valued in general.
  The construction that actually does the job in the `k < 2d` regime is the **sum over
  blocks of the product within each block**, `Σ_{i} ∏_{j} x_{(i-1)e+j}`: total degree
  `e = min d k ≤ d`, and Boolean on the slice precisely because `2·min(d,k) > k` when
  `k < 2d` (at most one block of size `e` fits inside a `k`-set). I formalized this
  reading. If the intended object really is the product-of-sums, my `blockFamily` should
  be replaced accordingly.
- **"not `ℓe`-juntas".** Literally the family *is* an `(ℓe)`-junta: it depends only on the
  `ℓe` block coordinates. The tight true statement is that it needs *all* `ℓe` of them, so
  I stated `∀ m, m < ℓ * min d k → ¬ IsJunta m (blockFamily …)`. This is exactly what the
  converse needs (given `m`, pick `ℓ` with `ℓ·e > m`).
- **`hkd : k < 2*d` as a hypothesis of the family theorem.** Needed for Booleanness of the
  sum-of-block-products reading (see above); the prompt's family clause does not list it
  explicitly but the surrounding converse assumes `k < 2d`.
- **`n ≥ 2ℓe`.** Kept as the prompt states it (room to realize the dependence on every
  block coordinate); I did not verify the constant `2` is tight.
- **Guessed Mathlib identifiers.** `MvPolynomial.eval`, `MvPolynomial.totalDegree`,
  `Finset.filter`, `Finset.card`, `Finset.range`, `Finset.inter`. I am fairly confident of
  all of these; `MvPolynomial.eval g p` returning `ℝ` via the bundled ring hom is the main
  spot to double-check.
- No claim is proved; correctness of the mathematics is assumed from the cited result
  (Filmus–Ihringer, *Boolean constant-degree functions on the slice are juntas*).
