# Agent 029 — note on the formalization

## What is stated

Three `sorry`-terminated theorems (statement only):

1. `slice_degree_junta` — **positive direction**. For `d ≥ 1`, `∃ m : ℕ` such that for all
   `k ≥ 2d`, all `n ≥ 2k`, every Boolean slice-degree-`d` function is an `m`-junta.
2. `slice_degree_not_junta` — **negative / sharpness direction**, as pure existence: for
   `1 ≤ k < 2d` and every `m`, there are `n ≥ 2k` and a Boolean slice-degree-`d` function
   that is not an `m`-junta.
3. `blockProd_witness` — the **explicit witnessing family**
   `∏_{i=1}^{ℓ} (Σ_{j=1}^{e} x_{(i-1)e+j})`, `e = min d k`, with its claimed properties
   (Boolean on the slice, slice-degree `≤ d`, not an `m`-junta for `m < ℓe`).

I stated both directions plus the explicit family, since the prompt lists that as an
allowed choice and it maximizes information for the diversity study.

## Encoding decisions

- **Slice.** `S : Finset (Fin n)` carried with an explicit side hypothesis `S.card = k`,
  rather than a subtype/`Sym`/`Set`. Keeps every definition first-order and Mathlib-native;
  `n`, `k`, `d` are ordinary `ℕ` parameters and the coordinate set is `Fin n`.
- **Boolean codomain.** Functions are `Finset (Fin n) → ℝ`, with Booleanity a separate
  predicate `IsBoolOn f k : ∀ S, S.card = k → f S = 0 ∨ f S = 1`. Real codomain is chosen
  so that "degree" can be phrased directly via real polynomials; `Bool`/`Fin 2`/`ZMod 2`
  would force a coercion at the polynomial-agreement step.
- **Degree.** `HasSliceDegreeLE f d k`: `∃ p : MvPolynomial (Fin n) ℝ`,
  `p.totalDegree ≤ d`, and `f S = eval (indicator S) p` for every `S` with `S.card = k`,
  where `indicator S i = if i ∈ S then 1 else 0`. This is exactly "agrees on the slice with
  a real polynomial of total degree ≤ d evaluated at the 0/1 indicator vector".
  I did **not** add a multilinearity constraint on `p`: over `0/1` evaluation points it is
  equivalent (`x_i^2 = x_i`), and dropping it keeps the statement lighter. An existential
  over polynomials also correctly captures that the *slice*-degree can be strictly below
  the degree of the naive representation (relevant for the witness family).
- **Junta.** `IsJuntaOn m f k`: `∃ J : Finset (Fin n)`, `J.card ≤ m`, and
  `S ∩ J = T ∩ J → f S = f T` for all slice `S, T`. Quantifiers restricted to `card = k`.
- **`m(d)`.** Existential *inside* the statement (`∃ m : ℕ, …`), matching "there is a
  constant `m(d)`". Not exposed as an explicit `m : ℕ → ℕ`.
- **Explicit family.** `blockProd n e ℓ S = ∏_{i ∈ range ℓ} (|S ∩ block i| : ℝ)` with
  `block i = { t : Fin n | i*e ≤ (t:ℕ) < i*e + e }` (0-based; the prompt's 1-based
  `x_{(i-1)e+j}` blocks). `e` is passed as `min d k`.

## Uncertainties / caveats

- **`ℓ` pinned to `k` in `blockProd_witness`.** The prompt writes the family with `ℓ`
  free. Working through it, the raw product `∏ |S ∩ block i|` is `{0,1}`-valued on the
  `k`-slice for *all* `ℓ` only in degenerate cases; in general it takes the value `2`
  (e.g. `d = 2, k = 3, e = 2, ℓ = 2`). It **is** Boolean when `ℓ = k`: `k` elements in `k`
  blocks with all blocks occupied forces one per block, product `1`; otherwise a block is
  empty, product `0`. So I added `hℓ : ℓ = k` to keep the stated conjunction a defensible
  (true) statement. This is a judgement call about the intended reading; a purist
  transcription would leave `ℓ` free and accept that the literal universal form need not
  be provable.
- **"not `ℓe`-juntas".** Read as "not an `m`-junta for every `m < ℓe`" (i.e. essentially
  depends on all `ℓe` block coordinates). Literally `¬ IsJuntaOn (ℓ*e) …` is false
  (the function *is* an `(ℓe)`-junta on the block coordinates); the meaningful claim is
  the strict-`<` one, which also feeds `slice_degree_not_junta`.
- **`slice-degree ≤ d` of the witness when `k > d`.** The naive representation of
  `blockProd` has total degree `ℓ = k > d`; the claim `HasSliceDegreeLE … d` relies on the
  Filmus–Ihringer fact that the slice-degree collapses to `d`. This is asserted, not
  checked (statement only).
- **Mathlib identifiers used:** `MvPolynomial (Fin n) ℝ`, `MvPolynomial.totalDegree`,
  `MvPolynomial.eval`, `Finset.filter`, `Finset.range`, `Finset.card`, `Finset` `∩`.
  All are standard in current Mathlib; `import Mathlib` is used for self-containedness.
  Decidability of the block-membership predicate for `Finset.filter` should be inferred
  from `Nat` order + `And` instances.
