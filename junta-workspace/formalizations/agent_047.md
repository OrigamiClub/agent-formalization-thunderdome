# Agent 047 — Filmus–Ihringer slice junta theorem (statement only)

## What I stated

All three of:

1. **`filmus_ihringer_forward`** — the junta direction. `∃ m : ℕ` placed *outside*
   the `∀ n k`, so `m` depends only on `d`. Hypotheses `2*d ≤ k`, `2*k ≤ n`.
2. **`filmus_ihringer_tight`** — the converse in pure existential form: for
   `1 ≤ k < 2*d`, for every `m` there exist `n ≥ 2k` and a Boolean degree-`≤ d`
   function that is not an `m`-junta.
3. **`filmus_ihringer_witness`** — the converse via the explicit family, with the
   polynomial written out (`witnessPoly` / `witnessFun`).

## Encoding decisions

- **Slice**: `abbrev Slice n k := {S : Finset (Fin n) // S.card = k}`. `abbrev` (not
  `def`) so `.1`, `.2`, `.card` work without unfolding. Ambient coordinate set is
  `Fin n`; `n`, `k`, `d` are plain `ℕ` arguments.
- **Boolean codomain**: functions are `Slice n k → ℝ` plus a predicate
  `IsBoolean f : ∀ S, f S = 0 ∨ f S = 1`. Real codomain chosen so the degree
  notion connects directly to real polynomials.
- **Degree ≤ d** (`HasDegreeLE`): there is `p : MvPolynomial (Fin n) ℝ` with
  `∀ i, MvPolynomial.degreeOf i p ≤ 1` (multilinear) and `p.totalDegree ≤ d`, such
  that `f S = MvPolynomial.eval (ind S.1) p` for every slice point, where
  `ind S i = if i ∈ S then 1 else 0`. The multilinearity clause is included for
  fidelity to the problem text ("multilinear real polynomial"); it is WLOG on the
  slice (reduce `x_i^2 → x_i` on 0/1 inputs) and could be dropped without changing
  the function class.
- **m-junta** (`IsJunta m f`): `∃ J : Finset (Fin n)`, `J.card ≤ m`, and
  `∀ S T, S.1 ∩ J = T.1 ∩ J → f S = f T`.
- **m(d)**: existential inside the statement (`∃ m : ℕ, …`), matching "there is a
  constant m(d)".

## The explicit witnessing family

The prompt writes `∏_{i=1}^{ℓ}(Σ_{j=1}^{e} x_{(i-1)e+j})`. Taken literally that is a
product of `ℓ` linear forms, hence degree `ℓ` (unbounded), which cannot be a
degree-`≤ d` function, and its "not `ℓe`-junta" claim with growing `ℓ` would be
impossible. I read this as a transposed `∏`/`Σ`, i.e.

  `f = Σ_{i=1}^{ℓ} ∏_{j=1}^{e} x_{(i-1)e+j}`  with  `e = min d k`,

a sum of `ℓ` pairwise-disjoint degree-`e` monomials. This has degree
`e = min(d,k) ≤ d`, depends on exactly `ℓe` coordinates, and is Boolean on the
slice: when `1 ≤ k < 2d` one has `2·min(d,k) > k` (if `k ≤ d`, `2k > k`; if
`d < k < 2d`, `2d > k`), so a `k`-set contains at most one full block, making the
sum `{0,1}`-valued. This is the encoding in `witnessPoly` (0-indexed;
out-of-range indices contribute `0` via `dite`, harmless when `n ≥ 2ℓe`).

- **"not `ℓe`-juntas"**: stated precisely as `∀ m < ℓe, ¬ IsJunta m f`. The
  function genuinely *is* an `ℓe`-junta (`J` = the `ℓe` used coordinates) but not on
  fewer; the prompt's phrasing is read as "requires `ℓe` coordinates".
- To defeat a prescribed `m` (as in `filmus_ihringer_tight`), pick `ℓ` with
  `ℓ·min(d,k) > m`.

## Uncertainties / guesses

- `MvPolynomial.degreeOf` — believed to be the Mathlib name for per-variable
  degree; `totalDegree` and `eval` are standard.
- Whether the intended "multilinear polynomial" constraint should be present at
  all (it is WLOG on the slice). Kept it.
- The `dite` guard inside `witnessPoly` is a device to keep the definition total
  without a side proof `i*e+j < n`; a cleaner version would carry `ℓ*e ≤ n` and
  build `Fin n` directly.
- Exact large-`n` thresholds (`2*k ≤ n`, `2*(ℓ*min d k) ≤ n`) follow the prompt;
  the true statements may need only "`n` large enough".
- No claim about which Mathlib lemmas exist for the proofs — statement only.
