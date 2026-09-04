# Agent 068 — formalization note

## What I stated

Both directions **and** the explicit witnessing family, as three `sorry` theorems:

1. `boolean_degree_junta_of_ge` — forward direction (`k ≥ 2d`): a single
   `m : ℕ → ℕ`, existentially quantified at the front of the statement, that bounds
   the junta size of every Boolean degree-`d` function for all admissible `k, n`.
2. `not_bounded_junta_of_lt` — converse direction (`1 ≤ k < 2d`): purely existential,
   "for every `m` there is `n ≥ 2k` and a Boolean degree-`d` non-`m`-junta".
3. `addrFun_witness` — the explicit family: `addrFun n k e ℓ` is Boolean, has degree
   `≤ d`, and is not an `m`-junta for any `m < ℓe`, whenever `e = min d k`,
   `1 ≤ k < 2d`, `n ≥ 2ℓe`, `n ≥ 2k`.

## Encoding decisions

- **Slice**: `abbrev Slice n k := {S : Finset (Fin n) // S.card = k}`. Subtype of
  `Finset (Fin n)`; `abbrev` so `S.1 : Finset (Fin n)` is available definitionally.
  The ambient coordinate set is `Fin n`, and `n`, `k`, `d`, `ℓ`, `e` are all carried
  as explicit `ℕ` arguments (the slice type genuinely depends on `n`, which varies).
- **Boolean codomain**: real-valued `f : Slice n k → ℝ` together with a separate
  predicate `IsBoolean f : ∀ x, f x = 0 ∨ f x = 1`. Chosen over `Bool`/`Fin 2`/`ZMod 2`
  because "degree" is intrinsically about a **real** polynomial; keeping `f` in `ℝ`
  avoids coercions in `HasDegreeLE`.
- **Degree `≤ d`**: via `MvPolynomial (Fin n) ℝ` and `MvPolynomial.totalDegree`.
  `HasDegreeLE f d` asserts `∃ p, p.totalDegree ≤ d ∧ ∀ x, f x = eval (indicator x.1) p`,
  where `indicator S i = if i ∈ S then 1 else 0`. I did **not** require `p` multilinear:
  multilinearization does not increase total degree, so the two definitions agree, and
  the weaker form is the standard "agrees with a degree-`≤ d` polynomial" phrasing.
- **`m`-junta**: `∃ J : Finset (Fin n), J.card ≤ m ∧ ∀ x y, x.1 ∩ J = y.1 ∩ J → f x = f y`.
  The "value depends only on `S ∩ J`" formulation, specialized to slice points.
- **`m(d)`**: an explicit `m : ℕ → ℕ` bound by `∃` inside the statement (not a fixed
  Mathlib term, since no such constant exists there).
- **Explicit family** (`block`, `addrFun`): `block n e i` is the `e` coordinates of
  `Fin n` with value in `[(i-1)e, ie)` (1-indexed `i`, cut off by `Finset.univ.filter`).
  `addrFun n k e ℓ S = if ∃ i, 1 ≤ i ≤ ℓ ∧ block n e i ⊆ S then 1 else 0` — the OR of
  `ℓ` disjoint size-`e` conjunctions. `noncomputable` + `open Classical` for the
  decidability of the bounded existential; irrelevant for a statement-only file.

## The `∏_i (∑_j x)` vs `∑_i (∏_j x)` discrepancy (main uncertainty)

The prose gives the witness as `∏_{i=1}^{ℓ}(∑_{j=1}^{e} x_{(i-1)e+j})` with `e = min(d,k)`.
As literally written this real polynomial evaluates on the `k`-slice to
`∏_i |S ∩ block_i|`, which is **not** `{0,1}`-valued (already for `ℓ = 1` it ranges over
`0..e`), contradicting "a Boolean degree-`d` function". The construction that *is*
Boolean, has degree `e = min(d,k) ≤ d`, and fails to be a junta as `ℓ → ∞` is the
**dual**: `∑_{i=1}^{ℓ} ∏_{j=1}^{e} x_{(i-1)e+j}` (an OR of `ℓ` disjoint `e`-ANDs). Here
`1 ≤ k < 2d` forces `e = min(d,k) > k/2`, so two disjoint blocks cannot both sit inside
a `k`-set, the sum is `0/1` on the slice, and every one of the `ℓe` block coordinates is
relevant once `n ≥ 2ℓe`. I formalized this corrected reading in `addrFun`. If the
intended object really is the product-of-sums, `addrFun` should be replaced, but then
`IsBoolean` would fail and the theorem as phrased would be inconsistent.

## Other uncertainties / guessed identifiers

- `MvPolynomial.eval`, `MvPolynomial.totalDegree` — names/signatures believed correct;
  `eval` is applied as `MvPolynomial.eval (v : Fin n → ℝ) p`.
- `totalDegree` of the zero polynomial is `0` in Mathlib, so constant Boolean functions
  correctly count as degree `≤ d`; fine here.
- `Finset.univ.filter (fun x => …)` surface syntax may need to be
  `{x ∈ Finset.univ | …}` / `Finset.filter … Finset.univ` in the current Mathlib;
  semantically unambiguous.
- I have not machine-checked any of this (no compiler available).
