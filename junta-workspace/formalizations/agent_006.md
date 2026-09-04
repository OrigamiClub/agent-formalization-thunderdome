# Agent 006 — formalization note

## What is stated

Both directions of the Filmus–Ihringer dichotomy, plus explicit witnesses for the
converse. All theorems are statement-only (`:= by sorry`).

1. `filmus_ihringer_forward` — the junta upper bound. For `d ≥ 1` there is an
   `m : ℕ` (existentially quantified inside the statement) with: `k ≥ 2d`,
   `n ≥ 2k` ⟹ every Boolean degree-`≤ d` function on `binom([n],k)` is an
   `m`-junta.
2. `filmus_ihringer_converse` — the lower bound, as a bare existential: for
   `1 ≤ k < 2d` and any `m`, there are `n ≥ 2k` and a Boolean degree-`≤ d`
   function on `binom([n],k)` that is not an `m`-junta.
3. `blockFamily` / `blockFamily_spec` — an explicit witnessing family realizing
   the converse: Boolean, degree `≤ d`, not an `m`-junta for any `m < ℓ·e`.

## Encoding decisions

- **Slice**: `abbrev Slice n k := {S : Finset (Fin n) // S.card = k}`. Subtype of
  `Finset (Fin n)`; `abbrev` so `Fintype`/`DecidableEq` instances flow through.
  Coordinates are carried as the explicit naturals `n`, `k`, `d`, ambient type
  `Fin n`.
- **Boolean codomain**: functions `Slice n k → ℝ` with a separate predicate
  `IsBooleanValued f := ∀ s, f s = 0 ∨ f s = 1`. Real-valued is chosen so that
  "degree" connects directly to real polynomials without a coercion layer.
- **Degree `≤ d`** (`HasDegreeLE`): `∃ p : MvPolynomial (Fin n) ℝ`,
  `p.totalDegree ≤ d` and `f` agrees on the whole slice with
  `MvPolynomial.eval (indicator s) p`, where `indicator s i = if i ∈ s.1 then 1
  else 0`. I did *not* force `p` multilinear: on `{0,1}` inputs the multilinear
  reduction has total degree `≤` the original, so the two formulations define the
  same function class. "degree-`d`" is read as "degree `≤ d`" throughout (the
  usual convention for "Boolean degree `d` function").
- **`m`-junta** (`IsJunta`): `∃ J : Finset (Fin n)`, `J.card ≤ m`, and for all
  slice points `s t`, `s.1 ∩ J = t.1 ∩ J → f s = f t`. Direct transcription of
  "value depends only on `S ∩ J`".
- **`m(d)`**: existential inside `filmus_ihringer_forward` rather than an explicit
  `m : ℕ → ℕ`. Matches the phrasing "there is a constant `m(d)`" and avoids
  committing to a specific (unknown to me) bound.
- **Hypotheses** `k ≥ 2d`, `n ≥ 2k`, `1 ≤ k < 2d` written as `2*d ≤ k`,
  `2*k ≤ n`, `1 ≤ k ∧ k < 2*d`.
- **Explicit family indexing**: instead of the literal arithmetic
  `x_{(i-1)e+j}` (which needs `Fin n` bounds proofs), the `ℓ × e` block
  coordinates are supplied as `b : Fin ℓ → Fin e → Fin n` with an injectivity
  hypothesis `hb`. Cleaner and strictly more general (any placement of disjoint
  blocks). Here `e = min d k`.

## Interpretation choices / uncertainties

- **Witness family form.** The theorem text writes the witnesses as
  `∏_{i=1}^{ℓ} (∑_{j=1}^{e} x_{(i-1)e+j})` with `e = min(d,k)`. Taken literally as
  a polynomial this is a product of `ℓ` linear forms — total degree `ℓ`, and not
  `{0,1}`-valued on a general `k`-set (e.g. one block containing two elements of
  `S` gives value `2`). On the slice `binom([n],k)` with `k < 2·min(d,k)`,
  however, no `k`-set contains two full blocks, so the product is supported on
  configurations with exactly one hit block and collapses to the sum of disjoint
  monomials `∑_{i<ℓ} ∏_{j<e} x_{b i j}`. I formalized that sum-of-products normal
  form (`blockFamily`): it is visibly Boolean on the slice (at most one monomial
  fires) and visibly of degree `min(d,k) ≤ d`. If the intended reading really is
  the raw product with degree reduced only via slice identities
  (`∑_all xᵢ = k`), the function object is the same but `HasDegreeLE` would then
  be the non-trivial content rather than immediate.
- **"not `ℓe`-juntas".** `blockFamily` visibly depends on exactly the `ℓ·e` block
  coordinates, so it *is* an `ℓe`-junta. I read the theorem's phrase as "the
  junta size is forced to grow like `ℓe`" and stated the sharp fact: it is not an
  `m`-junta for any `m < ℓ·e` (i.e. not an `(ℓe−1)`-junta). Choosing `ℓ` with
  `ℓ·e > m` then contradicts any fixed bound `m`, which is what the converse
  needs.
- **Mathlib identifiers used** (from memory, not compiler-checked):
  `MvPolynomial (Fin n) ℝ`, `MvPolynomial.totalDegree`, `MvPolynomial.eval`
  (as `MvPolynomial.eval (g) p`), `MvPolynomial.X`, `Finset.card`, `Finset` `∩`,
  `Function.Injective`, `BigOperators` `∑`/`∏` over `Fin`. Argument order of
  `MvPolynomial.eval` and the exact `totalDegree` spelling are the most likely
  points of drift.
- The `blockFamily_spec` side conditions (`hd`, `hk`, `hkd`, `hℓ`, `hn`, `hb`)
  are what the mathematics needs (`e ≥ 1`; `k < 2e` for Boolean-ness; enough free
  coordinates outside any candidate junta). They are not claimed to be minimal.
