# Agent 057 — formalization note

## What is stated

All three of:

1. `boolean_degree_d_is_junta` — the positive direction: `∀ d ≥ 1, ∃ M, ∀ k ≥ 2d,
   ∀ n ≥ 2k, every Boolean degree-`d` function on the slice is an `M`-junta`.
   `M` is existentially quantified *before* `k` and `n`, so it is genuinely a
   function of `d` alone (`M = m(d)`).
2. `sharp_below_two_d` — the converse: for `1 ≤ k < 2d`, for every `m` there is a
   large enough `n` and a Boolean degree-`d` non-`m`-junta on the slice.
3. `sharp_witness` — the same converse with the explicit witnessing family
   spelled out (`witnessFun`), asserting it is Boolean, degree `≤ d`, and not an
   `m`-junta.

## Encoding decisions

- **Slice**: `abbrev Slice n k := {S : Finset (Fin n) // S.card = k}`. Subtype of
  `Finset (Fin n)`; `abbrev` (not `def`) so `.1` / `.2` and typeclass search work
  transparently. Ambient coordinate set is `Fin n`; `n`, `k`, `d`, `m`, `ℓ` are
  all plain `ℕ` carried as explicit `∀`-binders in each theorem.
- **Boolean codomain**: functions `Slice n k → ℝ` together with
  `IsBoolean f : ∀ S, f S = 0 ∨ f S = 1`. Chose `{0,1} ⊆ ℝ` rather than `Bool` /
  `Fin 2` so that "agrees with a real polynomial" is stated without a coercion.
- **Degree ≤ d** (`HasDegreeLE`): `∃ p : MvPolynomial (Fin n) ℝ` with
  `p.totalDegree ≤ d`, `∀ i, MvPolynomial.degreeOf i p ≤ 1` (multilinearity), and
  `f S = MvPolynomial.eval (fun i => if i ∈ S.1 then 1 else 0) p` for every slice
  point. Multilinearity is included to match "multilinear real polynomial" in the
  statement; it is WLOG on the slice (`xᵢ² = xᵢ`) so its presence changes neither
  direction's mathematical content.
- **m-junta** (`IsJunta`): `∃ J : Finset (Fin n), J.card ≤ m ∧ ∀ S T,
  S.1 ∩ J = T.1 ∩ J → f S = f T`. "Depends only on `S ∩ J`" via `Finset`
  intersection equality.
- **Explicit family** (`witnessFun n ℓ e k`): defined directly on the slice as
  `∑ i ∈ range ℓ, if block n e i ⊆ S.1 then 1 else 0`, i.e. the number of the
  first `ℓ` width-`e` blocks contained in `S`. `block n e i` is
  `univ.filter (fun x : Fin n => i*e ≤ x ∧ x < i*e+e)`. Indexing: block `i` uses
  coordinates `i*e, …, i*e+e-1`, matching `x_{(i-1)e+j}` (0-based here). `e` is
  passed as `min d k` in `sharp_witness`. Defining the family as a function
  rather than as an `MvPolynomial` avoids a `Fin n` bound proof obligation in a
  statement-only file; its degree bound is asserted through `HasDegreeLE`.
- `sharp_witness` chooses `ℓ` via the hypothesis `m < ℓ * min d k` (any such `ℓ`
  works) and requires both `2*(ℓ*e) ≤ n` and `2*k ≤ n`.

## Interpretation / uncertainties

- **Product vs. sum in the given formula.** The prompt writes the witness as
  `∏_{i=1}^{ℓ}(Σ_{j=1}^{e} x_{(i-1)e+j})`. Taken literally this is a product of
  `ℓ` linear forms (total degree `ℓ`), which cannot have bounded degree `d` while
  `ℓ → ∞`, and is not `{0,1}`-valued on the slice. The reading that makes the
  theorem correct — bounded degree `e = min(d,k) ≤ d`, Boolean on the slice
  because `k < 2·min(d,k)` forbids two disjoint blocks in a `k`-set, and
  genuinely depending on `ℓ·e` coordinates — is the *sum of products*
  `Σ_{i=1}^{ℓ} ∏_{j=1}^{e} x_{(i-1)e+j}`. I formalized that reading (count of
  fully-contained blocks). I believe the prompt has `∏` and `Σ` swapped.
- "not `ℓe`-juntas": strictly the function *is* trivially an `ℓe`-junta (union of
  blocks). The intended content is that it depends on all `ℓe` block coordinates,
  hence is not an `m`-junta for `m < ℓe`; that is what `sharp_witness` states.
- Guessed / to-verify Mathlib identifiers: `MvPolynomial.degreeOf` (name and
  argument order `degreeOf i p`), `MvPolynomial.totalDegree`, `MvPolynomial.eval`
  applied as `MvPolynomial.eval g p`. `Finset.filter` decidability of the block
  predicate is assumed to be inferred. `∑ i ∈ Finset.range ℓ, _` uses current
  big-operator notation (`∈`, not `in`).
- No existing Mathlib "Boolean degree function on the slice" / "junta" notion was
  used; all four auxiliary notions are defined locally.
