# agent_023 — formalization note

## What I stated

All three pieces, as separate `theorem`s (statement only, each `:= by sorry`):

1. `boolean_degree_d_is_junta` — the forward direction: `∀ d ≥ 1, ∃ m(d), ∀ k ≥ 2d,
   ∀ n ≥ 2k`, every Boolean degree-`d` slice function is an `m(d)`-junta.
2. `boolean_degree_d_not_junta` — the converse in the clean "for every `m`" form:
   if `1 ≤ k < 2d` then for every `m` there exist `n ≥ 2k` and a Boolean degree-`d`
   slice function that is not an `m`-junta.
3. `witnessing_family` — the explicit witnessing family and its three properties
   (Boolean, degree `≤ d`, not an `m`-junta for `m < ℓe`).

## Encoding decisions

- **Slice.** `Slice n k := {S : Finset (Fin n) // S.card = k}`. Ambient coordinate
  set is `Fin n`; `n`, `k`, `d` are carried as explicit `ℕ` arguments.
- **Boolean codomain.** Real-valued `f : Slice n k → ℝ` together with
  `IsBoolean f : ∀ S, f S = 0 ∨ f S = 1`. Real-valued rather than `Bool`/`Fin 2`
  because "degree" is defined through real polynomials, and this keeps
  `HasDegreeLE` from needing a coercion.
- **Degree `≤ d`.** `HasDegreeLE f d`: there is `p : MvPolynomial (Fin n) ℝ` that is
  multilinear (`∀ i, MvPolynomial.degreeOf i p ≤ 1`) with `p.totalDegree ≤ d`, and
  `f S = MvPolynomial.eval (ind S.1) p` for every slice point, where `ind S` is the
  0/1 indicator vector. I included multilinearity because the problem says
  "multilinear"; on 0/1 points it is not a real restriction (any total-degree-`d`
  polynomial can be reduced mod `xᵢ² = xᵢ` without raising total degree), so a
  reader who prefers dropping that conjunct gets the same function class.
- **`m`-junta.** `IsJunta f m`: `∃ J : Finset (Fin n), J.card ≤ m ∧ ∀ S T,
  S.1 ∩ J = T.1 ∩ J → f S = f T`. "Value depends only on `S ∩ J`."
- **`m(d)`.** Existential inside the statement (`∃ m : ℕ, …`), matching "there is a
  constant `m(d)`". An explicit `m : ℕ → ℕ` parameter would be an equally faithful
  alternative.

## The explicit family (and a reading choice)

The prompt writes the witnesses as `∏_{i=1}^{ℓ} (Σ_{j=1}^{e} x_{(i-1)e+j})` with
`e = min(d,k)`. Read literally, a single block sum `Σ_{j=1}^{e} x_{(i-1)e+j}` is
`|S ∩ block_i|`, which ranges over `0..e`, so the product is not `{0,1}`-valued and
the "Boolean" claim fails. The side conditions point to the intended object: with
`e = min(d,k)` and `k < 2d` one has `⌊k/e⌋ = 1` (two disjoint `e`-blocks cannot both
fit in a `k`-set), and that is exactly the hypothesis under which the **`Σ_i ∏_j`**
form — `S ↦` number of the first `ℓ` blocks fully contained in `S` — takes values in
`{0,1}`. Its polynomial `Σ_{i<ℓ} ∏_{j<e} X_{ie+j}` has total degree `e ≤ d` and is
multilinear. So I formalized the witnesses as `familyPoly n ℓ e :=
∑ i ∈ range ℓ, ∏ j ∈ range e, X_{ie+j}` (a Π/Σ transcription swap in the prompt).

`familyPoly` is total: an index `ie + j ≥ n` contributes a `0` factor. Under
`witnessing_family`'s hypothesis `n ≥ 2ℓe` every index used is `< n`.

**"not `ℓe`-juntas".** `familyFun` manifestly reads only coordinates `0..ℓe-1`, so
it *is* an `ℓe`-junta; the literal negation would be false. I read the claim as
"genuinely depends on all `ℓe` coordinates", i.e. minimal junta arity exactly `ℓe`,
and stated it as `∀ m < ℓe, ¬ IsJunta (familyFun …) m`. The hypothesis `n ≥ 2ℓe`
(rather than `n ≥ ℓe`) is what forces the minimal arity up to `ℓe` instead of
`n - ℓe`, so this matches the intended content. This also immediately gives
`boolean_degree_d_not_junta` by choosing `ℓ` with `ℓe > m`.

## Uncertainties / guessed identifiers

- `MvPolynomial.degreeOf` (name and argument order `degreeOf i p`) — fairly sure it
  exists in current Mathlib; if not, `∀ i, p.degreeOf i ≤ 1` could be replaced by a
  `MvPolynomial` multilinearity predicate or dropped (see above).
- `MvPolynomial.totalDegree`, `MvPolynomial.eval`, `MvPolynomial.X` — standard.
- Big-operator notation `∑ i ∈ Finset.range ℓ, …` / `∏ j ∈ Finset.range e, …` —
  current Mathlib spelling; older spelling is `∑ i in Finset.range ℓ, …`.
- `noncomputable` is placed on every `ℝ`-valued def; harmless if some turn out to be
  computable.
- No `n ≥ k` hypothesis is added to `witnessing_family`: for `ℓ ≥ 1`, `n ≥ 2ℓe > k`
  already; for `ℓ = 0` the family is the constant `0` and the statement is trivially
  fine.
