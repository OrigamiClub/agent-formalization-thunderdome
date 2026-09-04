# Agent 087 — formalization note

## What is stated

All three, as separate `sorry`-terminated theorems in namespace `Agent087`:

1. `agent_087_slice_juntas_forward` — the positive result: `∀ d ≥ 1, ∃ m, ∀ k ≥ 2d,
   ∀ n ≥ 2k`, every Boolean degree-`d` function on the slice is an `m`-junta.
2. `agent_087_slice_juntas_converse` — tightness: `∀ d ≥ 1, ∀ k` with `1 ≤ k < 2d`,
   `∀ m`, there exist `n ≥ 2k` and a Boolean degree-`d` function that is not an `m`-junta.
3. `agent_087_slice_juntas_explicit_family` — the explicit witnesses
   `∏_{i<ℓ} ∑_{j<e} x_{i·e+j}` with `e = min d k`: their Boolean realization on the slice
   is Boolean, has degree `≤ d`, and is not an `m`-junta for any `m < ℓe`.

## Encoding decisions

- **Slice**: `abbrev Slice n k := {S : Finset (Fin n) // S.card = k}`. Subtype of
  `Finset (Fin n)`; `abbrev` (not `def`) so `.val` / `.card` projections and instances
  fire without manual unfolding. Ambient coordinate set is `Fin n`; `n, k, d, m` are
  plain `ℕ` carried by explicit quantifiers.
- **Boolean codomain**: functions `Slice n k → ℝ` together with the predicate
  `IsBoolean f := ∀ S, f S = 0 ∨ f S = 1`. Real-valued (not `Bool`/`Fin 2`) so that the
  degree notion is stated directly via real polynomial evaluation with no coercion layer.
- **Degree ≤ d**: `HasDegreeLE f d := ∃ p : MvPolynomial (Fin n) ℝ, p.totalDegree ≤ d ∧
  ∀ S, f S = MvPolynomial.eval (sliceIndicator S) p`, where `sliceIndicator S i = if i ∈ S
  then 1 else 0`. I did **not** impose multilinearity of `p`: on 0/1 points `xᵢ^2 = xᵢ`,
  so any polynomial reduces to a multilinear one of no larger total degree, giving the
  same class of "degree ≤ d" functions. Noted in a docstring.
- **m-junta**: `IsJunta f m := ∃ J : Finset (Fin n), J.card ≤ m ∧ ∀ S T,
  S.val ∩ J = T.val ∩ J → f S = f T` — "value depends only on `S ∩ J`" via `Finset`
  intersection.
- **m(d)**: existential *inside* the statement (`∃ m : ℕ, …`), placed outside the `∀ k`
  so it depends on `d` only. Chose existential over an explicit `m : ℕ → ℕ` because the
  paper only asserts existence of the constant.
- **Explicit family**: `e = min d k`; block `i` (`i < ℓ`) = coordinates with index in
  `[i·e, i·e+e)`. Two defs given:
  - `sliceWitnessPoly n ℓ e` — the literal real polynomial `∏_{i<ℓ} ∑_{j<e} x_{i·e+j}`
    (with `dif` guarding the `Fin n` index; out-of-range summands are `0`).
  - `sliceWitnessFun n k ℓ e` — the Boolean function actually used in the theorem: `1`
    iff every block meets `S`, i.e. the AND-of-ORs. This is the `[≠ 0]` indicator of
    `sliceWitnessPoly` on the slice; using it makes `IsBoolean` hold by construction and
    avoids asserting (falsely, as a bare real value) that the product-of-sums is itself
    `{0,1}`-valued.
  Indexing: `i ∈ Finset.range ℓ`, `j ∈ Finset.range e`. Hypotheses `2*ℓ*e ≤ n` and
  `2*k ≤ n`. Non-junta stated as `∀ m < ℓ·e, ¬ IsJunta f m` (the function depends on all
  `ℓe` block coordinates); take `ℓ` large for "not an `m`-junta" for arbitrary `m`.

## Uncertainties

- **Guessed / assumed Mathlib identifiers**: `MvPolynomial.totalDegree`,
  `MvPolynomial.eval`, `MvPolynomial.X` (all believed to exist with these names and
  signatures). No dedicated Mathlib notion of "Boolean function / degree on the slice"
  or "junta" is assumed — all such notions are defined locally here.
- **`IsBoolean` of the witness**: for `sliceWitnessFun` it is true by construction (an
  `if _ then 1 else 0`). The raw product-of-sums `sliceWitnessPoly` is *not* `{0,1}`-valued
  on the slice in general; I interpret the theorem's "∏(Σ xⱼ)" as denoting the AND-of-ORs
  Boolean function (its nonvanishing indicator), which is the standard tribes-style
  non-junta example.
- **`HasDegreeLE (sliceWitnessFun …) d`**: transcribed from the source's assertion that
  these witnesses have degree `min(d,k) ≤ d` on the slice (the degree drop relative to the
  hypercube comes from the slice relations). Not independently verified.
- **"not ℓe-juntas"**: read as "essentially depends on all `ℓe` block coordinates",
  formalized as `∀ m < ℓe, ¬ IsJunta f m`. A literal reading ("needs > ℓe coordinates")
  is impossible since the function only involves `ℓe` variables.
- Emptiness of `Slice n k` when `k > n` is a non-issue: all statements assume `n ≥ 2k`.
