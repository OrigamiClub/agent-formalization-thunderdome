# agent_043 — formalization note

## What is stated

All three components, as separate `sorry`-terminated theorems in namespace `FilmusIhringer`:

1. **`juntaBound`** — positive direction. `∀ d ≥ 1, ∃ m, ∀ k ≥ 2d, ∀ n ≥ 2k`, every Boolean
   degree-`≤ d` function on the slice is an `m`-junta. The constant `m(d)` is an
   *existential* `m : ℕ` chosen before `k`, `n`, `f`, so it genuinely depends only on `d`.
2. **`juntaBound_sharp`** — sharpness. `∀ d ≥ 1, ∀ k` with `1 ≤ k < 2d`, `∀ m, ∃ n ≥ 2k`
   and a Boolean degree-`≤ d` function on the slice that is not an `m`-junta.
3. **`blockFn_witness`** — the explicit family
   `∏_{i=1}^{ℓ}(∑_{j=1}^{e} x_{(i-1)e+j})`, `e = min d k`: for `1 ≤ k < 2d`, any `ℓ`, and
   `n ≥ 2(ℓe)`, it is Boolean, has degree `≤ d`, and is not an `(ℓe)`-junta.

## Encoding decisions

- **Slice**: `abbrev Slice n k := {S : Finset (Fin n) // S.card = k}`. Subtype of `Finset`
  keeps `S ∩ J` and `|J|` literal (`S.1 ∩ J`, `J.card`). `abbrev` so projections/coercions
  fire without unfolding lemmas.
- **Codomain**: real-valued `f : Slice n k → ℝ` plus a separate `IsBoolean` predicate
  (`∀ S, f S = 0 ∨ f S = 1`). Chosen over `Bool`/`Fin 2`/`ZMod 2` because "degree" is
  defined by comparison with a **real** polynomial; keeping `f` real-valued lets
  `HasDegreeLE` be a plain equation `f S = eval (indicator S) p` with no coercion.
- **Degree ≤ d**: `∃ p : MvPolynomial (Fin n) ℝ, p.totalDegree ≤ d ∧ ∀ S, f S = eval (indicator S.1) p`.
  `indicator S i = if i ∈ S then 1 else 0`. Multilinearity is *not* required: indicator
  vectors are `{0,1}`-valued, so any agreeing polynomial has a multilinear reduction of no
  larger total degree. Note this is the "degree on the slice" notion — the witnessing `p`
  may differ from any syntactic polynomial one first writes down (relevant to point 3,
  where `blockForm` itself has total degree `ℓ`, but a lower-degree `p` agrees on the slice).
- **m-junta**: `∃ J : Finset (Fin n), J.card ≤ m ∧ ∀ S T, S.1 ∩ J = T.1 ∩ J → f S = f T`.
  Direct transcription of "value depends only on `S ∩ J`".
- **m(d)**: existential inside the statement (not a supplied `m : ℕ → ℕ`), matching
  "there is a constant m(d)".
- **Explicit family indexing**: `blockForm ℓ e : MvPolynomial (Fin ℓ × Fin e) ℝ` defined as
  `∏ i : Fin ℓ, ∑ j : Fin e, X (i,j)`. It is placed into `Fin n` by
  `fun v => Fin.castLE hle (finProdFinEquiv v)`, sending `(i,j)` to coordinate `e*i + j`
  (0-indexed form of `(i-1)e + j`), then `blockFn` evaluates the renamed polynomial at
  indicator vectors. The block-count `ℓ` is a free parameter of the theorem; `e = min d k`
  is carried as a hypothesis `he : e = min d k`.
- `n`, `k`, `d`, `ℓ`, `e` are all explicit `ℕ` arguments; the ambient coordinate set is
  `Fin n` throughout.

## Uncertainties / guessed Mathlib identifiers

- `finProdFinEquiv` — recalled as `Fin m × Fin n ≃ Fin (m * n)` with forward map
  `(x.1, x.2) ↦ x.2 + n * x.1`. If Mathlib's version is stated as `Fin (n * m)` or with the
  other addend convention, the `Fin.castLE hle` argument type (`ℓ * e ≤ n`) or the exact
  coordinate offset would need a trivial adjustment. Used only to get an explicit injective
  placement of the blocks.
- `Fin.castLE : m ≤ n → Fin m → Fin n` — name and argument order assumed.
- `MvPolynomial.rename`, `MvPolynomial.eval`, `MvPolynomial.X`, `MvPolynomial.totalDegree` —
  standard; `rename`/`eval` applied via their bundled-hom `FunLike` coercions.
- "not an `ℓe`-junta": encoded literally as `¬ IsJunta (ℓ * e) (blockFn …)`, following the
  prompt's wording. If the intended claim is the weaker "not an `(ℓe − 1)`-junta" (i.e. the
  function depends on exactly `ℓe` coordinates), replace `ℓ * e` by `ℓ * e - 1` in
  `blockFn_witness`.
- `blockFn` is `noncomputable` (via `MvPolynomial` API); irrelevant to a statement-only file.
