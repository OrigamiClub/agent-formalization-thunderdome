# Agent 098 — Filmus–Ihringer, formalization note

## What I stated

Both directions of the dichotomy, plus the explicit witnessing family:

1. `boolean_degree_le_junta` — **positive direction**: `d ≥ 1 ⇒ ∃ M, ∀ k ≥ 2d, ∀ n ≥ 2k,
   every Boolean degree-`d` function on `binom([n],k)` is an `M`-junta`.
2. `exists_boolean_degree_not_junta` — **negative direction with the explicit family**:
   for `1 ≤ k < 2d` and any `m`, some `∑_{i<ℓ} ∏_{j<e} x_{emb(i,j)}` with `e = min d k`
   is Boolean, degree `≤ d`, and not an `m`-junta.
3. `exists_boolean_degree_not_junta'` — negative direction as a plain existential
   (no reference to the witness `def`), as a robustness fallback.

All bodies are `:= by sorry`. Nothing is proved.

## Encoding decisions

- **Slice**: `abbrev Slice n k := {S : Finset (Fin n) // S.card = k}`. `abbrev` (not `def`)
  so subtype projections / coercions stay transparent. Ambient coordinate set is `Fin n`,
  with `n k d` carried as explicit `ℕ` arguments.
- **Boolean codomain**: functions are `Slice n k → ℝ` together with a predicate
  `IsBoolean f : ∀ S, f S = 0 ∨ f S = 1`. Chosen over `Bool`/`Fin 2`/`ZMod 2` because the
  degree notion is most naturally phrased with a *real* polynomial, and `{0,1} ⊆ ℝ` is the
  convention in the Filmus line of work.
- **Degree ≤ d**: `HasSliceDegreeLE d f` = there exists `p : MvPolynomial (Fin n) ℝ` with
  `p.totalDegree ≤ d`, `p` multilinear (`∀ t ∈ p.support, ∀ i, t i ≤ 1`), and
  `f S = MvPolynomial.eval (slicePoint S) p` for all slice points `S`, where
  `slicePoint S i = if i ∈ S.1 then 1 else 0`. This is the "restriction of a low-degree
  polynomial to the slice" definition. Multilinearity is included to match the task's
  wording; it is WLOG since the slice ⊆ `{0,1}^n` and multilinearizing (`xᵢ^a ↦ xᵢ`) does
  not raise total degree.
- **m-junta**: `IsJunta m f` = `∃ J : Finset (Fin n), J.card ≤ m ∧ ∀ S T,
  S.1 ∩ J = T.1 ∩ J → f S = f T`. "Value depends only on `S ∩ J`."
- **m(d)**: stated as an existential `∃ M : ℕ` inside the theorem (parametrized by `d`),
  uniform over `k` and `n`. Not given as an explicit `m : ℕ → ℕ`.
- **Explicit family**: `witnessPoly ℓ e emb = ∑ i : Fin ℓ, ∏ j : Fin e, X (emb (i,j))`,
  with `emb : Fin ℓ × Fin e ↪ Fin n` a `Function.Embedding`. Using an injective `emb`
  rather than literal indices `(i-1)e + j` captures exactly what matters — `ℓ` pairwise
  **disjoint** blocks of size `e` — and avoids `Fin n` arithmetic / bound-proof clutter in
  a def. The consecutive-index version is the special case `emb (i,j) = ⟨i*e + j, _⟩`.
  `e` is fixed to `min d k` in the theorem statement.

## Uncertainties / caveats

- **`∑`/`∏` order.** The task's prose writes the witness as
  `∏_{i=1}^{ℓ} (∑_{j=1}^{e} x_{(i-1)e+j})` (product of sums). Taken literally that has
  total degree `ℓ` and, on the slice, collapses to a junta (e.g. `d=k=1, e=1`, `ℓ≥2`
  gives the constant `0`), so it cannot witness a non-junta. The construction that works —
  and, to my knowledge, the actual Filmus–Ihringer one — is the **sum of products**
  `∑_{i<ℓ} ∏_{j<e} x_{block i j}` with `e = min d k`: since `k < 2d ⇒ 2e > k`, at most one
  size-`e` block fits in a `k`-set, so the function is `{0,1}`-valued; its degree is
  `e ≤ d`; and it depends on `ℓe` coordinates, so for `ℓe > m` it is not an `m`-junta.
  I formalized the sum-of-products version. `exists_boolean_degree_not_junta'` avoids the
  witness `def` entirely if the family shape is disputed.
- "not `ℓe`-juntas" in the task is read as "not `m`-juntas for `m < ℓe`"; the statement
  quantifies `∀ m, ∃ ℓ …` accordingly (a genuinely-depends-on-`ℓe`-coordinates function
  is trivially an `ℓe`-junta, so the intended claim must be the strict one).
- **Guessed Mathlib identifiers** (no compiler was available): `MvPolynomial`,
  `MvPolynomial.X`, `MvPolynomial.eval`, `MvPolynomial.totalDegree`, `MvPolynomial.support`
  (elements `t : Fin n →₀ ℕ` applied as `t i`), `Function.Embedding` (`↪`) with `DFunLike`
  application `emb (i,j)`, `Finset.card`, `Finset.inter` (`∩`), `BigOperators` `∑`/`∏` over
  `Fin`. Names/API shapes may need adjustment.
- `n ≥ 2k` is encoded as `2 * k ≤ n`; `k ≥ 2d` as `2 * d ≤ k`; `k < 2d` as `k < 2 * d`.
- The positive direction does not separately assert that a valid `M(d)` witness bound
  exists as a closed form; only its existence, which is the theorem's content.
