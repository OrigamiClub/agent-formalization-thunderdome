# Agent 069 — Filmus–Ihringer junta theorem, statement-only formalization

## What is stated

Three theorems, all `:= by sorry`:

1. `boolean_degree_d_on_slice_is_junta` — the **positive** direction. The
   junta bound is given as an explicit Skolemized function `∃ m : ℕ → ℕ`
   at the front of the statement ("there is a constant `m(d)`"), then
   `∀ d ≥ 1, ∀ k ≥ 2d, ∀ n ≥ 2k`, every Boolean degree-`d` function on the
   slice is an `m d`-junta.

2. `boolean_degree_d_on_slice_not_junta` — the **converse**, as a plain
   existence statement: for `1 ≤ k < 2d` and every `m`, some slice
   (`n ≥ 2k`) carries a Boolean degree-`d` function that is not an
   `m`-junta.

3. `boolean_degree_d_on_slice_not_junta_witnessed` — the converse again,
   but naming the **explicit witnessing family**
   `∏_{i<ℓ} (∑_{j<e} x_{blk i j})` with `e = min d k`, asserting that for
   `ℓ` chosen large enough (`m < ℓe`) and `n ≥ 2ℓe` this function is
   Boolean, degree `≤ d`, and not an `ℓe`-junta.

## Encoding decisions

- **Slice**: `Slice n k := {S : Finset (Fin n) // S.card = k}`. Subtype of
  `Finset (Fin n)`. Chosen because it makes "intersect with a junta set
  `J`" (`x.1 ∩ J`) and "indicator vector" completely direct.

- **Boolean codomain**: functions are `Slice n k → ℝ`, with a separate
  predicate `IsBoolean f := ∀ x, f x = 0 ∨ f x = 1`. Picked over `Bool` /
  `Fin 2` / `ZMod 2` so that "agrees with a real polynomial" needs no
  coercion and degree is literally polynomial total degree.

- **Degree ≤ d**: `HasDegreeLE f d` = there is `p : MvPolynomial (Fin n) ℝ`
  with `p.totalDegree ≤ d` and `f x = MvPolynomial.eval (ind x.1) p` for
  all slice points, where `ind S i = if i ∈ S then 1 else 0`. I did *not*
  impose multilinearity of `p`: on `{0,1}` inputs it is not a real
  restriction, and there is no clean off-the-shelf Mathlib "is multilinear
  polynomial" predicate. An alternative encoding (restriction of a
  hypercube function, or Fourier/Johnson levels) was rejected as heavier
  and less standard.

- **m-junta**: `IsJunta f m` = there is `J : Finset (Fin n)`, `J.card ≤ m`,
  with `x.1 ∩ J = y.1 ∩ J → f x = f y`. This is the "value depends only on
  `S ∩ J`" formulation.

- **m(d)**: existential `∃ m : ℕ → ℕ` inside the statement rather than an
  explicit closed form (the paper's bound is not elementary and the task
  only asserts existence of the constant).

- **Parameters**: `d, k, n` are plain `ℕ` arguments with hypotheses
  `1 ≤ d`, `2 * d ≤ k` / `1 ≤ k`, `k < 2 * d`, `2 * k ≤ n`. Ambient
  coordinate type is `Fin n` throughout.

- **Explicit family indexing**: rather than literal indices `(i-1)e+j`
  into `Fin n` (which would need inline `Fin` bound proofs in a
  statement-only file), the `ℓ` disjoint blocks of `e = min d k`
  coordinates are given by an abstract map `blk : Fin ℓ → Fin e → Fin n`
  with an injectivity hypothesis on the uncurried
  `Fin ℓ × Fin e → Fin n`. `witnessFun ℓ e blk x = ∏_{i} ∑_{j} ind x.1 (blk i j)`.
  The task's `n ≥ 2ℓe` and "not an `ℓe`-junta" are kept verbatim
  (`2 * (ℓ * min d k) ≤ n`, `¬ IsJunta … (ℓ * min d k)`).

## Uncertainties

- **Consistency of the literal witness family.** I transcribed the family
  exactly as the task describes it. I am not fully confident that
  `∏_{i<ℓ} (∑_{j<e} x_{blk i j})` is literally `{0,1}`-valued and of
  polynomial degree `≤ d` on the slice for all `ℓ` (naively it is a
  product of `ℓ` linear forms, degree `ℓ`, and a block count `|S ∩ B_i|`
  can exceed `1`). The intended construction in Filmus–Ihringer presumably
  relies on a degree collapse on the slice (where `∑` of all coordinates
  is the constant `k`) or on a slightly more refined function than the
  bare product. `boolean_degree_d_on_slice_not_junta_witnessed` therefore
  faithfully mirrors the task's phrasing but its `IsBoolean` / `HasDegreeLE`
  conjuncts should be treated as "as claimed by the source" rather than
  independently sanity-checked. The pure-existence form
  `boolean_degree_d_on_slice_not_junta` is not subject to this doubt.

- **Guessed Mathlib identifiers**: `MvPolynomial.totalDegree`,
  `MvPolynomial.eval`, `MvPolynomial.X` (not used in the final file),
  `Finset` intersection notation `∩` on `Finset (Fin n)`, and the
  `∏ / ∑` `BigOperators` notation. These are standard; exact names/paths
  not compiler-verified here.

- `Slice n k` is a bare `def` (a subtype); no `Fintype`/`Nonempty`
  instances are asserted. The statements are still meaningful (vacuous
  when the slice is empty), and the hypotheses `2 * k ≤ n` keep the slice
  nonempty in the relevant ranges.
