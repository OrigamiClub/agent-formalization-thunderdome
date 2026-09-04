# agent_016 — Filmus–Ihringer, statement-only formalization

## What I stated

All three pieces, as separate `theorem … := by sorry`:

1. `filmus_ihringer_junta_upper` — the positive direction. `∀ d ≥ 1, ∃ M, …`,
   so `M = m(d)` is an existential *inside* the statement that depends only on
   `d` (it is bound before `k`, `n`, `f`). For `k ≥ 2d` and `n ≥ 2k`, every
   Boolean degree-`d` function on the slice is an `M`-junta.
2. `filmus_ihringer_junta_lower` — the converse, pure existential form. For
   `1 ≤ k < 2d` and every `m`, there exist `n ≥ 2k` and a Boolean degree-`d`
   function on `binom([n],k)` that is not an `m`-junta.
3. `filmus_ihringer_junta_lower_witnesses` — the converse with the explicit
   family named in the problem.

## Encoding decisions

- **Slice**: a set on the slice is a `Finset (Fin n)`; the constraint
  `S.card = k` is carried as an explicit hypothesis wherever quantified, rather
  than using a subtype `{S // S.card = k}`. This keeps `∩`, `⊆`, `eval` etc.
  defeq-friendly and avoids coercion noise.
- **Boolean codomain**: functions are `f : Finset (Fin n) → ℝ`, with
  "Boolean" a separate predicate `IsBooleanOnSlice` asserting `f S = 0 ∨ f S = 1`
  for `|S| = k`. Real codomain chosen so that "agrees with a real polynomial"
  is a plain equation.
- **Degree ≤ d** (`IsDegreeLE`): existence of `p : MvPolynomial (Fin n) ℝ` with
  `p.totalDegree ≤ d`, `∀ i, p.degreeOf i ≤ 1` (multilinearity, matching the
  wording of the theorem; harmless on `{0,1}`-points), and
  `f S = MvPolynomial.eval (indicator S) p` for every `|S| = k`, where
  `indicator S i = if i ∈ S then 1 else 0`.
- **m-junta** (`IsJunta`): existence of `J : Finset (Fin n)` with `J.card ≤ m`
  such that `S ∩ J = T ∩ J → f S = f T` for `S, T` on the slice. This is the
  "value depends only on `S ∩ J`" formulation.
- **n, k, d**: all plain `ℕ`, passed explicitly; the ambient coordinate set is
  `Fin n`. `m(d)` is an existential `M : ℕ` (not an explicit `m : ℕ → ℕ`), since
  the theorem only asserts existence of the constant.

## Explicit family

`e := min d k`. `block n e i` is `{x : Fin n | i*e ≤ x < i*e + e}` (a `filter`
over `univ`); consecutive blocks partition an initial segment of the
coordinates. `witness n e ℓ S := ∑_{i < ℓ} (if block n e i ⊆ S then 1 else 0)`,
i.e. the count of full blocks inside `S`. This is exactly the evaluation at the
indicator vector of the multilinear polynomial `∑_{i=1}^{ℓ} ∏_{j=1}^{e}
x_{(i-1)e+j}` (total degree `e = min d k ≤ d`).

**Deliberate reading of the family.** The problem text writes the witnesses as
`∏_{i=1}^{ℓ}(∑_{j=1}^{e} x_{(i-1)e+j})` — a *product of ℓ sums*. Taken
literally that polynomial has total degree `ℓ`, and on `binom([n],k)` with `k`
small and `ℓ` large it is identically `0` (some block misses `S`), hence a
`0`-junta — so the literal reading makes the "not an `ℓe`-junta" claim false.
The statement that actually works, and that has degree `min d k ≤ d` and is
`{0,1}`-valued precisely because `k < 2d`, is the *sum of block-monomials*
`∑_{i=1}^{ℓ} ∏_{j=1}^{e} x_{(i-1)e+j}`. I formalized that version. I am fairly
confident this is the intended construction (it is a Boolean degree-`min(d,k)`
function on the slice, supported on the first `ℓe` coordinates, and genuinely
needs all of them).

**Off-by-one in "not `ℓe`-juntas".** `witness n e ℓ` *is* an `ℓe`-junta
(`J` = first `ℓ` blocks, `ℓe` coordinates). What is true and meaningful is that
it is not an `m`-junta for any `m < ℓe`; that is what I stated, and it still
gives the unbounded-junta conclusion by choosing `ℓ` with `ℓe > m`.

## Uncertainties / guessed identifiers

- `MvPolynomial.degreeOf`, `MvPolynomial.totalDegree`, `MvPolynomial.eval` — I
  believe these are the correct current Mathlib names; `eval` is the ring hom
  applied as `MvPolynomial.eval (indicator S) p`.
- No dedicated Mathlib notion of "Boolean function on the slice" / "slice
  degree" is used; all four notions are defined from scratch here.
- Decidability of `block n e i ⊆ S` and of the `filter` predicate is expected to
  be found automatically (`Finset` instances); no `open Classical` added.
- `univ.filter (fun x => …)` argument order assumed to typecheck via dot
  notation on current Mathlib.
