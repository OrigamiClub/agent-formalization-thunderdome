# Agent 063 — formalization note

## What I stated

Statement only, three `theorem … := by sorry`:

1. `filmus_ihringer_forward` — the forward direction. `∃ M : ℕ` (the constant `m(d)`)
   quantified *before* `k`, `n`, `f`, so `M` depends only on `d`.
2. `filmus_ihringer_converse` — the converse in pure existential form: for fixed
   `1 ≤ k < 2d` and any `m`, an `n ≥ 2k` and a bad function exist.
3. `filmus_ihringer_converse_explicit` — the converse, but exhibiting the explicit
   witness polynomial `∏ i, ∑_{v ∈ blocks i} X v`.

## Encoding decisions

- **Slice**: `Slice n k := {S : Finset (Fin n) // S.card = k}`. Subtype of `Finset (Fin n)`
  is the most direct reading of `{S ⊆ {1,…,n} : |S| = k}` and makes "`S ∩ J`" literally
  `S.1 ∩ J`.
- **Coordinates / parameters**: `n k d m` are all `ℕ`, carried as explicit binders;
  the ambient coordinate set is `Fin n`. Hypotheses `1 ≤ d`, `2*d ≤ k`, `2*k ≤ n`,
  `1 ≤ k`, `k < 2*d` written with `*` and `≤`/`<` on `ℕ`.
- **Boolean codomain**: functions are `Slice n k → ℝ` with a separate predicate
  `IsBoolean f : ∀ S, f S = 0 ∨ f S = 1`. Real-valued is forced by the polynomial
  notion of degree; keeping `{0,1} ⊆ ℝ` avoids a coercion layer.
- **Degree**: `HasSliceDegreeLE f d` = `∃ p : MvPolynomial (Fin n) ℝ`, `p` multilinear
  (`IsMultilinear p : ∀ i, p.degreeOf i ≤ 1`), `p.totalDegree ≤ d`, and `f` agrees with
  `MvPolynomial.eval (indicator S) p` on every slice point. This is the "agrees on the
  slice with a multilinear real polynomial of total degree ≤ d evaluated at the indicator
  vector" phrasing verbatim. `indicator S i = if i ∈ S.1 then 1 else 0`.
- **Junta**: `IsJunta f m` = `∃ J : Finset (Fin n)`, `J.card ≤ m`, and
  `∀ S T, S.1 ∩ J = T.1 ∩ J → f S = f T` (value depends only on `S ∩ J`).
- **`m(d)`**: existential `∃ M : ℕ` inside the statement rather than an explicit
  `m : ℕ → ℕ`. "There is a constant" reads most naturally as an existential and keeps
  the statement free of an unspecified arithmetic function.
- **Explicit family**: abstracted as `blocks : Fin ℓ → Finset (Fin n)` with
  `(blocks i).card = min d k`, pairwise disjoint. The witness polynomial is
  `∏ i : Fin ℓ, ∑ v ∈ blocks i, X v`. I dropped the literal consecutive indexing
  `x_{(i-1)e+j}` because disjoint size-`e` blocks are equivalent under the symmetric
  group acting on the slice, and this avoids `Fin n` index arithmetic / bound proofs.
  `ℓ` is existentially chosen (large) so the conclusion is `¬ IsJunta f m` for the given
  `m`, matching how the family is used ("for every `m` … not an `m`-junta").

## Uncertainties

- **Roles of `ℓ` and `e` / "not `ℓe`-juntas".** Taken literally, the given formula
  `∏_{i=1}^{ℓ}(∑_{j=1}^{e} x_{(i-1)e+j})` with `e = min(d,k)` has `ℓ` factors and depends
  on exactly `ℓe` coordinates, so it is trivially an `ℓe`-junta, and for `d = 1`
  (`e = 1`, `k = 1`) it degenerates to `x_1⋯x_ℓ ≡ 0` on the slice. I suspect the paper's
  construction either swaps the roles (`e` factors, each a sum of `ℓ` variables) or means
  "not an `(ℓe−1)`-junta" (every relevant coordinate essential). I stated the operational
  consequence `¬ IsJunta f m` (with `ℓ` free) which is robust to this ambiguity, and I
  assert `IsBoolean`/`HasSliceDegreeLE f d` for the product as written, trusting the
  source; a literal transcription may need `e`/`ℓ` swapped and/or the block-sum products
  replaced by their `0/1` indicators.
- **`totalDegree ≤ d` for the explicit witness.** The product of `ℓ` block-sums has
  multilinear total degree `ℓ` as a free polynomial; the claim `≤ d` relies on the slice
  identity `∑_i x_i = k` collapsing it. This is the crux of the paper and is left to the
  (omitted) proof.
- **Guessed Mathlib identifiers**: `MvPolynomial.degreeOf`, `MvPolynomial.totalDegree`,
  `MvPolynomial.eval`, `MvPolynomial.X`, and dot-notation argument order for
  `p.degreeOf i` (expected to resolve to `degreeOf i p`). Big-operator notation
  `∏ i : Fin ℓ, …` / `∑ v ∈ blocks i, …` assumed current. `import Mathlib` used for
  self-containedness.
- Multilinearity is included in `HasSliceDegreeLE` to match "multilinear"; the class of
  degree-`≤ d` functions is unchanged whether or not it is required, so this is a safe
  faithful choice.
