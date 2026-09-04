# Agent 081 — formalization note

## What is stated

One `theorem filmus_ihringer` whose statement is a conjunction of **three** parts:

1. **(I) Positive direction.** `∃ m : ℕ → ℕ` such that for `d ≥ 1`, `k ≥ 2d`, `n ≥ 2k`,
   every Boolean degree-`d` function on the slice `binom([n],k)` is an `m d`-junta.
2. **(II) Sharpness.** For `d ≥ 1` and `1 ≤ k < 2d`, for **every** `M` there is `n ≥ 2k`
   and a Boolean degree-`d` function on `binom([n],k)` that is not an `M`-junta.
   (Kept abstract — an existential over `f` — because the parameters of the explicit
   family below are bounded in terms of `d`, so the family alone does not witness the
   "for every `M`" clause; a construction such as `f(S) = [S ⊆ A]` with `|A|` growing does.)
3. **(III) Explicit family.** `flowerFun n k d ℓ` `= ∏_{i<ℓ} (∑_{j<e} x_{i·e+j})` with
   `e = min d k`. For `1 ≤ ℓ ≤ e` and `n` large it is Boolean, has degree `≤ d`, and is
   not an `M`-junta for any `M < ℓ·e`.

All three are stated; nothing is proved (`:= by sorry`).

## Encoding decisions

- **Slice**: `Slice n k := {S : Finset (Fin n) // S.card = k}`. Ambient coordinate set is
  `Fin n`; `n`, `k`, `d`, `ℓ`, `M` are all plain `ℕ` carried by `∀`/`∃`.
- **Boolean codomain**: functions are `Slice n k → ℝ`, with a side predicate
  `IsBooleanOnSlice f : ∀ S, f S = 0 ∨ f S = 1`. Real-valued is the convenient common
  ground with the polynomial degree notion.
- **Degree ≤ d** (`HasDegreeLE`): `∃ p : MvPolynomial (Fin n) ℝ` with `p.totalDegree ≤ d`,
  `p` multilinear (`∀ i, MvPolynomial.degreeOf i p ≤ 1`), and `f S = eval (indicatorVec S) p`
  for all `S` on the slice. This is the "agrees on the slice with a low-degree multilinear
  polynomial at the indicator vector" definition from the problem statement. Note it is the
  *slice* degree: `flowerFun` has naive degree `ℓ`, but the definition only asks for *some*
  polynomial of degree `≤ d` agreeing on the slice.
- **m-junta** (`IsJunta`): `∃ J : Finset (Fin n)`, `J.card ≤ m`, and `f S = f T` whenever
  `S ∩ J = T ∩ J`.
- **m(d)**: existentially quantified `m : ℕ → ℕ` inside the statement (rather than a fixed
  explicit formula), matching "there is a constant `m(d)`".
- **Explicit family indexing**: block `i` (`i ∈ range ℓ`) is the coordinate window
  `[i·e, i·e+e)` with `e = min d k`; the `i`-th factor is realized as the cardinality of
  `S` restricted to that window (`= ∑_j x_{i·e+j}` at the indicator vector). `flowerFun` is
  a total function for all `n`; the hypotheses `2k ≤ n`, `2(ℓ·e) ≤ n` make it the intended
  object (all blocks fit, room to spare).

## Uncertainties / guesses

- `MvPolynomial.degreeOf` — name and argument order (`degreeOf (i : σ) (p) : ℕ`) written
  in prefix form to avoid a dot-notation mismatch. If absent, multilinearity could be
  dropped (equivalent here, since indicator vectors are `0/1`) or replaced by an
  `IsMultilinear`/support predicate.
- `MvPolynomial.eval`, `MvPolynomial.totalDegree` assumed as named.
- `∏ i ∈ Finset.range ℓ, …` big-operator syntax (`∈` vs `in`) and `Finset.filter` with an
  inferred `DecidablePred` on a decidable `≤/<` predicate over `ℕ`.
- The theorem's phrase "which for `n ≥ 2ℓe` are not `ℓe`-juntas": a function on `ℓe`
  coordinates is trivially an `ℓe`-junta, so I read this as "essentially `ℓe`-ary", i.e.
  **not an `M`-junta for any `M < ℓ·e`**, and stated it that way in (III).
- Constraint `ℓ ≤ min d k` in (III) is my reconstruction: it makes each of the `ℓ` blocks
  meetable by a `k`-set (so `flowerFun` is the `0/1` transversal indicator) and keeps the
  naive degree `ℓ ≤ d`. The source's exact admissible range for `ℓ` was not fully pinned
  down from the prompt.
- Parts (II) and (III) are stated as independent conjuncts; I did not attempt to derive
  one from the other.
