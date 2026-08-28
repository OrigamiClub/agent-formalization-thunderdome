# Agent 057 — improved sunflower lemma, statement note

## Form chosen

Two `theorem ... := by sorry` statements plus one auxiliary `def`:

- `IsSunflower (𝒮 : Finset (Finset α)) (Y : Finset α) : Prop` — "every two
  distinct members of `𝒮` intersect in exactly `Y`".
- `improved_sunflower_lemma` — existence of an absolute `C > 0` such that a
  `k`-uniform family `W` with `|W| > (C r log k)^k` contains a subfamily `𝒮 ⊆ W`
  with `𝒮.card = r` and some core `Y` with `IsSunflower 𝒮 Y`.
- `improved_sunflower_lemma_threshold` — the same content phrased as an upper
  bound on the sunflower function `f(k,r)`: whenever `(C r log k)^k < N`, family
  size `≥ N` forces an `r`-petal sunflower.

## Encoding decisions and why

- **Set representation:** `Finset α` over an ambient type `α`, family
  `W : Finset (Finset α)`, `[DecidableEq α]` for `∩`. Finiteness and
  distinctness of members come for free from `Finset`, so no separate
  distinctness hypothesis is needed. `α` is universe-polymorphic (`Type*`).
- **Absolute constant:** `C` is bound by the outermost `∃`, *before* `α`, `k`,
  `r`, `W`. This makes "absolute constant" literal — `C` cannot depend on the
  ambient type or the parameters. (Lean allows implicit binders like
  `∀ {α : Type*} [DecidableEq α]` inside the body of the `∃`.)
- **Sunflower definition:** explicit core `Y`, via "all pairwise intersections
  equal `Y`". This is equivalent to the "an element in ≥ 2 sets is in all"
  formulation and yields pairwise-disjoint petals. Chose explicit core because
  it is the most directly usable form and avoids committing to a possibly
  nonexistent Mathlib predicate.
- **Number of petals:** conclusion gives *exactly* `𝒮.card = r` (one can always
  shrink a larger sunflower). Hypothesis `1 ≤ r`.
- **Logarithm:** `Real.log` (natural log), with the real-valued inequality
  `(C * r * Real.log k) ^ k < (W.card : ℝ)` after `ℕ → ℝ` coercions. The base of
  the log is absorbed into `C`.
- **Small `k`:** hypothesis `2 ≤ k`, so `Real.log k > 0` and the bound is
  meaningful. `k = 0` (no such uniform family of interest) and `k = 1`
  (`log 1 = 0`, and the lemma degenerates to "`r` distinct singletons form a
  sunflower with empty core") are excluded by this hypothesis rather than
  patched with `log (k+1)` or `max (log k) 1`. Documented in the docstring.
- **Petals nonempty:** not required. At most one member can equal the core, so
  this only permits the mild degeneracy of a single empty petal.
- **Cardinality:** `Finset.card` throughout; uniformity as
  `∀ S ∈ W, S.card = k`.

## Uncertainties

- I did not assume any Mathlib `Sunflower` / sunflower-lemma API exists; I define
  `IsSunflower` locally. If Mathlib does have
  `Finset.Set.Sunflower` / `IsSunflower` / a `Sunflower` structure, names may
  clash or differ.
- `import Mathlib` (whole library) for safety; the precise minimal imports
  (`Mathlib.Analysis.SpecialFunctions.Log.Basic`,
  `Mathlib.Data.Finset.Card`, ...) not pinned down.
- Coercion elaboration: wrote `(k : ℝ)`, `(r : ℝ)`, `(W.card : ℝ)` explicitly to
  avoid ambiguous `ℕ`-vs-`ℝ` `^` and `*`; exact spots where Lean needs the hint
  not verified without a compiler.
- The `_threshold` variant's tie to the textbook definition of `f(k,r)` as a
  least element is informal; I state the forcing property directly rather than
  via `Nat.find`/`sInf`.
