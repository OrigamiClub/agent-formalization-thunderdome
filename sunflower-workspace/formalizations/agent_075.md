# Agent 075 — note on the formalization

## Form chosen

A single existential-constant statement:

```
∃ C : ℝ, 0 < C ∧ ∀ (k r : ℕ), 0 < k → 0 < r →
  ∀ {α} [DecidableEq α] (W : Finset (Finset α)),
    (∀ A ∈ W, A.card = k) →
    (C * r * max 1 (Real.log k)) ^ k < (W.card : ℝ) →
    ∃ S, S ⊆ W ∧ IsSunflower S r
```

plus a second, essentially equivalent `_threshold` version using
`Nat.ceil` and a `ℕ`-valued strict inequality `⌈bound⌉₊ < W.card`, matching
the "sunflower function `f(k,r) ≤ (C r log k)^k`" phrasing.

## Encoding decisions and why

- **Set representation.** `Finset α` over an ambient `α` with `[DecidableEq α]`;
  the family is `W : Finset (Finset α)`. This is the representation the existing
  Mathlib sunflower material uses, keeps `|W|`, `|A|`, `A ∩ B` all decidable and
  finite with no side finiteness hypotheses, and makes distinctness of members
  automatic (a `Finset` has no duplicates), so I do not state it separately.
- **`α` under the constant.** `α` (and its `DecidableEq` instance) are bound
  *inside* the `∃ C`, so `C` is genuinely absolute and cannot depend on the
  ambient type. The universe of `α` becomes a parameter of the theorem.
- **Sunflower definition.** Explicit core: `IsSunflowerWithCore S Y` says any two
  distinct members meet exactly in `Y`. `IsSunflower S r` bundles `S.card = r`
  with `∃ Y, IsSunflowerWithCore S Y`. This is a verbatim transcription of the
  informal "there is a core `Y` with `Sᵢ ∩ Sⱼ = Y` for all `i ≠ j`". Pairwise
  petal disjointness and the "in ≥2 ⇒ in all" property are consequences, not
  separately asserted.
- **Petals.** No nonemptiness required on `A \ Y` (the informal statement does
  not require it; `r` distinct equal-size sets with common intersection `Y` can
  still have a member equal to `Y` only if `k = |Y|`, an edge case I did not want
  to exclude).
- **`r` petals.** `S.card = r` with `S ⊆ W`. Because `S` is a `Finset`, this is
  exactly "`r` distinct sets".
- **Logarithm / small `k`.** `Real.log` (natural log; the constant `C` absorbs
  the base). `Real.log k = 0` for `k ≤ 1`, which would make the `k = 1` instance
  false, so the bound uses `max 1 (Real.log k)`. For all large `k` this is just
  `Real.log k`, so the asymptotic content is unchanged; the guard only rescues
  `k = 1`. `k = 0` is excluded by `0 < k` anyway (and `max 1 (Real.log 0) = 1`
  keeps it harmless in the `_threshold` form). `0 < r` likewise assumed.
- **Cardinality comparison.** Main version: strict `<` between reals, with
  `(W.card : ℝ)` cast from `ℕ`, mirroring `|W| > (C r log k)^k`. Threshold
  version: `Nat.ceil` of the bound, strict `<` in `ℕ`.
- **`C` existential vs named.** Existential and positive (`0 < C`), inside the
  theorem — this is the "absolute constant" of the statement and keeps the file
  self-contained with no axioms.

## Uncertainties

- Mathlib may already define a sunflower predicate (plausibly `Finset.IsSunflower`
  or `Set.IsSunflower`, in `Mathlib.Combinatorics.SetFamily.Sunflower`, with a
  classic Erdős–Rado bound theorem such as `Finset.exists_isSunflower`). I could
  not verify the exact name/signature without a compiler, so I defined my own
  predicates under `namespace Agent075` (`IsSunflowerWithCore`, `IsSunflower`) to
  avoid a name clash and to make the statement unambiguous. If the Mathlib
  predicate exists and matches, this definition should be defeq/iff to it.
- `import Mathlib` (blanket import) assumed available; only `Real.log`,
  `Nat.ceil` (`⌈·⌉₊`), `Finset` API are actually needed.
- Coercions written explicitly (`(r : ℝ)`, `(k : ℝ)`, `(W.card : ℝ)`); I believe
  elaboration would insert them anyway, but made them explicit to be safe.
- Instance binder `[DecidableEq α]` inside a `∀` after `{α : Type*}`: I believe
  this is accepted in term-level `∀`; if not, it would move to `variable`/section
  form, but then `α` could not sit under the `∃ C`. Kept as-is as the faithful
  choice.
