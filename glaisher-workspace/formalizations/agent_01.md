# Glaisher's theorem — agent_01

I represented a partition of `n` directly as a `Multiset ℕ` (not via Mathlib's
`Nat.Partition`), via the predicate `IsPartition n μ := (∀ x ∈ μ, 0 < x) ∧ μ.sum = n`,
i.e. a multiset of strictly positive parts summing to `n`. This sidesteps needing to
recall the exact `Nat.Partition` field/lemma names.

The "no part divisible by `k`" condition is `∀ x ∈ μ, ¬ k ∣ x`, defining the set
`NoMultipleParts n k`. The "every part repeated fewer than `k` times" condition uses
`Multiset.count x μ < k` for each `x ∈ μ`, defining `BoundedMultiplicityParts n k`.

The theorem `glaisher_agent01` states the equality as a cardinality equality,
`Nat.card (NoMultipleParts n k) = Nat.card (BoundedMultiplicityParts n k)`, using
`Nat.card` on the two `Set (Multiset ℕ)` (via the standard `Set → Type` coercion) rather
than exhibiting an explicit bijection. I took `k ≥ 2` as an explicit hypothesis, matching
the "fix an integer k ≥ 2" framing (k = 2 is Euler's odd/distinct-parts theorem). Both
sets are in fact finite (parts are bounded by `n`), so `Nat.card` gives the honest finite
count rather than defaulting to 0.
