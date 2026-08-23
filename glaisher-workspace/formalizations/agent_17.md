# Glaisher's theorem — agent 17 notes

I represented "a partition of n" with Mathlib's `Nat.Partition n`, the structure with fields
`parts : Multiset ℕ`, `parts_pos` (every part positive), and `parts_sum` (parts sum to `n`).
This gives positivity and the sum-to-n condition for free, so I only need to add the two
Glaisher predicates on top.

"No part divisible by k" is encoded as `∀ i ∈ p.parts, ¬ (k ∣ i)`, a direct membership
condition on the parts multiset. "Every part repeated fewer than k times" is encoded via
`Multiset.count`: `∀ i : ℕ, p.parts.count i < k`, quantifying over all naturals rather than
just the parts present (values not occurring have count 0, which is automatically `< k` since
`k ≥ 2`, so this is equivalent to restricting to `i ∈ p.parts`).

I stated the theorem as a `Nat.card` equality between the two subtypes of `Nat.Partition n`
cut out by these predicates, rather than as an explicit bijection — `Nat.card` requires no
`Fintype`/`Decidable` instances and Mathlib already knows `Nat.Partition n` is finite, so this
gives a clean, instance-free cardinality statement. The hypothesis `2 ≤ k` is included as an
explicit argument to match "fix an integer k ≥ 2" in the problem statement.

I was not 100% certain of the exact current Mathlib field/lemma names beyond the `Nat.Partition`
structure fields (`parts`, `parts_pos`, `parts_sum`), which I recall from memory rather than by
inspecting the library directly (no Lean environment was available to check).
