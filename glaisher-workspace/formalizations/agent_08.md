# Glaisher's theorem — formalization notes (agent 08)

I represented a partition of `n` using Mathlib's `Nat.Partition n` type, whose
`parts : Multiset ℕ` field is the underlying multiset of positive parts
summing to `n`. This avoids re-deriving the partition axioms from scratch and
reuses whatever finiteness/API infrastructure Mathlib already has for it.

The "no part divisible by k" condition is encoded pointwise over the multiset
as `∀ i ∈ p.parts, ¬ k ∣ i`. The "each part repeated fewer than k times"
condition is encoded using multiset multiplicity, `∀ i ∈ p.parts, p.parts.count i < k`,
i.e. every value that appears in the multiset appears with count strictly
less than `k`.

I stated the theorem as an equality of `Set.ncard` of the two subsets of
`Nat.Partition n` cut out by these predicates, rather than as an explicit
bijection, since a cardinality statement is more directly comparable across
independent formalizations and `Set.ncard` sidesteps the need to manufacture
`Fintype`/`DecidablePred` instances for the two conditions. I added the
hypothesis `2 ≤ k` since the theorem is only meaningful/true for `k ≥ 2`
(for `k = 0, 1` the "divisible by k" and "repeated < k times" conditions
degenerate). Main uncertainty: I am not 100% certain of the exact field name
`parts` and the exact statement of `parts_pos`/`parts_sum` in the current
Mathlib `Nat.Partition` definition, though I am fairly confident `parts` is
correct; `Multiset.count` is standard Mathlib API and should apply directly
to `p.parts : Multiset ℕ`.
