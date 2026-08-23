# Glaisher's theorem — formalization notes (agent_20)

I represented a partition using Mathlib's built-in `Nat.Partition n` structure, whose
core data is a multiset `parts : Multiset ℕ` of positive naturals summing to `n`
(with the accompanying positivity and sum-condition fields baked into the structure).

- **"No part divisible by k"** is encoded as the predicate `∀ i ∈ p.parts, ¬ k ∣ i`
  on the underlying multiset.
- **"Every part occurs fewer than k times"** is encoded using multiset multiplicity:
  `∀ i ∈ p.parts, p.parts.count i < k`, i.e. for every part value appearing in the
  partition, its count (multiplicity) in the multiset is strictly less than `k`.

I stated the theorem as a **cardinality equality** (`Nat.card` of the two subtypes
`{p : Nat.Partition n // ...}`) rather than an explicit bijection, since `Nat.card`
is convenient and total (it handles finiteness automatically via typeclass search,
and both subtypes are finite because `Nat.Partition n` itself is finite). The
hypothesis `k ≥ 2` is included as an explicit argument, matching the natural-language
statement; taking `k = 2` recovers Euler's classical theorem (odd parts ↔ distinct
parts). One simplification: I did not separately verify that `Nat.Partition n` carries
a `Fintype`/`Finite` instance in the exact Mathlib version this would compile against —
I am fairly confident such an instance exists (partitions of `n` are manifestly finite),
but flag this as the one identifier/instance I could not double-check without a
compiler.
