# Agent 10 — Glaisher's theorem

**Partition representation.** I used Mathlib's built-in `Nat.Partition n`
structure directly: a partition is a `Multiset ℕ` (`parts`) together with
proofs that every part is positive (`parts_pos`) and the parts sum to `n`
(`parts_sum`). No custom encoding of partitions was introduced.

**"No part divisible by k".** Encoded as `∀ x ∈ p.parts, ¬ k ∣ x` on the
underlying multiset — directly says every element of the multiset fails
divisibility by `k`.

**"Every part occurs fewer than k times".** Encoded via `Multiset.count`:
`∀ x ∈ p.parts, p.parts.count x < k`, i.e. for every part value `x`
appearing in the multiset, its multiplicity in the multiset is strictly
less than `k` (equivalently, no part is repeated `k` or more times).

**Statement form.** I stated the theorem as a cardinality equality,
`Nat.card {A_k-partitions} = Nat.card {B_k-partitions}`, using `Nat.card`
on the two subtypes of `Nat.Partition n` cut out by the predicates above,
rather than exhibiting an explicit bijection. `Nat.card` was chosen over
`Fintype.card`/`Finset.card` so I would not have to commit to (or recall
the exact name of) `Fintype`/`Decidable` instances for these subtypes;
both sets are finite in fact since they embed into the finite type of all
partitions of `n`, so `Nat.card` correctly reports their sizes rather than
the junk value 0. The hypothesis `k ≥ 2` is included as `hk : 2 ≤ k` since
the statement is only meaningful/true for `k ≥ 2` (k = 0, 1 degenerate the
two conditions). I made no other simplifications; `k = 2` specializes this
to Euler's odd-parts/distinct-parts theorem as expected.
