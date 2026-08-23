import Mathlib

namespace Agent01
open Multiset

/-- A partition of `n`, represented directly (not via `Nat.Partition`) as a multiset of
positive natural numbers ("parts") whose sum is `n`. Working with `Multiset ℕ` avoids
having to recall the exact field/lemma names of Mathlib's `Nat.Partition` API. -/
def IsPartition (n : ℕ) (μ : Multiset ℕ) : Prop :=
  (∀ x ∈ μ, 0 < x) ∧ μ.sum = n

/-- `A_k(n)`: partitions of `n` none of whose parts is divisible by `k`. -/
def NoMultipleParts (n k : ℕ) : Set (Multiset ℕ) :=
  {μ | IsPartition n μ ∧ ∀ x ∈ μ, ¬ k ∣ x}

/-- `B_k(n)`: partitions of `n` in which every distinct part occurs fewer than `k` times
(i.e. with multiplicity at most `k - 1`), using `Multiset.count` for the multiplicity of a
part. -/
def BoundedMultiplicityParts (n k : ℕ) : Set (Multiset ℕ) :=
  {μ | IsPartition n μ ∧ ∀ x ∈ μ, μ.count x < k}

/-- **Glaisher's theorem.** For every `k ≥ 2` and every `n`, the number of partitions of `n`
into parts not divisible by `k` equals the number of partitions of `n` in which no part is
repeated `k` or more times. Both sets are finite (parts are bounded by `n`, multisets sum to
`n`), so `Nat.card` (applied to the sets via the `Set → Type` coercion) faithfully reports
their cardinalities; the theorem is stated as an equality of these two cardinalities rather
than as an explicit bijection. The case `k = 2` recovers Euler's odd/distinct-parts theorem. -/
theorem glaisher_agent01 (k : ℕ) (hk : 2 ≤ k) (n : ℕ) :
    Nat.card (NoMultipleParts n k) = Nat.card (BoundedMultiplicityParts n k) := by
  sorry
end Agent01

namespace Agent02
/-!
# Glaisher's theorem

For a fixed integer `k ≥ 2`, the number of partitions of `n` into parts
none of which is divisible by `k` equals the number of partitions of `n`
in which no part occurs `k` or more times (i.e. every distinct part
value occurs with multiplicity at most `k - 1`).

A partition of `n` is represented directly as a `Multiset ℕ`, `s`,
satisfying:
  * `∀ i ∈ s, 0 < i`   (all parts are positive), and
  * `s.sum = n`        (the parts sum to `n`).

"No part divisible by `k`" is `∀ i ∈ s, ¬ k ∣ i`.
"No part repeated `k` or more times" is `∀ i ∈ s, s.count i < k`.

The two families of partitions are packaged as `Set (Multiset ℕ)`, and
the theorem is stated as an equality of their `Set.ncard` (cardinality),
matching the classical statement `A_k(n) = B_k(n)`. The special case
`k = 2` recovers Euler's theorem: partitions into odd parts biject with
partitions into distinct parts.
-/

theorem glaisher_agent02 (k : ℕ) (hk : 2 ≤ k) (n : ℕ) :
    {s : Multiset ℕ | (∀ i ∈ s, 0 < i) ∧ s.sum = n ∧ ∀ i ∈ s, ¬ k ∣ i}.ncard
      =
    {s : Multiset ℕ | (∀ i ∈ s, 0 < i) ∧ s.sum = n ∧ ∀ i ∈ s, s.count i < k}.ncard := by
  sorry
end Agent02

namespace Agent03
/-
Glaisher's theorem.

For a fixed integer `k ≥ 2` and every natural number `n`, the number of
partitions of `n` all of whose parts are *not* divisible by `k` equals
the number of partitions of `n` in which every part occurs (with
multiplicity) strictly fewer than `k` times.

We use Mathlib's `Nat.Partition n`, a structure bundling
`parts : Multiset ℕ` together with proofs that every part is positive
(`parts_pos`) and that the parts sum to `n` (`parts_sum`).

- "no part divisible by k" is encoded as `∀ i ∈ p.parts, ¬ k ∣ i`.
- "every part occurs fewer than k times" is encoded via multiset
  multiplicity as `∀ i, p.parts.count i < k` (for `i` not occurring at
  all, `count i = 0 < k` holds automatically, so this correctly only
  constrains parts that actually occur).

`Nat.Partition n` is a finite type (there are finitely many partitions
of a natural number), so we state the theorem as an equality of
`Nat.card` of the two subtypes cut out by these predicates; `Nat.card`
gives the honest finite cardinality here since both subtypes are
finite.
-/

theorem glaisher_agent03 (k : ℕ) (hk : 2 ≤ k) (n : ℕ) :
    Nat.card {p : Nat.Partition n // ∀ i ∈ p.parts, ¬ k ∣ i} =
      Nat.card {p : Nat.Partition n // ∀ i, p.parts.count i < k} := by
  sorry
end Agent03

namespace Agent04
/-
Glaisher's theorem.

We use Mathlib's `Nat.Partition n`, which represents a partition of `n` as a
structure bundling a multiset `parts : Multiset ℕ` together with proofs that
every part is positive and that the parts sum to `n`.

  A_k(n) = partitions of `n` none of whose parts is divisible by `k`
         : { p : Nat.Partition n // ∀ i ∈ p.parts, ¬ k ∣ i }

  B_k(n) = partitions of `n` in which every part value occurs strictly
           fewer than `k` times (i.e. at most `k - 1` times), where the
           multiplicity of a value `i` in the partition is the multiset
           count `p.parts.count i`
         : { p : Nat.Partition n // ∀ i, p.parts.count i < k }

We state Glaisher's theorem as an equality of `Nat.card` of these two
subtypes, for every `k ≥ 2` and every `n`. `Nat.card` is used rather than
`Fintype.card` so that we do not need to exhibit `Fintype`/`Decidable`
instances explicitly; both subtypes are in fact finite since
`Nat.Partition n` is finite for each `n`.
-/

theorem glaisher_agent04 (k : ℕ) (hk : 2 ≤ k) (n : ℕ) :
    Nat.card {p : Nat.Partition n // ∀ i ∈ p.parts, ¬ k ∣ i} =
    Nat.card {p : Nat.Partition n // ∀ i, p.parts.count i < k} := by
  sorry
end Agent04

namespace Agent05
/-!
Glaisher's theorem: for `k ≥ 2`, the number of partitions of `n` into parts none of
which is divisible by `k` equals the number of partitions of `n` in which every part
occurs fewer than `k` times.

We represent a partition of `n` explicitly, without using `Nat.Partition`, as a
`Multiset ℕ` all of whose elements are positive and which sums to `n`.
-/

/-- `s` is a partition of `n`: a multiset of positive naturals summing to `n`. -/
def IsPartition (n : ℕ) (s : Multiset ℕ) : Prop :=
  (∀ x ∈ s, 0 < x) ∧ s.sum = n

/-- Partitions of `n` into parts none of which is divisible by `k`. -/
def GlaisherA (k n : ℕ) : Set (Multiset ℕ) :=
  {s | IsPartition n s ∧ ∀ x ∈ s, ¬ k ∣ x}

/-- Partitions of `n` in which every (distinct) part occurs fewer than `k` times,
i.e. no part is repeated `k` or more times. -/
def GlaisherB (k n : ℕ) : Set (Multiset ℕ) :=
  {s | IsPartition n s ∧ ∀ x ∈ s, s.count x < k}

/-- Glaisher's theorem: for `k ≥ 2` and every `n`, the number of partitions of `n`
into parts not divisible by `k` equals the number of partitions of `n` in which
every part occurs at most `k - 1` times. Stated as an equality of cardinalities of
the two (finite, though finiteness is not asserted here) sets of partitions. -/
theorem glaisher_agent05 (k : ℕ) (hk : 2 ≤ k) (n : ℕ) :
    Nat.card (GlaisherA k n) = Nat.card (GlaisherB k n) := by sorry
end Agent05

namespace Agent06
open Nat

/-- **Glaisher's theorem.**
For a fixed integer `k ≥ 2` and any natural number `n`, the number of
partitions of `n` in which no part is divisible by `k` equals the number of
partitions of `n` in which every part value occurs with multiplicity
strictly less than `k` (i.e. no part is repeated `k` or more times).

We represent a partition of `n` via Mathlib's `Nat.Partition n`, whose
underlying data is a multiset `parts : Multiset ℕ` of positive naturals
summing to `n`. The condition "no part divisible by `k`" is stated as
`∀ x ∈ p.parts, ¬ k ∣ x`, and the condition "every part occurs fewer than
`k` times" is stated using the multiset multiplicity function
`p.parts.count x < k` for every part `x` occurring in `p.parts`. The two
counts are compared as `Nat.card` of the corresponding subtypes of
`Nat.Partition n`.

The special case `k = 2` recovers Euler's classical theorem: partitions
into odd parts (no part divisible by `2`) are equinumerous with partitions
into distinct parts (every part occurs at most once, i.e. with
multiplicity `< 2`). -/
theorem glaisher_agent06 (k : ℕ) (hk : 2 ≤ k) (n : ℕ) :
    Nat.card { p : Nat.Partition n // ∀ x ∈ p.parts, ¬ (k ∣ x) } =
    Nat.card { p : Nat.Partition n // ∀ x ∈ p.parts, p.parts.count x < k } := by
  sorry
end Agent06

namespace Agent07
/-!
Glaisher's theorem.

Representation of "a partition of `n`": Mathlib's `Nat.Partition n`, a structure
bundling a multiset `parts : Multiset ℕ` together with proofs that every part is
positive (`parts_pos`) and that the parts sum to `n` (`parts_sum`). `Nat.Partition n`
carries a `Fintype` instance, so subtypes of it cut out by decidable predicates are
finite and `Nat.card` gives the honest (finite) count.

- "No part of `p` is divisible by `k`" is encoded as `∀ i ∈ p.parts, ¬ k ∣ i`.
- "Every part occurs fewer than `k` times" (i.e. at most `k - 1` times) is encoded
  using `Multiset.count`, as `∀ i ∈ p.parts, p.parts.count i < k`.

The theorem is stated as an equality of `Nat.card` of the two subtypes of
`Nat.Partition n` satisfying these predicates, for every `k ≥ 2` and every `n`.
-/

theorem glaisher_agent07 (k : ℕ) (hk : 2 ≤ k) (n : ℕ) :
    Nat.card {p : n.Partition // ∀ i ∈ p.parts, ¬ k ∣ i} =
      Nat.card {p : n.Partition // ∀ i ∈ p.parts, p.parts.count i < k} := by
  sorry
end Agent07

namespace Agent08
/-
Glaisher's theorem.

Fix k ≥ 2. For every n : ℕ, the number of partitions of n in which no part is
divisible by k equals the number of partitions of n in which every distinct
part occurs strictly fewer than k times (i.e. at most k - 1 times).

Representation choice: we use Mathlib's `Nat.Partition n`, a structure with
field `parts : Multiset ℕ` satisfying `parts_pos` (all parts positive) and
`parts_sum : parts.sum = n`. We do not need those fields explicitly here,
only `p.parts`.

- "no part of p is divisible by k" is encoded as `∀ i ∈ p.parts, ¬ k ∣ i`.
- "every part of p occurs fewer than k times" is encoded via multiset
  multiplicity `Multiset.count`, as `∀ i ∈ p.parts, p.parts.count i < k`.

We state the theorem as an equality of `Set.ncard` of the two defining sets
of partitions of n, rather than as an explicit bijection. `Set.ncard` is used
(instead of `Finset.card`) so that we do not need to separately supply
`Fintype`/`Decidable` instances for these subsets; the statement is correct
regardless (both sets are in fact finite, being subsets of the finite type
`Nat.Partition n`).
-/

theorem glaisher_agent08 (k : ℕ) (hk : 2 ≤ k) (n : ℕ) :
    Set.ncard {p : Nat.Partition n | ∀ i ∈ p.parts, ¬ k ∣ i} =
    Set.ncard {p : Nat.Partition n | ∀ i ∈ p.parts, p.parts.count i < k} := by
  sorry
end Agent08

namespace Agent09
/-
Glaisher's theorem.

Representation of "a partition of n": we use Mathlib's `Nat.Partition n`, a structure
  parts     : Multiset ℕ
  parts_pos : ∀ ⦃i⦄, i ∈ parts → 0 < i
  parts_sum : parts.sum = n

- "No part divisible by k" is encoded as: ∀ j ∈ p.parts, ¬ (k ∣ j).
- "Every part occurs fewer than k times" (no part repeated k or more times) is encoded via
  the multiset's `count` function: ∀ j ∈ p.parts, Multiset.count j p.parts < k.

We state the theorem as an equality of `Nat.card` of the two subtypes of `Nat.Partition n`
cut out by these conditions, for every k ≥ 2 and every n : ℕ.
-/

theorem glaisher_agent09 (k : ℕ) (hk : 2 ≤ k) (n : ℕ) :
    Nat.card {p : Nat.Partition n // ∀ j ∈ p.parts, ¬ (k ∣ j)} =
    Nat.card {p : Nat.Partition n // ∀ j ∈ p.parts, Multiset.count j p.parts < k} := by
  sorry
end Agent09

namespace Agent10
/-
Glaisher's theorem.

We use Mathlib's `Nat.Partition n`, a structure bundling
  * `parts : Multiset ℕ`
  * `parts_pos : ∀ ⦃i⦄, i ∈ parts → 0 < i`
  * `parts_sum : parts.sum = n`
i.e. a multiset of positive naturals summing to `n`.

For a fixed `k ≥ 2` we consider, among all partitions of `n`:
  * `A_k(n)`: those none of whose parts is divisible by `k`
      (`∀ x ∈ p.parts, ¬ k ∣ x`);
  * `B_k(n)`: those in which every part value occurs strictly fewer than
      `k` times (`∀ x ∈ p.parts, p.parts.count x < k`), i.e. no part is
      repeated `k` or more times.

Glaisher's theorem asserts these two collections of partitions of `n`
have the same (finite) cardinality, for every `n`. We phrase this as an
equality of `Nat.card` on the corresponding subtypes of `Nat.Partition n`;
`Nat.card` is well-behaved here since both subtypes are finite (they sit
inside the finite type of all partitions of `n`), and using it lets us
avoid committing to a particular `Fintype`/`Decidable` instance.
-/

theorem glaisher_agent10 (k : ℕ) (hk : 2 ≤ k) (n : ℕ) :
    Nat.card {p : Nat.Partition n // ∀ x ∈ p.parts, ¬ k ∣ x} =
    Nat.card {p : Nat.Partition n // ∀ x ∈ p.parts, p.parts.count x < k} := by
  sorry
end Agent10

namespace Agent11
open Nat

/-!
Glaisher's theorem.

Representation of "a partition of `n`": we use Mathlib's `Nat.Partition n`,
a structure with field `parts : Multiset ℕ` satisfying `parts_pos`
(every part is positive) and `parts_sum : parts.sum = n`. Multiplicities
are tracked by the multiset structure itself (a part `i` occurring `m`
times has `p.parts.count i = m`).

- "No part of `p` is divisible by `k`" is encoded as
  `∀ i ∈ p.parts, ¬ k ∣ i`.
- "Every part occurs fewer than `k` times" (i.e. at most `k - 1` times) is
  encoded as `∀ i, p.parts.count i < k`. Note this is stated for *all*
  naturals `i`, not just `i ∈ p.parts`: for `i ∉ p.parts` we have
  `p.parts.count i = 0 < k` automatically (since `k ≥ 2`), so the
  quantifier over all `i` is equivalent to quantifying only over the
  parts that actually occur.

We state the theorem as an equality of cardinalities (`Nat.card`) of the
two subtypes of `Nat.Partition n` cut out by these predicates, rather than
as an explicit bijection. `Nat.card` is used (instead of `Fintype.card`)
so that we do not have to separately supply/derive `Fintype`/`Decidable`
instances for the subtypes; `Nat.Partition n` is itself a finite type in
Mathlib, so both subtypes are finite and `Nat.card` computes their actual
sizes.
-/

/-- **Glaisher's theorem.** Fix `k ≥ 2`. For every `n`, the number of
partitions of `n` with no part divisible by `k` equals the number of
partitions of `n` in which every part occurs fewer than `k` times
(equivalently, at most `k - 1` times). The case `k = 2` is Euler's
theorem: partitions into odd parts biject with partitions into distinct
parts. -/
theorem glaisher_agent11 (k : ℕ) (hk : 2 ≤ k) (n : ℕ) :
    Nat.card {p : Nat.Partition n // ∀ i ∈ p.parts, ¬ k ∣ i} =
      Nat.card {p : Nat.Partition n // ∀ i, p.parts.count i < k} := by
  sorry
end Agent11

namespace Agent12
open Nat

/-!
Glaisher's theorem.

We represent a partition of `n` using Mathlib's `Nat.Partition n`, a structure
bundling a multiset `parts : Multiset ℕ` of positive naturals summing to `n`
(fields `parts`, `parts_pos`, `parts_sum`).

- "No part of `p` is divisible by `k`" is encoded as
  `∀ i ∈ p.parts, ¬ (k ∣ i)`.
- "Every part occurs fewer than `k` times" (no part repeated `k` or more
  times) is encoded via multiset multiplicity as
  `∀ i ∈ p.parts, p.parts.count i < k`.

We state the theorem as an equality of cardinalities (`Nat.card`) of the two
subtypes of `Nat.Partition n` cut out by these predicates; `Nat.card` is used
so that no `Fintype`/`Decidable` instances need to be supplied explicitly
(both subtypes are finite since `Nat.Partition n` is finite for each `n`).
-/

/-- **Glaisher's theorem.** Fix `k ≥ 2`. For every `n`, the number of
partitions of `n` into parts none of which is divisible by `k` equals the
number of partitions of `n` in which every part occurs fewer than `k` times
(i.e. no part is repeated `k` or more times). The case `k = 2` recovers
Euler's theorem that partitions into odd parts biject with partitions into
distinct parts. -/
theorem glaisher_agent12 (k : ℕ) (hk : 2 ≤ k) (n : ℕ) :
    Nat.card { p : Nat.Partition n // ∀ i ∈ p.parts, ¬ (k ∣ i) } =
    Nat.card { p : Nat.Partition n // ∀ i ∈ p.parts, p.parts.count i < k } := by
  sorry
end Agent12

namespace Agent13
open Nat

/-!
Glaisher's theorem (independent formalization, agent 13).

Representation choice: rather than using Mathlib's `Nat.Partition` structure,
a partition of `n` is represented directly and explicitly as a
`Multiset ℕ` `s` satisfying:
  * `∀ i ∈ s, 0 < i`   (all parts are positive), and
  * `s.sum = n`        (the parts sum to `n`).

This is the standard "multiset of positive naturals summing to n" encoding
of an (unordered) partition, spelled out inline instead of going through a
bundled structure.

The two families of partitions are then the following `Set (Multiset ℕ)`:

  * `glaisherParts k n`  : partitions of `n` with no part divisible by `k`,
      i.e. `∀ i ∈ s, ¬ (k ∣ i)`;
  * `boundedRepParts k n`: partitions of `n` in which every distinct part
      occurs strictly fewer than `k` times, i.e. `∀ i ∈ s, s.count i < k`
      (multiplicity of `i` in the multiset `s` is `< k`).

The theorem is stated as an equality of `Set.ncard` (natural-number
cardinalities of these sets), rather than as an explicit bijection. Since
both sets are finite (bounded-part-count multisets summing to a fixed `n`
form a finite set), `Set.ncard` faithfully counts them and the equality
`Set.ncard (glaisherParts k n) = Set.ncard (boundedRepParts k n)` is a
faithful transcription of "the two counting functions A_k(n) and B_k(n)
agree for every n". Finiteness itself is not asserted here since it is not
needed to *state* the theorem; only the counts are asserted equal.

The hypothesis `k ≥ 2` is required (Glaisher's theorem is stated for
k ≥ 2; k = 2 recovers Euler's odd/distinct-parts theorem).
-/

/-- The set of partitions of `n` (as multisets of positive naturals summing
to `n`) none of whose parts is divisible by `k`. -/
def glaisherParts (k n : ℕ) : Set (Multiset ℕ) :=
  {s : Multiset ℕ | (∀ i ∈ s, 0 < i) ∧ s.sum = n ∧ ∀ i ∈ s, ¬ (k ∣ i)}

/-- The set of partitions of `n` (as multisets of positive naturals summing
to `n`) in which every part occurs strictly fewer than `k` times (no part
is repeated `k` or more times). -/
def boundedRepParts (k n : ℕ) : Set (Multiset ℕ) :=
  {s : Multiset ℕ | (∀ i ∈ s, 0 < i) ∧ s.sum = n ∧ ∀ i ∈ s, s.count i < k}

/-- **Glaisher's theorem.** Fix `k ≥ 2`. For every natural number `n`, the
number of partitions of `n` into parts none of which is divisible by `k`
equals the number of partitions of `n` in which every part occurs fewer
than `k` times. (The case `k = 2` is Euler's theorem: partitions into odd
parts are equinumerous with partitions into distinct parts.) -/
theorem glaisher_agent13 (k : ℕ) (hk : 2 ≤ k) (n : ℕ) :
    (glaisherParts k n).ncard = (boundedRepParts k n).ncard := by
  sorry
end Agent13

namespace Agent14
/-
Glaisher's theorem.

We use Mathlib's `Nat.Partition n`, the type of partitions of `n`, whose
underlying data is a multiset `parts : Multiset ℕ` of positive naturals
summing to `n` (fields `parts_pos : ∀ {i}, i ∈ parts → 0 < i` and
`parts_sum : parts.sum = n`).

For a fixed integer `k ≥ 2`:
* "no part divisible by `k`" is encoded as `∀ j ∈ p.parts, ¬ k ∣ j`;
* "every part occurs fewer than `k` times" is encoded as
  `∀ j ∈ p.parts, Multiset.count j p.parts < k`, i.e. the multiplicity
  of every value occurring in the multiset of parts is strictly less
  than `k`.

We state the theorem as an equality of cardinalities (`Set.ncard`) of
the two corresponding subsets of `Nat.Partition n`, for every `n`.
-/

theorem glaisher_agent14 (k : ℕ) (hk : 2 ≤ k) (n : ℕ) :
    Set.ncard {p : Nat.Partition n | ∀ j ∈ p.parts, ¬ k ∣ j} =
    Set.ncard {p : Nat.Partition n | ∀ j ∈ p.parts, Multiset.count j p.parts < k} := by
  sorry
end Agent14

namespace Agent15
/-
Glaisher's theorem.

We represent a partition of `n` using Mathlib's `Nat.Partition n`, a structure
bundling a multiset `parts : Multiset ℕ` of positive naturals with
`parts.sum = n`.

For a fixed `k ≥ 2` we consider, among all partitions of `n`:
  * `A_k(n)`: those partitions all of whose parts are NOT divisible by `k`;
  * `B_k(n)`: those partitions in which every part value occurs with
    multiplicity strictly less than `k` (i.e. no part is repeated `k`
    or more times), expressed via `Multiset.count`.

Glaisher's theorem asserts these two collections have the same cardinality,
for every `n`. We state this as an equality of `Set.ncard`s of the
corresponding subsets of `Nat.Partition n` (equivalently, one could give an
explicit bijection; we chose the cardinality-equality form as more natural
for a direct statement).
-/

theorem glaisher_agent15 (k : ℕ) (hk : 2 ≤ k) (n : ℕ) :
    Set.ncard {p : Nat.Partition n | ∀ i ∈ p.parts, ¬ k ∣ i} =
    Set.ncard {p : Nat.Partition n | ∀ i ∈ p.parts, p.parts.count i < k} := by
  sorry
end Agent15

namespace Agent16
/-
Glaisher's theorem.

We use Mathlib's `Nat.Partition n`, which represents a partition of `n` as a
structure bundling a multiset `parts : Multiset ℕ` together with proofs that
every element of `parts` is positive (`parts_pos`) and that `parts.sum = n`
(`parts_sum`). `Nat.Partition n` carries a `Fintype`/`DecidableEq` instance in
Mathlib (it is finite, since the parts are bounded by `n`), so we can count
partitions satisfying a predicate with `Finset.filter` over `Finset.univ` and
take `.card`.

* "No part of λ is divisible by k" is encoded as: for every `i ∈ p.parts`,
  `¬ k ∣ i`.
* "Every part occurs at most `k - 1` times" (equivalently, strictly fewer than
  `k` times) is encoded via the multiset multiplicity function
  `Multiset.count`: for every `i ∈ p.parts`, `p.parts.count i < k`.

We state Glaisher's theorem as an equality of `Finset.card`s of these two
filtered sets of partitions, for every `n : ℕ` and every `k ≥ 2`.
-/

theorem glaisher_agent16 (k : ℕ) (hk : 2 ≤ k) (n : ℕ) :
    (Finset.univ.filter
        (fun p : n.Partition => ∀ i ∈ p.parts, ¬ k ∣ i)).card
      =
    (Finset.univ.filter
        (fun p : n.Partition => ∀ i ∈ p.parts, p.parts.count i < k)).card := by
  sorry
end Agent16

namespace Agent17
/-
Glaisher's theorem.

We use Mathlib's `Nat.Partition n`, defined as a structure bundling
`parts : Multiset ℕ`, a proof that every part is positive, and a proof
that the parts sum to `n`.

For `k ≥ 2` and `n : ℕ`:
* `A_k(n)` is the set of partitions of `n` all of whose parts are *not*
  divisible by `k` (formalized as: for every `i` in the parts multiset,
  `¬ (k ∣ i)`).
* `B_k(n)` is the set of partitions of `n` in which every part value
  occurs with multiplicity strictly less than `k` (formalized via
  `Multiset.count`: for every `i : ℕ`, `p.parts.count i < k`; note that
  if `i` does not occur at all this count is `0 < k`, which is
  automatically satisfied since `k ≥ 2`).

We state the theorem as an equality of cardinalities of these two
subtypes of `Nat.Partition n`, using `Nat.card`, which needs no
`Fintype`/`Decidable` instances since `Nat.Partition n` is already
known to be finite in Mathlib.
-/

theorem glaisher_agent17 (k : ℕ) (hk : 2 ≤ k) (n : ℕ) :
    Nat.card {p : Nat.Partition n // ∀ i ∈ p.parts, ¬ (k ∣ i)} =
    Nat.card {p : Nat.Partition n // ∀ i : ℕ, p.parts.count i < k} := by
  sorry
end Agent17

namespace Agent18
/-
Glaisher's theorem.

We represent a partition of `n` using Mathlib's `Nat.Partition n`, a structure
bundling a multiset `parts : Multiset ℕ` of positive naturals summing to `n`.

Given `k ≥ 2`:
* "no part divisible by `k`" is expressed as `∀ p ∈ c.parts, ¬ k ∣ p`.
* "every part occurs fewer than `k` times" is expressed via multiset
  multiplicity: `∀ p ∈ c.parts, c.parts.count p < k`.

We state the theorem as an equality of `Nat.card` of the two corresponding
subtypes of `Nat.Partition n` (both are in fact finite, since `Nat.Partition n`
itself is finite, so `Nat.card` agrees with the naive count).
-/

theorem glaisher_agent18 (k : ℕ) (hk : 2 ≤ k) (n : ℕ) :
    Nat.card {c : Nat.Partition n // ∀ p ∈ c.parts, ¬ (k ∣ p)} =
    Nat.card {c : Nat.Partition n // ∀ p ∈ c.parts, c.parts.count p < k} := by
  sorry
end Agent18

namespace Agent19
open Nat

/-- **Glaisher's theorem.**
Fix `k ≥ 2`. For every `n`, the number of partitions of `n` in which no part
is divisible by `k` equals the number of partitions of `n` in which every
part occurs fewer than `k` times (i.e. with multiplicity at most `k - 1`).

We represent a partition of `n` via Mathlib's `Nat.Partition n`, whose
underlying data is a multiset `parts : Multiset ℕ` of positive naturals
summing to `n`. "No part divisible by `k`" is `∀ i ∈ p.parts, ¬ k ∣ i`.
"Every part occurs fewer than `k` times" is `∀ i ∈ p.parts, p.parts.count i < k`,
using `Multiset.count`. The theorem is stated as an equality of `Nat.card`
of the two corresponding subtypes of `Nat.Partition n`. -/
theorem glaisher_agent19 (k : ℕ) (hk : 2 ≤ k) (n : ℕ) :
    Nat.card {p : Nat.Partition n // ∀ i ∈ p.parts, ¬ (k ∣ i)} =
    Nat.card {p : Nat.Partition n // ∀ i ∈ p.parts, p.parts.count i < k} := by
  sorry
end Agent19

namespace Agent20
open Nat

/-- **Glaisher's theorem.**
For a fixed `k ≥ 2` and every `n : ℕ`, the number of partitions of `n` all of
whose parts are *not* divisible by `k` equals the number of partitions of `n`
in which every part occurs *fewer than `k` times* (i.e. no part is repeated
`k` or more times).

We use Mathlib's `Nat.Partition n`, whose underlying data is a multiset
`parts : Multiset ℕ` of positive naturals with `parts.sum = n`.
- "No part divisible by `k`" is encoded as `∀ i ∈ p.parts, ¬ k ∣ i`.
- "Every part occurs fewer than `k` times" is encoded via multiset
  multiplicity as `∀ i ∈ p.parts, p.parts.count i < k`.

We state the theorem as an equality of `Nat.card` of the two subtypes
(`Nat.card` gracefully handles finiteness, and each subtype here is finite
since it is a subtype of the finite type `Nat.Partition n`). Taking `k = 2`
recovers Euler's theorem: partitions into odd parts biject with partitions
into distinct parts. -/
theorem glaisher_agent20 (k : ℕ) (hk : 2 ≤ k) (n : ℕ) :
    Nat.card {p : Nat.Partition n // ∀ i ∈ p.parts, ¬ k ∣ i} =
    Nat.card {p : Nat.Partition n // ∀ i ∈ p.parts, p.parts.count i < k} := by
  sorry
end Agent20
