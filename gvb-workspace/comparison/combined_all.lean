import Mathlib

namespace Agent01
/-
Gilbert–Varshamov bound (combinatorial / existential form).

Alphabet of size `q` is modelled as `Fin q`, and codewords of length `n` are
modelled as functions `Fin n → Fin q` (i.e. `(Fin q) ^ n` under the standard
Mathlib Pi-type identification). The ambient type `Fin n → Fin q` is a
`Fintype` with `Fintype.card (Fin n → Fin q) = q ^ n`, and has decidable
equality, so `Finset (Fin n → Fin q)` and the Hamming distance between two
codewords both make sense.

We use Mathlib's `hammingDist` (from `Mathlib.InformationTheory.Hamming`),
which for `x y : Fin n → Fin q` is defined as
`(Finset.univ.filter fun i => x i ≠ y i).card`, i.e. exactly "the number of
coordinates in which `x` and `y` differ".

The Gilbert–Varshamov bound: if `M` is small enough relative to the volume
of a Hamming ball of radius `d - 1` (the sum `∑_{i=0}^{d-2} C(n-1,i) (q-1)^i`
counting, for a fixed codeword, an upper bound on the number of other
codewords that could collide with it within distance `< d`), then a code of
size `M` and minimum distance `≥ d` exists.
-/

theorem gvb_bound_agent01
    (q n d M : ℕ)
    (hq : 2 ≤ q) (hn : 0 < n) (hd1 : 1 ≤ d) (hdn : d ≤ n) (hM : 0 < M)
    (hbound :
      M * (∑ i ∈ Finset.range (d - 1), (n - 1).choose i * (q - 1) ^ i) < q ^ n) :
    ∃ C : Finset (Fin n → Fin q),
      C.card = M ∧
      ∀ x ∈ C, ∀ y ∈ C, x ≠ y → d ≤ hammingDist x y := by
  sorry
end Agent01

namespace Agent02
/-
Gilbert–Varshamov bound (combinatorial / existential form).

Setup:
- `q` is the alphabet size, `n` the block length, `d` the desired minimum
  Hamming distance, `M` a target codebook size.
- Codewords are elements of `Fin n → Fin q` (functions from coordinates to
  alphabet symbols), i.e. the ambient space `Fin q`^n.
- Hamming distance between two codewords is `hammingDist`, from
  `Mathlib.InformationTheory.Hamming`, i.e. the number of coordinates on
  which the two functions disagree.

If `M * (∑_{i=0}^{d-2} C(n-1, i) * (q-1)^i) < q^n`, then there is a code
`C` (a `Finset` of codewords) of size exactly `M` in which every pair of
distinct codewords has Hamming distance at least `d`.
-/

theorem gvb_bound_agent02
    (q n d M : ℕ)
    (hq : 2 ≤ q) (hn : 0 < n) (hd1 : 1 ≤ d) (hd2 : d ≤ n) (hM : 0 < M)
    (hbound :
      M * (∑ i ∈ Finset.range (d - 1), (n - 1).choose i * (q - 1) ^ i)
        < q ^ n) :
    ∃ C : Finset (Fin n → Fin q),
      C.card = M ∧
      ∀ x ∈ C, ∀ y ∈ C, x ≠ y → d ≤ hammingDist x y := by
  sorry
end Agent02

namespace Agent03
/-
Gilbert–Varshamov bound (combinatorial/existential form).

Alphabet: `Fin q`, codeword length `n`, so the ambient space of all words is
`Fin n → Fin q`, which has cardinality `q ^ n`.

Hamming distance between two words is taken to be Mathlib's `hammingDist`
(from `Mathlib.InformationTheory.Hamming`), i.e. the number of coordinates
on which the two functions disagree.

Statement: if `q ≥ 2`, `n ≥ 1`, `1 ≤ d ≤ n`, `M ≥ 1`, and

    M * (∑_{i=0}^{d-2} C(n-1, i) * (q-1)^i) < q^n

(encoded below as `∑ i in Finset.range (d - 1), ...`, since
`Finset.range (d - 1) = {0, 1, ..., d - 2}`), then there is a code
`C : Finset (Fin n → Fin q)` of size exactly `M` all of whose distinct
pairs of codewords are at Hamming distance at least `d`.
-/

theorem gvb_bound_agent03
    (q n d M : ℕ)
    (hq : 2 ≤ q)
    (hn : 0 < n)
    (hd1 : 1 ≤ d)
    (hd2 : d ≤ n)
    (hM : 0 < M)
    (hbound :
      M * (∑ i ∈ Finset.range (d - 1), (n - 1).choose i * (q - 1) ^ i) < q ^ n) :
    ∃ C : Finset (Fin n → Fin q),
      C.card = M ∧
      ∀ x ∈ C, ∀ y ∈ C, x ≠ y → d ≤ hammingDist x y := by
  sorry
end Agent03

namespace Agent04
open Finset

/-!
Gilbert–Varshamov bound (combinatorial / existential form).

Alphabet size `q`, block length `n`, minimum distance target `d`, and desired code
size `M` are all natural numbers. Codewords are modeled as functions `Fin n → Fin q`
(the `q^n`-element ambient space), and "Hamming distance at least `d`" between two
codewords `x y` is expressed directly as: the number of coordinates `i : Fin n` on
which `x i ≠ y i` is at least `d` (this is spelled out inline via `Finset.filter`
and `Finset.card` rather than via Mathlib's `hammingDist`, to avoid relying on the
exact signature/namespace of that definition).

The Gilbert–Varshamov inequality
  M * (∑_{i=0}^{d-2} C(n-1, i) * (q-1)^i) < q^n
is encoded with the sum over `Finset.range (d - 1)` (using truncated natural
subtraction), since `Finset.range (d - 1) = {0, 1, ..., d-2}` has exactly `d - 1`
elements, matching the mathematical sum `∑_{i=0}^{d-2}`. When `d = 1` this range is
empty, correctly encoding the (by convention, empty) sum `∑_{i=0}^{-1}`.
-/

theorem gvb_bound_agent04
    (q n d M : ℕ) (hq : 2 ≤ q) (hn : 1 ≤ n) (hd1 : 1 ≤ d) (hd2 : d ≤ n) (hM : 1 ≤ M)
    (hbound :
      M * (∑ i ∈ Finset.range (d - 1), (Nat.choose (n - 1) i) * (q - 1) ^ i)
        < q ^ n) :
    ∃ C : Finset (Fin n → Fin q),
      C.card = M ∧
      ∀ x ∈ C, ∀ y ∈ C, x ≠ y →
        d ≤ (Finset.univ.filter (fun i : Fin n => x i ≠ y i)).card := by
  sorry
end Agent04

namespace Agent05
open Finset

/-- **The Gilbert–Varshamov bound** (combinatorial / existential form).

Let `q ≥ 2` be an alphabet size, `n ≥ 1` a block length, and `d` a desired
minimum Hamming distance with `1 ≤ d ≤ n`. A codeword is a function
`Fin n → Fin q` (a length-`n` string over an alphabet of size `q`), and the
Hamming distance between two codewords is the number of coordinates on which
they differ (`hammingDist`, from `Mathlib.InformationTheory.Hamming`).

If a positive integer `M` satisfies
  `M * (∑_{i=0}^{d-2} C(n-1, i) * (q-1)^i) < q^n`
(the sum ranges over `i ∈ Finset.range (d - 1)`, i.e. `i = 0, …, d - 2`; it
is the empty sum, hence `0`, when `d = 1`), then there exists a code
`C ⊆ (Fin n → Fin q)` (a `Finset` of codewords) with `C.card = M` such that
every two *distinct* codewords of `C` are at Hamming distance at least `d`
from one another. -/
theorem gvb_bound_agent05
    (q n d M : ℕ)
    (hq : 2 ≤ q) (hn : 0 < n) (hd1 : 1 ≤ d) (hd2 : d ≤ n) (hM : 0 < M)
    (hbound :
      M * (∑ i ∈ Finset.range (d - 1), (n - 1).choose i * (q - 1) ^ i)
        < q ^ n) :
    ∃ C : Finset (Fin n → Fin q),
      C.card = M ∧
        ∀ x ∈ C, ∀ y ∈ C, x ≠ y → d ≤ hammingDist x y := by
  sorry
end Agent05

namespace Agent06
/-
Gilbert–Varshamov bound (combinatorial / existential form).

Alphabet of size `q` is modeled as `Fin q`, and codewords of length `n` over
this alphabet as functions `Fin n → Fin q`. The Hamming distance between two
codewords is the number of coordinates on which they differ; we use
Mathlib's `hammingDist` (from `Mathlib.InformationTheory.Hamming`) for this,
which is defined (up to the `Hamming` type-synonym wrapper) as
`(Finset.univ.filter fun i => x i ≠ y i).card`. If `hammingDist` turns out
not to be the exact identifier/API in the Mathlib version being used, the
same quantity can be written inline as
`(Finset.univ.filter (fun i => x i ≠ y i)).card`.

Statement: if `q ≥ 2`, `n ≥ 1`, `1 ≤ d ≤ n`, and a positive integer `M`
satisfies
  M * (∑_{i=0}^{d-2} C(n-1, i) * (q-1)^i) < q^n,
then there is a code `C` (a `Finset` of codewords) with `C.card = M` such
that every two distinct codewords of `C` have Hamming distance at least `d`.
-/

theorem gvb_bound_agent06
    (q n d M : ℕ)
    (hq : 2 ≤ q) (hn : 0 < n) (hd1 : 1 ≤ d) (hdn : d ≤ n) (hM : 0 < M)
    (hbound :
      M * (∑ i ∈ Finset.range (d - 1), (n - 1).choose i * (q - 1) ^ i) < q ^ n) :
    ∃ C : Finset (Fin n → Fin q),
      C.card = M ∧
        ∀ x ∈ C, ∀ y ∈ C, x ≠ y → d ≤ hammingDist x y := by
  sorry
end Agent06

namespace Agent07
open Finset

/-- **Gilbert–Varshamov bound** (combinatorial / existential form).

If `q ≥ 2` is an alphabet size, `n ≥ 1` a block length, `d` with `1 ≤ d ≤ n`
a target minimum Hamming distance, and `M ≥ 1` satisfies the
Gilbert–Varshamov inequality

  `M * (∑_{i=0}^{d-2} C(n-1, i) * (q-1)^i) < q^n`,

then there exists a code `C ⊆ (Fin n → Fin q)` (i.e. a set of codewords of
length `n` over an alphabet of size `q`) with `|C| = M` such that every two
distinct codewords of `C` have Hamming distance at least `d`. -/
theorem gvb_bound_agent07
    (q n d M : ℕ)
    (hq : 2 ≤ q)
    (hn : 0 < n)
    (hd1 : 1 ≤ d)
    (hd2 : d ≤ n)
    (hM : 0 < M)
    (hbound :
      M * (∑ i ∈ Finset.range (d - 1), (n - 1).choose i * (q - 1) ^ i)
        < q ^ n) :
    ∃ C : Finset (Fin n → Fin q),
      C.card = M ∧
      ∀ x ∈ C, ∀ y ∈ C, x ≠ y →
        d ≤ (Finset.univ.filter (fun i : Fin n => x i ≠ y i)).card := by
  sorry
end Agent07

namespace Agent08
open Finset

/-!
Gilbert–Varshamov bound — combinatorial / existential form.

If `q ≥ 2` is an alphabet size, `n > 0` is the code length, `d` with `1 ≤ d ≤ n` is the
desired minimum Hamming distance, and `M > 0` is a target code size satisfying

  `M * (∑_{i=0}^{d-2} C(n-1, i) * (q-1)^i) < q^n`,

then there exists a code `C`, a finset of codewords of length `n` over an alphabet of size
`q` (modeled as `Fin n → Fin q`), with `|C| = M`, such that every two distinct codewords of
`C` are at Hamming distance at least `d` apart.

The alphabet is modeled by `Fin q`, which has cardinality `q` (using `2 ≤ q` to guarantee
`Fin q` is nonempty/well-behaved), and a codeword is a function `Fin n → Fin q`. Hamming
distance between two codewords `x y : Fin n → Fin q` is taken to be
`hammingDist x y = (Finset.univ.filter fun i => x i ≠ y i).card`, i.e. the number of
coordinates in which they differ (`Mathlib.InformationTheory.Hamming`).
-/
theorem gvb_bound_agent08
    (q n d M : ℕ) (hq : 2 ≤ q) (hn : 0 < n) (hd1 : 1 ≤ d) (hd2 : d ≤ n) (hM : 0 < M)
    (hbound :
      M * (∑ i ∈ Finset.range (d - 1), (n - 1).choose i * (q - 1) ^ i) < q ^ n) :
    ∃ C : Finset (Fin n → Fin q),
      C.card = M ∧
      ∀ x ∈ C, ∀ y ∈ C, x ≠ y → d ≤ hammingDist x y := by
  sorry
end Agent08

namespace Agent09
/-
Gilbert–Varshamov bound (combinatorial / existential form).

Setting: alphabet of size `q` (encoded as `Fin q`), block length `n`
(encoded as `Fin n`), so a codeword is a function `Fin n → Fin q` and
the ambient space `Fin n → Fin q` is finite of cardinality `q ^ n`.
A code `C` is a `Finset (Fin n → Fin q)`. Two codewords `x y` have
Hamming distance `≥ d` iff the number of coordinates where they differ
is `≥ d`; this is spelled out inline as
`(Finset.univ.filter (fun i => x i ≠ y i)).card`.

Statement: if `M` codewords are sought with pairwise Hamming distance
at least `d`, and `M` satisfies the Gilbert–Varshamov counting bound
  `M * (∑_{i=0}^{d-2} C(n-1, i) * (q-1)^i) < q^n`,
then such a code of size exactly `M` exists.
-/

theorem gvb_bound_agent09
    (q n d M : ℕ)
    (hq : 2 ≤ q)
    (hn : 0 < n)
    (hd1 : 1 ≤ d)
    (hd2 : d ≤ n)
    (hM : 0 < M)
    (hbound :
      M * (∑ i ∈ Finset.range (d - 1), (n - 1).choose i * (q - 1) ^ i) < q ^ n) :
    ∃ C : Finset (Fin n → Fin q),
      C.card = M ∧
        ∀ x ∈ C, ∀ y ∈ C, x ≠ y →
          d ≤ (Finset.univ.filter (fun i : Fin n => x i ≠ y i)).card := by
  sorry
end Agent09

namespace Agent10
/-!
# Gilbert–Varshamov bound (combinatorial/existential form)

For alphabet size `q ≥ 2`, block length `n ≥ 1`, and desired minimum Hamming
distance `d` with `1 ≤ d ≤ n`: if a positive integer `M` satisfies

  `M * (∑_{i=0}^{d-2} C(n-1, i) * (q-1)^i) < q^n`

then there exists a code `C`, i.e. a `Finset` of codewords (functions
`Fin n → Fin q`, thought of as length-`n` strings over an alphabet of size
`q`), with `|C| = M`, such that every two *distinct* codewords of `C` have
Hamming distance (the number of coordinates in which they differ) at least
`d`.

The Hamming distance between `x y : Fin n → Fin q` is encoded inline as
`(Finset.univ.filter (fun i => x i ≠ y i)).card`, i.e. the cardinality of the
set of coordinates on which `x` and `y` disagree; this avoids relying on a
specific Mathlib `Hamming` API name that we were not fully certain of.

The sum `∑_{i=0}^{d-2} C(n-1, i) * (q-1)^i` is encoded as
`∑ i ∈ Finset.range (d - 1), Nat.choose (n - 1) i * (q - 1) ^ i`, since
`Finset.range (d - 1) = {0, 1, ..., d - 2}` for `d ≥ 1` (and is empty when
`d = 1`, matching the convention that the sum is empty / `0` in that edge
case, forcing `M < q^n`, which is the correct GV statement for `d = 1`).
-/

theorem gvb_bound_agent10
    (q n d M : ℕ) (hq : 2 ≤ q) (hn : 0 < n) (hd1 : 1 ≤ d) (hdn : d ≤ n) (hM : 0 < M)
    (hbound :
      M * (∑ i ∈ Finset.range (d - 1), Nat.choose (n - 1) i * (q - 1) ^ i) < q ^ n) :
    ∃ C : Finset (Fin n → Fin q),
      C.card = M ∧
      ∀ x ∈ C, ∀ y ∈ C, x ≠ y →
        d ≤ (Finset.univ.filter (fun i : Fin n => x i ≠ y i)).card := by
  sorry
end Agent10

namespace Agent11
/-!
# Gilbert–Varshamov bound (combinatorial / existential form)

For alphabet size `q ≥ 2`, block length `n ≥ 1`, and target minimum Hamming
distance `d` with `1 ≤ d ≤ n`: if a positive integer `M` satisfies

  `M * (∑_{i=0}^{d-2} C(n-1, i) * (q-1)^i) < q^n`,

then there exists a code `C ⊆ (Fin n → Fin q)` (thought of as the set of
length-`n` strings over a `q`-ary alphabet) with `|C| = M`, such that every
two distinct codewords of `C` have Hamming distance at least `d`, where the
Hamming distance between `x y : Fin n → Fin q` is encoded inline as the
number of coordinates `i : Fin n` on which `x i ≠ y i`.

Encoding notes:
* The alphabet `Fin q` and ambient space `Fin n → Fin q` are the standard
  Mathlib-style encodings of "q-ary strings of length n"; `Fintype.card
  (Fin n → Fin q) = q ^ n` matches the right-hand side of the hypothesis.
* The sum `∑_{i=0}^{d-2} C(n-1,i) (q-1)^i` (the size of a Hamming ball of
  radius `d-2` around a fixed point in the "one fewer coordinate" space,
  as used in the classical greedy/counting proof of GVB) is written as
  `∑ i in Finset.range (d - 1), (n-1).choose i * (q-1)^i` using truncated
  natural-number subtraction; `Finset.range (d - 1) = {0, ..., d-2}`, and
  when `d = 1` this range is empty, so the sum correctly degenerates to `0`.
* Hamming distance itself is not looked up as a named Mathlib definition;
  it is spelled out directly via `Finset.filter` on `Finset.univ : Finset (Fin n)`
  to avoid guessing at an unfamiliar identifier (Mathlib does have a
  `Hamming` type synonym with a `hammingDist` function, which would be an
  equally faithful alternative encoding).
-/

theorem gvb_bound_agent11
    (q n d M : ℕ) (hq : 2 ≤ q) (hn : 0 < n) (hd1 : 1 ≤ d) (hdn : d ≤ n) (hM : 0 < M)
    (hbound :
      M * (∑ i in Finset.range (d - 1), (n - 1).choose i * (q - 1) ^ i) < q ^ n) :
    ∃ C : Finset (Fin n → Fin q),
      C.card = M ∧
      ∀ x ∈ C, ∀ y ∈ C, x ≠ y →
        d ≤ (Finset.univ.filter (fun i : Fin n => x i ≠ y i)).card := by
  sorry
end Agent11

namespace Agent12
open Finset

/-!
Gilbert–Varshamov bound (combinatorial / existential form).

Let `q ≥ 2` be an alphabet size, `n ≥ 1` a block length, and `d` with
`1 ≤ d ≤ n` a target minimum Hamming distance. Codewords are modeled as
functions `Fin n → Fin q` (length-`n` strings over an alphabet of size
`q`). If a positive integer `M` satisfies

  `M * (∑_{i=0}^{d-2} (n-1).choose i * (q-1)^i) < q^n`

then there exists a code `C`, i.e. a `Finset (Fin n → Fin q)` of size
`M`, such that every two distinct codewords in `C` have Hamming distance
at least `d`.

We spell out the Hamming-distance condition inline as
`d ≤ (univ.filter (fun i => x i ≠ y i)).card`, i.e. `x` and `y` differ
in at least `d` coordinates, rather than relying on Mathlib's
`hammingDist` (whose exact API/import path we were not fully certain
of), to keep the statement self-contained and unambiguous.
-/

theorem gvb_bound_agent12
    (q n d M : ℕ) (hq : 2 ≤ q) (hn : 1 ≤ n) (hd1 : 1 ≤ d) (hd2 : d ≤ n)
    (hM : 0 < M)
    (hbound :
      M * (∑ i ∈ Finset.range (d - 1), (n - 1).choose i * (q - 1) ^ i) < q ^ n) :
    ∃ C : Finset (Fin n → Fin q),
      C.card = M ∧
      ∀ x ∈ C, ∀ y ∈ C, x ≠ y →
        d ≤ (Finset.univ.filter (fun i : Fin n => x i ≠ y i)).card := by
  sorry
end Agent12

namespace Agent13
/-
Gilbert–Varshamov bound (combinatorial / existential form).

Setup: an alphabet of size `q` is modeled as `Fin q`, and a codeword of length `n`
is modeled as a function `Fin n → Fin q`. Two codewords `x y : Fin n → Fin q` have
Hamming distance `≥ d` exactly when they differ in at least `d` of the `n`
coordinates, which we spell out inline as
`d ≤ (Finset.univ.filter (fun i => x i ≠ y i)).card`.

The hypothesis is the classical Gilbert–Varshamov inequality
`M * (∑_{i=0}^{d-2} C(n-1, i) * (q-1)^i) < q^n`,
encoded via `Finset.range (d - 1)` (which enumerates `i = 0, …, d-2`).

The conclusion asserts the existence of a code `C`, i.e. a finite set of
codewords of length `n` over the `q`-ary alphabet, with exactly `M` codewords,
such that every two *distinct* codewords of `C` have Hamming distance at
least `d`.
-/

theorem gvb_bound_agent13
    (q n d M : ℕ)
    (hq : 2 ≤ q)
    (hn : 0 < n)
    (hd1 : 1 ≤ d)
    (hd2 : d ≤ n)
    (hM : 0 < M)
    (hbound :
      M * (∑ i ∈ Finset.range (d - 1), Nat.choose (n - 1) i * (q - 1) ^ i)
        < q ^ n) :
    ∃ C : Finset (Fin n → Fin q),
      C.card = M ∧
      ∀ x ∈ C, ∀ y ∈ C, x ≠ y →
        d ≤ (Finset.univ.filter (fun i : Fin n => x i ≠ y i)).card := by
  sorry
end Agent13

namespace Agent14
open Finset

/-
Gilbert–Varshamov bound (combinatorial existence form).

Alphabet: `Fin q`.  Codeword: a function `Fin n → Fin q` (a length-`n` string
over the alphabet).  Two codewords `x y` "differ in at least `d`
coordinates" iff the finset of indices on which they disagree has size
`≥ d`; this is exactly the Hamming distance, written out inline via
`Finset.filter`/`Finset.card` to avoid depending on a guessed Mathlib name.

The bound: if `M` codewords of length `n` over an alphabet of size `q`
satisfy `M * (∑_{i=0}^{d-2} C(n-1,i) * (q-1)^i) < q^n`, then there exists a
code `C` (a `Finset` of codewords) with exactly `M` codewords, pairwise at
Hamming distance `≥ d`.
-/

theorem gvb_bound_agent14
    (q n d M : ℕ)
    (hq : 2 ≤ q) (hn : 0 < n) (hd1 : 1 ≤ d) (hdn : d ≤ n) (hM : 0 < M)
    (hbound :
      M * (∑ i ∈ Finset.range (d - 1), (n - 1).choose i * (q - 1) ^ i) < q ^ n) :
    ∃ C : Finset (Fin n → Fin q),
      C.card = M ∧
      ∀ x ∈ C, ∀ y ∈ C, x ≠ y →
        d ≤ (Finset.univ.filter (fun i : Fin n => x i ≠ y i)).card := by
  sorry
end Agent14

namespace Agent15
/-
Gilbert–Varshamov bound (combinatorial / existential form).

Alphabet: `Fin q` (a type of cardinality `q`).
Codeword space: `Fin n → Fin q`, functions from coordinates `Fin n` to the alphabet.
Hamming distance between two codewords is taken from Mathlib's `hammingDist`,
defined (for Pi types with `DecidableEq` on each fiber) as the number of
coordinates on which the two functions disagree:
  `hammingDist x y = (Finset.univ.filter fun i => x i ≠ y i).card`.

Statement: if `M` is a positive integer with
  `M * (∑_{i=0}^{d-2} C(n-1, i) * (q-1)^i) < q^n`
then there is a code `C` (a `Finset` of codewords) with `C.card = M` such that
every two distinct codewords of `C` have Hamming distance at least `d`.
-/

theorem gvb_bound_agent15
    (q n d M : ℕ) (hq : 2 ≤ q) (hn : 0 < n) (hd1 : 1 ≤ d) (hdn : d ≤ n) (hM : 0 < M)
    (hbound :
      M * (∑ i ∈ Finset.range (d - 1), (n - 1).choose i * (q - 1) ^ i) < q ^ n) :
    ∃ C : Finset (Fin n → Fin q),
      C.card = M ∧
      ∀ x ∈ C, ∀ y ∈ C, x ≠ y → d ≤ hammingDist x y := by
  sorry
end Agent15

namespace Agent16
/-
Gilbert–Varshamov bound (combinatorial / existential form).

Setup: codewords of length `n` over an alphabet of size `q` are modeled as functions
`Fin n → Fin q` (a `Fintype` of cardinality `q ^ n`). The Hamming distance between two
codewords `x y : Fin n → Fin q` is defined inline as the number of coordinates on which
they differ, `(Finset.univ.filter (fun i => x i ≠ y i)).card`.

Statement: if `q ≥ 2`, `n ≥ 1`, `1 ≤ d ≤ n`, and a positive integer `M` satisfies the
Gilbert–Varshamov inequality
  `M * (∑_{i=0}^{d-2} C(n-1, i) * (q-1)^i) < q^n`,
then there exists a code `C`, i.e. a finite set of codewords of length `n` over the
`q`-symbol alphabet, with `|C| = M`, such that every two distinct codewords of `C` have
Hamming distance at least `d`.
-/

theorem gvb_bound_agent16
    (q n d M : ℕ) (hq : 2 ≤ q) (hn : 0 < n) (hd : 1 ≤ d) (hdn : d ≤ n) (hM : 0 < M)
    (hbound :
      M * (∑ i ∈ Finset.range (d - 1), Nat.choose (n - 1) i * (q - 1) ^ i) < q ^ n) :
    ∃ C : Finset (Fin n → Fin q),
      C.card = M ∧
        ∀ x ∈ C, ∀ y ∈ C, x ≠ y →
          d ≤ (Finset.univ.filter (fun i => x i ≠ y i)).card := by
  sorry
end Agent16

namespace Agent17
open Finset

/-- The Gilbert–Varshamov bound (combinatorial / existential form).

For an alphabet size `q ≥ 2`, code length `n ≥ 1`, and target minimum
Hamming distance `d` with `1 ≤ d ≤ n`: if a positive integer `M` satisfies

  `M * (∑_{i=0}^{d-2} C(n-1, i) * (q-1)^i) < q^n`,

then there exists a code `C`, i.e. a finite set of codewords of length `n`
over an alphabet of size `q` (modeled as `Fin n → Fin q`), with `|C| = M`,
such that every two *distinct* codewords in `C` have Hamming distance at
least `d`. The Hamming distance between `x y : Fin n → Fin q` is taken
here as the number of coordinates on which they differ, encoded inline as
`(Finset.univ.filter (fun i => x i ≠ y i)).card`.

The sum `∑_{i=0}^{d-2} C(n-1, i) * (q-1)^i` (an empty sum, i.e. `0`, when
`d = 1`) is encoded as `∑ i ∈ Finset.range (d - 1), ...`, since
`Finset.range (d - 1) = {0, 1, ..., d - 2}` for `d ≥ 1`. -/
theorem gvb_bound_agent17
    (q n d M : ℕ)
    (hq : 2 ≤ q) (hn : 0 < n) (hd1 : 1 ≤ d) (hd2 : d ≤ n) (hM : 0 < M)
    (hbound :
      M * (∑ i ∈ Finset.range (d - 1), Nat.choose (n - 1) i * (q - 1) ^ i)
        < q ^ n) :
    ∃ C : Finset (Fin n → Fin q),
      C.card = M ∧
      ∀ x ∈ C, ∀ y ∈ C, x ≠ y →
        d ≤ (Finset.univ.filter (fun i : Fin n => x i ≠ y i)).card := by
  sorry
end Agent17

namespace Agent18
/-
Gilbert–Varshamov bound (combinatorial/existential form).

Setting: alphabet size `q ≥ 2`, block length `n ≥ 1`, target minimum Hamming
distance `d` with `1 ≤ d ≤ n`. Codewords are elements of `Fin n → Fin q`
(functions from coordinates to alphabet symbols), and `Fintype.card (Fin n → Fin q) = q ^ n`.

We use Mathlib's `hammingDist` (from `Mathlib.InformationTheory.Hamming`), which for
`x y : ∀ i, β i` with `Fintype ι` and `DecidableEq (β i)` is defined as
`(Finset.univ.filter fun i => x i ≠ y i).card`, i.e. exactly the number of coordinates
in which `x` and `y` differ.

The hypothesis is the classical Varshamov-style sphere-packing inequality:
`M * (∑_{i=0}^{d-2} C(n-1, i) * (q-1)^i) < q^n`,
encoded via `Finset.range (d - 1)` (so `i` ranges over `0, ..., d - 2`, matching the
convention that an empty sum is `0` when `d = 1`).

Conclusion: there exists a code `C : Finset (Fin n → Fin q)` of exactly size `M` such
that every two distinct codewords of `C` have Hamming distance at least `d`.
-/

theorem gvb_bound_agent18
    (q n d : ℕ) (hq : 2 ≤ q) (hn : 1 ≤ n) (hd1 : 1 ≤ d) (hdn : d ≤ n)
    (M : ℕ) (hM : 0 < M)
    (hbound :
      M * (∑ i ∈ Finset.range (d - 1), (n - 1).choose i * (q - 1) ^ i) < q ^ n) :
    ∃ C : Finset (Fin n → Fin q),
      C.card = M ∧
        ∀ x ∈ C, ∀ y ∈ C, x ≠ y → d ≤ hammingDist x y := by
  sorry
end Agent18

namespace Agent19
/-
Gilbert–Varshamov bound (combinatorial/existential form).

Setting: alphabet of size `q` is modeled as `Fin q`, codewords of length `n`
are functions `Fin n → Fin q`, and a "code" is a `Finset` of such codewords.
The Hamming distance condition "every two distinct codewords differ in at
least `d` coordinates" is spelled out inline as a cardinality condition on
the filtered set of coordinates where the two codewords disagree.

If `M` is small enough relative to the Gilbert–Varshamov sum
  ∑_{i=0}^{d-2} C(n-1, i) * (q-1)^i
(encoded below as `∑ i in Finset.range (d - 1), (n - 1).choose i * (q - 1) ^ i`,
since `Finset.range (d - 1)` ranges over `i = 0, 1, ..., d - 2`), then there
exists a code `C` of size exactly `M` with minimum Hamming distance at
least `d`.
-/

theorem gvb_bound_agent19
    (q n d M : ℕ) (hq : 2 ≤ q) (hn : 0 < n) (hd : 1 ≤ d) (hdn : d ≤ n)
    (hM : 0 < M)
    (hbound :
      M * (∑ i in Finset.range (d - 1), (n - 1).choose i * (q - 1) ^ i)
        < q ^ n) :
    ∃ C : Finset (Fin n → Fin q),
      C.card = M ∧
        ∀ x ∈ C, ∀ y ∈ C, x ≠ y →
          d ≤ (Finset.univ.filter (fun i => x i ≠ y i)).card := by
  sorry
end Agent19

namespace Agent20
/-
Gilbert–Varshamov bound (combinatorial existence form).

Setting: alphabet size `q`, block length `n`, minimum distance target `d`,
codewords modeled as functions `Fin n → Fin q`. Hamming distance between
two codewords `x y : Fin n → Fin q` is encoded inline as the cardinality
of the Finset of coordinates on which they differ.

Statement: if `M` is a positive integer with
  M * (∑_{i=0}^{d-2} C(n-1, i) * (q-1)^i) < q^n
then there exists a Finset `C` of codewords with `C.card = M` such that any
two distinct codewords in `C` have Hamming distance at least `d`.
-/

theorem gvb_bound_agent20
    (q n d M : ℕ)
    (hq : 2 ≤ q)
    (hn : 0 < n)
    (hd1 : 1 ≤ d)
    (hd2 : d ≤ n)
    (hM : 0 < M)
    (hbound :
      M * (∑ i ∈ Finset.range (d - 1), (n - 1).choose i * (q - 1) ^ i) < q ^ n) :
    ∃ C : Finset (Fin n → Fin q),
      C.card = M ∧
        ∀ x ∈ C, ∀ y ∈ C, x ≠ y →
          d ≤ (Finset.univ.filter (fun i : Fin n => x i ≠ y i)).card := by
  sorry
end Agent20
