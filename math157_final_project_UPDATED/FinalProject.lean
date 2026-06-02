import Mathlib

open Finset
open BigOperators

/-!
# Math 157 Final Project

## Topic
This project formalizes the theorem that the sum of the first `n` odd numbers is
`n^2`.

The informal theorem is:

  1 + 3 + 5 + ... + (2n - 1) = n^2.

In this Lean file, I index the odd numbers starting at `0`, so the first odd
number is written as `2 * 0 + 1`, the second as `2 * 1 + 1`, and so on. This
means the sum of the first `n` odd numbers is written as

  `∑ i in Finset.range n, (2 * i + 1)`.

## Project goal
The goal of the code component is to turn a familiar induction proof into a
machine-checked Lean proof. This fits the course because it practices the main
ideas of formalization: choosing definitions, breaking a proof into smaller
pieces, using Mathlib, and writing code that a human reader can understand.

## Connection to course themes
One theme from the June 1 lecture was that the code component should be readable
on its own and should not rely only on the documentation component. For that
reason, this file includes comments explaining the mathematical meaning of the
Lean definitions and the structure of the proof.
-/

/--
The `n`th odd number, starting with `n = 0`.

For example:
* `oddTerm 0 = 1`
* `oddTerm 1 = 3`
* `oddTerm 2 = 5`
-/
def oddTerm (n : ℕ) : ℕ :=
  2 * n + 1

/-- The first odd term is `1`. -/
example : oddTerm 0 = 1 := by
  unfold oddTerm
  norm_num

/-- The second odd term is `3`. -/
example : oddTerm 1 = 3 := by
  unfold oddTerm
  norm_num

/-- The third odd term is `5`. -/
example : oddTerm 2 = 5 := by
  unfold oddTerm
  norm_num

/-- The fourth odd term is `7`. -/
example : oddTerm 3 = 7 := by
  unfold oddTerm
  norm_num

/--
The sum of the first `n` odd numbers.

Since `Finset.range n` is `{0, 1, ..., n - 1}`, this represents

  `1 + 3 + 5 + ... + (2 * (n - 1) + 1)`.
-/
def sumOddTerms (n : ℕ) : ℕ :=
  ∑ i in range n, oddTerm i

/-- The sum of the first zero odd numbers is the empty sum, which is `0`. -/
example : sumOddTerms 0 = 0 := by
  unfold sumOddTerms
  simp

/-- The sum of the first one odd number is `1`. -/
example : sumOddTerms 1 = 1 := by
  unfold sumOddTerms oddTerm
  norm_num

/-- The sum of the first two odd numbers is `4`. -/
example : sumOddTerms 2 = 4 := by
  unfold sumOddTerms oddTerm
  norm_num

/-- The sum of the first three odd numbers is `9`. -/
example : sumOddTerms 3 = 9 := by
  unfold sumOddTerms oddTerm
  norm_num

/-- The sum of the first four odd numbers is `16`. -/
example : sumOddTerms 4 = 16 := by
  unfold sumOddTerms oddTerm
  norm_num

/--
A useful rewrite lemma: adding one more odd term extends the finite sum.

Mathematically, this says

  sum of first `n + 1` odd numbers
  = sum of first `n` odd numbers + the next odd number.

Lean proves this using `Finset.sum_range_succ`, a Mathlib theorem about sums
over `Finset.range`.
-/
lemma sumOddTerms_succ (n : ℕ) :
    sumOddTerms (n + 1) = sumOddTerms n + oddTerm n := by
  unfold sumOddTerms
  rw [Finset.sum_range_succ]

/--
Main theorem: the sum of the first `n` odd numbers is `n^2`.

Proof idea:
* Base case: for `n = 0`, the sum is empty, so it is `0 = 0^2`.
* Inductive step: assume the sum of the first `n` odd numbers is `n^2`.
  The next odd number is `2n + 1`, so the next sum is
  `n^2 + 2n + 1`, which is `(n + 1)^2`.

This proof has no `sorry`; the algebra in the last step is handled by `ring`.
-/
theorem sum_first_n_odd (n : ℕ) :
    sumOddTerms n = n ^ 2 := by
  induction n with
  | zero =>
      unfold sumOddTerms
      simp
  | succ n ih =>
      rw [show Nat.succ n = n + 1 by omega]
      rw [sumOddTerms_succ]
      rw [ih]
      unfold oddTerm
      ring

/--
The same theorem written directly with the `Finset` sum notation.

This version makes the final result easy to recognize if someone expects the
statement to be written as a summation instead of using the helper definition
`sumOddTerms`.
-/
theorem sum_first_n_odd_finset (n : ℕ) :
    (∑ i in Finset.range n, (2 * i + 1)) = n ^ 2 := by
  simpa [sumOddTerms, oddTerm] using sum_first_n_odd n
