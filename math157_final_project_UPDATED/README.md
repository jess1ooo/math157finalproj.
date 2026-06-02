# Project Purpose
This project formalizes the theorem that the sum of the first n odd numbers equals n².

# Main theorem:

theorem sum_first_n_odd_finset (n : ℕ) :
    (∑ i in Finset.range n, (2 * i + 1)) = n ^ 2

# Files:

FinalProject.lean – Lean code component
Documentation_Component.md – written component

The proof uses mathematical induction together with finite sums from Mathlib. The project was completed individually for the class Math 157 and shows how a familiar mathematical proof can be translated into a machine verified proof in Lean.