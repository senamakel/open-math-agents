import OMAReductions.R_OeisA76495_conjecture_R2_H1_R1

open ArithmeticFunction

namespace OMA.R_OeisA76495_conjecture_R2_H1_R1_H2_R1

/-! Separate the checked small-support case from the outstanding case with a
prime factor above 31. -/

def H1 : Prop :=
  ∀ n : ℕ, Odd n → IsSquare n → n.primeFactors.card = 5 → 5 ∣ n →
    (∀ p ∈ n.primeFactors, p ≤ 31) → sigma 1 n % n ≠ 5

def H2 : Prop :=
  ∀ n : ℕ, Odd n → IsSquare n → n.primeFactors.card = 5 → 5 ∣ n →
    (∃ p ∈ n.primeFactors, 31 < p) → sigma 1 n % n ≠ 5

theorem main : H1 → H2 → OMA.R_OeisA76495_conjecture_R2_H1_R1.H2 := by
  classical
  intro hsmall hlarge n hn hsquare hcount hfive
  by_cases h : ∀ p ∈ n.primeFactors, p ≤ 31
  · exact hsmall n hn hsquare hcount hfive h
  · exact hlarge n hn hsquare hcount hfive (by
      push Not at h
      exact h)

end OMA.R_OeisA76495_conjecture_R2_H1_R1_H2_R1
