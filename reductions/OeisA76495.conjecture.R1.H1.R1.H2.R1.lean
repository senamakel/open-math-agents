import OMAReductions.R_OeisA76495_conjecture_R1_H1_R1

/-! Separate the small-support five-prime case from the case with a prime above 31. -/

open ArithmeticFunction

namespace OMA.R_OeisA76495_conjecture_R1_H1_R1_H2_R1

def H1 : Prop :=
  ∀ n : ℕ, Odd n → IsSquare n → n.primeFactors.card = 5 → 5 ∣ n →
    (∀ p ∈ n.primeFactors, p ≤ 31) → sigma 1 n % n ≠ 5

def H2 : Prop :=
  ∀ n : ℕ, Odd n → IsSquare n → n.primeFactors.card = 5 → 5 ∣ n →
    (∃ p ∈ n.primeFactors, 31 < p) → sigma 1 n % n ≠ 5

theorem main : H1 → H2 → OMA.R_OeisA76495_conjecture_R1_H1_R1.H2 := by
  classical
  intro hsmall hlarge n hn hs hc h5
  by_cases h : ∀ p ∈ n.primeFactors, p ≤ 31
  · exact hsmall n hn hs hc h5 h
  · exact hlarge n hn hs hc h5 (by
      push Not at h
      exact h)

end OMA.R_OeisA76495_conjecture_R1_H1_R1_H2_R1
