import OMAReductions.R_OeisA76495_conjecture_R1_H2_R1

/-! Separate the first even support size when the valuation of two is one. -/

open ArithmeticFunction

namespace OMA.R_OeisA76495_conjecture_R1_H2_R1_H1_R1

/-- The first support size for an even candidate with exactly one factor of two. -/
def H1 : Prop :=
  ∀ n : ℕ, Even n → n.primeFactors.card = 3 → Odd (sigma 1 n) →
    n % 4 = 2 → sigma 1 n % n ≠ 5

/-- At least three odd prime factors in addition to the factor of two. -/
def H2 : Prop :=
  ∀ n : ℕ, Even n → 4 ≤ n.primeFactors.card → Odd (sigma 1 n) →
    n % 4 = 2 → sigma 1 n % n ≠ 5

theorem main : H1 → H2 → OMA.R_OeisA76495_conjecture_R1_H2_R1.H1 := by
  intro hthree hmore n hn hcard hodd htwo
  by_cases h : n.primeFactors.card = 3
  · exact hthree n hn h hodd htwo
  · exact hmore n hn (by omega) hodd htwo

end OMA.R_OeisA76495_conjecture_R1_H2_R1_H1_R1
