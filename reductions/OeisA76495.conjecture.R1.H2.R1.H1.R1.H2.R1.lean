import OMAReductions.R_OeisA76495_conjecture_R1_H2_R1_H1_R1
import Mathlib.Tactic
import Mathlib.NumberTheory.ArithmeticFunction.Misc

/-! Split the remaining even valuation-one candidates by their exact odd support size. -/

open ArithmeticFunction

namespace OMA.R_OeisA76495_conjecture_R1_H2_R1_H1_R1_H2_R1

def H1 : Prop :=
  ∀ n : ℕ, Even n → n.primeFactors.card = 4 → Odd (sigma 1 n) →
    n % 4 = 2 → sigma 1 n % n ≠ 5

def H2 : Prop :=
  ∀ n : ℕ, Even n → 5 ≤ n.primeFactors.card → Odd (sigma 1 n) →
    n % 4 = 2 → sigma 1 n % n ≠ 5

theorem main : H1 → H2 → OMA.R_OeisA76495_conjecture_R1_H2_R1_H1_R1.H2 := by
  intro hfour hfive n hn hcard hodd htwo
  by_cases h : n.primeFactors.card = 4
  · exact hfour n hn h hodd htwo
  · exact hfive n hn (by omega) hodd htwo

end OMA.R_OeisA76495_conjecture_R1_H2_R1_H1_R1_H2_R1
