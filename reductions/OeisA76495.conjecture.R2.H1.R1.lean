import OMAReductions.R_OeisA76495_conjecture_R2

open ArithmeticFunction

namespace OMA.R_OeisA76495_conjecture_R2_H1_R1

/-! Split the odd-square branch by support size and whether the five-prime
support contains five. -/

def H1 : Prop :=
  ∀ n : ℕ, Odd n → IsSquare n → n.primeFactors.card = 5 → ¬ (5 ∣ n) →
    sigma 1 n % n ≠ 5

def H2 : Prop :=
  ∀ n : ℕ, Odd n → IsSquare n → n.primeFactors.card = 5 → 5 ∣ n →
    sigma 1 n % n ≠ 5

def H3 : Prop :=
  ∀ n : ℕ, Odd n → IsSquare n → 6 ≤ n.primeFactors.card →
    sigma 1 n % n ≠ 5

theorem main : H1 → H2 → H3 → OMA.R_OeisA76495_conjecture_R2.H1 := by
  intro hWithoutFive hWithFive hMorePrimes n hn hcard hsquare
  by_cases hcount : n.primeFactors.card = 5
  · by_cases hfive : 5 ∣ n
    · exact hWithFive n hn hsquare hcount hfive
    · exact hWithoutFive n hn hsquare hcount hfive
  · exact hMorePrimes n hn hsquare (by omega)

end OMA.R_OeisA76495_conjecture_R2_H1_R1
