import OMAReductions.R_OeisA76495_conjecture_R1

open ArithmeticFunction

namespace OMA.R_OeisA76495_conjecture_R1_H1_R1

/-- Five distinct prime factors, with five absent from the support. The divisor-sum
equation in this branch admits a finite mixed prime and exponent search. -/
def H1 : Prop :=
  ∀ n : ℕ, Odd n → IsSquare n → n.primeFactors.card = 5 → ¬ (5 ∣ n) →
    sigma 1 n % n ≠ 5

/-- Five distinct prime factors, with five in the support. This branch has its own
congruence constraint from the divisor sum modulo five. -/
def H2 : Prop :=
  ∀ n : ℕ, Odd n → IsSquare n → n.primeFactors.card = 5 → 5 ∣ n →
    sigma 1 n % n ≠ 5

/-- Odd squares beyond the five-prime range. -/
def H3 : Prop :=
  ∀ n : ℕ, Odd n → IsSquare n → 6 ≤ n.primeFactors.card →
    sigma 1 n % n ≠ 5

/-- Odd nonsquares, for which the divisor sum is even. -/
def H4 : Prop :=
  ∀ n : ℕ, Odd n → ¬ IsSquare n → 8 ≤ n.primeFactors.card →
    sigma 1 n % n ≠ 5

theorem main : H1 → H2 → H3 → H4 → OMA.R_OeisA76495_conjecture_R1.H1 := by
  intro hWithoutFive hWithFive hSquare hNonsquare n hn hcard hshape
  by_cases hs : IsSquare n
  · by_cases hcount : n.primeFactors.card = 5
    · by_cases hd : 5 ∣ n
      · exact hWithFive n hn hs hcount hd
      · exact hWithoutFive n hn hs hcount hd
    · exact hSquare n hn hs (by omega)
  · exact hNonsquare n hn hs (hshape.resolve_left hs)

end OMA.R_OeisA76495_conjecture_R1_H1_R1
