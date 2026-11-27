import OMAReductions.R_OeisA76495_conjecture_R1_H1_R1_H4_R1_H2_R1

/-! Separate the large ninth-prime range from the finite range for the four exceptional prefixes. -/

namespace OMA.R_OeisA76495_conjecture_R1_H1_R1_H4_R1_H2_R1_H2_R1

def H1 : Prop :=
  ∀ p e : Fin 9 → ℕ, StrictMono p → (∀ i, (p i).Prime ∧ 3 ≤ p i) →
    (∀ i, 1 ≤ e i) →
    List.ofFn (fun i : Fin 8 => p i.castSucc) ∈
      ([[3,5,7,11,13,17,19,23], [3,5,7,11,13,17,19,29],
        [3,5,7,11,13,17,19,31], [3,5,7,11,13,17,19,37]] : List (List ℕ)) →
    68482549 < p 8 →
    (∏ i, ∑ j ∈ Finset.range (e i + 1), p i ^ j) ≠ 3 * (∏ i, p i ^ e i) + 5

def H2 : Prop :=
  ∀ p e : Fin 9 → ℕ, StrictMono p → (∀ i, (p i).Prime ∧ 3 ≤ p i) →
    (∀ i, 1 ≤ e i) →
    List.ofFn (fun i : Fin 8 => p i.castSucc) ∈
      ([[3,5,7,11,13,17,19,23], [3,5,7,11,13,17,19,29],
        [3,5,7,11,13,17,19,31], [3,5,7,11,13,17,19,37]] : List (List ℕ)) →
    p 8 ≤ 68482549 →
    (∏ i, ∑ j ∈ Finset.range (e i + 1), p i ^ j) ≠ 3 * (∏ i, p i ^ e i) + 5

theorem main : H1 → H2 → OMA.R_OeisA76495_conjecture_R1_H1_R1_H4_R1_H2_R1.H2 := by
  intro habove hbelow p e hs hp he hprefix
  by_cases hq : p 8 ≤ 68482549
  · exact hbelow p e hs hp he hprefix hq
  · exact habove p e hs hp he hprefix (by omega)

end OMA.R_OeisA76495_conjecture_R1_H1_R1_H4_R1_H2_R1_H2_R1
