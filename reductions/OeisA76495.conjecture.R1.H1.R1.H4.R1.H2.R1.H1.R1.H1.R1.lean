import OMAReductions.R_OeisA76495_conjecture_R1_H1_R1_H4_R1_H2_R1_H1_R1

/-! Split the smallest eighth-prime support by the ninth prime. -/

namespace OMA.R_OeisA76495_conjecture_R1_H1_R1_H4_R1_H2_R1_H1_R1_H1_R1

open ArithmeticFunction

private abbrev Prefix := Fin 9 → ℕ

private def Common (p e : Prefix) : Prop :=
  StrictMono p ∧ (∀ i, (p i).Prime ∧ 3 ≤ p i) ∧ (∀ i, 1 ≤ e i) ∧
    (∀ i : Fin 8, p i.castSucc ≤ (![8,12,15,19,23,28,38,77] : Fin 8 → ℕ) i)

private def SmallLast (p : Prefix) : Prop := p 8 ≤ 3009

private def RatioBound (p : Prefix) : Prop :=
  (∏ i : Fin 8, p i.castSucc) < 3 * (∏ i : Fin 8, (p i.castSucc - 1))

private def Conclusion (p e : Prefix) : Prop :=
  (∏ i, ∑ j ∈ Finset.range (e i + 1), p i ^ j) ≠
    3 * (∏ i, p i ^ e i) + 5

/-- The first ninth-prime interval in the p₇ ≤ 29 case. -/
def H1 : Prop := ∀ p e : Prefix, Common p e → SmallLast p → p 7 ≤ 29 →
  RatioBound p → p 8 < 1278 → Conclusion p e

/-- The middle ninth-prime interval in the p₇ ≤ 29 case. -/
def H2 : Prop := ∀ p e : Prefix, Common p e → SmallLast p → p 7 ≤ 29 →
  RatioBound p → (1278 ≤ p 8 ∧ p 8 < 2046) → Conclusion p e

/-- The final ninth-prime interval in the p₇ ≤ 29 case. -/
def H3 : Prop := ∀ p e : Prefix, Common p e → SmallLast p → p 7 ≤ 29 →
  RatioBound p → 2046 ≤ p 8 → Conclusion p e

theorem main : H1 → H2 → H3 →
    OMA.R_OeisA76495_conjecture_R1_H1_R1_H4_R1_H2_R1_H1_R1.H1 := by
  intro first second third
  intro p e hcommon hsmall h29 hratio
  by_cases h1278 : p 8 < 1278
  · exact first p e hcommon hsmall h29 hratio h1278
  · by_cases h2046 : p 8 < 2046
    · exact second p e hcommon hsmall h29 hratio ⟨by omega, h2046⟩
    · exact third p e hcommon hsmall h29 hratio (by omega)

end OMA.R_OeisA76495_conjecture_R1_H1_R1_H4_R1_H2_R1_H1_R1_H1_R1
