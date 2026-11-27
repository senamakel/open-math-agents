import OMAReductions.R_OeisA76495_conjecture_R1_H1_R1_H4_R1_H2_R1

/-! Split the bounded support certificate by the eighth prime. -/

namespace OMA.R_OeisA76495_conjecture_R1_H1_R1_H4_R1_H2_R1_H1_R1

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

/-- The first bounded window: eighth prime at most 29. -/
def H1 : Prop := ∀ p e : Prefix, Common p e → SmallLast p → p 7 ≤ 29 →
  RatioBound p → Conclusion p e

/-- The second bounded window: eighth prime between 29 and 37. -/
def H2 : Prop := ∀ p e : Prefix, Common p e → SmallLast p →
  (29 < p 7 ∧ p 7 ≤ 37) → RatioBound p → Conclusion p e

/-- The third bounded window: eighth prime between 37 and 41. -/
def H3 : Prop := ∀ p e : Prefix, Common p e → SmallLast p →
  (37 < p 7 ∧ p 7 ≤ 41) → RatioBound p → Conclusion p e

/-- The final bounded window: eighth prime greater than 41. -/
def H4 : Prop := ∀ p e : Prefix, Common p e → SmallLast p → 41 < p 7 →
  RatioBound p → Conclusion p e

theorem main : H1 → H2 → H3 → H4 →
    OMA.R_OeisA76495_conjecture_R1_H1_R1_H4_R1_H2_R1.H1 := by
  intro first second third fourth
  intro p e hmono hprime hexponent hcap hsmall hratio
  have hcommon : Common p e := ⟨hmono, hprime, hexponent, hcap⟩
  by_cases h29 : p 7 ≤ 29
  · exact first p e hcommon hsmall h29 hratio
  · by_cases h37 : p 7 ≤ 37
    · exact second p e hcommon hsmall ⟨by omega, h37⟩ hratio
    · by_cases h41 : p 7 ≤ 41
      · exact third p e hcommon hsmall ⟨by omega, h41⟩ hratio
      · exact fourth p e hcommon hsmall (by omega) hratio

end OMA.R_OeisA76495_conjecture_R1_H1_R1_H4_R1_H2_R1_H1_R1
