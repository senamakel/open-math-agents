import OMAReductions.R_OeisA195441_conjecture_R1_H2_R1
import Mathlib

/-! The semiprime case has three fixed small-prime digit-sum obstructions. -/

namespace OMA.R_OeisA195441_conjecture_R1_H2_R1_H2_R1

private theorem expand_digits (b : ℕ) (L : List ℕ) :
    ∃ E : List ℕ, E.length = L.sum ∧
      (E.map (fun i => b^i)).sum = Nat.ofDigits b L := by
  have hfactor (E : List ℕ) :
      (E.map (fun i => b^(i+1))).sum = b * (E.map (fun i => b^i)).sum := by
    induction E with
    | nil => simp
    | cons i E ih =>
      simp only [pow_succ] at ih
      simp only [List.map_cons, List.sum_cons, pow_succ]
      rw [ih]
      ring
  induction L with
  | nil => exact ⟨[],rfl,rfl⟩
  | cons d L ih =>
    obtain ⟨E,hlen,hval⟩ := ih
    refine ⟨List.replicate d 0 ++ E.map (·+1), by simp [hlen], ?_⟩
    simp only [List.map_append, List.map_replicate, List.sum_append,
      List.sum_replicate, smul_eq_mul, Nat.ofDigits_cons, List.map_map]
    simp only [Function.comp_def, Nat.add_zero, pow_zero, Nat.mul_one]
    rw [hfactor, hval]

private theorem digit_sum_powers {b n s : ℕ} (hs : (b.digits n).sum = s) :
    ∃ E : List ℕ, E.length = s ∧ (E.map (fun i => b^i)).sum = n := by
  obtain ⟨E,hlen,hval⟩ := expand_digits b (b.digits n)
  refine ⟨E, ?_, ?_⟩
  · simpa [hs] using hlen
  · simpa [Nat.ofDigits_digits] using hval

def H1 : Prop :=
  ∀ q : ℕ, q.Prime → 61 < q → q % 30 = 1 →
    (∃ u v : ℕ, u.Prime ∧ v.Prime ∧ q+1=2*u ∧ q+2=3*v) →
    (7 ∣ q-1 ∧ 11 ∣ q-1 ∧ 31 ∣ q-1) →
    ∃ p : ℕ, p.Prime ∧ ¬p ∣ q-1 ∧ p ≤ (p.digits (q-2)).sum

def H2 : Prop :=
  ∀ q : ℕ, q.Prime → 61 < q → q % 30 = 1 →
    (∃ u v : ℕ, u.Prime ∧ v.Prime ∧ q+1=2*u ∧ q+2=3*v) →
    ( (7 ∣ q-1 ∨ ∃ E : List ℕ, E.length = 5 ∧
          (E.map (fun i => 7^i)).sum = q-2) ∧
      (11 ∣ q-1 ∨ ∃ E : List ℕ, E.length = 9 ∧
          (E.map (fun i => 11^i)).sum = q-2) ∧
      (31 ∣ q-1 ∨ ∃ E : List ℕ, E.length = 29 ∧
          (E.map (fun i => 31^i)).sum = q-2) ) →
    ( (¬7 ∣ q-1 ∧ ∃ E : List ℕ, E.length = 5 ∧
          (E.map (fun i => 7^i)).sum = q-2) ∨
      (¬11 ∣ q-1 ∧ ∃ E : List ℕ, E.length = 9 ∧
          (E.map (fun i => 11^i)).sum = q-2) ∨
      (¬31 ∣ q-1 ∧ ∃ E : List ℕ, E.length = 29 ∧
          (E.map (fun i => 31^i)).sum = q-2) ) →
    ∃ p : ℕ, p.Prime ∧ ¬p ∣ q-1 ∧ p ≤ (p.digits (q-2)).sum

theorem main : H1 → H2 → OMA.R_OeisA195441_conjecture_R1_H2_R1.H2 := by
  intro hall hsparse
  intro q hq hq61 hqmod hsem
  have hq6 : q % 6 = 1 := by
    rw [← Nat.mod_mod_of_dvd q (by norm_num : 6 ∣ 30), hqmod]
  have hq10 : q % 10 = 1 := by
    rw [← Nat.mod_mod_of_dvd q (by norm_num : 10 ∣ 30), hqmod]
  have hn6 : (q-2)%6=5 := by omega
  have hn10 : (q-2)%10=9 := by omega
  have hn30 : (q-2)%30=29 := by omega
  have hmod7 : ((7 : ℕ).digits (q-2)).sum % 6 = 5 := by
    have h := Nat.modEq_digits_sum 6 7 (by norm_num) (q-2)
    change (q-2)%6 = ((7 : ℕ).digits (q-2)).sum%6 at h
    rw [hn6] at h
    exact h.symm
  have hmod11 : ((11 : ℕ).digits (q-2)).sum % 10 = 9 := by
    have h := Nat.modEq_digits_sum 10 11 (by norm_num) (q-2)
    change (q-2)%10 = ((11 : ℕ).digits (q-2)).sum%10 at h
    rw [hn10] at h
    exact h.symm
  have hmod31 : ((31 : ℕ).digits (q-2)).sum % 30 = 29 := by
    have h := Nat.modEq_digits_sum 30 31 (by norm_num) (q-2)
    change (q-2)%30 = ((31 : ℕ).digits (q-2)).sum%30 at h
    rw [hn30] at h
    exact h.symm
  have hsplit7 :
      (∃ p : ℕ, p.Prime ∧ ¬p ∣ q-1 ∧ p ≤ (p.digits (q-2)).sum) ∨
      (7 ∣ q-1 ∨ (¬7 ∣ q-1 ∧ ∃ E : List ℕ, E.length = 5 ∧
        (E.map (fun i => 7^i)).sum = q-2)) := by
    by_cases hd : 7 ∣ q-1
    · exact Or.inr (Or.inl hd)
    · by_cases hs : 7 ≤ ((7 : ℕ).digits (q-2)).sum
      · exact Or.inl ⟨7,by norm_num,hd,hs⟩
      · have heq : ((7 : ℕ).digits (q-2)).sum = 5 := by
          have hh := hmod7
          rw [Nat.mod_eq_of_lt (by omega)] at hh
          omega
        obtain ⟨E,hlen,hval⟩ := digit_sum_powers heq
        exact Or.inr (Or.inr ⟨hd,⟨E,by simpa [heq] using hlen,hval⟩⟩)
  rcases hsplit7 with hw | h7
  · exact hw
  have hsplit11 :
      (∃ p : ℕ, p.Prime ∧ ¬p ∣ q-1 ∧ p ≤ (p.digits (q-2)).sum) ∨
      (11 ∣ q-1 ∨ (¬11 ∣ q-1 ∧ ∃ E : List ℕ, E.length = 9 ∧
        (E.map (fun i => 11^i)).sum = q-2)) := by
    by_cases hd : 11 ∣ q-1
    · exact Or.inr (Or.inl hd)
    · by_cases hs : 11 ≤ ((11 : ℕ).digits (q-2)).sum
      · exact Or.inl ⟨11,by norm_num,hd,hs⟩
      · have heq : ((11 : ℕ).digits (q-2)).sum = 9 := by
          have hh := hmod11
          rw [Nat.mod_eq_of_lt (by omega)] at hh
          omega
        obtain ⟨E,hlen,hval⟩ := digit_sum_powers heq
        exact Or.inr (Or.inr ⟨hd,⟨E,by simpa [heq] using hlen,hval⟩⟩)
  rcases hsplit11 with hw | h11
  · exact hw
  have hsplit31 :
      (∃ p : ℕ, p.Prime ∧ ¬p ∣ q-1 ∧ p ≤ (p.digits (q-2)).sum) ∨
      (31 ∣ q-1 ∨ (¬31 ∣ q-1 ∧ ∃ E : List ℕ, E.length = 29 ∧
        (E.map (fun i => 31^i)).sum = q-2)) := by
    by_cases hd : 31 ∣ q-1
    · exact Or.inr (Or.inl hd)
    · by_cases hs : 31 ≤ ((31 : ℕ).digits (q-2)).sum
      · exact Or.inl ⟨31,by norm_num,hd,hs⟩
      · have heq : ((31 : ℕ).digits (q-2)).sum = 29 := by
          have hh := hmod31
          rw [Nat.mod_eq_of_lt (by omega)] at hh
          omega
        obtain ⟨E,hlen,hval⟩ := digit_sum_powers heq
        exact Or.inr (Or.inr ⟨hd,⟨E,by simpa [heq] using hlen,hval⟩⟩)
  rcases hsplit31 with hw | h31
  · exact hw
  rcases h7 with h7div | h7sparse
  · rcases h11 with h11div | h11sparse
    · rcases h31 with h31div | h31sparse
      · exact hall q hq hq61 hqmod hsem ⟨h7div,h11div,h31div⟩
      · exact hsparse q hq hq61 hqmod hsem
          ⟨Or.inl h7div,Or.inl h11div,Or.inr h31sparse.2⟩ (Or.inr (Or.inr h31sparse))
    · exact hsparse q hq hq61 hqmod hsem
        ⟨Or.inl h7div,Or.inr h11sparse.2,(by
          rcases h31 with h31div | h31sparse
          · exact Or.inl h31div
          · exact Or.inr h31sparse.2)⟩
        (Or.inr (Or.inl h11sparse))
  · exact hsparse q hq hq61 hqmod hsem
      ⟨Or.inr h7sparse.2,(by
        rcases h11 with h11div | h11sparse
        · exact Or.inl h11div
        · exact Or.inr h11sparse.2),(by
        rcases h31 with h31div | h31sparse
        · exact Or.inl h31div
        · exact Or.inr h31sparse.2)⟩
      (Or.inl h7sparse)

end OMA.R_OeisA195441_conjecture_R1_H2_R1_H2_R1
