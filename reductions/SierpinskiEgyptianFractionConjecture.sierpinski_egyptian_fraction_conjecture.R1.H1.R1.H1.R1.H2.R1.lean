import OMAReductions.R_SierpinskiEgyptianFractionConjecture_sierpinski_egyptian_fraction_conjecture_R1_H1_R1_H1_R1

open SierpinskiEgyptianFractionConjecture
open OMA.R_SierpinskiEgyptianFractionConjecture_sierpinski_egyptian_fraction_conjecture_R1

namespace OMA.R_SierpinskiEgyptianFractionConjecture_sierpinski_egyptian_fraction_conjecture_R1_H1_R1_H1_R1_H2_R1

private lemma decomposition_of_fourteen_divisor (p r : ℕ)
    (hp180 : p % 180 = 1)
    (hr : r ∣ (p + 14) / 15) (hr14 : r % 14 = 9) :
    HasSierpinskiDecomposition p := by
  have hp15 : p % 15 = 1 := by
    have hmod := Nat.mod_mod_of_dvd p (by decide : 15 ∣ 180)
    omega
  have hdiv15 : 15 ∣ p + 14 := by
    apply Nat.dvd_iff_mod_eq_zero.mpr
    have hm : (p + 14) % 15 = (p % 15 + 14 % 15) % 15 := Nat.add_mod p 14 15
    rw [hp15] at hm
    norm_num at hm
    exact hm
  have hu : 15 * ((p + 14) / 15) = p + 14 := Nat.mul_div_cancel' hdiv15
  let a := (p + 14) / 5
  have ha : 5 * a = p + 14 := by
    dsimp [a]
    apply Nat.mul_div_cancel'
    exact dvd_trans (by decide : 5 ∣ 15) hdiv15
  have hthree : a = 3 * ((p + 14) / 15) := by omega
  have hqa : 3 * r ∣ a := by rw [hthree]; exact Nat.mul_dvd_mul_left 3 hr
  have hqdiv : 3 * r ∣ p * a := by
    obtain ⟨c, hc⟩ := hqa
    refine ⟨p * c, ?_⟩
    rw [hc]
    ring
  have hq14 : 14 ∣ 3 * r + 1 := by
    apply Nat.dvd_iff_mod_eq_zero.mpr
    have hm : (3 * r + 1) % 14 = ((3 * r) % 14 + 1 % 14) % 14 :=
      Nat.add_mod (3 * r) 1 14
    rw [Nat.mul_mod, hr14] at hm
    norm_num at hm
    exact hm
  have hp : 0 < p := by omega
  have hapos : 0 < a := by omega
  exact decomposition_of_remainder hp hapos ha hqdiv hq14

private lemma prime_factor_residue (p q : ℕ)
    (hp : p.Prime) (hpLarge : 18001 < p) (hp180 : p % 180 = 1)
    (hq : q.Prime) (hqu : q ∣ (p + 14) / 15)
    (hno9 : ∀ r : ℕ, r ∣ (p + 14) / 15 → r % 14 ≠ 9) :
    q % 14 = 1 ∨ q % 14 = 3 ∨ q % 14 = 5 ∨ q % 14 = 11 ∨ q % 14 = 13 := by
  have hp15 : p % 15 = 1 := by
    have hmod := Nat.mod_mod_of_dvd p (by decide : 15 ∣ 180)
    omega
  have hpodd : p % 2 = 1 := by omega
  have hdiv15 : 15 ∣ p + 14 := by
    apply Nat.dvd_iff_mod_eq_zero.mpr
    have hm : (p + 14) % 15 = (p % 15 + 14 % 15) % 15 := Nat.add_mod p 14 15
    rw [hp15] at hm
    norm_num at hm
    exact hm
  have hu : 15 * ((p + 14) / 15) = p + 14 := Nat.mul_div_cancel' hdiv15
  have huodd : ((p + 14) / 15) % 2 = 1 := by omega
  have hqnot2 : q ≠ 2 := by
    intro heq
    subst q
    have hdiv : 2 ∣ (p + 14) / 15 := by exact hqu
    have hzero := Nat.dvd_iff_mod_eq_zero.mp hdiv
    omega
  have hqnot7 : q ≠ 7 := by
    intro heq
    subst q
    have h7u : 7 ∣ (p + 14) / 15 := hqu
    have h7sum : 7 ∣ p + 14 := by
      obtain ⟨c, hc⟩ := h7u
      refine ⟨15 * c, ?_⟩
      calc
        p + 14 = 15 * ((p + 14) / 15) := hu.symm
        _ = 7 * (15 * c) := by rw [hc]; ring
    have h7p : 7 ∣ p := by
      apply Nat.dvd_iff_mod_eq_zero.mpr
      have hsum0 := Nat.dvd_iff_mod_eq_zero.mp h7sum
      have hm : (p + 14) % 7 = (p % 7 + 14 % 7) % 7 := Nat.add_mod p 14 7
      rw [hsum0] at hm
      norm_num at hm
      omega
    have hpq := hp.eq_one_or_self_of_dvd 7 h7p
    rcases hpq with hpone | hpseven <;> omega
  have hqnot9res : q % 14 ≠ 9 := by
    intro hres
    exact hno9 q hqu hres
  have hqmod : q % 14 < 14 := Nat.mod_lt _ (by decide)
  have hqoddNat := hq.odd_of_ne_two hqnot2
  obtain ⟨k, hk⟩ := hqoddNat
  have hqodd : q % 2 = 1 := by omega
  have hq14odd : (q % 14) % 2 = 1 := by
    have hmod := Nat.mod_mod_of_dvd q (by decide : 2 ∣ 14)
    omega
  interval_cases h : q % 14
  · omega
  · simpa [h]
  · omega
  · simpa [h]
  · omega
  · simpa [h]
  · omega
  · have hmod := Nat.mod_mod_of_dvd q (by decide : 7 ∣ 14)
    rw [h] at hmod
    norm_num at hmod
    have hq7 : 7 ∣ q := Nat.dvd_iff_mod_eq_zero.mpr hmod.symm
    have hqeq := hq.eq_one_or_self_of_dvd 7 hq7
    rcases hqeq with hqone | hqseven <;> omega
  · omega
  · omega
  · omega
  · simpa [h]
  · omega
  · simpa [h]

def H1 : Prop :=
  ∀ p : ℕ, p.Prime → p % 180 = 1 → 18001 < p → ((p + 4) / 5).Prime →
    (∀ d : ℕ, d ∣ p + 5 → d % 5 ≠ 4) →
    (∀ d : ℕ, d ∣ p ^ 2 + 5 → d % 5 ≠ 4) →
    (∀ d : ℕ, d ∣ p + 1 → d % 5 ≠ 4) → ((p + 5) / 6).Prime →
    (∀ r : ℕ, r ∣ (p + 9) / 10 → r % 9 = 1) → ¬ ((p + 9) / 10).Prime →
    (∀ q : ℕ, q.Prime → q ∣ (p + 14) / 15 → (q % 14 = 1 ∨ q % 14 = 13)) →
    HasSierpinskiDecomposition p

def H2 : Prop :=
  ∀ p : ℕ, p.Prime → p % 180 = 1 → 18001 < p → ((p + 4) / 5).Prime →
    (∀ d : ℕ, d ∣ p + 5 → d % 5 ≠ 4) →
    (∀ d : ℕ, d ∣ p ^ 2 + 5 → d % 5 ≠ 4) →
    (∀ d : ℕ, d ∣ p + 1 → d % 5 ≠ 4) → ((p + 5) / 6).Prime →
    (∀ r : ℕ, r ∣ (p + 9) / 10 → r % 9 = 1) → ¬ ((p + 9) / 10).Prime →
    (∃ q : ℕ, q.Prime ∧ q ∣ (p + 14) / 15 ∧
      (q % 14 = 3 ∨ q % 14 = 5 ∨ q % 14 = 11) ∧
      (∀ r : ℕ, r.Prime → r ∣ (p + 14) / 15 → r % 14 = 3 → ¬ r ^ 2 ∣ (p + 14) / 15) ∧
      (∀ r : ℕ, r.Prime → r ∣ (p + 14) / 15 → r % 14 = 11 → ¬ r ^ 2 ∣ (p + 14) / 15) ∧
      (∀ r : ℕ, r.Prime → r ∣ (p + 14) / 15 → r % 14 = 5 → ¬ r ^ 4 ∣ (p + 14) / 15)) →
    HasSierpinskiDecomposition p

theorem main : H1 → H2 →
    OMA.R_SierpinskiEgyptianFractionConjecture_sierpinski_egyptian_fraction_conjecture_R1_H1_R1_H1_R1.H2 := by
  intro hsub houtside p hp h180 hlarge h4 h5 hsq h1 h6
  intro hcomp hbcomp
  by_cases hbad : ∃ r : ℕ, r ∣ (p + 14) / 15 ∧ r % 14 = 9
  · obtain ⟨r, hr, hr14⟩ := hbad
    exact decomposition_of_fourteen_divisor p r h180 hr hr14
  · have hno9 : ∀ r : ℕ, r ∣ (p + 14) / 15 → r % 14 ≠ 9 := by
      intro r hr hr14
      exact hbad ⟨r, hr, hr14⟩
    have hp15 : p % 15 = 1 := by
      have hmod := Nat.mod_mod_of_dvd p (by decide : 15 ∣ 180)
      omega
    have hdiv15 : 15 ∣ p + 14 := by
      apply Nat.dvd_iff_mod_eq_zero.mpr
      have hm : (p + 14) % 15 = (p % 15 + 14 % 15) % 15 := Nat.add_mod p 14 15
      rw [hp15] at hm
      norm_num at hm
      exact hm
    have hpos : 0 < (p + 14) / 15 := by omega
    by_cases hall : ∀ q : ℕ, q.Prime → q ∣ (p + 14) / 15 → (q % 14 = 1 ∨ q % 14 = 13)
    · exact hsub p hp h180 hlarge h4 h5 hsq h1 h6 hcomp hbcomp hall
    · push Not at hall
      obtain ⟨q, hq, hqu, hnot⟩ := hall
      have hres := prime_factor_residue p q hp (by omega) h180 hq hqu hno9
      change q % 14 ≠ 1 ∧ q % 14 ≠ 13 at hnot
      have hout : q % 14 = 3 ∨ q % 14 = 5 ∨ q % 14 = 11 := by
        rcases hres with h1' | h3' | h5' | h11' | h13'
        · exact False.elim (hnot.1 h1')
        · exact Or.inl h3'
        · exact Or.inr (Or.inl h5')
        · exact Or.inr (Or.inr h11')
        · exact False.elim (hnot.2 h13')
      have hprofile :
          (∀ r : ℕ, r.Prime → r ∣ (p + 14) / 15 → r % 14 = 3 → ¬ r ^ 2 ∣ (p + 14) / 15) ∧
          (∀ r : ℕ, r.Prime → r ∣ (p + 14) / 15 → r % 14 = 11 → ¬ r ^ 2 ∣ (p + 14) / 15) ∧
          (∀ r : ℕ, r.Prime → r ∣ (p + 14) / 15 → r % 14 = 5 → ¬ r ^ 4 ∣ (p + 14) / 15) := by
        constructor
        · intro r hr hru hr3 hpow
          have hmod : r ^ 2 % 14 = 9 := by norm_num [pow_two, Nat.mul_mod, hr3]
          exact (hno9 (r ^ 2) hpow) hmod
        constructor
        · intro r hr hru hr11 hpow
          have hmod : r ^ 2 % 14 = 9 := by norm_num [pow_two, Nat.mul_mod, hr11]
          exact (hno9 (r ^ 2) hpow) hmod
        · intro r hr hru hr5 hpow
          have hmod : r ^ 4 % 14 = 9 := by
            norm_num [show r ^ 4 = (r ^ 2) ^ 2 by ring, pow_two, Nat.mul_mod, hr5]
          exact (hno9 (r ^ 4) hpow) hmod
      exact houtside p hp h180 hlarge h4 h5 hsq h1 h6 hcomp hbcomp ⟨q, hq, hqu, hout, hprofile.1, hprofile.2.1, hprofile.2.2⟩

end OMA.R_SierpinskiEgyptianFractionConjecture_sierpinski_egyptian_fraction_conjecture_R1_H1_R1_H1_R1_H2_R1
