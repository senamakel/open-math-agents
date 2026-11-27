import OMAReductions.R_OeisA76495_conjecture_R1_H1_R1_H2_R1
import Mathlib

/-! The earlier quotient-abundancy helper forces a residue-3 support prime, not a
   residue-1 prime.  The exact remainder-five equation supplies the new mod-5
   input used here: 5 divides sigma, and hence one local factor vanishes mod 5. -/
open ArithmeticFunction
open scoped BigOperators

namespace OMA.R_OeisA76495_conjecture_R1_H1_R1_H2_R1_H2_R1

private def geom (p e : ℕ) : ℕ := ∑ i ∈ Finset.range (e + 1), p ^ i

private theorem five_dvd_geom_even_exp {p e : ℕ} (he : Even e)
    (hdiv : 5 ∣ geom p e) : p % 5 = 1 ∧ e % 10 = 4 := by
  let z : ZMod 5 := p
  have hpcast : (p : ZMod 5) = (p % 5 : ℕ) := by
    exact (ZMod.natCast_eq_natCast_iff p (p % 5) 5).2
      (Nat.ModEq.symm (Nat.mod_modEq p 5))
  have hzsum : (geom p e : ZMod 5) = ∑ i ∈ Finset.range (e + 1), z ^ i := by
    simp [geom, z]
  have hzero : (geom p e : ZMod 5) = 0 :=
    (ZMod.natCast_eq_zero_iff (geom p e) 5).2 hdiv
  have hiden := geom_sum_mul z (e + 1)
  rw [← hzsum] at hiden
  have hpow : z ^ (e + 1) = 1 := by
    rw [hzero] at hiden
    have hh : z ^ (e + 1) - 1 = 0 := by simpa using hiden.symm
    exact sub_eq_zero.mp hh
  have hrem : e % 2 = 0 := by obtain ⟨k,hk⟩ := he; omega
  have hcases : p % 5 = 0 ∨ p % 5 = 1 ∨ p % 5 = 2 ∨ p % 5 = 3 ∨ p % 5 = 4 := by omega
  rcases hcases with h0 | h1 | h2 | h3 | h4
  · have hz : z = 0 := by
      calc z = (p : ZMod 5) := rfl
        _ = (p % 5 : ℕ) := hpcast
        _ = 0 := by simp [h0]
    rw [hz] at hpow
    exfalso
    have hmod : Nat.ModEq 5 0 1 := (ZMod.natCast_eq_natCast_iff 0 1 5).1 hpow
    norm_num [Nat.ModEq] at hmod
  · have hz : z = 1 := by
      calc z = (p : ZMod 5) := rfl
        _ = (p % 5 : ℕ) := hpcast
        _ = 1 := by simp [h1]
    have hlin : (geom p e : ZMod 5) = (e + 1 : ℕ) := by
      rw [hzsum]
      simp [hz]
    rw [hlin] at hzero
    have h5 : 5 ∣ e + 1 := by
      have : ((e + 1 : ℕ) : ZMod 5) = 0 := by simpa using hzero
      exact (ZMod.natCast_eq_zero_iff (e + 1) 5).1 this
    exact ⟨h1, by omega⟩
  · have hz : z = 2 := by
      calc z = (p : ZMod 5) := rfl
        _ = (p % 5 : ℕ) := hpcast
        _ = 2 := by simp [h2]
    rw [hz] at hpow
    have hnot : (2 : ZMod 5) ^ (e + 1) ≠ 1 := by
      obtain ⟨k,hk⟩ := he
      have hmod : (e + 1) % 4 = 1 ∨ (e + 1) % 4 = 3 := by omega
      rcases hmod with hm | hm
      · have hexp : e + 1 = 4*((e+1)/4)+1 := by omega
        rw [hexp, pow_add, pow_mul]
        have hb : (16 : ZMod 5) = 1 := by
          apply (ZMod.natCast_eq_natCast_iff 16 1 5).2; decide
        rw [show (2 : ZMod 5)^4 = (16 : ZMod 5) by norm_num, hb]
        have h2 : (2 : ZMod 5) ≠ 1 := by
          intro hh
          have hmod := (ZMod.natCast_eq_natCast_iff 2 1 5).1 hh
          norm_num [Nat.ModEq] at hmod
        simpa using h2
      · have hexp : e + 1 = 4*((e+1)/4)+3 := by omega
        rw [hexp, pow_add, pow_mul]
        have hb : (16 : ZMod 5) = 1 := by
          apply (ZMod.natCast_eq_natCast_iff 16 1 5).2; decide
        rw [show (2 : ZMod 5)^4 = (16 : ZMod 5) by norm_num, hb]
        have h8 : (8 : ZMod 5) ≠ 1 := by
          intro hh
          have hmod := (ZMod.natCast_eq_natCast_iff 8 1 5).1 hh
          norm_num [Nat.ModEq] at hmod
        have hpow8 : (2 : ZMod 5)^3 = (8 : ZMod 5) := by norm_num
        exact fun hh => h8 (by simpa [hpow8] using hh)
    exact (hnot hpow).elim
  · have hz : z = 3 := by
      calc z = (p : ZMod 5) := rfl
        _ = (p % 5 : ℕ) := hpcast
        _ = 3 := by simp [h3]
    rw [hz] at hpow
    have hnot : (3 : ZMod 5) ^ (e + 1) ≠ 1 := by
      obtain ⟨k,hk⟩ := he
      have hmod : (e + 1) % 4 = 1 ∨ (e + 1) % 4 = 3 := by omega
      rcases hmod with hm | hm
      · have hexp : e + 1 = 4*((e+1)/4)+1 := by omega
        rw [hexp, pow_add, pow_mul]
        have hb : (81 : ZMod 5) = 1 := by
          apply (ZMod.natCast_eq_natCast_iff 81 1 5).2; decide
        rw [show (3 : ZMod 5)^4 = (81 : ZMod 5) by norm_num, hb]
        have h3 : (3 : ZMod 5) ≠ 1 := by
          intro hh
          have hmod := (ZMod.natCast_eq_natCast_iff 3 1 5).1 hh
          norm_num [Nat.ModEq] at hmod
        simpa using h3
      · have hexp : e + 1 = 4*((e+1)/4)+3 := by omega
        rw [hexp, pow_add, pow_mul]
        have hb : (81 : ZMod 5) = 1 := by
          apply (ZMod.natCast_eq_natCast_iff 81 1 5).2; decide
        rw [show (3 : ZMod 5)^4 = (81 : ZMod 5) by norm_num, hb]
        have h27 : (27 : ZMod 5) ≠ 1 := by
          intro hh
          have hmod := (ZMod.natCast_eq_natCast_iff 27 1 5).1 hh
          norm_num [Nat.ModEq] at hmod
        have hpow27 : (3 : ZMod 5)^3 = (27 : ZMod 5) := by norm_num
        exact fun hh => h27 (by simpa [hpow27] using hh)
    exact (hnot hpow).elim
  · have hz : z = 4 := by
      calc z = (p : ZMod 5) := rfl
        _ = (p % 5 : ℕ) := hpcast
        _ = 4 := by simp [h4]
    rw [hz] at hpow
    have hnot : (4 : ZMod 5) ^ (e + 1) ≠ 1 := by
      obtain ⟨k,hk⟩ := he
      have hodd : Odd (e+1) := by use k; omega
      obtain ⟨j,hj⟩ := hodd
      rw [show e+1=2*j+1 by omega, pow_add, pow_mul]
      have hb : (16 : ZMod 5) = 1 := by
        apply (ZMod.natCast_eq_natCast_iff 16 1 5).2; decide
      rw [show (4 : ZMod 5)^2 = (16 : ZMod 5) by norm_num, hb]
      have h4 : (4 : ZMod 5) ≠ 1 := by
        intro hh
        have hmod := (ZMod.natCast_eq_natCast_iff 4 1 5).1 hh
        norm_num [Nat.ModEq] at hmod
      simpa using h4
    exact (hnot hpow).elim

private theorem remainder_five_has_mod5_support {n : ℕ}
    (hn : Odd n) (hsq : IsSquare n) (hcard : n.primeFactors.card = 5)
    (h5 : 5 ∣ n) (hmod : sigma 1 n % n = 5) :
    ∃ p ∈ n.primeFactors, p % 5 = 1 ∧ n.factorization p % 10 = 4 := by
  classical
  letI : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  have hn0 : n ≠ 0 := by
    intro hz
    subst n
    obtain ⟨k,hk⟩ := hn
    omega
  obtain ⟨m,hm⟩ := hsq
  have hfac : n.factorization = (2 : ℕ) • m.factorization := by
    rw [hm, show m*m=m^2 by rw [pow_two], Nat.factorization_pow]
  let f := n.primeFactors.orderEmbOfFin hcard
  let e (i : Fin 5) := n.factorization (f i)
  have hfmem (i : Fin 5) : f i ∈ n.primeFactors := Finset.orderEmbOfFin_mem _ _ _
  have hp (i : Fin 5) : (f i).Prime := Nat.prime_of_mem_primeFactors (hfmem i)
  have he (i : Fin 5) : Even (e i) := by
    refine ⟨m.factorization (f i), ?_⟩
    simp [e, hfac, two_smul]
  have hsigmaDvd : 5 ∣ sigma 1 n := by
    have hdecomp := Nat.mod_add_div (sigma 1 n) n
    rw [hmod] at hdecomp
    rw [← hdecomp]
    exact dvd_add (dvd_refl 5) (dvd_mul_of_dvd_left h5 _)
  have hfactor : sigma 1 n =
      ∏ p ∈ n.primeFactors, sigma 1 (p ^ n.factorization p) := by
    rw [isMultiplicative_sigma.multiplicative_factorization _ hn0]
    simp [Finsupp.prod, Nat.support_factorization]
  rw [← Finset.map_orderEmbOfFin_univ n.primeFactors hcard, Finset.prod_map] at hfactor
  have hprodSigma : sigma 1 n = ∏ i : Fin 5, sigma 1 ((f i) ^ e i) := by
    simpa [f,e] using hfactor
  have hzero : ((∏ i : Fin 5, sigma 1 ((f i) ^ e i) : ℕ) : ZMod 5) = 0 :=
    (ZMod.natCast_eq_zero_iff _ 5).2 (by simpa [hprodSigma] using hsigmaDvd)
  have hcast : ((∏ i : Fin 5, sigma 1 ((f i) ^ e i) : ℕ) : ZMod 5) =
      ∏ i : Fin 5, (sigma 1 ((f i) ^ e i) : ZMod 5) := by simp
  have hprod : ∏ i : Fin 5, (sigma 1 ((f i) ^ e i) : ZMod 5) = 0 := by
    calc
      _ = ((∏ i : Fin 5, sigma 1 ((f i) ^ e i) : ℕ) : ZMod 5) := hcast.symm
      _ = 0 := hzero
  obtain ⟨i,hi,hlocal⟩ := (Finset.prod_eq_zero_iff (s := Finset.univ)).1 hprod
  have hlocalDiv : 5 ∣ sigma 1 ((f i) ^ e i) := (ZMod.natCast_eq_zero_iff _ 5).1 hlocal
  have hlocalGeom : 5 ∣ geom (f i) (e i) := by
    have hformula : sigma 1 ((f i) ^ e i) = geom (f i) (e i) := by
      rw [sigma_one_apply_prime_pow (hp i)]
      rfl
    rw [← hformula]
    exact hlocalDiv
  have hres := five_dvd_geom_even_exp (he i) hlocalGeom
  exact ⟨f i, hfmem i, hres.1, hres.2⟩

private theorem small_residue_one_prime (p : ℕ) (hp : p.Prime)
    (hbound : p ≤ 31) (hmod : p % 5 = 1) : p = 11 ∨ p = 31 := by
  interval_cases p
  all_goals norm_num at *

def H1 : Prop :=
  ∀ n : ℕ, Odd n → IsSquare n → n.primeFactors.card = 5 → 5 ∣ n →
    (∃ p ∈ n.primeFactors, p ≤ 31 ∧ (p = 11 ∨ p = 31) ∧
      ∃ k, n.factorization p = 10*k+4) → sigma 1 n % n ≠ 5

def H2 : Prop :=
  ∀ n : ℕ, Odd n → IsSquare n → n.primeFactors.card = 5 → 5 ∣ n →
    (∃ p ∈ n.primeFactors, 31 < p ∧ p % 5 = 1 ∧
      ∃ k, n.factorization p = 10*k+4) → sigma 1 n % n ≠ 5

theorem main : H1 → H2 →
    OMA.R_OeisA76495_conjecture_R1_H1_R1_H2_R1.H2 := by
  classical
  intro hsmall hlarge n hn hs hc h5 hhigh
  intro hmod
  by_cases hsmallCase : ∃ q ∈ n.primeFactors,
      q ≤ 31 ∧ q % 5 = 1 ∧ n.factorization q % 10 = 4
  · obtain ⟨q,hqmem,hqle,hqmod,hqexp⟩ := hsmallCase
    have hqprime : q.Prime := Nat.prime_of_mem_primeFactors hqmem
    have hchoices := small_residue_one_prime q hqprime hqle hqmod
    have hquotient := Nat.mod_add_div (n.factorization q) 10
    rw [hqexp] at hquotient
    exact (hsmall n hn hs hc h5 ⟨q,hqmem,hqle,hchoices,
      ⟨n.factorization q / 10, by omega⟩⟩) hmod
  · obtain ⟨p,hpmem,hpmod,hemod⟩ :=
      remainder_five_has_mod5_support hn hs hc h5 hmod
    have hlargep : 31 < p := by
      by_contra hnot
      have hple : p ≤ 31 := by omega
      exact hsmallCase ⟨p,hpmem,hple,hpmod,hemod⟩
    have hquotient := Nat.mod_add_div (n.factorization p) 10
    rw [hemod] at hquotient
    exact (hlarge n hn hs hc h5 ⟨p,hpmem,hlargep,hpmod,
      ⟨n.factorization p / 10, by omega⟩⟩) hmod

end OMA.R_OeisA76495_conjecture_R1_H1_R1_H2_R1_H2_R1
