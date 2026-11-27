import OMAReductions.R_OeisA76495_conjecture_R2_H4_R1
import Mathlib

/-! Exclude all six supports in the valuation-two, three-prime case. -/

open ArithmeticFunction Finset

namespace SigmaA76495Vtwo

def geometric (p : ℕ) : ℕ → ℕ
  | 0 => 1
  | e + 1 => 1 + p * geometric p e

theorem geometric_eq_sum (p e : ℕ) :
    geometric p e = ∑ i ∈ Finset.range (e + 1), p ^ i := by
  induction e with
  | zero => simp [geometric]
  | succ e ih =>
      rw [geometric, ih, Finset.sum_range_succ' (fun i : ℕ => p ^ i) (e + 1)]
      simp only [pow_zero, pow_succ', Finset.mul_sum, add_comm]

theorem geometric_scaled_mono (p : ℕ) {a b : ℕ} (hab : a ≤ b) :
    geometric p a * p ^ b ≤ geometric p b * p ^ a := by
  induction b generalizing a with
  | zero =>
      have : a = 0 := by omega
      subst a
      rfl
  | succ b ih =>
      by_cases he : a = b + 1
      · subst a
        rfl
      · have hab' : a ≤ b := by omega
        calc
          geometric p a * p ^ (b + 1) = (geometric p a * p ^ b) * p := by
            rw [pow_succ, mul_assoc]
          _ ≤ (geometric p b * p ^ a) * p := Nat.mul_le_mul_right p (ih hab')
          _ = (p * geometric p b) * p ^ a := by ring
          _ ≤ geometric p (b + 1) * p ^ a :=
            Nat.mul_le_mul_right _ (by simp [geometric])

theorem geometric_scaled (p e : ℕ) (hp : 1 ≤ p) :
    geometric p e * (p - 1) + 1 = p * p ^ e := by
  induction e with
  | zero =>
      simp only [geometric, one_mul, pow_zero, mul_one]
      omega
  | succ e ih =>
      rw [geometric, pow_succ']
      calc
        (1 + p * geometric p e) * (p - 1) + 1 = p * (geometric p e * (p - 1) + 1) := by
          have hs : p - 1 + 1 = p := by omega
          linear_combination hs
        _ = p * (p * p ^ e) := by rw [ih]

private theorem geometric_upper (p e : ℕ) (hp : 1 ≤ p) :
    geometric p e * (p - 1) ≤ p * p ^ e := by
  have h := geometric_scaled p e hp
  omega

private theorem pow_le_geometric (p e : ℕ) : p ^ e ≤ geometric p e := by
  rw [geometric_eq_sum]
  exact Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_range.mpr (by omega))

private theorem no_target_from_box_excess {p q e f a b : ℕ}
    (hp : 1 ≤ p) (hq : 1 ≤ q)
    (he : a ≤ e) (hf : b ≤ f)
    (hbase : 7 * (geometric p a * geometric q b) ≥ 8 * (p ^ a * q ^ b) + 6)
    (htarget : 7 * (geometric p e * geometric q f) = 8 * (p ^ e * q ^ f) + 5) :
    False := by
  have hscaleP := geometric_scaled_mono p he
  have hscaleQ := geometric_scaled_mono q hf
  have hscale0 := Nat.mul_le_mul hscaleP hscaleQ
  have hscale :
      (geometric p a * geometric q b) * (p ^ e * q ^ f) ≤
        (geometric p e * geometric q f) * (p ^ a * q ^ b) := by
    simpa [mul_assoc, mul_left_comm, mul_comm] using hscale0
  have hscale7 := Nat.mul_le_mul_left 7 hscale
  have hbaseMul := Nat.mul_le_mul_right (p ^ e * q ^ f) hbase
  have htargetMul := congrArg (fun x : ℕ => x * (p ^ a * q ^ b)) htarget
  have hpow : p ^ a * q ^ b ≤ p ^ e * q ^ f :=
    Nat.mul_le_mul (Nat.pow_le_pow_right (by omega : 0 < p) he)
      (Nat.pow_le_pow_right (by omega : 0 < q) hf)
  have hcore :
      (8 * (p ^ a * q ^ b) + 6) * (p ^ e * q ^ f) ≤
        (8 * (p ^ e * q ^ f) + 5) * (p ^ a * q ^ b) := by
    calc
      _ ≤ 7 * (geometric p a * geometric q b) * (p ^ e * q ^ f) := by
        simpa [mul_assoc, mul_left_comm, mul_comm] using hbaseMul
      _ ≤ 7 * (geometric p e * geometric q f) * (p ^ a * q ^ b) := by
        simpa [mul_assoc, mul_left_comm, mul_comm] using hscale7
      _ = _ := by simpa [mul_assoc, mul_left_comm, mul_comm] using htargetMul
  have hbasePos : 0 < p ^ a * q ^ b := by positivity
  have hpowPos : 0 < p ^ e * q ^ f := by positivity
  nlinarith [hcore, hpow]

private theorem support_of_card_three {n : ℕ} (hc : n.primeFactors.card = 3)
    (h2 : 2 ∈ n.primeFactors) :
    ∃ p q : ℕ, p ≠ 2 ∧ q ≠ 2 ∧ p < q ∧ n.primeFactors = {2, p, q} := by
  have hc' : (n.primeFactors.erase 2).card = 2 := by
    rw [Finset.card_erase_of_mem h2, hc]
  obtain ⟨p, q, hpq, hset⟩ := Finset.card_eq_two.mp hc'
  have hp : p ≠ 2 := Finset.ne_of_mem_erase
    (hset.symm ▸ Finset.mem_insert_self p {q})
  have hq : q ≠ 2 := Finset.ne_of_mem_erase
    (hset.symm ▸ Finset.mem_insert_of_mem (Finset.mem_singleton_self q))
  have hs : n.primeFactors = {2, p, q} := by
    rw [← Finset.insert_erase h2, hset]
  rcases lt_or_gt_of_ne hpq with h | h
  · exact ⟨p, q, hp, hq, h, hs⟩
  · refine ⟨q, p, hq, hp, h, hs.trans ?_⟩
    ext x
    simp only [Finset.mem_insert, Finset.mem_singleton]
    tauto

private theorem pair_upper_ratio {p q P Q A B : ℕ}
    (hp : 3 ≤ p) (hq : 5 ≤ q)
    (hA : A * (p - 1) ≤ p * P) (hB : B * (q - 1) ≤ q * Q) :
    8 * (A * B) ≤ 15 * (P * Q) := by
  have hp' : 2 * p ≤ 3 * (p - 1) := by omega
  have hq' : 4 * q ≤ 5 * (q - 1) := by omega
  have hcoeff : 8 * (p * q) ≤ 15 * ((p - 1) * (q - 1)) := by
    calc
      8 * (p * q) = (2 * p) * (4 * q) := by ring
      _ ≤ (3 * (p - 1)) * (5 * (q - 1)) := Nat.mul_le_mul hp' hq'
      _ = 15 * ((p - 1) * (q - 1)) := by ring
  have hprod := Nat.mul_le_mul hA hB
  have hcancel :
      (8 * (A * B)) * ((p - 1) * (q - 1)) ≤
        (15 * (P * Q)) * ((p - 1) * (q - 1)) := by
    calc
      _ = 8 * (A * (p - 1) * (B * (q - 1))) := by ring
      _ ≤ 8 * (p * P * (q * Q)) := Nat.mul_le_mul_left 8 hprod
      _ = 8 * (p * q) * (P * Q) := by ring
      _ ≤ 15 * ((p - 1) * (q - 1)) * (P * Q) := Nat.mul_le_mul_right (P * Q) hcoeff
      _ = _ := by ring
  have hCpos : 0 < (p - 1) * (q - 1) := Nat.mul_pos (by omega) (by omega)
  exact Nat.le_of_mul_le_mul_right hcancel hCpos

private theorem quotient_not_three {m : ℕ} (hm : IsSquare m)
    (h : 7 ∣ 12*m+5) : False := by
  have h' : 7∣5*(m+1)+7*m := by
    rw [show 5*(m+1)+7*m=12*m+5 by ring]
    exact h
  have hmul : 7∣7*m := ⟨m,rfl⟩
  have h5 : 7∣5*(m+1) := (Nat.dvd_add_iff_left hmul).mpr h'
  have h7 : 7∣m+1 := (Nat.Prime.dvd_mul (by decide : Nat.Prime 7)).mp h5 |>.resolve_left (by decide)
  obtain ⟨u,hu⟩ := hm
  have hm2 : m=u^2 := by simpa only [pow_two] using hu
  have hmod := Nat.dvd_iff_mod_eq_zero.mp h7
  rw [hm2,Nat.add_mod,Nat.pow_mod] at hmod
  have hlt : u%7<7 := Nat.mod_lt _ (by decide)
  generalize hr : u%7=r at hmod hlt
  interval_cases r <;> norm_num at hmod

private theorem q_bound {p q : ℕ} (hp : 11 ≤ p) (hq : 1 ≤ q)
    (h : 8*((p-1)*(q-1)) < 7*(p*q)) :
    q*(p-8) < 8*(p-1) := by
  have h1 := congrArg (fun v : ℕ => q*v) (Nat.sub_add_cancel (show 8≤p by omega))
  have h2 := congrArg (fun v : ℕ => (p-1)*v) (Nat.sub_add_cancel hq)
  have h3 := congrArg (fun v : ℕ => v*q) (Nat.sub_add_cancel (show 1≤p by omega))
  nlinarith only [h,h1,h2,h3]

private theorem six_supports {p q : ℕ}
    (hp : p.Prime) (hq : q.Prime) (hp11 : 11 ≤ p) (hgap : p+2 ≤ q)
    (h : q*(p-8) < 8*(p-1)) :
    (p=11 ∧ (q=13 ∨ q=17 ∨ q=19 ∨ q=23)) ∨
    (p=13 ∧ (q=17 ∨ q=19)) := by
  have hp13 : p ≤ 13 := by
    by_contra! hpbig
    have hp14 : p ≠ 14 := fun heq => (by decide : ¬Nat.Prime 14) (heq ▸ hp)
    have hp15 : 15 ≤ p := by omega
    have hprod := Nat.mul_le_mul_right (p-8) (show 16 ≤ q by omega)
    omega
  have hp_not_twelve : p≠12 := fun hp12 => (by decide : ¬Nat.Prime 12) (hp12 ▸ hp)
  by_cases h11 : p=11
  · subst p
    have hqlo : 13≤q := by omega
    have hqhi : q<27 := by omega
    have cert : ∀ q : Fin 27, 13≤q.val → q.val.Prime →
        q.val=13 ∨ q.val=17 ∨ q.val=19 ∨ q.val=23 := by decide +kernel
    exact Or.inl ⟨rfl,cert ⟨q,hqhi⟩ hqlo hq⟩
  · have h13 : p=13 := by omega
    subst p
    have hqlo : 15≤q := by omega
    have hqhi : q<20 := by omega
    have cert : ∀ q : Fin 20, 15≤q.val → q.val.Prime →
        q.val=17 ∨ q.val=19 := by decide +kernel
    exact Or.inr ⟨rfl,cert ⟨q,hqhi⟩ hqlo hq⟩

set_option maxHeartbeats 1600000 in
private theorem from_factor_pair {n p q e f : ℕ}
    (hp : p.Prime) (hq : q.Prime) (hp2 : p ≠ 2) (hpq : p < q)
    (he : Even e) (hf : Even f) (he2 : 2 ≤ e) (hf2 : 2 ≤ f)
    (hn : n = 4 * (p ^ e * q ^ f))
    (hs : sigma 1 n = 7 * (geometric p e * geometric q f))
    (hmod : sigma 1 n % n = 5) : False := by
  let P := p^e
  let Q := q^f
  let G := geometric p e
  let J := geometric q f
  let m := P*Q
  let k := sigma 1 n/n
  have hp3 : 3 ≤ p := by have := hp.two_le; omega
  have hgap : p+2 ≤ q := by
    have hb := hp.odd_of_ne_two hp2
    have hc := hq.odd_of_ne_two (by omega)
    obtain ⟨u,hu⟩ := hb
    obtain ⟨v,hv⟩ := hc
    omega
  have hq5 : 5 ≤ q := by omega
  have hq25 : 25 ≤ q^2 := Nat.pow_le_pow_left hq5 2
  have hP1 : 1≤P := Nat.succ_le_of_lt (pow_pos hp.pos _)
  have hQ25 : 25≤Q := hq25.trans (Nat.pow_le_pow_right hq.pos hf2)
  have hm25 : 25 ≤ m := by
    calc
      25 ≤ Q := hQ25
      _ = 1*Q := (one_mul _).symm
      _ ≤ m := Nat.mul_le_mul_right Q hP1
  have hmpos : 0 < m := by omega
  have hmG : m ≤ G*J := Nat.mul_le_mul (pow_le_geometric p e) (pow_le_geometric q f)
  have hA : G*(p-1) ≤ p*P := geometric_upper p e (by omega)
  have hB : J*(q-1) ≤ q*Q := geometric_upper q f (by omega)
  have hratio : 8*(G*J) ≤ 15*m := pair_upper_ratio hp3 hq5 hA hB
  have heq : 7*(G*J)=k*(4*m)+5 := by
    have h := Nat.mod_add_div (sigma 1 n) n
    rw [hmod] at h
    change 5+n*k=sigma 1 n at h
    rw [hs,hn] at h
    change 5+4*m*k=7*(G*J) at h
    nlinarith only [h]
  have hklo : 2 ≤ k := by
    by_contra! h
    have hh := Nat.mul_le_mul_right (4*m) (show k≤1 by omega)
    nlinarith only [hm25,hmG,heq,hh]
  have hkhi : k ≤ 3 := by
    by_contra! h
    have hh := Nat.mul_le_mul_right (4*m) h
    nlinarith only [hratio,hmpos,heq,hh]
  have hk2 : k=2 := by
    by_contra! h
    have hk3 : k=3 := by omega
    have hmSq : IsSquare m := by
      obtain ⟨u,hu⟩ := he
      obtain ⟨v,hv⟩ := hf
      refine ⟨p^u*q^v,?_⟩
      dsimp [m,P,Q]
      rw [hu,hv,pow_add,pow_add]
      ring
    apply quotient_not_three hmSq
    have hseven : 7∣k*(4*m)+5 := heq ▸ dvd_mul_right 7 (G*J)
    rw [hk3] at hseven
    rwa [show 3*(4*m)+5 = 12*m+5 by ring] at hseven
  have ht : 7*(G*J)=8*m+5 := by
    rw [hk2] at heq
    nlinarith only [heq]
  have htarget : 7*(geometric p e*geometric q f)=8*(p^e*q^f)+5 := ht
  have hcase : 11≤p := by
    by_contra! h
    have cert : ∀ p : Fin 11, 3≤p.val → p.val.Prime →
        8*p.val^2+1 ≤ 7*geometric p.val 2 := by decide +kernel
    have hbasep := cert ⟨p,h⟩ hp3 hp
    have hbaseq := pow_le_geometric q 2
    have hh := Nat.mul_le_mul hbasep hbaseq
    have hbase : 7*(geometric p 2*geometric q 2) ≥ 8*(p^2*q^2)+6 := by
      nlinarith only [hh,hq25]
    exact no_target_from_box_excess (by omega) (by omega) he2 hf2 hbase htarget
  have hcross : 8*((p-1)*(q-1)) < 7*(p*q) := by
    let D := (p-1)*(q-1)
    have hD : 0<D := Nat.mul_pos (by omega) (by omega)
    have hprod := Nat.mul_le_mul hA hB
    have hprod' : (G*J)*D ≤ (p*q)*m := by
      simpa only [D, m, mul_assoc, mul_comm, mul_left_comm] using hprod
    have hscaled := congrArg (fun t : ℕ => t*D) ht
    have hlt : m*(8*D) < m*(7*(p*q)) := by
      nlinarith only [hprod',hscaled,hD]
    exact Nat.lt_of_mul_lt_mul_left hlt
  rcases six_supports hp hq hcase hgap (q_bound hcase (by omega) hcross) with
    ⟨rfl,hq13|hq17|hq19|hq23⟩ | ⟨rfl,hq17|hq19⟩
  · subst q
    exact no_target_from_box_excess (p := 11) (q := 13) (by decide) (by decide)
      he2 hf2 (by norm_num [geometric]) htarget
  · subst q
    exact no_target_from_box_excess (p := 11) (q := 17) (by decide) (by decide)
      he2 hf2 (by norm_num [geometric]) htarget
  · subst q
    exact no_target_from_box_excess (p := 11) (q := 19) (by decide) (by decide)
      he2 hf2 (by norm_num [geometric]) htarget
  · subst q
    exact no_target_from_box_excess (p := 11) (q := 23) (by decide) (by decide)
      he2 hf2 (by norm_num [geometric]) htarget
  · subst q
    exact no_target_from_box_excess (p := 13) (q := 17) (by decide) (by decide)
      he2 hf2 (by norm_num [geometric]) htarget
  · subst q
    by_cases heq : e=2
    · by_cases hfeq : f=2
      · subst e f
        norm_num [geometric] at htarget
      · have hf4 : 4≤f := by have := Nat.even_iff.mp hf; omega
        exact no_target_from_box_excess (p := 13) (q := 19) (a := 2) (b := 4)
          (by decide) (by decide) he2 hf4 (by norm_num [geometric]) htarget
    · have he4 : 4≤e := by have := Nat.even_iff.mp he; omega
      exact no_target_from_box_excess (p := 13) (q := 19) (a := 4) (b := 2)
        (by decide) (by decide) he4 hf2 (by norm_num [geometric]) htarget

theorem solution : OMA.R_OeisA76495_conjecture_R2_H4_R1.H1 := by
  intro n hn hcard3 hodd hfour hwitness hval2
  have hn0 : n ≠ 0 := by
    intro hz
    subst n
    simp at hcard3
  have h2dvd : 2 ∣ n := by
    exact Nat.dvd_trans (by norm_num : 2 ∣ 4) hfour
  have h2mem : 2 ∈ n.primeFactors :=
    Nat.Prime.mem_primeFactors Nat.prime_two h2dvd hn0
  obtain ⟨p, q, hp2, hq2, hpq, hs⟩ := support_of_card_three hcard3 h2mem
  let e := n.factorization p
  let f := n.factorization q
  have hpmem : p ∈ n.primeFactors := by simp [hs]
  have hqmem : q ∈ n.primeFactors := by simp [hs]
  have hp := Nat.prime_of_mem_primeFactors hpmem
  have hq := Nat.prime_of_mem_primeFactors hqmem
  have hs2 : 2 ∉ ({p, q} : Finset ℕ) := by
    simp [Ne.symm hp2, Ne.symm hq2]
  have hlower (r : ℕ) (hm : r ∈ n.primeFactors) (hne : r ≠ 2) :
      2 ≤ n.factorization r := by
    have heven :=
      R2EvenSeed.factorizationEvenOfOddSigma hodd r hm hne
    have hpos := (Nat.prime_of_mem_primeFactors hm).factorization_pos_of_dvd hn0
      (Nat.dvd_of_mem_primeFactors hm)
    have heven' := Nat.even_iff.mp heven
    omega
  have htwoExp : n.factorization 2 = 2 := hval2
  have hvalue : n = 4 * (p ^ e * q ^ f) := by
    have h := Nat.prod_primeFactors_pow_factorization hn0
    rw [hs, Finset.prod_insert hs2, Finset.prod_pair hpq.ne, htwoExp] at h
    simpa [e, f, Nat.pow_succ, mul_assoc] using h
  have hsum : sigma 1 n = 7 * (geometric p e * geometric q f) := by
    rw [isMultiplicative_sigma.multiplicative_factorization _ hn0]
    simp only [Finsupp.prod, Nat.support_factorization]
    rw [hs, Finset.prod_insert hs2, Finset.prod_pair hpq.ne, htwoExp]
    have hsig2 : sigma 1 (2 ^ 2) = 7 := by decide +kernel
    rw [sigma_one_apply_prime_pow hp, sigma_one_apply_prime_pow hq,
      geometric_eq_sum, geometric_eq_sum]
    simp only [e, f, hsig2]
  have heven : Even e := by
    have h :=
      R2EvenSeed.factorizationEvenOfOddSigma hodd p hpmem hp2
    simpa [e] using h
  have hfEven : Even f := by
    have h :=
      R2EvenSeed.factorizationEvenOfOddSigma hodd q hqmem hq2
    simpa [f] using h
  have he2 : 2 ≤ e := by exact hlower p hpmem hp2
  have hf2 : 2 ≤ f := by exact hlower q hqmem hq2
  intro hmod
  exact from_factor_pair hp hq hp2 hpq heven hfEven he2 hf2 hvalue hsum hmod

end SigmaA76495Vtwo

theorem OMA.solution : OMA.R_OeisA76495_conjecture_R2_H4_R1.H1 :=
  SigmaA76495Vtwo.solution
