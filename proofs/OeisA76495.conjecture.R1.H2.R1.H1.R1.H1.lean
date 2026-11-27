import OMAReductions.R_OeisA76495_conjecture_R1_H2_R1_H1_R1
import Mathlib

/-! At valuation one, three-prime candidates must use one of three odd pairs,
whose smallest allowed exponents already overshoot the target. -/

open ArithmeticFunction Finset

namespace SigmaAbundancyBounds

def geometric (p : ℕ) : ℕ → ℕ
  | 0 => 1
  | e+1 => 1+p*geometric p e

theorem geometric_eq_sum (p e : ℕ) :
    geometric p e = ∑ i ∈ Finset.range (e+1), p^i := by
  induction e with
  | zero => simp [geometric]
  | succ e ih =>
    rw [geometric, ih, Finset.sum_range_succ' (fun i : ℕ => p^i) (e+1)]
    simp only [pow_zero, pow_succ', Finset.mul_sum, add_comm]

theorem geometric_scaled_mono (p : ℕ) {a b : ℕ} (hab : a ≤ b) :
    geometric p a * p^b ≤ geometric p b * p^a := by
  induction b generalizing a with
  | zero =>
    have : a = 0 := by omega
    subst a
    rfl
  | succ b ih =>
    by_cases he : a = b+1
    · subst a
      rfl
    have hab' : a ≤ b := by omega
    calc
      geometric p a * p^(b+1) = (geometric p a*p^b)*p := by rw [pow_succ, mul_assoc]
      _ ≤ (geometric p b*p^a)*p := Nat.mul_le_mul_right p (ih hab')
      _ = (p*geometric p b)*p^a := by ring
      _ ≤ geometric p (b+1)*p^a := by
        exact Nat.mul_le_mul_right _ (by simp [geometric])

theorem geometric_scaled (p e : ℕ) (hp : 1 ≤ p) :
    geometric p e*(p-1)+1 = p*p^e := by
  induction e with
  | zero =>
    simp only [geometric, one_mul, pow_zero, mul_one]
    omega
  | succ e ih =>
    rw [geometric, pow_succ']
    calc
      (1+p*geometric p e)*(p-1)+1 = p*(geometric p e*(p-1)+1) := by
        have hs : p-1+1 = p := by omega
        linear_combination hs
      _ = p*(p*p^e) := by rw [ih]

theorem geometric_upper (p e : ℕ) (hp : 1 ≤ p) :
    geometric p e * (p-1) ≤ p * p^e := by
  have h := geometric_scaled p e hp
  omega

theorem geometric_lower_base_bound {p q e : ℕ} (hq : 2 ≤ q)
    (hqp : q ≤ p) : geometric p e*(q-1) ≤ q*p^e := by
  have hp : 1 ≤ p := by omega
  have hq1 : 1 ≤ q := by omega
  have hc : p*(q-1) ≤ q*(p-1) := by
    have hpq' : (q : ℤ) ≤ p := by exact_mod_cast hqp
    have hc' : (p : ℤ)*((q : ℤ)-1) ≤ (q : ℤ)*((p : ℤ)-1) := by
      nlinarith only [hpq']
    exact_mod_cast (show (p : ℤ)*(((q-1 : ℕ) : ℤ)) ≤
      (q : ℤ)*(((p-1 : ℕ) : ℤ)) by
        rw [Nat.cast_sub hp, Nat.cast_sub hq1]
        exact hc')
  have hmul : (geometric p e*(q-1))*(p-1) ≤ (q*p^e)*(p-1) := by
    calc
      _ = (geometric p e*(p-1))*(q-1) := by ring
      _ ≤ (p*p^e)*(q-1) := Nat.mul_le_mul_right _ (geometric_upper p e hp)
      _ = (p*(q-1))*p^e := by ring
      _ ≤ (q*(p-1))*p^e := Nat.mul_le_mul_right _ hc
      _ = _ := by ring
  exact Nat.le_of_mul_le_mul_right hmul (by omega)


end SigmaAbundancyBounds

namespace SigmaEvenThree

open SigmaAbundancyBounds

private theorem support_of_card_three {n : ℕ} (hc : n.primeFactors.card = 3)
    (h2 : 2 ∈ n.primeFactors) :
    ∃ p q : ℕ, p ≠ 2 ∧ q ≠ 2 ∧ p < q ∧ n.primeFactors = {2,p,q} := by
  have hc' : (n.primeFactors.erase 2).card = 2 := by
    rw [Finset.card_erase_of_mem h2, hc]
  obtain ⟨p, q, hpq, hset⟩ := Finset.card_eq_two.mp hc'
  have hp : p ≠ 2 := Finset.ne_of_mem_erase (hset.symm ▸ Finset.mem_insert_self p {q})
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

private theorem from_factor_pair {p q e f n S : ℕ} (hp : p.Prime) (hq : q.Prime)
    (hp2 : p ≠ 2) (hpq : p < q) (he : 2 ≤ e) (hf : 2 ≤ f)
    (hn : n = 2 * p^e * q^f) (hs : S = 3 * geometric p e * geometric q f)
    (hmod : S % n = 5) : False := by
  let k := S / n
  let P := p^e
  let Q := q^f
  let A := geometric p e
  let B := geometric q f
  have hpPos : 0 < P := pow_pos hp.pos _
  have hqPos : 0 < Q := pow_pos hq.pos _
  change n = 2 * P * Q at hn
  change S = 3 * A * B at hs
  have hpos : 0 < n := by rw [hn]; positivity
  have hdiv := Nat.mod_add_div S n
  rw [hmod] at hdiv
  change 5 + n * k = S at hdiv
  have hn3 : n % 3 ≠ 0 := by
    intro hzero
    have hleft := congrArg (fun t : ℕ => t % 3) hdiv
    rw [hs, Nat.add_mod, Nat.mul_mod n k, hzero] at hleft
    have hright : (3*A*B) % 3 = 0 :=
      Nat.dvd_iff_mod_eq_zero.mp ⟨A*B, by ring⟩
    rw [hright] at hleft
    simp at hleft
  have p_not_three : p ≠ 3 := by
    intro hz
    have hp_dvd : p ∣ P := dvd_pow_self _ (by omega)
    have hp_n : p ∣ n := by rw [hn]; exact dvd_mul_of_dvd_left (dvd_mul_of_dvd_right hp_dvd 2) _
    exact hn3 (Nat.dvd_iff_mod_eq_zero.mp (hz ▸ hp_n))
  have q_not_three : q ≠ 3 := by
    intro hz
    have hq_dvd : q ∣ Q := dvd_pow_self _ (by omega)
    have hq_n : q ∣ n := by rw [hn]; exact dvd_mul_of_dvd_right hq_dvd _
    exact hn3 (Nat.dvd_iff_mod_eq_zero.mp (hz ▸ hq_n))
  have hp5 : 5 ≤ p := by
    have hh := hp.two_le
    by_contra! h
    interval_cases p <;> first | omega | norm_num at hp
  have hq7 : 7 ≤ q := by
    have hq6 : 6 ≤ q := by omega
    by_contra! h
    interval_cases q
    norm_num at hq
  have power_le_geo (r t : ℕ) : r^t ≤ geometric r t := by
    rw [geometric_eq_sum]
    exact Finset.single_le_sum (fun _ _ => Nat.zero_le _)
      (Finset.mem_range.mpr (Nat.lt_succ_self _))
  have hlarge : n + 5 < S := by
    have hh := Nat.mul_le_mul (power_le_geo p e) (power_le_geo q f)
    change P * Q ≤ A * B at hh
    have hP5 : 5 < P := by
      have h1 : p^2 ≤ P := Nat.pow_le_pow_right hp.pos he
      nlinarith only [h1, hp5]
    have hQ1 : 1 ≤ Q := hqPos
    have hPQ : P ≤ P * Q := by simpa using Nat.mul_le_mul_left P hQ1
    rw [hn, hs]
    nlinarith only [hh, hP5, hPQ]
  have hS2 : 2 ≤ k := by
    by_contra! hk
    have hh := Nat.mul_le_mul_left n (show k ≤ 1 by omega)
    nlinarith only [hdiv, hlarge, hh]
  have h2n : 2 * n ≤ S := by
    have hh := Nat.mul_le_mul_left n hS2
    nlinarith only [hh, hdiv]
  have cut (a b : ℕ) (ha : 2 ≤ a) (hb : 2 ≤ b) (hap : a ≤ p) (hbq : b ≤ q) :
      (2*(a-1)*(b-1))*S ≤ (3*a*b)*n := by
    have hupper1 : A*(a-1) ≤ a*P := geometric_lower_base_bound (e := e) ha hap
    have hupper2 : B*(b-1) ≤ b*Q := geometric_lower_base_bound (e := f) hb hbq
    have hh := Nat.mul_le_mul hupper1 hupper2
    rw [hs, hn]
    nlinarith only [Nat.mul_le_mul_left 6 hh]
  have hpEq : p = 5 := by
    by_contra h
    have hp7 : 7 ≤ p := by
      by_contra! hc
      interval_cases p <;> first | omega | norm_num at hp
    have hq11 : 11 ≤ q := by
      have hq8 : 8 ≤ q := by omega
      by_contra! hc
      interval_cases q <;> norm_num at hq
    have hu := cut 7 11 (by decide) (by decide) hp7 hq11
    norm_num at hu
    nlinarith only [hu, h2n, hpos]
  have hqLt : q < 17 := by
    by_contra! h
    have hu := cut 5 17 (by decide) (by decide) hp5 h
    norm_num at hu
    nlinarith only [hu, h2n, hpos]
  have hqCases : q = 7 ∨ q = 11 ∨ q = 13 := by
    interval_cases q <;> first | (norm_num; done) | norm_num at hq
  have hk : k = 2 := by
    have hu := cut 5 7 (by decide) (by decide) hp5 hq7
    norm_num at hu
    by_contra h
    have h3 : 3 ≤ k := by omega
    have hh := Nat.mul_le_mul_left n h3
    nlinarith only [hu, hh, hpos, hdiv]
  have heq : S = 2*n+5 := by rw [hk] at hdiv; omega
  have hlo :
      3 * geometric p 2 * geometric q 2 > 2*(2*p^2*q^2)+5 := by
    rcases hqCases with h | h | h <;> (rw [hpEq, h]; decide)
  have hnlow : 2*p^2*q^2 ≤ n := by
    have hP := Nat.pow_le_pow_right hp.pos he
    have hQ := Nat.pow_le_pow_right hq.pos hf
    rw [hn]
    exact Nat.mul_le_mul (Nat.mul_le_mul_left 2 hP) hQ
  have ha := geometric_scaled_mono p he
  have hb := geometric_scaled_mono q hf
  have hprod := Nat.mul_le_mul ha hb
  change (geometric p 2 * P) * (geometric q 2 * Q) ≤ (A * p^2) * (B * q^2) at hprod
  have hratio : (3 * geometric p 2 * geometric q 2)*n ≤ S*(2*p^2*q^2) := by
    rw [hn, hs]
    nlinarith only [Nat.mul_le_mul_left 6 hprod]
  have hstrict := Nat.mul_lt_mul_of_pos_right hlo hpos
  nlinarith only [hstrict, hratio, heq, hnlow]

theorem solution : OMA.R_OeisA76495_conjecture_R1_H2_R1_H1_R1.H1 := by
  intro n hn hcard hodd htwo hmod
  have hn0 : n ≠ 0 := by omega
  have h2dvd : 2 ∣ n := hn.two_dvd
  have h2mem : 2 ∈ n.primeFactors :=
    Nat.Prime.mem_primeFactors Nat.prime_two h2dvd hn0
  have htwoExp : n.factorization 2 = 1 := by
    have hlo := (Nat.prime_two.pow_dvd_iff_le_factorization hn0).mp
      (show 2^1 ∣ n by simpa using h2dvd)
    by_contra! h
    have hle : 2 ≤ n.factorization 2 := by omega
    have hd := (Nat.prime_two.pow_dvd_iff_le_factorization hn0).mpr hle
    have hf : n % 4 = 0 := Nat.dvd_iff_mod_eq_zero.mp hd
    omega
  obtain ⟨p, q, p_not_two, q_not_two, hlt, hs⟩ := support_of_card_three hcard h2mem
  let e := n.factorization p
  let f := n.factorization q
  have hpmem : p ∈ n.primeFactors := by simp [hs]
  have hqmem : q ∈ n.primeFactors := by simp [hs]
  have hp := Nat.prime_of_mem_primeFactors hpmem
  have hq := Nat.prime_of_mem_primeFactors hqmem
  have hs2 : 2 ∉ ({p,q} : Finset ℕ) := by
    simp [Ne.symm p_not_two, Ne.symm q_not_two]
  have hlower (r : ℕ) (hm : r ∈ n.primeFactors) (hne : r ≠ 2) :
      2 ≤ n.factorization r := by
    have he :=
      OMA.R_OeisA76495_conjecture_R1_H2_R1.factorizationEvenOfOddSigma hodd r hm hne
    have hpos := (Nat.prime_of_mem_primeFactors hm).factorization_pos_of_dvd hn0
      (Nat.dvd_of_mem_primeFactors hm)
    have hpar := Nat.even_iff.mp he
    omega
  have hvalue : n = 2 * p^e * q^f := by
    have h := Nat.prod_primeFactors_pow_factorization hn0
    rw [hs, Finset.prod_insert hs2, Finset.prod_pair hlt.ne, htwoExp, pow_one] at h
    simpa [e, f, mul_assoc] using h
  have hsig_two : sigma 1 2 = 3 := by decide +kernel
  have hsum : sigma 1 n = 3 * geometric p e * geometric q f := by
    rw [isMultiplicative_sigma.multiplicative_factorization _ hn0]
    simp only [Finsupp.prod, Nat.support_factorization]
    rw [hs, Finset.prod_insert hs2, Finset.prod_pair hlt.ne, htwoExp, pow_one, hsig_two]
    rw [sigma_one_apply_prime_pow hp, sigma_one_apply_prime_pow hq,
      geometric_eq_sum, geometric_eq_sum]
    simp only [e, f, mul_assoc]
  exact from_factor_pair hp hq p_not_two hlt (hlower p hpmem p_not_two)
    (hlower q hqmem q_not_two) hvalue hsum hmod

end SigmaEvenThree

theorem OMA.solution : OMA.R_OeisA76495_conjecture_R1_H2_R1_H1_R1.H1 :=
  SigmaEvenThree.solution
