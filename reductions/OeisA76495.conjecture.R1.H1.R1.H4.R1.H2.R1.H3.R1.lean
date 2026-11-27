import OMAReductions.R_OeisA76495_conjecture_R1_H1_R1_H4_R1_H2_R1

/-! Split the ten-factor remainder-five case by its residue modulo eight. -/

open ArithmeticFunction

namespace OMA.R_OeisA76495_conjecture_R1_H1_R1_H4_R1_H2_R1_H3_R1

private def G (p e : ℕ) : ℕ := ∑ j ∈ Finset.range (e + 1), p ^ j

private theorem G_succ (p e : ℕ) : G p (e+1) = G p e + p^(e+1) := by
  simp [G, Finset.sum_range_succ]

private theorem G_succ2 (p e : ℕ) : G p (e+2) = G p e + p^(e+1) + p^(e+2) := by
  rw [show e+2 = (e+1)+1 by omega, G_succ, G_succ]

private theorem G_odd_zero_mod4 {p e : ℕ} (hp : p % 4 = 3) (he : Odd e) : G p e % 4 = 0 := by
  obtain ⟨k, rfl⟩ := he
  induction k with
  | zero =>
      norm_num [G]
      omega
  | succ k ih =>
      have hh := G_succ2 p (2*k+1)
      have hpow : (p^(2*k+2) + p^(2*k+3)) % 4 = 0 := by
        have hp1 : (1+p) % 4 = 0 := by omega
        have hdiv : 4 ∣ 1+p := Nat.dvd_of_mod_eq_zero hp1
        have ht : p^(2*k+2) + p^(2*k+3) = p^(2*k+2) * (1+p) := by
          rw [pow_succ]
          ring
        rw [ht]
        exact Nat.mod_eq_zero_of_dvd (dvd_mul_of_dvd_right hdiv _)
      rw [show 2*(k+1)+1 = (2*k+1)+2 by omega]
      have hh' : G p ((2*k+1)+2) = G p (2*k+1) + p^(2*k+2) + p^(2*k+3) := by
        simpa only [show 2*k+1+1 = 2*k+2 by omega,
          show 2*k+1+2 = 2*k+3 by omega] using hh
      rw [hh']
      have hmods : ((p^(2*k+2) % 4) + (p^(2*k+3) % 4)) % 4 = 0 := by
        rw [Nat.add_mod] at hpow
        exact hpow
      rw [Nat.add_mod (G p (2*k+1) + p^(2*k+2)) (p^(2*k+3)) 4,
        Nat.add_mod (G p (2*k+1)) (p^(2*k+2)) 4, ih]
      simp only [Nat.zero_add]
      rw [Nat.mod_mod]
      exact hmods

theorem sigma_shape_mod_four {n : ℕ} (hn : Odd n)
    (hσ : sigma 1 n = 3*n + 5) : n % 4 = 1 := by
  by_contra hnot
  have hn0 : n ≠ 0 := by
    intro hz
    obtain ⟨k, hk⟩ := hn
    omega
  have hnmod : n % 4 = 3 := by
    have hodd := Nat.odd_iff.mp hn
    have hrel := Nat.mod_mod_of_dvd n (by norm_num : 2 ∣ 4)
    have hlt := Nat.mod_lt n (by norm_num : 0 < 4)
    omega
  have hsigmod : sigma 1 n % 4 = 2 := by rw [hσ]; omega
  have hsigcast : (sigma 1 n : ZMod 4) = 2 := by
    apply (ZMod.natCast_eq_natCast_iff (sigma 1 n) 2 4).2
    change sigma 1 n % 4 = 2 % 4
    exact hsigmod
  have hfactor : sigma 1 n = ∏ p ∈ n.primeFactors, sigma 1 (p ^ n.factorization p) := by
    rw [isMultiplicative_sigma.multiplicative_factorization _ hn0]
    simp [Finsupp.prod, Nat.support_factorization]
  have hfactorCast : (sigma 1 n : ZMod 4) =
      ∏ p ∈ n.primeFactors, (sigma 1 (p ^ n.factorization p) : ZMod 4) := by
    rw [hfactor]
    simp
  have hlocal_ne (p : ℕ) (hp : p ∈ n.primeFactors) :
      (sigma 1 (p ^ n.factorization p) : ZMod 4) ≠ 0 := by
    intro hz
    have hzprod : (∏ p ∈ n.primeFactors,
        (sigma 1 (p ^ n.factorization p) : ZMod 4)) = 0 := Finset.prod_eq_zero hp hz
    rw [← hfactorCast, hsigcast] at hzprod
    have h2 : (2 : ZMod 4) ≠ 0 := by decide
    exact h2 hzprod
  have hlocal_exp (p : ℕ) (hp : p ∈ n.primeFactors)
      (hpmod : p % 4 = 3) : ¬ Odd (n.factorization p) := by
    intro he
    have hpr : p.Prime := Nat.prime_of_mem_primeFactors hp
    have hzero : (sigma 1 (p ^ n.factorization p) : ZMod 4) = 0 := by
      rw [sigma_one_apply_prime_pow hpr]
      change (G p (n.factorization p) : ZMod 4) = 0
      apply (ZMod.natCast_eq_zero_iff (G p (n.factorization p)) 4).2
      exact Nat.dvd_of_mod_eq_zero (G_odd_zero_mod4 hpmod he)
    exact hlocal_ne p hp hzero
  have hnprod : n = ∏ p ∈ n.primeFactors, p ^ n.factorization p :=
    Nat.prod_primeFactors_pow_factorization hn0
  have hnprodCast : (n : ZMod 4) = ∏ p ∈ n.primeFactors,
      (p : ZMod 4) ^ n.factorization p := by
    simpa using congrArg (fun t : ℕ => (t : ZMod 4)) hnprod
  have hpowone (p : ℕ) (hp : p ∈ n.primeFactors) :
      (p : ZMod 4) ^ n.factorization p = 1 := by
    have hpr : p.Prime := Nat.prime_of_mem_primeFactors hp
    have hpne2 : p ≠ 2 := by
      intro hp2
      subst p
      exact hn.not_two_dvd_nat (Nat.dvd_of_mem_primeFactors hp)
    have hoddp := hpr.odd_of_ne_two hpne2
    have hpmodcases : p % 4 = 1 ∨ p % 4 = 3 := by
      have hodd := Nat.odd_iff.mp hoddp
      have hrel := Nat.mod_mod_of_dvd p (by norm_num : 2 ∣ 4)
      have hlt := Nat.mod_lt p (by norm_num : 0 < 4)
      omega
    rcases hpmodcases with hp1 | hp3
    · have hpz : (p : ZMod 4) = 1 := by
        apply (ZMod.natCast_eq_natCast_iff p 1 4).2
        change p % 4 = 1 % 4
        exact hp1
      rw [hpz]
      simp
    · have heven : Even (n.factorization p) :=
        (Nat.not_odd_iff_even).mp (hlocal_exp p hp hp3)
      have hpz : (p : ZMod 4) = -1 := by
        have ht : (p : ZMod 4) = 3 := by
          apply (ZMod.natCast_eq_natCast_iff p 3 4).2
          change p % 4 = 3 % 4
          exact hp3
        rw [ht]
        have h3 : (3 : ZMod 4) = -1 := by decide
        exact h3
      rcases heven with ⟨k, hk⟩
      rw [hpz, hk]
      simp
  have hncast1 : (n : ZMod 4) = 1 := by
    rw [hnprodCast]
    exact Finset.prod_eq_one fun p hp => hpowone p hp
  have hmod1 : n % 4 = 1 := by
    have hh := (ZMod.natCast_eq_natCast_iff n 1 4).1 hncast1
    change n % 4 = 1 % 4 at hh
    exact hh
  exact hnot hmod1

private theorem rank_lower_bound (p : Fin 10 → ℕ)
    (hprime : ∀ i, Nat.Prime (p i)) (hlower : ∀ i, 3 ≤ p i)
    (hstrict : StrictMono p) :
    ∀ i : Fin 10, (![3,5,7,11,13,17,19,23,29,31] : Fin 10 → ℕ) i ≤ p i := by
  intro i
  by_contra! hbad
  let pre : Finset (Fin 10) := Finset.Iic i
  have hprefix_sub : pre.image p ⊆
      (Finset.range ((![3,5,7,11,13,17,19,23,29,31] : Fin 10 → ℕ) i)).filter
        (fun q => q.Prime ∧ 3 ≤ q) := by
    apply Finset.image_subset_iff.mpr
    intro j hj
    have hji : j ≤ i := Finset.mem_Iic.mp hj
    have hpji : p j ≤ p i := by
      rcases eq_or_lt_of_le hji with h | h
      · simp [h]
      · exact (hstrict h).le
    exact Finset.mem_filter.mpr
      ⟨Finset.mem_range.mpr (lt_of_le_of_lt hpji hbad), hprime j, hlower j⟩
  have hcount :
      ((Finset.range ((![3,5,7,11,13,17,19,23,29,31] : Fin 10 → ℕ) i)).filter
        (fun q => q.Prime ∧ 3 ≤ q)).card = i.val := by
    fin_cases i <;> decide
  have hprefix_card : (pre.image p).card = i.val + 1 := by
    rw [Finset.card_image_of_injective _ hstrict.injective, Fin.card_Iic]
  have hcard := Finset.card_le_card hprefix_sub
  rw [hprefix_card, hcount] at hcard
  omega

private theorem sigma_lt_five_of_ten_factors {n : ℕ} (hn : Odd n)
    (hc : n.primeFactors.card = 10) : sigma 1 n < 5*n := by
  have hn0 : n ≠ 0 := by
    obtain ⟨k, hk⟩ := hn
    omega
  let p := n.primeFactors.orderEmbOfFin hc
  let e : Fin 10 → ℕ := fun i => n.factorization (p i)
  have hmem (i : Fin 10) : p i ∈ n.primeFactors :=
    Finset.orderEmbOfFin_mem _ _ _
  have hp (i : Fin 10) : (p i).Prime ∧ 3 ≤ p i := by
    have hpr := Nat.prime_of_mem_primeFactors (hmem i)
    have hne : p i ≠ 2 := fun hz => hn.not_two_dvd_nat
      (hz ▸ Nat.dvd_of_mem_primeFactors (hmem i))
    exact ⟨hpr, by have := hpr.two_le; omega⟩
  have hval : (∏ i : Fin 10, p i ^ e i) = n := by
    have hprod := (Nat.prod_primeFactors_pow_factorization hn0).symm
    rw [← Finset.map_orderEmbOfFin_univ n.primeFactors hc, Finset.prod_map] at hprod
    exact hprod
  have hsum : (∏ i : Fin 10, G (p i) (e i)) = sigma 1 n := by
    have hfactor : sigma 1 n =
        ∏ r ∈ n.primeFactors, sigma 1 (r ^ n.factorization r) := by
      rw [isMultiplicative_sigma.multiplicative_factorization _ hn0]
      simp [Finsupp.prod, Nat.support_factorization]
    rw [← Finset.map_orderEmbOfFin_univ n.primeFactors hc, Finset.prod_map] at hfactor
    rw [hfactor]
    apply Finset.prod_congr rfl
    intro i _
    simpa [G] using (sigma_one_apply_prime_pow (hp i).1).symm
  let m : Fin 10 → ℕ := ![3,5,7,11,13,17,19,23,29,31]
  let D := ∏ i, (m i - 1)
  let Q := ∏ i, m i
  have htwo (i : Fin 10) (_hi : i ∈ Finset.univ) : 2 ≤ m i := by
    fin_cases i <;> decide
  have hm (i : Fin 10) (_hi : i ∈ Finset.univ) : m i ≤ p i :=
    rank_lower_bound p (fun i => (hp i).1) (fun i => (hp i).2) p.strictMono i
  have hbound := OMA.R_OeisA76495_conjecture_R1_H1_R1_H4_R1.product_profile_bound
    Finset.univ p m e htwo hm
  change (∏ i : Fin 10, G (p i) (e i)) * D ≤ Q * (∏ i : Fin 10, p i ^ e i) at hbound
  rw [hval, hsum] at hbound
  have hQ : Q < 5 * D := by decide +kernel
  by_contra! hu
  have hD := Nat.mul_le_mul_right D hu
  have hl := Nat.mul_lt_mul_of_pos_right hQ (Nat.pos_of_ne_zero hn0)
  nlinarith only [hbound, hD, hl]

def H1 : Prop :=
  ∀ n : ℕ, Odd n → ¬ IsSquare n → n.primeFactors.card = 10 →
    n % 8 = 1 → sigma 1 n = 3*n+5 → False

def H2 : Prop :=
  ∀ n : ℕ, Odd n → ¬ IsSquare n → n.primeFactors.card = 10 →
    n % 8 = 5 → sigma 1 n = 3*n+5 → False

def H3 : Prop :=
  ∀ n : ℕ, Odd n → ¬ IsSquare n → 11 ≤ n.primeFactors.card →
    sigma 1 n % n ≠ 5

theorem main : H1 → H2 → H3 →
    OMA.R_OeisA76495_conjecture_R1_H1_R1_H4_R1_H2_R1.H3 := by
  intro h1 h2 h3 n hn hnsq hcard
  by_cases hc : n.primeFactors.card = 10
  · intro hmod
    have hn0 : n ≠ 0 := by
      obtain ⟨k, hk⟩ := hn
      omega
    have hsigmaEven := SigmaFive.even_sigma_of_odd_nonsquare hn0 hn hnsq
    have hquotOdd := SigmaFive.odd_quotient_of_even_sigma hn hmod hsigmaEven
    have hlow := SigmaFive.large_sigma_of_four_odd_factors hn (by omega)
    have hupper := sigma_lt_five_of_ten_factors hn hc
    let k := sigma 1 n / n
    have hd := Nat.mod_add_div (sigma 1 n) n
    rw [hmod] at hd
    change 5 + n*k = sigma 1 n at hd
    have hk5 : k < 5 := by
      by_contra! h
      have hu := Nat.mul_le_mul_left n h
      nlinarith only [hu, hupper, hd]
    have hk1 : k ≠ 1 := by
      intro hk
      rw [hk, mul_one] at hd
      omega
    have hkodd : k % 2 = 1 := Nat.odd_iff.mp hquotOdd
    have hk3 : k = 3 := by
      rcases hquotOdd with ⟨j, hj⟩
      omega
    have hshape : sigma 1 n = 3*n+5 := by
      rw [hk3] at hd
      nlinarith only [hd]
    have hmod4 : n % 4 = 1 := sigma_shape_mod_four hn hshape
    have hmod8 : n % 8 = 1 ∨ n % 8 = 5 := by
      have hrel := Nat.mod_mod_of_dvd n (by norm_num : 4 ∣ 8)
      have hlt := Nat.mod_lt n (by norm_num : 0 < 8)
      omega
    rcases hmod8 with hres | hres
    · exact h1 n hn hnsq hc hres hshape
    · exact h2 n hn hnsq hc hres hshape
  · exact h3 n hn hnsq (by omega)

end OMA.R_OeisA76495_conjecture_R1_H1_R1_H4_R1_H2_R1_H3_R1
