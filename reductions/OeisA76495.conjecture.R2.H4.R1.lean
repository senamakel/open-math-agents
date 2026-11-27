import OMAReductions.R_OeisA76495_conjecture_R2
import Mathlib

/-! Factor out the full two-power. In the two specified valuation residue
classes, up to sixteen support primes force the quotient to be two and
give an incompatible congruence on the odd square. -/

open ArithmeticFunction Finset

namespace R2EvenSeed

theorem factorizationEvenOfOddSigma {n : ℕ} (hs : Odd (sigma 1 n))
    (p : ℕ) (hp : p ∈ n.primeFactors) (hp2 : p ≠ 2) :
    Even (n.factorization p) := by
  have hn0 : n ≠ 0 := by
    intro hz
    simp [hz] at hs
  have hpr := Nat.prime_of_mem_primeFactors hp
  have hodd := hpr.odd_of_ne_two hp2
  let e := n.factorization p
  let f := fun q => sigma 1 (q ^ n.factorization q)
  have hf : f p ∣ sigma 1 n := by
    rw [ArithmeticFunction.isMultiplicative_sigma.multiplicative_factorization _ hn0]
    exact Finset.dvd_prod_of_mem f hp
  have hos : Odd (f p) := Nat.not_even_iff_odd.mp fun he => hs.not_two_dvd_nat (he.two_dvd.trans hf)
  change Odd (sigma 1 (p ^ e)) at hos
  rw [ArithmeticFunction.sigma_one_apply_prime_pow hpr, Finset.odd_sum_iff_odd_card_odd] at hos
  have hall : (Finset.range (e + 1)).filter (fun i => Odd (p ^ i)) = Finset.range (e + 1) :=
    Finset.filter_true_of_mem fun i _ => hodd.pow
  rw [hall, Finset.card_range] at hos
  have hm := Nat.odd_iff.mp hos
  change Even e
  rw [Nat.even_iff]
  omega

theorem odd_prime_powers_mod_four {p : ℕ} (hp : p % 4 = 3) (b : ℕ) :
    p ^ (2*b) % 4 = 1 ∧ p ^ (2*b+1) % 4 = 3 := by
  have hpdiv := Nat.mod_add_div p 4
  rw [hp] at hpdiv
  have hpsq : p ^ 2 % 4 = 1 := by
    have heq : p = 4 * (p / 4) + 3 := by omega
    have hrepr : p ^ 2 = 4 * (4 * (p / 4)^2 + 6 * (p / 4) + 2) + 1 := by nlinarith
    rw [hrepr]
    omega
  induction b with
  | zero => simp [hp]
  | succ b ih =>
    constructor
    · have he : 2 * (b+1) = 2*b+2 := by omega
      rw [he, pow_add, Nat.mul_mod]
      simp [ih.1, hpsq]
    · have he : 2 * (b+1) + 1 = (2*b+1)+2 := by omega
      rw [he, pow_add, Nat.mul_mod]
      simp [ih.2, hpsq]

theorem sigma_odd_prime_square_mod_four {p b : ℕ} (hprime : Nat.Prime p)
    (hp : p % 4 = 3) : sigma 1 (p^(2*b)) % 4 = 1 := by
  rw [sigma_one_apply_prime_pow hprime]
  have hsum : ∀ b, (∑ i ∈ Finset.range (2*b+1), p^i) % 4 = 1 := by
    intro b
    induction b with
    | zero => simp
    | succ b ih =>
      have he : 2*(b+1)+1 = (2*b+1)+2 := by omega
      rw [he, Finset.sum_range_succ, Finset.sum_range_succ]
      have hpow := odd_prime_powers_mod_four hp b
      have hpow2 : p^(2*b+2)%4=1 := by
        have hh := (odd_prime_powers_mod_four hp (b+1)).1
        simpa only [Nat.mul_succ] using hh
      simp only [Nat.add_mod, ih, hpow.2, hpow2, Nat.mod_mod]
  exact hsum b

theorem sigma_prime_power_one_mod_four {p e : ℕ} (hprime : Nat.Prime p)
    (hp : p % 4 = 1) : sigma 1 (p^e) % 4 = (e+1) % 4 := by
  rw [sigma_one_apply_prime_pow hprime]
  have hpow : ∀ i, p^i % 4 = 1 := by
    intro i
    induction i with
    | zero => simp
    | succ i ih =>
      rw [pow_succ, Nat.mul_mod, ih, hp]
  have hsum : ∀ e, (∑ i ∈ Finset.range (e+1), p^i) % 4 = (e+1)%4 := by
    intro e
    induction e with
    | zero => simp
    | succ e ih =>
      rw [Finset.sum_range_succ, Nat.add_mod, ih, hpow]
      omega
  exact hsum e

theorem sigma_two_power_mod_four (a : ℕ) (ha : 1 ≤ a) :
    sigma 1 (2^a) % 4 = 3 := by
  have hsum : ∀ a, 1 ≤ a → (∑ i ∈ Finset.range (a+1), 2^i) % 4 = 3 := by
    intro a
    induction a with
    | zero => intro h; omega
    | succ a ih =>
      intro h
      by_cases ha0 : a = 0
      · subst a
        norm_num
      · have ha1 : 1 ≤ a := by omega
        rw [Finset.sum_range_succ, Nat.add_mod, ih ha1]
        have hd : 4 ∣ 2^(a+1) := by
          have hx : 4 = 2^2 := by norm_num
          rw [hx]
          exact Nat.pow_dvd_pow 2 (by omega)
        rw [Nat.mod_eq_zero_of_dvd hd]
  rw [sigma_one_apply_prime_pow Nat.prime_two]
  exact hsum a ha

theorem four_dvd_candidate_forces_prime {n : ℕ} (hn0 : n ≠ 0)
    (hn : Even n) (hodd : Odd (sigma 1 n)) (hfour : 4 ∣ n)
    (hmod : sigma 1 n % n = 5) :
    ∃ p : ℕ, p ∈ n.primeFactors ∧ Nat.Prime p ∧ p % 4 = 1 ∧ n.factorization p % 4 = 2 := by
  let f : ℕ → ℕ := fun p => sigma 1 (p ^ n.factorization p)
  let S := n.primeFactors
  have h2dvd : 2 ∣ n := by
    obtain ⟨k, hk⟩ := hn
    exact ⟨k, by simpa [two_mul] using hk⟩
  have h2mem : 2 ∈ S := Nat.Prime.mem_primeFactors Nat.prime_two h2dvd hn0
  have h2exp : 1 ≤ n.factorization 2 := by
    exact Nat.prime_two.factorization_pos_of_dvd hn0 h2dvd
  have hprod : sigma 1 n = ∏ p ∈ S, f p := by
    rw [ArithmeticFunction.sigma_eq_prod_primeFactors_sum_range_factorization_pow_mul hn0]
    apply Finset.prod_congr rfl
    intro p hp
    simpa [f, Nat.mul_one] using
      (sigma_one_apply_prime_pow (Nat.prime_of_mem_primeFactors hp)).symm
  by_contra hno
  have hnotbad : ∀ p, p ∈ S → Nat.Prime p → p % 4 = 1 → n.factorization p % 4 ≠ 2 := by
    intro p hp hprime hpmod hval
    exact hno ⟨p, hp, hprime, hpmod, hval⟩
  have hlocal : ∀ p ∈ S.erase 2, f p % 4 = 1 := by
    intro p hp
    rcases Finset.mem_erase.mp hp with ⟨hp2, hpmem⟩
    have hprime := Nat.prime_of_mem_primeFactors hpmem
    have heven := factorizationEvenOfOddSigma hodd p hpmem hp2
    have hpmod : p % 4 = 1 ∨ p % 4 = 3 := by
      have hpodd := hprime.odd_of_ne_two hp2
      rcases hpodd with ⟨k, hk⟩
      have hpdiv := Nat.mod_add_div p 4
      have hplt := Nat.mod_lt p (by decide : 0 < 4)
      omega
    rcases hpmod with hp1 | hp3
    · have hnot := hnotbad p hpmem hprime hp1
      have he4 : n.factorization p % 4 = 0 := by
        have he2 := Nat.even_iff.mp heven
        omega
      have hl := sigma_prime_power_one_mod_four (e := n.factorization p) hprime hp1
      change sigma 1 (p ^ n.factorization p) % 4 = 1
      rw [hl]
      omega
    · obtain ⟨b, hb⟩ := heven
      change sigma 1 (p ^ n.factorization p) % 4 = 1
      have hl := sigma_odd_prime_square_mod_four (b := b) hprime hp3
      simpa [hb, two_mul] using hl
  have hrest : (∏ p ∈ S.erase 2, f p) % 4 = 1 := by
    rw [Finset.prod_nat_mod]
    have hprodone : ∏ p ∈ S.erase 2, f p % 4 = 1 :=
      Finset.prod_eq_one (fun p hp => hlocal p hp)
    rw [hprodone]
  have htwo : f 2 % 4 = 3 := by
    dsimp [f]
    exact sigma_two_power_mod_four (n.factorization 2) h2exp
  have hsigmod : sigma 1 n % 4 = 3 := by
    rw [hprod, ← Finset.prod_erase_mul S f h2mem, Nat.mul_mod, hrest, htwo]
  have hmodfour := Nat.mod_mod_of_dvd (sigma 1 n) hfour
  rw [hmod, hsigmod] at hmodfour
  norm_num at hmodfour


end R2EvenSeed

namespace SigmaEvenValuationGeneric

private theorem square_five_dvd {m : ℕ} (h : IsSquare m) (h5 : 5∣m) : 25∣m := by
  obtain ⟨u,hu⟩ := h
  have hd : 5∣u := by
    rw [hu] at h5
    exact (Nat.prime_five.dvd_mul.mp h5).elim id id
  rw [hu]
  exact Nat.mul_dvd_mul hd hd

private theorem sigma_five_lower {m : ℕ} (hm : 0 < m) (h : IsSquare m)
    (h5 : 5∣m) : 31*m ≤ 25*sigma 1 m := by
  obtain ⟨t,ht⟩ := square_five_dvd h h5
  have htpos : 0 < t := by omega
  have hd0 : m ∈ m.divisors := Nat.mem_divisors.mpr ⟨dvd_refl m, hm.ne'⟩
  have hd1 : 5*t ∈ m.divisors := Nat.mem_divisors.mpr
    ⟨⟨5, by rw [ht]; ring⟩, hm.ne'⟩
  have hd2 : t ∈ m.divisors := Nat.mem_divisors.mpr
    ⟨⟨25, by rw [ht]; ring⟩, hm.ne'⟩
  have hfin : ({m,5*t,t} : Finset ℕ) ⊆ m.divisors := by
    intro j hj
    simp only [Finset.mem_insert, Finset.mem_singleton] at hj
    rcases hj with rfl | rfl | rfl
    · exact hd0
    · exact hd1
    · exact hd2
  have hne1 : m ≠ 5*t := by omega
  have hne2 : m ≠ t := by omega
  have hne3 : 5*t ≠ t := by omega
  have hsum := Finset.sum_le_sum_of_subset_of_nonneg hfin
    (f := fun x : ℕ => x) (fun j _ _ => Nat.zero_le j)
  rw [← sigma_one_apply] at hsum
  have htot : ∑ j ∈ ({m,5*t,t} : Finset ℕ), j = 31*t := by
    have hnmem : m ∉ ({5*t,t} : Finset ℕ) := by simp [hne1,hne2]
    rw [Finset.sum_insert hnmem, Finset.sum_pair hne3]
    omega
  rw [htot] at hsum
  have hmul := Nat.mul_le_mul_left 25 hsum
  nlinarith only [ht,hmul]

theorem excludes_of_odd_part_abundance {a m k : ℕ}
    (ha : a%4=3 ∨ a%10=9) (hm : 0 < m) (hs : IsSquare m)
    (hsmall : 2*sigma 1 m < 5*m) :
    (2^(a+1)-1)*sigma 1 m ≠ k*(2^a*m)+5 := by
  intro heq
  let A := 2^a
  let M := 2^(a+1)-1
  let G := sigma 1 m
  change M*G=k*(A*m)+5 at heq
  have hA : 8 ≤ A := by
    exact Nat.pow_le_pow_right (show (0:ℕ)<2 by decide) (show 3 ≤ a by omega)
  have hM : M+1=2*A := by
    dsimp [M, A]
    rw [pow_succ']
    have hp : 0 < (2:ℕ)^a := by positivity
    omega
  have hmG : m ≤ G := by
    change m ≤ sigma 1 m
    rw [sigma_one_apply]
    exact Finset.single_le_sum (fun d _ => Nat.zero_le d)
      (Nat.mem_divisors.mpr ⟨dvd_refl m, hm.ne'⟩)
  have hMpos : 0 < M := by omega
  have hlow : A*m+5 < M*G := by
    have hmul := Nat.mul_le_mul_left M hmG
    have hMlarge : A+6 ≤ M := by omega
    have hMbig := Nat.mul_le_mul_right m hMlarge
    nlinarith only [hmul,hMbig,hm]
  have hhigh : M*G < 5*(A*m) := by
    have hGB : 2*G < 5*m := hsmall
    have hmul := Nat.mul_lt_mul_of_pos_left hGB (show 0<A by omega)
    have hshort : M ≤ 2*A := by omega
    have hmul' := Nat.mul_le_mul_right G hshort
    nlinarith only [hmul,hmul']
  have hk2 : 2 ≤ k := by
    by_contra! hn
    have h := Nat.mul_le_mul_right (A*m) (show k≤1 by omega)
    nlinarith only [h,hlow,heq]
  have hk5 : k < 5 := by
    by_contra! hn
    have h := Nat.mul_le_mul_right (A*m) hn
    nlinarith only [h,hhigh,heq]
  have hdiv3 : 3 ∣ M := by
    have h2 : 2 ∣ a+1 := by
      exact ⟨(a+1)/2, by omega⟩
    simpa [M] using Nat.pow_sub_one_dvd_pow_sub_one 2 h2
  have hdiv3eq : 3∣k*(A*m)+5 := heq ▸ dvd_mul_of_dvd_left hdiv3 _
  have hm3 : ¬3∣m := by
    intro hd
    have hN3 : 3∣k*(A*m) := dvd_mul_of_dvd_right (dvd_mul_of_dvd_right hd _) _
    exact (by decide : ¬3∣5) ((Nat.dvd_add_iff_right hN3).mpr hdiv3eq)
  have hmodA : A%3=2 := by
    have ha' : a=2*(a/2)+1 := by omega
    have hA' : 2^a=2*(4^(a/2)) := by
      conv_lhs => rw [ha']
      rw [pow_succ', pow_mul]
      norm_num
    dsimp [A]
    rw [hA', Nat.mul_mod]
    have hmodpow : 4^(a/2)%3=1 := by
      rw [Nat.pow_mod]
      norm_num
    simp [hmodpow]
  have hmodm : m%3=1 := by
    obtain ⟨u,hu⟩ := hs
    have hnot : m%3≠0 := fun h => hm3 (Nat.dvd_of_mod_eq_zero h)
    rw [hu,Nat.mul_mod] at hnot ⊢
    have hlt : u%3<3 := Nat.mod_lt _ (by decide)
    generalize hr : u%3=r at hlt hnot ⊢
    interval_cases r <;> norm_num at *
  have hk : k=2 := by
    have hmod := Nat.dvd_iff_mod_eq_zero.mp hdiv3eq
    rw [Nat.add_mod, Nat.mul_mod k, Nat.mul_mod A, hmodA, hmodm] at hmod
    norm_num at hmod
    omega
  have hN : 2*(A*m)=M*m+m := by
    have := congrArg (fun n => n*m) hM
    nlinarith only [this]
  rcases ha with ha4 | ha10
  · have hdiv5 : 5 ∣ M := by
      have h4 : 4 ∣ a+1 := ⟨a/4+1, by omega⟩
      have h15 : 15 ∣ M := by simpa [M] using Nat.pow_sub_one_dvd_pow_sub_one 2 h4
      exact (show 5 ∣ 15 by decide).trans h15
    have hm5 : 5 ∣ m := by
      have hs : 5 ∣ k*(A*m)+5 := heq ▸ dvd_mul_of_dvd_left hdiv5 _
      rw [hk] at hs
      have hh : 5 ∣ 2*(A*m) := (Nat.dvd_add_iff_left (dvd_refl 5)).mpr hs
      rw [hN] at hh
      exact (Nat.dvd_add_iff_right (dvd_mul_of_dvd_left hdiv5 m)).mpr hh
    have hG5 : 31*m ≤ 25*G := sigma_five_lower hm hs hm5
    have hm25 : 25 ≤ m := Nat.le_of_dvd hm (square_five_dvd hs hm5)
    have hmul := Nat.mul_le_mul_left M hG5
    have heqx := congrArg (fun n => 25*n) heq
    rw [hk] at heqx
    have hMx := congrArg (fun n => 31*n*m) hM
    have hAm := Nat.mul_le_mul_right m hA
    nlinarith only [hmul,heqx,hMx,hAm,hm25]
  · have h10 : 10 ∣ a+1 := ⟨a/10+1, by omega⟩
    have h1023 : 1023 ∣ M := by simpa [M] using Nat.pow_sub_one_dvd_pow_sub_one 2 h10
    have h11 : 11 ∣ M := (show 11∣1023 by decide).trans h1023
    have hk5 : 11 ∣ M*m+(m+5) := by
      have h : 11 ∣ k*(A*m)+5 := heq ▸ dvd_mul_of_dvd_left h11 _
      rw [hk, hN] at h
      simpa [Nat.add_assoc] using h
    have hm5 : 11 ∣ m+5 :=
      (Nat.dvd_add_iff_right (dvd_mul_of_dvd_left h11 m)).mpr hk5
    obtain ⟨u,hu⟩ := hs
    have hsq : m=u^2 := by simpa only [pow_two] using hu
    have hmod := Nat.dvd_iff_mod_eq_zero.mp hm5
    rw [hsq, Nat.add_mod, Nat.pow_mod] at hmod
    have hlt : u%11<11 := Nat.mod_lt _ (by decide)
    generalize hres : u%11=r at hmod hlt
    interval_cases r <;> norm_num at hmod


end SigmaEvenValuationGeneric

namespace BoundedOddAbundance

private def G (p e : ℕ) : ℕ := ∑ j ∈ Finset.range (e + 1), p ^ j
private theorem geometric_succ (p e : ℕ) :
    G p (e + 1) = 1 + p * G p e := by
  change (∑ j ∈ Finset.range (e + 1 + 1), p ^ j) = 1 + p * ∑ j ∈ Finset.range (e + 1), p ^ j
  rw [Finset.sum_range_succ' (fun i : ℕ => p ^ i) (e + 1)]
  simp only [pow_zero, pow_succ', Finset.mul_sum, add_comm]

theorem geometric_scaled (p e : ℕ) (hp : 1 ≤ p) :
    G p e*(p-1)+1 = p*p^e := by
  induction e with
  | zero =>
    simp [G]
    omega
  | succ e ih =>
    rw [geometric_succ, pow_succ']
    calc
      (1+p*G p e)*(p-1)+1 = p*(G p e*(p-1)+1) := by
        have hs : p-1+1 = p := by omega
        linear_combination hs
      _ = p*(p*p^e) := by rw [ih]

theorem geometric_upper (p e : ℕ) (hp : 1 ≤ p) :
    G p e * (p-1) ≤ p * p^e := by
  have h := geometric_scaled p e hp
  omega

theorem geometric_lower_base_bound {p q e : ℕ} (hq : 2 ≤ q)
    (hqp : q ≤ p) : G p e*(q-1) ≤ q*p^e := by
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
  have hmul : (G p e*(q-1))*(p-1) ≤ (q*p^e)*(p-1) := by
    calc
      _ = (G p e*(p-1))*(q-1) := by ring
      _ ≤ (p*p^e)*(q-1) := Nat.mul_le_mul_right _ (geometric_upper p e hp)
      _ = (p*(q-1))*p^e := by ring
      _ ≤ (q*(p-1))*p^e := Nat.mul_le_mul_right _ hc
      _ = _ := by ring
  exact Nat.le_of_mul_le_mul_right hmul (by omega)

/-- Lower bounds on each ordered prime give an upper bound on the full
abundancy product. -/
theorem product_profile_bound {ι : Type*} (I : Finset ι) (p q e : ι → ℕ)
    (hq : ∀ i ∈ I, 2 ≤ q i) (hp : ∀ i ∈ I, q i ≤ p i) :
    (∏ i ∈ I, G (p i) (e i))*(∏ i ∈ I, (q i-1)) ≤
      (∏ i ∈ I, q i)*(∏ i ∈ I, p i ^ e i) := by
  rw [← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]
  exact Finset.prod_le_prod (fun _ _ => Nat.zero_le _)
    (fun i hi => geometric_lower_base_bound (hq i hi) (hp i hi))

private def base : ℕ → ℕ
  | 0 => 5 | 1 => 7 | 2 => 11 | 3 => 13 | 4 => 17
  | 5 => 19 | 6 => 23 | 7 => 29 | 8 => 31 | 9 => 37
  | 10 => 41 | 11 => 43 | 12 => 47 | 13 => 53 | 14 => 59 | _ => 0

private theorem base_ratio (k : ℕ) (hk : k ≤ 15) :
    2 * (∏ i : Fin k, base i.val) < 5 * (∏ i : Fin k, (base i.val - 1)) := by
  interval_cases k <;> norm_num [base] <;> decide +kernel

private theorem rank_lower {m k : ℕ} (hs : m.primeFactors.card = k) (hk : k ≤ 15)
    (hprime : ∀ p ∈ m.primeFactors, p.Prime) (hlower : ∀ p ∈ m.primeFactors, 5 ≤ p) :
    ∀ i : Fin k, base i.val ≤ m.primeFactors.orderEmbOfFin hs i := by
  intro i
  by_contra! hbad
  let f := m.primeFactors.orderEmbOfFin hs
  let pre : Finset (Fin k) := Finset.Iic i
  have hsub : pre.image f ⊆ (Finset.range (base i.val)).filter
      (fun q => q.Prime ∧ 5 ≤ q) := by
    apply Finset.image_subset_iff.mpr
    intro j hj
    have hjle : j ≤ i := Finset.mem_Iic.mp hj
    have hji : f j ≤ f i := f.monotone hjle
    exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (lt_of_le_of_lt hji hbad),
      hprime (f j) (Finset.orderEmbOfFin_mem _ _ _),
      hlower (f j) (Finset.orderEmbOfFin_mem _ _ _)⟩
  have hcount : ((Finset.range (base i.val)).filter (fun q => q.Prime ∧ 5 ≤ q)).card = i.val := by
    have hi : i.val < 15 := lt_of_lt_of_le i.isLt hk
    interval_cases hval : i.val <;> norm_num [base, hval] <;> decide +kernel
  have hprecard : (pre.image f).card = i.val + 1 := by
    rw [Finset.card_image_of_injective _ f.injective, Fin.card_Iic]
  have hcard := Finset.card_le_card hsub
  rw [hprecard, hcount] at hcard
  omega

theorem scaled_sigma_lt_five_of_small_prime_support {m : ℕ} (hm : Odd m)
    (h3 : ¬ 3 ∣ m) (hcard : m.primeFactors.card ≤ 15) : 2*sigma 1 m < 5*m := by
  have hm0 : m ≠ 0 := by
    obtain ⟨k, hk⟩ := hm
    omega
  let k := m.primeFactors.card
  have hk : k ≤ 15 := hcard
  let p := m.primeFactors.orderEmbOfFin rfl
  let e : Fin k → ℕ := fun i => m.factorization (p i)
  have hmem (i : Fin k) : p i ∈ m.primeFactors := Finset.orderEmbOfFin_mem _ _ _
  have hp (i : Fin k) : (p i).Prime := Nat.prime_of_mem_primeFactors (hmem i)
  have hprimeSet (q : ℕ) (hq : q ∈ m.primeFactors) : q.Prime :=
    Nat.prime_of_mem_primeFactors hq
  have hlowerSet (q : ℕ) (hq : q ∈ m.primeFactors) : 5 ≤ q := by
    have hpr := hprimeSet q hq
    have hdiv := Nat.dvd_of_mem_primeFactors hq
    have hpne2 : q ≠ 2 := by
      intro heq
      have htwo : 2 ∣ m := by rw [← heq]; exact hdiv
      exact hm.not_two_dvd_nat htwo
    have hpne3 : q ≠ 3 := by
      intro heq
      have hthree : 3 ∣ m := by rw [← heq]; exact hdiv
      exact h3 hthree
    by_contra! hlt
    interval_cases q <;> norm_num at *
  have hpmin := rank_lower (m := m) (k := k) rfl hk hprimeSet hlowerSet
  let q : Fin k → ℕ := fun i => base i.val
  have hq : ∀ i, 2 ≤ q i := by
    intro i
    have hi : i.val < 15 := lt_of_lt_of_le i.isLt hk
    interval_cases hval : i.val <;> norm_num [q, base, hval]
  have hD : 0 < ∏ i : Fin k, (q i - 1) :=
    Finset.prod_pos fun i _ => by have := hq i; omega
  have hQ : 2 * (∏ i : Fin k, q i) < 5 * (∏ i : Fin k, (q i - 1)) := by
    exact base_ratio k hk
  have hval : (∏ i : Fin k, p i ^ e i) = m := by
    have hprod := (Nat.prod_primeFactors_pow_factorization hm0).symm
    rw [← Finset.map_orderEmbOfFin_univ m.primeFactors rfl, Finset.prod_map] at hprod
    exact hprod
  have hsum : (∏ i : Fin k, G (p i) (e i)) = sigma 1 m := by
    have hfactor : sigma 1 m =
        ∏ r ∈ m.primeFactors, sigma 1 (r ^ m.factorization r) := by
      rw [isMultiplicative_sigma.multiplicative_factorization _ hm0]
      simp [Finsupp.prod, Nat.support_factorization]
    rw [← Finset.map_orderEmbOfFin_univ m.primeFactors rfl, Finset.prod_map] at hfactor
    rw [hfactor]
    apply Finset.prod_congr rfl
    intro i _
    simpa [G] using (sigma_one_apply_prime_pow (hp i)).symm
  have hbound := product_profile_bound
    Finset.univ p q e (fun i _ => hq i) (fun i _ => hpmin i)
  let D := ∏ i : Fin k, (q i - 1)
  let Q := ∏ i : Fin k, q i
  change (∏ i : Fin k, G (p i) (e i)) * D ≤ Q * (∏ i : Fin k, p i ^ e i) at hbound
  rw [hval, hsum] at hbound
  by_contra! hu
  have hmul := Nat.mul_le_mul_right D hu
  have hQ' : 2*Q < 5*D := hQ
  have hlt := Nat.mul_lt_mul_of_pos_right hQ' (Nat.pos_of_ne_zero hm0)
  nlinarith only [hbound,hmul,hlt]

end BoundedOddAbundance

namespace SigmaEvenValuationGeneric

private theorem square_of_even_factorization {m : ℕ} (hm0 : m ≠ 0)
    (h : ∀ p, p.Prime → Even (m.factorization p)) : IsSquare m := by
  refine ⟨m.factorization.prod fun a b => a ^ (b / 2), ?_⟩
  rw [← pow_two, ← powMonoidHom_apply, map_finsuppProd]
  nth_rw 1 [← Nat.prod_factorization_pow_eq_self hm0]
  refine Finsupp.prod_congr fun p hp => ?_
  rw [powMonoidHom_apply, ← pow_mul,
    Nat.div_two_mul_two_of_even (h p (Nat.prime_of_mem_primeFactors hp))]

theorem excludes_even_small_support_residue {n : ℕ} (hn : Even n)
    (hcard : n.primeFactors.card ≤ 16) (hodd : Odd (sigma 1 n))
    (ha : n.factorization 2 % 4 = 3 ∨ n.factorization 2 % 10 = 9) :
    sigma 1 n % n ≠ 5 := by
  intro hmod
  have hn0 : n ≠ 0 := by
    intro h
    subst n
    simp at ha
  let a := n.factorization 2
  let m := n / 2^a
  let M := 2^(a+1)-1
  have hnprod : 2^a*m=n := Nat.ordProj_mul_ordCompl_eq_self n 2
  have hmpos : 0 < m := Nat.ordCompl_pos 2 hn0
  have hmOdd : Odd m := Nat.not_even_iff_odd.mp fun h =>
    Nat.not_dvd_ordCompl Nat.prime_two hn0 h.two_dvd
  have hcop : (2^a).Coprime m :=
    (Nat.coprime_ordCompl Nat.prime_two hn0).pow_left a
  have hM : sigma 1 (2^a)=M := by
    rw [sigma_one_apply_prime_pow Nat.prime_two]
    change BoundedOddAbundance.G 2 a=2^(a+1)-1
    rw [pow_succ']
    have h := BoundedOddAbundance.geometric_scaled 2 a (by decide)
    norm_num at h
    omega
  have hsig : sigma 1 n=M*sigma 1 m := by
    rw [← hnprod, isMultiplicative_sigma.map_mul_of_coprime hcop, hM]
  let k := sigma 1 n/n
  have hdiv := Nat.mod_add_div (sigma 1 n) n
  rw [hmod] at hdiv
  have heq : M*sigma 1 m=k*(2^a*m)+5 := by
    calc
      _ = sigma 1 n := hsig.symm
      _ = 5+n*k := hdiv.symm
      _ = _ := by rw [hnprod]; ring
  have h3M : 3∣M := by
    have h2 : 2∣a+1 := ⟨(a+1)/2, by dsimp [a]; omega⟩
    simpa [M] using Nat.pow_sub_one_dvd_pow_sub_one 2 h2
  have hm3 : ¬3∣m := by
    intro h3m
    have h3σ : 3∣k*(2^a*m)+5 := heq ▸ dvd_mul_of_dvd_left h3M _
    have h3n : 3∣ k*(2^a*m) :=
      dvd_mul_of_dvd_right (dvd_mul_of_dvd_right h3m _) _
    exact (by decide : ¬3∣5) ((Nat.dvd_add_iff_right h3n).mpr h3σ)
  have hf : m.factorization = n.factorization.erase 2 := Nat.factorization_ordCompl n 2
  have hfs : m.primeFactors = n.primeFactors.erase 2 := by
    simp only [← Nat.support_factorization, hf, Finsupp.support_erase]
  have h2mem : 2 ∈ n.primeFactors :=
    Nat.Prime.mem_primeFactors Nat.prime_two hn.two_dvd hn0
  have hmcard : m.primeFactors.card ≤ 15 := by
    rw [hfs, Finset.card_erase_of_mem h2mem]
    omega
  have hmSq : IsSquare m := by
    apply square_of_even_factorization hmpos.ne'
    intro p hp
    rw [hf]
    by_cases h : p=2
    · simp [h]
    · rw [Finsupp.erase_ne h]
      by_cases hpmem : p∈n.primeFactors
      · exact R2EvenSeed.factorizationEvenOfOddSigma hodd p hpmem h
      · have hzero : n.factorization p=0 := Finsupp.notMem_support_iff.mp
          (by rwa [Nat.support_factorization])
        simp [hzero]
  have hsmall := BoundedOddAbundance.scaled_sigma_lt_five_of_small_prime_support hmOdd hm3 hmcard
  exact excludes_of_odd_part_abundance ha hmpos hmSq hsmall heq

end SigmaEvenValuationGeneric



namespace OMA.R_OeisA76495_conjecture_R2_H4_R1

/-- Valuation two with exactly three support primes. -/
def H1 : Prop :=
  ∀ n : ℕ, Even n → n.primeFactors.card = 3 → Odd (sigma 1 n) → 4 ∣ n →
    (∃ p : ℕ, p ∈ n.primeFactors ∧ Nat.Prime p ∧ p % 4 = 1 ∧
      n.factorization p % 4 = 2) →
    n.factorization 2 = 2 → sigma 1 n % n ≠ 5

/-- Valuation two with at least four support primes. -/
def H2 : Prop :=
  ∀ n : ℕ, Even n → 4 ≤ n.primeFactors.card → Odd (sigma 1 n) → 4 ∣ n →
    (∃ p : ℕ, p ∈ n.primeFactors ∧ Nat.Prime p ∧ p % 4 = 1 ∧
      n.factorization p % 4 = 2) →
    n.factorization 2 = 2 → sigma 1 n % n ≠ 5

/-- Valuation at least three and three through sixteen support primes, after
excluding the two congruence classes of the valuation. -/
def H3 : Prop :=
  ∀ n : ℕ, Even n → 3 ≤ n.primeFactors.card → n.primeFactors.card ≤ 16 →
    Odd (sigma 1 n) → 4 ∣ n →
    (∃ p : ℕ, p ∈ n.primeFactors ∧ Nat.Prime p ∧ p % 4 = 1 ∧
      n.factorization p % 4 = 2) →
    3 ≤ n.factorization 2 → n.factorization 2 % 4 ≠ 3 →
    n.factorization 2 % 10 ≠ 9 → sigma 1 n % n ≠ 5

/-- Valuation at least three and support of at least seventeen primes. -/
def H4 : Prop :=
  ∀ n : ℕ, Even n → 17 ≤ n.primeFactors.card → Odd (sigma 1 n) → 4 ∣ n →
    (∃ p : ℕ, p ∈ n.primeFactors ∧ Nat.Prime p ∧ p % 4 = 1 ∧
      n.factorization p % 4 = 2) →
    3 ≤ n.factorization 2 → sigma 1 n % n ≠ 5

theorem main : H1 → H2 → H3 → H4 → OMA.R_OeisA76495_conjecture_R2.H4 := by
  intro h23 h24 hlo hhi n heven hcard hodd hfour hmod
  have hn0 : n ≠ 0 := by
    intro hz
    subst n
    simp at hcard
  have hseed := R2EvenSeed.four_dvd_candidate_forces_prime hn0 heven hodd hfour hmod
  have hd : 2 ≤ n.factorization 2 :=
    (Nat.prime_two.pow_dvd_iff_le_factorization hn0).mp (by simpa using hfour)
  by_cases hv : n.factorization 2 = 2
  · by_cases hc : n.primeFactors.card = 3
    · exact h23 n heven hc hodd hfour hseed hv hmod
    · exact h24 n heven (by omega) hodd hfour hseed hv hmod
  · have hv3 : 3 ≤ n.factorization 2 := by omega
    by_cases hc : n.primeFactors.card ≤ 16
    · by_cases hres : n.factorization 2 % 4 = 3 ∨ n.factorization 2 % 10 = 9
      · exact SigmaEvenValuationGeneric.excludes_even_small_support_residue heven hc hodd hres hmod
      · exact hlo n heven hcard hc hodd hfour hseed hv3
          (fun h => hres (Or.inl h)) (fun h => hres (Or.inr h)) hmod
    · exact hhi n heven (by omega) hodd hfour hseed hv3 hmod

end OMA.R_OeisA76495_conjecture_R2_H4_R1
