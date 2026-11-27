import OMAReductions.R_OeisA76495_conjecture_R1_H1_R1_H2_R1

/-! Exclude remainder five for odd squares whose five prime factors include five and lie at most 31. -/

open Finset ArithmeticFunction BigOperators

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

theorem quotient_two {n s : ℕ} (hn : Odd n) (hs : Odd s)
    (hmod : s % n = 5) (hlarge : 5 < s) (hupper : s < 3*n) :
    s = 2*n+5 := by
  let k := s / n
  have hd := Nat.mod_add_div s n
  rw [hmod] at hd
  change 5+n*k = s at hd
  have hn2 := Nat.odd_iff.mp hn
  have hs2 := Nat.odd_iff.mp hs
  have hm := congrArg (fun a : ℕ => a % 2) hd
  rw [Nat.add_mod, Nat.mul_mod, hn2, hs2] at hm
  have he : k % 2 = 0 := by
    change (1 + (1 * (k % 2)) % 2) % 2 = 1 at hm
    simp only [one_mul, Nat.mod_mod] at hm
    omega
  have hk0 : k ≠ 0 := by
    intro hzero
    simp [hzero] at hd
    omega
  have hk3 : k < 3 := by
    by_contra! hk
    have hmul := Nat.mul_le_mul_left n hk
    nlinarith only [hd, hmul, hupper]
  have hparity : ∀ j : ℕ, j % 2 = 0 → j ≠ 0 → j < 3 → j = 2 := by
    intro j hj h0 hj3
    omega
  have hk2 : k = 2 := hparity k he hk0 hk3
  rw [hk2] at hd
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

theorem product_profile_bound {ι : Type*} (I : Finset ι) (p q e : ι → ℕ)
    (hq : ∀ i ∈ I, 2 ≤ q i) (hp : ∀ i ∈ I, q i ≤ p i) :
    (∏ i ∈ I, geometric (p i) (e i))*(∏ i ∈ I, (q i-1)) ≤
      (∏ i ∈ I, q i)*(∏ i ∈ I, p i ^ e i) := by
  rw [← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]
  exact Finset.prod_le_prod (fun _ _ => Nat.zero_le _)
    (fun i hi => geometric_lower_base_bound (hq i hi) (hp i hi))

theorem geometric_even_odd (p k : ℕ) (hp : Odd p) :
    Odd (geometric p (2*k)) := by
  induction k with
  | zero => exact ⟨0, by simp [geometric]⟩
  | succ k ih =>
    obtain ⟨a, ha⟩ := hp
    obtain ⟨b, hb⟩ := ih
    refine ⟨p*(2*a*b+a+b+1), ?_⟩
    rw [show 2*(k+1) = 2*k+1+1 by omega, geometric, geometric, hb, ha]
    ring

theorem three_mem_five_prime_support (p e : Fin 5 → ℕ)
    (hs : StrictMono p) (hp : ∀ i, (p i).Prime) (hodd : ∀ i, Odd (p i))
    (hlarge : 2*(∏ i, p i ^ e i) ≤ ∏ i, geometric (p i) (e i)) :
    ∃ i, p i = 3 := by
  by_contra! hn
  have h0 : 5 ≤ p 0 := by
    have hp0 := hp 0
    have ho0 := hodd 0
    have hn0 := hn 0
    have hlow := hp0.two_le
    by_contra! ht
    interval_cases p 0 <;> norm_num at ho0 <;> contradiction
  have h1 : 7 ≤ p 1 := by
    have hm := hs (by decide : (0 : Fin 5) < 1)
    have ho := hodd 1
    by_contra! ht
    have hl : 6 ≤ p 1 := by omega
    interval_cases p 1 <;> norm_num at ho
  have h2 : 11 ≤ p 2 := by
    have hm := hs (by decide : (1 : Fin 5) < 2)
    have hp2 := hp 2
    by_contra! ht
    have hl : 8 ≤ p 2 := by omega
    interval_cases p 2 <;> norm_num at hp2
  have h3 : 13 ≤ p 3 := by
    have hm := hs (by decide : (2 : Fin 5) < 3)
    have ho := hodd 3
    by_contra! ht
    have hl : 12 ≤ p 3 := by omega
    interval_cases p 3 <;> norm_num at ho
  have h4 : 17 ≤ p 4 := by
    have hm := hs (by decide : (3 : Fin 5) < 4)
    have hp4 := hp 4
    by_contra! ht
    have hl : 14 ≤ p 4 := by omega
    interval_cases p 4 <;> norm_num at hp4
  let q : Fin 5 → ℕ := ![5,7,11,13,17]
  have hq (i : Fin 5) : 2 ≤ q i := by fin_cases i <;> decide
  have hqp (i : Fin 5) : q i ≤ p i := by
    fin_cases i
    · exact h0
    · exact h1
    · exact h2
    · exact h3
    · exact h4
  have hb := product_profile_bound Finset.univ p q e
    (fun i _ => hq i) (fun i _ => hqp i)
  have hnpos : 0 < ∏ i, p i ^ e i :=
    Finset.prod_pos (fun i _ => pow_pos (hp i).pos _)
  let N := ∏ i, p i ^ e i
  let S := ∏ i, geometric (p i) (e i)
  change 2*N ≤ S at hlarge
  change 0 < N at hnpos
  have hqden : (∏ i, (q i-1)) = 46080 := by decide
  have hqnum : (∏ i, q i) = 85085 := by decide
  change S*(∏ i, (q i-1)) ≤ (∏ i, q i)*N at hb
  rw [hqden, hqnum] at hb
  omega

end SigmaAbundancyBounds

namespace SigmaFiveExactBridge
open SigmaAbundancyBounds

private def leastOddPrime (i : ℕ) : ℕ :=
  match i with
  | 0 => 3
  | 1 => 5
  | 2 => 7
  | 3 => 11
  | _ => 13

private theorem rank_filter_bound {s : Finset ℕ} {k : ℕ} (hs : s.card = k)
    (i : Fin k) (t : ℕ) (hfi : s.orderEmbOfFin hs i < t) :
    i.val + 1 ≤ (s.filter (fun x => x < t)).card := by
  let f := s.orderEmbOfFin hs
  let pre := Finset.Iic i
  have hsub : Finset.image f pre ⊆ s.filter (fun x => x < t) := by
    apply Finset.image_subset_iff.mpr
    intro j hj
    have hjle : j ≤ i := Finset.mem_Iic.mp hj
    have hmem : f j ∈ s := Finset.orderEmbOfFin_mem _ _ _
    have hlt : f j < t := lt_of_le_of_lt (f.monotone hjle) hfi
    exact Finset.mem_filter.mpr ⟨hmem, hlt⟩
  have hc := Finset.card_le_card hsub
  rw [Finset.card_image_of_injective pre f.injective, Fin.card_Iic] at hc
  exact hc

private theorem rank_lower_bound {s : Finset ℕ} {k : ℕ} (hs : s.card = k)
    (hk : k ≤ 5) (hprime : ∀ p ∈ s, p.Prime) (hlower : ∀ p ∈ s, 3 ≤ p) :
    ∀ i : Fin k, leastOddPrime i.val ≤ s.orderEmbOfFin hs i := by
  intro i
  have hi7 : i.val < 5 := lt_of_lt_of_le i.isLt hk
  interval_cases hval : i.val
  all_goals
    by_contra! hlt
    have hsub : s.filter (fun p => p < leastOddPrime i.val) ⊆
        (Finset.range (leastOddPrime i.val)).filter (fun p => p.Prime ∧ 3 ≤ p) := by
      intro p hp
      rcases Finset.mem_filter.mp hp with ⟨hps, hpt⟩
      exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hpt,
        ⟨hprime p hps, hlower p hps⟩⟩
    have hcount : (s.filter (fun p => p < leastOddPrime i.val)).card ≤ i.val := by
      calc
        _ ≤ ((Finset.range (leastOddPrime i.val)).filter
            (fun p => p.Prime ∧ 3 ≤ p)).card := Finset.card_le_card hsub
        _ = i.val := by rw [hval]; simp [leastOddPrime]; decide
    have hprefix := rank_filter_bound hs i (leastOddPrime i.val) (by
      simpa [leastOddPrime, hval] using hlt)
    omega

theorem odd_square_five_sigma_lt_three {n : ℕ} (hn : Odd n)
    (hcard : n.primeFactors.card = 5) : sigma 1 n < 3*n := by
  classical
  have hn0 : n ≠ 0 := by
    intro hz
    subst n
    obtain ⟨k, hk⟩ := hn
    omega
  let f := n.primeFactors.orderEmbOfFin hcard
  let e : Fin 5 → ℕ := fun i => n.factorization (f i)
  have hmem (i : Fin 5) : f i ∈ n.primeFactors := Finset.orderEmbOfFin_mem _ _ _
  have hp (i : Fin 5) : (f i).Prime := Nat.prime_of_mem_primeFactors (hmem i)
  have hq (i : Fin 5) (_hi : i ∈ Finset.univ) : 2 ≤ leastOddPrime i.val := by
    fin_cases i <;> norm_num [leastOddPrime]
  have hpall (p : ℕ) (hp : p ∈ n.primeFactors) : p.Prime :=
    Nat.prime_of_mem_primeFactors hp
  have hlowerall (p : ℕ) (hp : p ∈ n.primeFactors) : 3 ≤ p := by
    have hd := (Nat.mem_primeFactors.mp hp).2.1
    have hne : p ≠ 2 := by
      intro he
      exact hn.not_two_dvd_nat (he ▸ hd)
    have hp2 := (hpall p hp).two_le
    omega
  have hrank := rank_lower_bound hcard (by omega) hpall hlowerall
  have hlower (i : Fin 5) (hi : i ∈ Finset.univ) : leastOddPrime i.val ≤ f i := by
    exact hrank i
  have hprod : (∏ i : Fin 5, f i ^ e i) = n := by
    have hh := Nat.prod_primeFactors_pow_factorization hn0
    rw [← Finset.map_orderEmbOfFin_univ n.primeFactors hcard,
      Finset.prod_map] at hh
    simpa [e, f] using hh.symm
  have hsig : sigma 1 n = ∏ i : Fin 5,
      SigmaAbundancyBounds.geometric (f i) (e i) := by
    have hfactor : sigma 1 n =
        ∏ p ∈ n.primeFactors, sigma 1 (p ^ n.factorization p) := by
      rw [isMultiplicative_sigma.multiplicative_factorization _ hn0]
      simp [Finsupp.prod, Nat.support_factorization]
    rw [← Finset.map_orderEmbOfFin_univ n.primeFactors hcard,
      Finset.prod_map] at hfactor
    calc
      sigma 1 n = ∏ i : Fin 5, sigma 1 ((f i) ^ e i) := by simpa [f, e] using hfactor
      _ = _ := by
        apply Finset.prod_congr rfl
        intro i hi
        rw [sigma_one_apply_prime_pow (hp i)]
        exact (SigmaAbundancyBounds.geometric_eq_sum _ _).symm
  let D := ∏ i : Fin 5, (leastOddPrime i - 1)
  let Q := ∏ i : Fin 5, leastOddPrime i
  have hprofile := SigmaAbundancyBounds.product_profile_bound
    Finset.univ f (fun i => leastOddPrime i.val) e hq hlower
  have hD : 0 < D := by norm_num [D, leastOddPrime, Fin.prod_univ_succ]
  have hQ : Q < 3*D := by norm_num [Q, D, leastOddPrime, Fin.prod_univ_succ]
  have hscaled := Nat.mul_lt_mul_of_pos_right hQ (Nat.pos_of_ne_zero hn0)
  have hmain : (∏ i : Fin 5, SigmaAbundancyBounds.geometric (f i) (e i))*D <
      3*D*n := by
    calc
      _ ≤ Q*n := by simpa [D, hsig, hprod] using hprofile
      _ < 3*D*n := by nlinarith [hscaled]
  by_contra! hnot
  have hcontra := Nat.mul_le_mul_right D hnot
  nlinarith [hmain]

end SigmaFiveExactBridge

namespace SigmaFiveWithFiveSmall

open SigmaAbundancyBounds

private def profile : Fin 5 → ℕ := ![3, 5, 23, 29, 31]

theorem profile_excess :
    (192751417677 - 2 * 96196124025) * 3^10 > 5 * 96196124025 := by norm_num

private theorem geometric_profile_lower (p Q e : ℕ) (hQ : 2 ≤ Q)
    (hpQ : p ≤ Q) (he : 2 ≤ e) :
    geometric Q 2 * p^e ≤ geometric p e * Q^2 := by
  have hscale := geometric_scaled_mono p he
  have hbase : geometric Q 2 * p^2 ≤ geometric p 2 * Q^2 := by
    have hcross : (p : ℤ) ≤ Q := by exact_mod_cast hpQ
    have hdiff : (Q : ℤ) - p ≥ 0 := by omega
    have hfactor := mul_nonneg hdiff (show (0 : ℤ) ≤ Q*p + Q + p by positivity)
    have hiden : ((p:ℤ)^2 + p + 1) * Q^2 - ((Q:ℤ)^2 + Q + 1) * p^2 =
        (Q-p) * (Q*p+Q+p) := by ring_nf
    have hpolyInt : ((Q:ℤ)^2 + Q + 1) * p^2 ≤ ((p:ℤ)^2 + p + 1) * Q^2 := by nlinarith [hiden, hfactor]
    have hpoly : (Q^2 + Q + 1) * p^2 ≤ (p^2 + p + 1) * Q^2 := by exact_mod_cast hpolyInt
    rw [geometric_eq_sum, geometric_eq_sum]
    norm_num [Finset.sum_range_succ]
    nlinarith [hpoly]
  have hA := Nat.mul_le_mul_right (p^e) hbase
  have hB := Nat.mul_le_mul_right (Q^2) hscale
  have hcancel : p^2 * (geometric Q 2 * p^e) ≤
      p^2 * (geometric p e * Q^2) := by
    calc
      _ = (geometric Q 2 * p^2) * p^e := by ring
      _ ≤ (geometric p 2 * Q^2) * p^e := by simpa [Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm] using hA
      _ = (geometric p 2 * p^e) * Q^2 := by ring
      _ ≤ (geometric p e * p^2) * Q^2 := by simpa [Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm] using hB
      _ = _ := by ring
  by_cases hp0 : p = 0
  · simp [hp0, geometric_eq_sum, show e ≠ 0 by omega]
  · exact Nat.le_of_mul_le_mul_left hcancel (pow_pos (Nat.pos_of_ne_zero hp0) 2)

/-- Exact abundance-profile contradiction for a five-prime support with profile
    bounded by [3,5,23,29,31]. -/
theorem no_equation_of_profile
    (p e : Fin 5 → ℕ) (hp : ∀ i, p i ≤ profile i)
    (he : ∀ i, 2 ≤ e i) (hn : 3^10 ≤ ∏ i, p i ^ e i) :
    ∏ i, geometric (p i) (e i) ≠ 2 * (∏ i, p i ^ e i) + 5 := by
  intro heq
  have hterm : ∀ i : Fin 5,
      geometric (profile i) 2 * p i ^ e i ≤
        geometric (p i) (e i) * (profile i)^2 := by
    intro i
    exact geometric_profile_lower (p i) (profile i) (e i) (by fin_cases i <;> norm_num [profile]) (hp i) (he i)
  have hprod := Finset.prod_le_prod (s := Finset.univ)
    (f := fun i : Fin 5 => geometric (profile i) 2 * p i ^ e i)
    (g := fun i => geometric (p i) (e i) * (profile i)^2)
    (by intro i hi; positivity) (by intro i hi; exact hterm i)
  simp only [Finset.prod_mul_distrib] at hprod
  have hvals1 : ∏ i : Fin 5, geometric (profile i) 2 = 192751417677 := by decide
  have hvals2 : ∏ i : Fin 5, (profile i)^2 = 96196124025 := by decide
  have hdiff := profile_excess
  rw [hvals1, hvals2] at hprod
  rw [heq] at hprod
  nlinarith [hdiff, hn]

end SigmaFiveWithFiveSmall

namespace SigmaFiveWithFiveSmall

open scoped BigOperators
open SigmaAbundancyBounds

/-- Five distinct odd support primes, all at most 31 and including five,
cannot satisfy the quotient-two divisor-sum equation at even positive valuations. -/
theorem no_equation_small_odd_support
    (p e : Fin 5 → ℕ) (hstrict : StrictMono p)
    (hprime : ∀ i, (p i).Prime) (hodd : ∀ i, Odd (p i))
    (hmax : ∀ i, p i ≤ 31) (hf : ∃ i, p i = 5) (he : ∀ i, 2 ≤ e i) :
    ∏ i, geometric (p i) (e i) ≠ 2 * (∏ i, p i ^ e i) + 5 := by
  intro heq
  have hp3 (i : Fin 5) : 3 ≤ p i := by
    have hh := (hprime i).two_le
    obtain ⟨u,hu⟩ := hodd i
    omega
  have hsum : 2 * (∏ i, p i ^ e i) ≤ ∏ i, geometric (p i) (e i) := by
    rw [heq]
    exact Nat.le_add_right _ _
  obtain ⟨i,hthree⟩ := three_mem_five_prime_support p e hstrict hprime hodd hsum
  have h0 : p 0 = 3 := by
    have hh := hstrict.monotone (Fin.zero_le i)
    have hmin := hp3 0
    omega
  obtain ⟨j,hfive⟩ := hf
  have hj0 : j ≠ 0 := by
    intro hj
    subst j
    omega
  have hj1 : (1 : Fin 5) ≤ j := by
    change 1 ≤ j.val
    have hval : j.val ≠ 0 := by
      intro hzero
      exact hj0 (Fin.ext hzero)
    omega
  have h1 : p 1 = 5 := by
    have hl := hstrict (by decide : (0 : Fin 5) < 1)
    have hu := hstrict.monotone hj1
    obtain ⟨u,hu1⟩ := hodd 1
    omega
  have h4 : p 4 ≤ 31 := hmax 4
  have h3 : p 3 ≤ 29 := by
    have hl := hstrict (by decide : (3 : Fin 5) < 4)
    obtain ⟨u,hu⟩ := hodd 3
    omega
  have h2 : p 2 ≤ 23 := by
    have hl := hstrict (by decide : (2 : Fin 5) < 3)
    have hp := hprime 2
    by_contra! hnot
    have hu : p 2 ≤ 28 := by omega
    interval_cases p 2 <;> norm_num at hp
  have hprofile (i : Fin 5) : p i ≤ (![3,5,23,29,31] : Fin 5 → ℕ) i := by
    fin_cases i
    · exact h0.le
    · exact h1.le
    · exact h2
    · exact h3
    · exact h4
  have hn : 3^10 ≤ ∏ i, p i ^ e i := by
    have hpow (i : Fin 5) : (3 : ℕ)^2 ≤ p i ^ e i :=
      (Nat.pow_le_pow_left (hp3 i) _).trans (Nat.pow_le_pow_right (hprime i).one_le (he i))
    have hb : (∏ _i : Fin 5, (3 : ℕ)^2) ≤ ∏ i, p i ^ e i :=
      Finset.prod_le_prod (fun _ _ => Nat.zero_le _) (fun i _ => hpow i)
    calc
      (3 : ℕ)^10 = ∏ _i : Fin 5, (3 : ℕ)^2 := by decide
      _ ≤ _ := hb
  exact no_equation_of_profile p e hprofile he hn heq

open ArithmeticFunction

theorem exclude_small_omega5_includes_five {n : ℕ} (hn : Odd n) (hsq : IsSquare n)
    (hcard : n.primeFactors.card = 5) (h5 : 5 ∣ n)
    (hmax : ∀ p ∈ n.primeFactors, p ≤ 31) : sigma 1 n % n ≠ 5 := by
  classical
  intro hmod
  have hn0 : n ≠ 0 := by
    obtain ⟨k,hk⟩ := hn
    omega
  obtain ⟨m, hm⟩ := hsq
  have hfac : n.factorization = (2 : ℕ) • m.factorization := by
    rw [hm, show m*m = m^2 by rw [pow_two], Nat.factorization_pow]
  let f := n.primeFactors.orderEmbOfFin hcard
  let e (i : Fin 5) := n.factorization (f i)
  have hfmem (i : Fin 5) : f i ∈ n.primeFactors := Finset.orderEmbOfFin_mem _ _ _
  have hp (i : Fin 5) : (f i).Prime := Nat.prime_of_mem_primeFactors (hfmem i)
  have hodd (i : Fin 5) : Odd (f i) := by
    have hd := Nat.dvd_of_mem_primeFactors (hfmem i)
    have hne : f i ≠ 2 := by
      intro htwo
      exact hn.not_two_dvd_nat (htwo ▸ hd)
    exact (hp i).odd_of_ne_two hne
  have he (i : Fin 5) : Even (e i) := by
    refine ⟨m.factorization (f i), ?_⟩
    simp [e, hfac, two_smul]
  have he2 (i : Fin 5) : 2 ≤ e i := by
    have hpos : 0 < e i := (hp i).factorization_pos_of_dvd hn0
      (Nat.dvd_of_mem_primeFactors (hfmem i))
    obtain ⟨a,ha⟩ := he i
    omega
  have hmem5 : 5 ∈ n.primeFactors := Nat.mem_primeFactors.mpr ⟨by decide, h5, hn0⟩
  rw [← Finset.map_orderEmbOfFin_univ n.primeFactors hcard] at hmem5
  obtain ⟨j,_,hj⟩ := Finset.mem_map.mp hmem5
  have hN : (∏ i, (f i)^e i) = n := by
    have hprod := Nat.prod_primeFactors_pow_factorization hn0
    rw [← Finset.map_orderEmbOfFin_univ n.primeFactors hcard, Finset.prod_map] at hprod
    simpa [e, f] using hprod.symm
  have hS : (∏ i, geometric (f i) (e i)) = sigma 1 n := by
    have hfactor : sigma 1 n = ∏ p ∈ n.primeFactors, sigma 1 (p ^ n.factorization p) := by
      rw [isMultiplicative_sigma.multiplicative_factorization _ hn0]
      simp [Finsupp.prod,Nat.support_factorization]
    rw [← Finset.map_orderEmbOfFin_univ n.primeFactors hcard, Finset.prod_map] at hfactor
    calc
      _ = ∏ i : Fin 5, sigma 1 (f i ^ e i) := by
        apply Finset.prod_congr rfl
        intro i hi
        rw [sigma_one_apply_prime_pow (hp i)]
        exact geometric_eq_sum (f i) (e i)
      _ = sigma 1 n := hfactor.symm
  have hoddSum : Odd (sigma 1 n) := by
    rw [← hS]
    have hl (i : Fin 5) : Odd (geometric (f i) (e i)) := by
      obtain ⟨a,ha⟩ := he i
      have hh : e i = 2*a := by omega
      rw [hh]
      exact geometric_even_odd (f i) a (hodd i)
    have hall (I : Finset (Fin 5)) : Odd (∏ i ∈ I, geometric (f i) (e i)) := by
      induction I using Finset.induction_on with
      | empty => simp
      | @insert i I hi ih =>
        rw [Finset.prod_insert hi]
        exact (hl i).mul ih
    exact hall Finset.univ
  have hn5 : 5 < n := by
    have hh := Nat.mod_lt (sigma 1 n) (Nat.pos_of_ne_zero hn0)
    rwa [hmod] at hh
  have hle : n ≤ sigma 1 n := by
    rw [sigma_one_apply]
    exact Finset.single_le_sum (f := fun d : ℕ => d)
      (fun _ _ => Nat.zero_le _) (Nat.mem_divisors_self n hn0)
  have heq : sigma 1 n = 2*n+5 :=
    quotient_two hn hoddSum hmod (hn5.trans_le hle)
      (SigmaFiveExactBridge.odd_square_five_sigma_lt_three hn hcard)
  apply no_equation_small_odd_support f e f.strictMono hp hodd
    (fun i => hmax (f i) (hfmem i)) ⟨j,hj⟩ he2
  rw [hN,hS,heq]



end SigmaFiveWithFiveSmall

theorem OMA.solution : OMA.R_OeisA76495_conjecture_R1_H1_R1_H2_R1.H1 := by
  intro n hn hs hc h5 hmax
  exact SigmaFiveWithFiveSmall.exclude_small_omega5_includes_five hn hs hc h5 hmax
