import OMAReductions.R_OeisA76495_conjecture_R1_H1_R1

/-! Reduce the first odd nonsquare support size to four explicit prime supports. -/

open ArithmeticFunction

namespace OMA.R_OeisA76495_conjecture_R1_H1_R1_H4_R1

private theorem geometric_succ (p e : ℕ) :
    (fun p e : ℕ => ∑ j ∈ Finset.range (e + 1), p ^ j) p (e + 1) = 1 + p * (fun p e : ℕ => ∑ j ∈ Finset.range (e + 1), p ^ j) p e := by
  change (∑ j ∈ Finset.range (e + 1 + 1), p ^ j) = 1 + p * ∑ j ∈ Finset.range (e + 1), p ^ j
  rw [Finset.sum_range_succ' (fun i : ℕ => p ^ i) (e + 1)]
  simp only [pow_zero, pow_succ', Finset.mul_sum, add_comm]

theorem geometric_scaled (p e : ℕ) (hp : 1 ≤ p) :
    (fun p e : ℕ => ∑ j ∈ Finset.range (e + 1), p ^ j) p e*(p-1)+1 = p*p^e := by
  induction e with
  | zero =>
    simp
    omega
  | succ e ih =>
    rw [geometric_succ, pow_succ']
    calc
      (1+p*(fun p e : ℕ => ∑ j ∈ Finset.range (e + 1), p ^ j) p e)*(p-1)+1 = p*((fun p e : ℕ => ∑ j ∈ Finset.range (e + 1), p ^ j) p e*(p-1)+1) := by
        have hs : p-1+1 = p := by omega
        linear_combination hs
      _ = p*(p*p^e) := by rw [ih]

theorem geometric_upper (p e : ℕ) (hp : 1 ≤ p) :
    (fun p e : ℕ => ∑ j ∈ Finset.range (e + 1), p ^ j) p e * (p-1) ≤ p * p^e := by
  have h := geometric_scaled p e hp
  omega

theorem geometric_lower_base_bound {p q e : ℕ} (hq : 2 ≤ q)
    (hqp : q ≤ p) : (fun p e : ℕ => ∑ j ∈ Finset.range (e + 1), p ^ j) p e*(q-1) ≤ q*p^e := by
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
  have hmul : ((fun p e : ℕ => ∑ j ∈ Finset.range (e + 1), p ^ j) p e*(q-1))*(p-1) ≤ (q*p^e)*(p-1) := by
    calc
      _ = ((fun p e : ℕ => ∑ j ∈ Finset.range (e + 1), p ^ j) p e*(p-1))*(q-1) := by ring
      _ ≤ (p*p^e)*(q-1) := Nat.mul_le_mul_right _ (geometric_upper p e hp)
      _ = (p*(q-1))*p^e := by ring
      _ ≤ (q*(p-1))*p^e := Nat.mul_le_mul_right _ hc
      _ = _ := by ring
  exact Nat.le_of_mul_le_mul_right hmul (by omega)

/-- Lower bounds on each ordered prime give an upper bound on the full
abundancy product. -/
theorem product_profile_bound {ι : Type*} (I : Finset ι) (p q e : ι → ℕ)
    (hq : ∀ i ∈ I, 2 ≤ q i) (hp : ∀ i ∈ I, q i ≤ p i) :
    (∏ i ∈ I, (fun p e : ℕ => ∑ j ∈ Finset.range (e + 1), p ^ j) (p i) (e i))*(∏ i ∈ I, (q i-1)) ≤
      (∏ i ∈ I, q i)*(∏ i ∈ I, p i ^ e i) := by
  rw [← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]
  exact Finset.prod_le_prod (fun _ _ => Nat.zero_le _)
    (fun i hi => geometric_lower_base_bound (hq i hi) (hp i hi))

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

private theorem rank_lower_bound {s : Finset ℕ} (hs : s.card = 8)
    (hprime : ∀ p ∈ s, p.Prime) (hlower : ∀ p ∈ s, 3 ≤ p) :
    ∀ i : Fin 8, (![3, 5, 7, 11, 13, 17, 19, 23] : Fin 8 → ℕ) i ≤ s.orderEmbOfFin hs i := by
  intro i
  by_contra! hlt
  have hsub : s.filter (fun p => p < (![3, 5, 7, 11, 13, 17, 19, 23] : Fin 8 → ℕ) i) ⊆
      (Finset.range ((![3, 5, 7, 11, 13, 17, 19, 23] : Fin 8 → ℕ) i)).filter (fun p => p.Prime ∧ 3 ≤ p) := by
    intro p hp
    rcases Finset.mem_filter.mp hp with ⟨hps, hpt⟩
    exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hpt, ⟨hprime p hps, hlower p hps⟩⟩
  have hcount : ((Finset.range ((![3, 5, 7, 11, 13, 17, 19, 23] : Fin 8 → ℕ) i)).filter (fun p => p.Prime ∧ 3 ≤ p)).card =
      i.val := by fin_cases i <;> decide
  have hprefix := rank_filter_bound hs i ((![3, 5, 7, 11, 13, 17, 19, 23] : Fin 8 → ℕ) i) hlt
  have hcard := Finset.card_le_card hsub
  omega

private theorem supports_eq : ((((Finset.range 38).filter (fun p => p.Prime ∧ 3 ≤ p)).powersetCard 8).filter
      (fun s => 3 * (∏ p ∈ s, (p - 1)) < ∏ p ∈ s, p)) =
    {{3, 5, 7, 11, 13, 17, 19, 23}, {3, 5, 7, 11, 13, 17, 19, 29},
     {3, 5, 7, 11, 13, 17, 19, 31}, {3, 5, 7, 11, 13, 17, 19, 37}} := by
  decide +kernel

theorem mem_supports_of_large_abundancy {s : Finset ℕ} (hs : s.card = 8)
    (hp : ∀ p ∈ s, p.Prime) (hl : ∀ p ∈ s, 3 ≤ p) (e : ℕ → ℕ)
    (hlarge : 3 * (∏ p ∈ s, p ^ e p) <
      ∏ p ∈ s, (fun p e : ℕ => ∑ j ∈ Finset.range (e + 1), p ^ j) p (e p)) :
    s ∈ ({{3, 5, 7, 11, 13, 17, 19, 23}, {3, 5, 7, 11, 13, 17, 19, 29},
      {3, 5, 7, 11, 13, 17, 19, 31}, {3, 5, 7, 11, 13, 17, 19, 37}} :
      Finset (Finset ℕ)) := by
  let f := s.orderEmbOfFin hs
  let E : Fin 8 → ℕ := fun i => e (f i)
  have hrank := rank_lower_bound hs hp hl
  have hmap : Finset.map f.toEmbedding Finset.univ = s :=
    Finset.map_orderEmbOfFin_univ s hs
  have hbig : 3 * (∏ i : Fin 8, f i ^ E i) <
      ∏ i : Fin 8, (fun p e : ℕ => ∑ j ∈ Finset.range (e + 1), p ^ j) (f i) (E i) := by
    rw [← hmap, Finset.prod_map, Finset.prod_map] at hlarge
    exact hlarge
  have hfmax : f 7 < 41 := by
    by_contra! hmax
    have hcap (i : Fin 8) (_hi : i ∈ Finset.univ) : (fun i : Fin 8 => if i.val = 7 then 41 else (![3, 5, 7, 11, 13, 17, 19, 23] : Fin 8 → ℕ) i) i ≤ f i := by
      by_cases he : i.val = 7
      · have hi : i = 7 := Fin.ext he
        subst i
        simpa [] using hmax
      · simpa [he] using hrank i
    have htwo (i : Fin 8) (_hi : i ∈ Finset.univ) : 2 ≤ (fun i : Fin 8 => if i.val = 7 then 41 else (![3, 5, 7, 11, 13, 17, 19, 23] : Fin 8 → ℕ) i) i := by
      fin_cases i <;> decide
    let D := ∏ i : Fin 8, ((fun i : Fin 8 => if i.val = 7 then 41 else (![3, 5, 7, 11, 13, 17, 19, 23] : Fin 8 → ℕ) i) i - 1)
    let Q := ∏ i : Fin 8, (fun i : Fin 8 => if i.val = 7 then 41 else (![3, 5, 7, 11, 13, 17, 19, 23] : Fin 8 → ℕ) i) i
    have hd : 0 < D := by decide
    have hq : Q ≤ 3 * D := by decide
    have hbound := product_profile_bound Finset.univ f (fun i : Fin 8 => if i.val = 7 then 41 else (![3, 5, 7, 11, 13, 17, 19, 23] : Fin 8 → ℕ) i) E
      htwo hcap
    have hlt := Nat.mul_lt_mul_of_pos_right hbig hd
    have hle := Nat.mul_le_mul_right (∏ i : Fin 8, f i ^ E i) hq
    change (∏ i : Fin 8, (fun p e : ℕ => ∑ j ∈ Finset.range (e + 1), p ^ j) (f i) (E i)) * D ≤
      Q * (∏ i : Fin 8, f i ^ E i) at hbound
    nlinarith
  have hall (p : ℕ) (hm : p ∈ s) : p < 38 := by
    rw [← hmap, Finset.mem_map] at hm
    obtain ⟨i, _, rfl⟩ := hm
    have hi : i ≤ (7 : Fin 8) := by
      change i.val ≤ 7
      omega
    have hup := lt_of_le_of_lt (f.monotone hi) hfmax
    have hpr := hp (f i) (Finset.orderEmbOfFin_mem _ _ _)
    change Nat.Prime (f i) at hpr
    by_contra! h
    interval_cases he : f i <;> norm_num [he] at hpr
  have htwo (p : ℕ) (hm : p ∈ s) : 2 ≤ p := (hp p hm).two_le
  let D := ∏ p ∈ s, (p - 1)
  let N := ∏ p ∈ s, p ^ e p
  have hd : 0 < D := Finset.prod_pos (fun p hm => by have := hl p hm; omega)
  have hn : 0 < N := Finset.prod_pos (fun p hm => pow_pos (hp p hm).pos _)
  have hb := product_profile_bound s id id e htwo
    (fun _ _ => le_rfl)
  change (∏ p ∈ s, (fun p e : ℕ => ∑ j ∈ Finset.range (e + 1), p ^ j) p (e p)) * D ≤
    (∏ p ∈ s, p) * N at hb
  change 3 * N < (∏ p ∈ s, (fun p e : ℕ => ∑ j ∈ Finset.range (e + 1), p ^ j) p (e p)) at hlarge
  have hstrict : 3 * D < ∏ p ∈ s, p := by
    by_contra! h
    have hlt := Nat.mul_lt_mul_of_pos_right hlarge hd
    have hle := Nat.mul_le_mul_right N h
    nlinarith
  rw [← supports_eq]
  exact Finset.mem_filter.mpr ⟨Finset.mem_powersetCard.mpr
    ⟨fun p hm => Finset.mem_filter.mpr
      ⟨Finset.mem_range.mpr (hall p hm), hp p hm, hl p hm⟩, hs⟩, hstrict⟩

theorem abundancy_lt_five {s : Finset ℕ} (hs : s.card = 8)
    (hp : ∀ p ∈ s, p.Prime) (hl : ∀ p ∈ s, 3 ≤ p) (e : ℕ → ℕ) :
    (∏ p ∈ s, (fun p e : ℕ => ∑ j ∈ Finset.range (e + 1), p ^ j) p (e p)) <
      5 * (∏ p ∈ s, p ^ e p) := by
  let f := s.orderEmbOfFin hs
  let E : Fin 8 → ℕ := fun i => e (f i)
  let D := ∏ i : Fin 8, ((![3, 5, 7, 11, 13, 17, 19, 23] : Fin 8 → ℕ) i - 1)
  let Q := ∏ i : Fin 8, (![3, 5, 7, 11, 13, 17, 19, 23] : Fin 8 → ℕ) i
  let N := ∏ i : Fin 8, f i ^ E i
  have hmap : Finset.map f.toEmbedding Finset.univ = s :=
    Finset.map_orderEmbOfFin_univ s hs
  rw [← hmap, Finset.prod_map, Finset.prod_map]
  change (∏ i : Fin 8, (fun p e : ℕ => ∑ j ∈ Finset.range (e + 1), p ^ j) (f i) (E i)) < 5 * N
  have htwo (i : Fin 8) (_hi : i ∈ Finset.univ) : 2 ≤ (![3, 5, 7, 11, 13, 17, 19, 23] : Fin 8 → ℕ) i := by
    fin_cases i <;> decide
  have hrank := rank_lower_bound hs hp hl
  have hbound := product_profile_bound Finset.univ f (![3, 5, 7, 11, 13, 17, 19, 23] : Fin 8 → ℕ) E
    htwo (fun i _ => hrank i)
  change (∏ i : Fin 8, (fun p e : ℕ => ∑ j ∈ Finset.range (e + 1), p ^ j) (f i) (E i)) * D ≤ Q * N
    at hbound
  have hq : Q < 5 * D := by decide
  have hn : 0 < N := Finset.prod_pos (fun i _ =>
    pow_pos (hp (f i) (Finset.orderEmbOfFin_mem _ _ _)).pos _)
  have hlt := Nat.mul_lt_mul_of_pos_right hq hn
  by_contra! h
  have hle := Nat.mul_le_mul_right D h
  nlinarith

private theorem primeFactors_of_sigma_eq_three_mul_add_five {n : ℕ} (hn : Odd n)
    (hc : n.primeFactors.card = 8) (hsigma : sigma 1 n = 3 * n + 5) :
    n.primeFactors ∈ ({{3, 5, 7, 11, 13, 17, 19, 23}, {3, 5, 7, 11, 13, 17, 19, 29},
      {3, 5, 7, 11, 13, 17, 19, 31}, {3, 5, 7, 11, 13, 17, 19, 37}} :
      Finset (Finset ℕ)) := by
  have hn0 : n ≠ 0 := by
    obtain ⟨k, hk⟩ := hn
    omega
  have hp (p : ℕ) (hm : p ∈ n.primeFactors) : p.Prime := Nat.prime_of_mem_primeFactors hm
  have hl (p : ℕ) (hm : p ∈ n.primeFactors) : 3 ≤ p := by
    have hd := (Nat.mem_primeFactors.mp hm).2.1
    have hne : p ≠ 2 := fun he => hn.not_two_dvd_nat (he ▸ hd)
    have htwo := (hp p hm).two_le
    omega
  apply mem_supports_of_large_abundancy hc hp hl n.factorization
  have hfactor : sigma 1 n =
      ∏ p ∈ n.primeFactors, sigma 1 (p ^ n.factorization p) := by
    rw [isMultiplicative_sigma.multiplicative_factorization _ hn0]
    simp [Finsupp.prod, Nat.support_factorization]
  have hlhs : (∏ p ∈ n.primeFactors, (fun p e : ℕ => ∑ j ∈ Finset.range (e + 1), p ^ j) p (n.factorization p))
      = sigma 1 n := by
    rw [hfactor]
    apply Finset.prod_congr rfl
    intro p hm
    rw [sigma_one_apply_prime_pow (hp p hm)]
  have hprod : (∏ p ∈ n.primeFactors, p ^ n.factorization p) = n :=
    (Nat.prod_primeFactors_pow_factorization hn0).symm
  rw [hlhs, hprod, hsigma]
  omega

/-- The first nonsquare support size has quotient three and only four possible supports. -/
def H1 : Prop :=
  ∀ n : ℕ, Odd n → (∃ q ∈ ({23, 29, 31, 37} : Finset ℕ),
    n.primeFactors = insert q {3, 5, 7, 11, 13, 17, 19}) → sigma 1 n ≠ 3 * n + 5

/-- The odd nonsquare case with at least nine distinct prime factors. -/
def H2 : Prop :=
  ∀ n : ℕ, Odd n → ¬ IsSquare n → 9 ≤ n.primeFactors.card → sigma 1 n % n ≠ 5

theorem main : H1 → H2 → OMA.R_OeisA76495_conjecture_R1_H1_R1.H4 := by
  intro heq hlarge n hn hnsq hcard
  by_cases hc : n.primeFactors.card = 8
  · intro hmod
    have hn0 : n ≠ 0 := by obtain ⟨k, hk⟩ := hn; omega
    have hp (p : ℕ) (hm : p ∈ n.primeFactors) : p.Prime := Nat.prime_of_mem_primeFactors hm
    have hl (p : ℕ) (hm : p ∈ n.primeFactors) : 3 ≤ p := by
      have hne : p ≠ 2 := fun h => hn.not_two_dvd_nat (h ▸ Nat.dvd_of_mem_primeFactors hm)
      have := (hp p hm).two_le
      omega
    have hu := abundancy_lt_five hc hp hl n.factorization
    have hsigma : sigma 1 n =
        ∏ p ∈ n.primeFactors, (fun p e : ℕ => ∑ j ∈ Finset.range (e + 1), p ^ j) p (n.factorization p) := by
      rw [isMultiplicative_sigma.multiplicative_factorization _ hn0]
      simp only [Finsupp.prod, Nat.support_factorization]
      exact Finset.prod_congr rfl (fun p hm => sigma_one_apply_prime_pow (hp p hm))
    have hprod : (∏ p ∈ n.primeFactors, p ^ n.factorization p) = n :=
      (Nat.prod_primeFactors_pow_factorization hn0).symm
    rw [← hsigma, hprod] at hu
    have hlow := SigmaFive.large_sigma_of_four_odd_factors hn (by omega)
    have ho := SigmaFive.odd_quotient_of_even_sigma hn hmod
      (SigmaFive.even_sigma_of_odd_nonsquare hn0 hn hnsq)
    let k := sigma 1 n / n
    have hd := Nat.mod_add_div (sigma 1 n) n
    rw [hmod] at hd
    change 5 + n * k = sigma 1 n at hd
    have hk5 : k < 5 := by
      by_contra! h
      have := Nat.mul_le_mul_left n h
      nlinarith
    have hk1 : k ≠ 1 := by
      intro h
      rw [h, mul_one] at hd
      omega
    have hkodd : k % 2 = 1 := Nat.odd_iff.mp ho
    have classify (j : ℕ) (h5 : j < 5) (h1 : j ≠ 1) (ho : j % 2 = 1) : j = 3 := by
      omega
    have hk := classify k hk5 hk1 hkodd
    have h3 : sigma 1 n = 3 * n + 5 := by
      rw [hk] at hd
      omega
    have hs := primeFactors_of_sigma_eq_three_mul_add_five hn hc h3
    simp only [Finset.mem_insert, Finset.mem_singleton] at hs
    apply heq n hn _ h3
    rcases hs with hs | hs | hs | hs
    · exact ⟨23, by decide, hs.trans (by decide)⟩
    · exact ⟨29, by decide, hs.trans (by decide)⟩
    · exact ⟨31, by decide, hs.trans (by decide)⟩
    · exact ⟨37, by decide, hs.trans (by decide)⟩
  · exact hlarge n hn hnsq (by omega)

end OMA.R_OeisA76495_conjecture_R1_H1_R1_H4_R1
