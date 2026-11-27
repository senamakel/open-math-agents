import OMAReductions.R_OeisA76495_conjecture_R1_H1_R1_H4_R1

/-! Reduce nine-prime odd nonsquares to a bounded search and four prime prefixes. -/

open ArithmeticFunction

namespace OMA.R_OeisA76495_conjecture_R1_H1_R1_H4_R1_H2_R1

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

private theorem rank_lower_bound (p : Fin 9 → ℕ)
    (hprime : ∀ i, Nat.Prime (p i)) (hlower : ∀ i, 3 ≤ p i)
    (hstrict : StrictMono p) :
    ∀ i : Fin 9, (![3,5,7,11,13,17,19,23,29] : Fin 9 → ℕ) i ≤ p i := by
  intro i
  by_contra! hbad
  let pre : Finset (Fin 9) := Finset.Iic i
  have hprefix_sub : pre.image p ⊆
      (Finset.range ((![3,5,7,11,13,17,19,23,29] : Fin 9 → ℕ) i)).filter
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
      ((Finset.range ((![3,5,7,11,13,17,19,23,29] : Fin 9 → ℕ) i)).filter
        (fun q => q.Prime ∧ 3 ≤ q)).card = i.val := by
    fin_cases i <;> decide
  have hprefix_card : (pre.image p).card = i.val + 1 := by
    rw [Finset.card_image_of_injective _ hstrict.injective, Fin.card_Iic]
  have hcard := Finset.card_le_card hprefix_sub
  rw [hprefix_card, hcount] at hcard
  omega

/-- If nine increasing primes at least three have geometric abundancy above
three, then the first eight lie below the stated coordinate caps. -/
theorem first_eight_below_caps (p : Fin 9 → ℕ) (e : Fin 9 → ℕ)
    (hprime : ∀ i, Nat.Prime (p i)) (hlower : ∀ i, 3 ≤ p i)
    (hstrict : StrictMono p)
    (hlarge : 3 * (∏ i : Fin 9, p i ^ e i) <
      ∏ i : Fin 9, (fun p e : ℕ => ∑ j ∈ Finset.range (e + 1), p ^ j) (p i) (e i)) :
    ∀ j : Fin 8, p j.castSucc ≤ (![8,12,15,19,23,28,38,77] : Fin 8 → ℕ) j := by
  have hrank := rank_lower_bound p hprime hlower hstrict
  intro j
  by_contra! hcapj
  let q : Fin 9 → ℕ := fun i =>
    if j.castSucc ≤ i then max ((![3,5,7,11,13,17,19,23,29] : Fin 9 → ℕ) i) ((![8,12,15,19,23,28,38,77] : Fin 8 → ℕ) j + 1) else (![3,5,7,11,13,17,19,23,29] : Fin 9 → ℕ) i
  have hle (i : Fin 9) : q i ≤ p i := by
    have hr := hrank i
    by_cases hij : j.castSucc ≤ i
    · have hpj : (![8,12,15,19,23,28,38,77] : Fin 8 → ℕ) j + 1 ≤ p j.castSucc := by omega
      have hpji : p j.castSucc ≤ p i := by
        rcases eq_or_lt_of_le hij with h | h
        · simp [h]
        · exact (hstrict h).le
      simp [q, hij]
      exact ⟨hr, hpj.trans hpji⟩
    · simp [q, hij]
      exact hr
  have htwo (i : Fin 9) (_hi : i ∈ Finset.univ) : 2 ≤ q i := by
    have hmin : 2 ≤ (![3,5,7,11,13,17,19,23,29] : Fin 9 → ℕ) i := by fin_cases i <;> decide
    dsimp only [q]
    split
    · exact hmin.trans (le_max_left _ _)
    · exact hmin
  let D := ∏ i : Fin 9, (q i - 1)
  let Q := ∏ i : Fin 9, q i
  let N := ∏ i : Fin 9, p i ^ e i
  let S := ∏ i : Fin 9, (fun p e : ℕ => ∑ j ∈ Finset.range (e + 1), p ^ j) (p i) (e i)
  have hD : 0 < D := by
    dsimp [D]
    apply Finset.prod_pos
    intro i _
    have := htwo i (Finset.mem_univ _)
    omega
  have hprofile := product_profile_bound
    Finset.univ p q e htwo (fun i _ => hle i)
  change S * D ≤ Q * N at hprofile
  have hQD : Q ≤ 3 * D := by
    dsimp [Q, D]
    fin_cases j <;> decide +kernel
  have hscale := Nat.mul_lt_mul_of_pos_right hlarge hD
  have hqscale := Nat.mul_le_mul_right N hQD
  change 3 * N < S at hlarge
  change S * D ≤ Q * N at hprofile
  nlinarith [hprofile, hscale, hqscale]

set_option maxHeartbeats 2000000 in
private theorem screen_lists (ps : List ℕ)
    (hs : List.Forall₂ (fun p c => p ≤ c ∧ p.Prime) ps [8, 12, 15, 19, 23, 28, 38, 77])
    (hp : (2 :: ps).Pairwise (· < ·))
    {q : ℕ} (hlab : 3 * (ps.map (· - 1)).prod * (q - 1) < ps.prod * q) :
    ps ∈ ([[3,5,7,11,13,17,19,23], [3,5,7,11,13,17,19,29],
           [3,5,7,11,13,17,19,31], [3,5,7,11,13,17,19,37]] : List (List ℕ)) ∨
      (ps.prod < 3 * (ps.map (· - 1)).prod ∧ q ≤ 3009) := by
  let prefixes : ℕ → List ℕ → List (List ℕ) := fun prev caps =>
    caps.foldr
      (fun cap rest lower =>
        ((List.range (cap+1)).filter (fun p => decide (lower < p ∧ p.Prime))).flatMap
          (fun p => (rest p).map (p :: ·)))
      (fun _ => [[]]) prev
  have mem_prefixes {s caps : List ℕ} {prev : ℕ}
      (hs : List.Forall₂ (fun p c => p ≤ c ∧ p.Prime) s caps)
      (hp : (prev :: s).Pairwise (· < ·)) : s ∈ prefixes prev caps := by
    induction hs generalizing prev with
    | nil => simp [prefixes]
    | @cons p cap s caps hc tail ih =>
        obtain ⟨hbefore, hafter⟩ := List.pairwise_cons.mp hp
        change p :: s ∈
          (((List.range (cap+1)).filter (fun r => decide (prev < r ∧ r.Prime))).flatMap
            (fun r => (prefixes r caps).map (r :: ·)))
        apply List.mem_flatMap.mpr
        have hlt : prev < p := hbefore p (by simp)
        refine ⟨p, ?_, List.mem_map.mpr ⟨s, ih hafter, rfl⟩⟩
        exact List.mem_filter.mpr ⟨List.mem_range.mpr (Nat.lt_succ_of_le hc.1),
          decide_eq_true ⟨hlt, hc.2⟩⟩
  let exceptional : List (List ℕ) :=
    [[3,5,7,11,13,17,19,23], [3,5,7,11,13,17,19,29],
     [3,5,7,11,13,17,19,31], [3,5,7,11,13,17,19,37]]
  let den : List ℕ → ℕ := fun ps => (ps.map (· - 1)).prod
  let test (ps : List ℕ) : Bool :=
    if 3 * den ps ≤ ps.prod then decide (ps ∈ exceptional)
    else decide (ps.prod * 3010 ≤ 3 * den ps * 3009)
  have finite_test : (prefixes 2 [8,12,15,19,23,28,38,77]).all test = true := by
    decide +kernel
  have h := List.all_eq_true.mp finite_test ps (mem_prefixes hs hp)
  change 3 * den ps * (q - 1) < ps.prod * q at hlab
  change ps ∈ exceptional ∨ (ps.prod < 3 * den ps ∧ q ≤ 3009)
  by_cases hp : 3 * den ps ≤ ps.prod
  · exact Or.inl (of_decide_eq_true (by simpa only [test, if_pos hp] using h))
  · refine Or.inr ⟨by omega, ?_⟩
    have h3010 : ps.prod * 3010 ≤ 3 * den ps * 3009 :=
      of_decide_eq_true (by simpa only [test, if_neg hp] using h)
    by_contra! hq'
    obtain ⟨t, rfl⟩ := Nat.exists_eq_add_of_le (show 3010 ≤ q by omega)
    have hchain : ps.prod * (3010 + t) ≤ 3 * den ps * ((3010 + t) - 1) := by
      calc
        _ = ps.prod * 3010 + ps.prod * t := by ring
        _ ≤ 3 * den ps * 3009 + (3 * den ps) * t :=
          Nat.add_le_add h3010 (Nat.mul_le_mul_right _ (by omega))
        _ = _ := by rw [show (3010+t)-1 = 3009+t by omega]; ring
    exact (not_le_of_gt hlab) hchain

def H1 : Prop :=
  ∀ p e : Fin 9 → ℕ, StrictMono p → (∀ i, (p i).Prime ∧ 3 ≤ p i) →
    (∀ i, 1 ≤ e i) → (∀ i : Fin 8, p i.castSucc ≤ (![8,12,15,19,23,28,38,77] : Fin 8 → ℕ) i) →
    p 8 ≤ 3009 →
    (∏ i : Fin 8, p i.castSucc) < 3 * (∏ i : Fin 8, (p i.castSucc - 1)) →
    (∏ i, ∑ j ∈ Finset.range (e i + 1), p i ^ j) ≠ 3 * (∏ i, p i ^ e i) + 5

def H2 : Prop :=
  ∀ p e : Fin 9 → ℕ, StrictMono p → (∀ i, (p i).Prime ∧ 3 ≤ p i) →
    (∀ i, 1 ≤ e i) →
    List.ofFn (fun i : Fin 8 => p i.castSucc) ∈
      ([[3,5,7,11,13,17,19,23], [3,5,7,11,13,17,19,29],
        [3,5,7,11,13,17,19,31], [3,5,7,11,13,17,19,37]] : List (List ℕ)) →
    (∏ i, ∑ j ∈ Finset.range (e i + 1), p i ^ j) ≠ 3 * (∏ i, p i ^ e i) + 5

def H3 : Prop :=
  ∀ n : ℕ, Odd n → ¬ IsSquare n → 10 ≤ n.primeFactors.card → sigma 1 n % n ≠ 5

theorem main : H1 → H2 → H3 → OMA.R_OeisA76495_conjecture_R1_H1_R1_H4_R1.H2 := by
  intro hfinite hexceptional hmore n hn hnsq hcard
  by_cases hc : n.primeFactors.card = 9
  · intro hmod
    have hn0 : n ≠ 0 := by obtain ⟨k, hk⟩ := hn; omega
    let p := n.primeFactors.orderEmbOfFin hc
    let e : Fin 9 → ℕ := fun i => n.factorization (p i)
    have hmem (i : Fin 9) : p i ∈ n.primeFactors := Finset.orderEmbOfFin_mem _ _ _
    have hp (i : Fin 9) : (p i).Prime ∧ 3 ≤ p i := by
      have hpr := Nat.prime_of_mem_primeFactors (hmem i)
      have hne : p i ≠ 2 := fun hz => hn.not_two_dvd_nat (hz ▸ Nat.dvd_of_mem_primeFactors (hmem i))
      exact ⟨hpr, by have := hpr.two_le; omega⟩
    have he (i : Fin 9) : 1 ≤ e i :=
      (hp i).1.factorization_pos_of_dvd hn0 (Nat.dvd_of_mem_primeFactors (hmem i))
    have hvalue : (∏ i : Fin 9, p i ^ e i) = n := by
      have hprod := (Nat.prod_primeFactors_pow_factorization hn0).symm
      rw [← Finset.map_orderEmbOfFin_univ n.primeFactors hc, Finset.prod_map] at hprod
      exact hprod
    have hsum : (∏ i : Fin 9, (fun p e : ℕ => ∑ j ∈ Finset.range (e + 1), p ^ j) (p i) (e i)) = sigma 1 n := by
      have hfactor : sigma 1 n =
          ∏ r ∈ n.primeFactors, sigma 1 (r ^ n.factorization r) := by
        rw [isMultiplicative_sigma.multiplicative_factorization _ hn0]
        simp [Finsupp.prod, Nat.support_factorization]
      rw [← Finset.map_orderEmbOfFin_univ n.primeFactors hc, Finset.prod_map] at hfactor
      rw [hfactor]
      apply Finset.prod_congr rfl
      intro i _
      change (fun p e : ℕ => ∑ j ∈ Finset.range (e + 1), p ^ j) (p i) (e i) = sigma 1 (p i ^ e i)
      rw [sigma_one_apply_prime_pow (hp i).1]
    let m : Fin 9 → ℕ := ![3,5,7,11,13,17,19,23,29]
    let D := ∏ i, (m i - 1)
    let Q := ∏ i, m i
    have h2 (i : Fin 9) (_hi : i ∈ Finset.univ) : 2 ≤ m i := by fin_cases i <;> decide
    have hm (i : Fin 9) (_hi : i ∈ Finset.univ) : m i ≤ p i := rank_lower_bound p (fun i => (hp i).1) (fun i => (hp i).2) p.strictMono i
    have hbound := product_profile_bound Finset.univ p m e h2 hm
    change (∏ i : Fin 9, (fun p e : ℕ => ∑ j ∈ Finset.range (e + 1), p ^ j) (p i) (e i)) * D ≤ Q * (∏ i : Fin 9, p i ^ e i) at hbound
    rw [hvalue, hsum] at hbound
    have hQ : Q < 5 * D := by decide +kernel
    have hupper : sigma 1 n < 5 * n := by
      by_contra! hu
      have hD := Nat.mul_le_mul_right D hu
      have hl := Nat.mul_lt_mul_of_pos_right hQ (Nat.pos_of_ne_zero hn0)
      nlinarith only [hbound, hD, hl]
    have hlow := SigmaFive.large_sigma_of_four_odd_factors hn (by omega)
    let k := sigma 1 n / n
    have hd := Nat.mod_add_div (sigma 1 n) n
    rw [hmod] at hd
    change 5 + n * k = sigma 1 n at hd
    have hk5 : k < 5 := by
      by_contra! h
      have hu := Nat.mul_le_mul_left n h
      nlinarith only [hu, hupper, hd]
    have hk1 : k ≠ 1 := by
      intro h
      rw [h, mul_one] at hd
      omega
    have hkodd : k % 2 = 1 := Nat.odd_iff.mp
      (SigmaFive.odd_quotient_of_even_sigma hn hmod
        (SigmaFive.even_sigma_of_odd_nonsquare hn0 hn hnsq))
    have classify (j : ℕ) (h5 : j < 5) (h1 : j ≠ 1) (ho : j % 2 = 1) : j = 3 := by omega
    have hk := classify k hk5 hk1 hkodd
    have h3 : sigma 1 n = 3 * n + 5 := by rw [hk] at hd; omega
    have hlarge : 3 * (∏ i : Fin 9, p i ^ e i) < ∏ i : Fin 9, (fun p e : ℕ => ∑ j ∈ Finset.range (e + 1), p ^ j) (p i) (e i) := by
      rw [hsum, hvalue, h3]
      omega
    have hpCap := first_eight_below_caps p e (fun i => (hp i).1) (fun i => (hp i).2) p.strictMono hlarge
    have hlimit :=
      product_profile_bound Finset.univ p p e (fun i _ => (hp i).1.two_le) (fun _ _ => le_rfl)
    let den := ∏ i : Fin 9, (p i - 1)
    let num := ∏ i : Fin 9, p i
    change (∏ i : Fin 9, (fun p e : ℕ => ∑ j ∈ Finset.range (e + 1), p ^ j) (p i) (e i)) * den ≤ num * (∏ i : Fin 9, p i ^ e i)
      at hlimit
    rw [hvalue, hsum, h3] at hlimit
    have hden : 0 < den := Finset.prod_pos (fun i _ => by have := (hp i).2; omega)
    have hstrict : 3 * den < num := by
      by_contra! h
      have hweight := Nat.mul_le_mul_right n h
      nlinarith only [hlimit, hweight, hden]
    dsimp only [den, num] at hstrict
    rw [Fin.prod_univ_castSucc (fun i : Fin 9 => p i - 1),
      Fin.prod_univ_castSucc (fun i : Fin 9 => p i)] at hstrict
    let ps := List.ofFn (fun i : Fin 8 => p i.castSucc)
    have hsort : (2 :: ps).Pairwise (· < ·) := by
      refine List.pairwise_cons.mpr ⟨?_, ?_⟩
      · intro a ha
        obtain ⟨i, rfl⟩ := List.mem_ofFn.mp ha
        exact (hp i.castSucc).2
      · rw [List.pairwise_ofFn]
        intro i j hij
        exact p.strictMono (show i.castSucc < j.castSucc from hij)
    have hpair : List.Forall₂ (fun p c => p ≤ c ∧ p.Prime) ps [8,12,15,19,23,28,38,77] := by
      change List.Forall₂ (fun p c => p ≤ c ∧ p.Prime) ps
        (List.ofFn (![8,12,15,19,23,28,38,77] : Fin 8 → ℕ))
      rw [List.forall₂_iff_get]
      refine ⟨by simp [ps], ?_⟩
      intro j hj hj'
      have h8 : j < 8 := by simpa [ps] using hj
      simpa only [ps, List.get_eq_getElem, List.getElem_ofFn] using
        (And.intro (hpCap ⟨j,h8⟩) (hp (Fin.castSucc ⟨j,h8⟩)).1)
    have hdenPs : (ps.map (· - 1)).prod = ∏ i : Fin 8, (p i.castSucc - 1) := by
      rw [show ps = List.ofFn (fun i : Fin 8 => p i.castSucc) by rfl,
        List.map_ofFn, List.prod_ofFn]
      rfl
    have hnumPs : ps.prod = ∏ i : Fin 8, p i.castSucc := List.prod_ofFn
    have hstrip : 3 * (ps.map (· - 1)).prod * (p 8 - 1) < ps.prod * p 8 := by
      rw [hdenPs, hnumPs]
      have hlast : Fin.last 8 = (8 : Fin 9) := by decide
      simpa only [mul_assoc, hlast] using hstrict
    have heq : (∏ i : Fin 9, ∑ j ∈ Finset.range (e i + 1), p i ^ j) =
        3 * (∏ i : Fin 9, p i ^ e i) + 5 := by
      rw [hvalue, hsum, h3]
    rcases screen_lists ps hpair hsort hstrip with ha | ⟨hb, hl⟩
    · exact hexceptional p e p.strictMono hp he ha heq
    · rw [hnumPs, hdenPs] at hb
      exact hfinite p e p.strictMono hp he hpCap hl hb heq
  · exact hmore n hn hnsq (by omega)

end OMA.R_OeisA76495_conjecture_R1_H1_R1_H4_R1_H2_R1
