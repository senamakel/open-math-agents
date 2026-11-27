import OMAStatements.S_oeis_a211419

namespace FactorialRatio

def floorStep (m n : ℕ) : ℤ :=
  ((6*n)/m : ℕ) + ((2*n)/m : ℕ) - ((4*n)/m : ℕ) -
    ((3*n)/m : ℕ) - (n/m : ℕ)

private theorem mul_div_reduce (a n m : ℕ) (hm : 0 < m) :
    (a*n)/m = a*(n/m)+(a*(n%m))/m := by
  have h : a*n = m*(a*(n/m))+a*(n%m) := by
    conv_lhs => rw [← Nat.mod_add_div n m]
    ring
  rw [h, Nat.mul_add_div hm]

theorem floorStep_mod (m n : ℕ) (hm : 0 < m) :
    floorStep m n = floorStep m (n%m) := by
  unfold floorStep
  rw [mul_div_reduce 6 n m hm, mul_div_reduce 2 n m hm, mul_div_reduce 4 n m hm,
    mul_div_reduce 3 n m hm, Nat.div_eq_of_lt (Nat.mod_lt _ hm)]
  push_cast
  ring

private theorem floorStep_reduced (m r : ℕ) (hm : 0 < m) (hr : r < m) :
    floorStep m r = (((6*r)/m+1)/2 : ℕ) - (((4*r)/m+1)/2 : ℕ) := by
  have h₃ : ((6*r)/m)/2=(3*r)/m := by
    rw [Nat.div_div_eq_div_mul]
    rw [show 6*r=2*(3*r) by ring, Nat.mul_comm m 2, Nat.mul_div_mul_left _ _ (by decide : 0 < 2)]
  have h₂ : ((4*r)/m)/2=(2*r)/m := by
    rw [Nat.div_div_eq_div_mul]
    rw [show 4*r=2*(2*r) by ring, Nat.mul_comm m 2, Nat.mul_div_mul_left _ _ (by decide : 0 < 2)]
  unfold floorStep
  rw [← h₃, ← h₂, Nat.div_eq_of_lt hr]
  omega

theorem floorStep_nonneg (m n : ℕ) (hm : 0 < m) : 0 ≤ floorStep m n := by
  rw [floorStep_mod m n hm, floorStep_reduced m _ hm (Nat.mod_lt _ hm)]
  have h : (4*(n%m))/m ≤ (6*(n%m))/m := Nat.div_le_div_right (by omega)
  omega

theorem floorStep_n_add_one (m n : ℕ) (hm : m=3 ∨ 6 ≤ m) (hd : m ∣ n+1) :
    1 ≤ floorStep m n := by
  have hm0 : 0 < m := by omega
  have hr : n%m=m-1 := by
    have h0 := Nat.dvd_iff_mod_eq_zero.mp hd
    rw [Nat.add_mod, Nat.mod_eq_of_lt (by omega : 1 < m)] at h0
    have hb := Nat.mod_lt n hm0
    have ha : 0 < n%m+1 := by omega
    have ht : m∣(n%m+1) := Nat.dvd_iff_mod_eq_zero.mpr h0
    obtain ⟨k,hk⟩ := ht
    have hk1 : k=1 := by
      by_contra h
      have hk2 : 2 ≤ k := by
        by_contra nh
        have hk0 : k=0 := by omega
        simp [hk0] at hk
      have hb2 := Nat.mul_le_mul_left m hk2
      omega
    simp [hk1] at hk
    omega
  rw [floorStep_mod m n hm0, hr, floorStep_reduced m _ hm0 (by omega)]
  rcases hm with rfl | hm
  · norm_num
  · have h6 : (6*(m-1))/m=5 := Nat.div_eq_of_lt_le (by omega) (by omega)
    have h4 : (4*(m-1))/m=3 := Nat.div_eq_of_lt_le (by omega) (by omega)
    norm_num [h6,h4]


end FactorialRatio
namespace FactorialRatio

open Finset

def num (n : ℕ) : ℕ := (6*n).factorial * (2*n).factorial
def den (n : ℕ) : ℕ := (4*n).factorial * (3*n).factorial * n.factorial

theorem valuation_difference (p n b : ℕ) [Fact p.Prime] (hb : Nat.log p (6*n) < b) :
    (padicValNat p (num n) : ℤ) - padicValNat p (den n) =
      ∑ e ∈ Ico 1 b, floorStep (p^e) n := by
  have hl (m : ℕ) (hm : m ≤ 6*n) :
      padicValNat p m.factorial = ∑ e ∈ Ico 1 b, m / p^e :=
    padicValNat_factorial ((Nat.log_mono_right hm).trans_lt hb)
  have hv (a c : ℕ) : padicValNat p (a.factorial*c.factorial) =
      padicValNat p a.factorial+padicValNat p c.factorial :=
    padicValNat.mul (Nat.factorial_ne_zero _) (Nat.factorial_ne_zero _)
  have hn : ((4*n).factorial*(3*n).factorial) ≠ 0 := by positivity
  unfold num den
  rw [padicValNat.mul hn (Nat.factorial_ne_zero n), hv, hv,
    hl (6*n) (by omega), hl (2*n) (by omega), hl (4*n) (by omega),
    hl (3*n) (by omega), hl n (by omega)]
  simp only [floorStep, sum_sub_distrib, sum_add_distrib]
  push_cast
  ring


end FactorialRatio
namespace FactorialRatio

theorem floorStep_pos_regions {m r : ℕ} (hm : 0 < m) (hr : r < m)
    (h : (m ≤ 6*r ∧ 4*r < m) ∨ (m ≤ 2*r ∧ 4*r < 3*m) ∨ 5*m ≤ 6*r) :
    1 ≤ floorStep m r := by
  rw [floorStep_reduced _ _ hm hr]
  rcases h with h | h | h
  · have h₁ : 1 ≤ (6*r)/m := (Nat.le_div_iff_mul_le hm).mpr (by omega)
    have h₀ := Nat.div_eq_of_lt h.2
    omega
  · have h₃ : 3 ≤ (6*r)/m := (Nat.le_div_iff_mul_le hm).mpr (by omega)
    have h₂ : (4*r)/m < 3 := (Nat.div_lt_iff_lt_mul hm).mpr (by omega)
    omega
  · have h₅ : 5 ≤ (6*r)/m := (Nat.le_div_iff_mul_le hm).mpr (by omega)
    have h₄ : (4*r)/m < 4 := (Nat.div_lt_iff_lt_mul hm).mpr (by omega)
    omega

theorem floorStep_four_shift {m n d : ℕ} (hd : d % 2 = 1) (hsmall : 3*d ≤ m)
    (hdiv : m ∣ 4*n+d) : 1 ≤ floorStep m n := by
  have hm : 0 < m := by omega
  let r := n%m
  have hr : r < m := Nat.mod_lt _ hm
  have hmod : (4*r+d) % m = 0 := by
    have hEq : 4*r+d ≡ 4*n+d [MOD m] :=
      ((Nat.ModEq.refl 4).mul (Nat.mod_modEq n m)).add (Nat.ModEq.refl d)
    exact Nat.dvd_iff_mod_eq_zero.mp ((hEq.dvd_iff (dvd_refl m)).mpr hdiv)
  let k := (4*r+d)/m
  have hk : k < 5 := (Nat.div_lt_iff_lt_mul hm).mpr (by omega)
  have he : 4*r+d = m*k := by
    have := Nat.mod_add_div (4*r+d) m
    rw [hmod, zero_add] at this
    exact this.symm
  rw [floorStep_mod m n hm]
  change 1 ≤ floorStep m r
  apply floorStep_pos_regions hm hr
  interval_cases k <;> omega

theorem floorStep_six_remainder {m n d : ℕ} (hd : d % 2 = 1) (hsmall : 2*d < m)
    (hrem : (6*(n%m))%m=d) : 1 ≤ floorStep m n := by
  have hm : 0 < m := by omega
  let r := n%m
  have hr : r < m := Nat.mod_lt _ hm
  let k := (6*r)/m
  have hk : k < 6 := (Nat.div_lt_iff_lt_mul hm).mpr (by omega)
  have he : 6*r = m*k+d := by
    have he0 := Nat.mod_add_div (6*r) m
    rw [show (6*r)%m=d from hrem] at he0
    simpa only [k, Nat.add_comm] using he0.symm
  rw [floorStep_mod m n hm]
  change 1 ≤ floorStep m r
  apply floorStep_pos_regions hm hr
  interval_cases k <;> omega

theorem floorStep_six_shift {m n d : ℕ} (hd : d % 2 = 1) (hsmall : 2*d < m)
    (hdiv : (m : ℤ) ∣ 6*(n : ℤ)-(d : ℤ)) : 1 ≤ floorStep m n := by
  have hInt : (d : ℤ) ≡ ((6*n : ℕ) : ℤ) [ZMOD (m : ℤ)] :=
    Int.modEq_iff_dvd.mpr (by push_cast; exact hdiv)
  have hn : d ≡ 6*n [MOD m] := Int.natCast_modEq_iff.mp hInt
  have hr : 6*(n%m) ≡ 6*n [MOD m] := (Nat.ModEq.refl 6).mul (Nat.mod_modEq n m)
  have h := hr.trans hn.symm
  change (6*(n%m))%m=d%m at h
  rw [Nat.mod_eq_of_lt (by omega : d < m)] at h
  exact floorStep_six_remainder hd hsmall h


end FactorialRatio
namespace FactorialRatio

private def bits (n : ℕ) : ℕ := (Nat.digits 2 n).sum

private theorem bits_double (n : ℕ) : bits (2*n) = bits n := by
  by_cases hn : n=0
  · simp [bits,hn]
  · unfold bits
    rw [Nat.digits_base_mul (by norm_num) (Nat.pos_of_ne_zero hn)]
    simp

private theorem bits_le (n : ℕ) : bits n ≤ n := by
  have h (l : List ℕ) : l.sum ≤ Nat.ofDigits 2 l := by
    induction l with
    | nil => exact Nat.zero_le _
    | cons a l ih =>
      rw [List.sum_cons, Nat.ofDigits_cons]
      omega
  simpa [bits, Nat.ofDigits_digits] using h (Nat.digits 2 n)

theorem valuation_two (n : ℕ) :
    padicValNat 2 (num n) = padicValNat 2 (den n) + bits n := by
  letI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hleg (k : ℕ) : padicValNat 2 k.factorial = k - bits k := by
    simpa [bits] using (sub_one_mul_padicValNat_factorial (p := 2) k)
  have hv (a c : ℕ) : padicValNat 2 (a.factorial*c.factorial) =
      padicValNat 2 a.factorial+padicValNat 2 c.factorial :=
    padicValNat.mul (Nat.factorial_ne_zero _) (Nat.factorial_ne_zero _)
  have hn : ((4*n).factorial*(3*n).factorial) ≠ 0 := by positivity
  unfold num den
  rw [padicValNat.mul hn (Nat.factorial_ne_zero n), hv, hv,
    hleg (6*n), hleg (2*n), hleg (4*n), hleg (3*n), hleg n]
  have h₂ := bits_double n
  have h₄ : bits (4*n) = bits n := by rw [show 4*n=2*(2*n) by ring,bits_double,h₂]
  have h₆ : bits (6*n) = bits (3*n) := by rw [show 6*n=2*(3*n) by ring,bits_double]
  have ha := bits_le (6*n)
  have hb := bits_le (2*n)
  have hc := bits_le (4*n)
  have hd := bits_le (3*n)
  have he := bits_le n
  omega

theorem padicVal_two_succ_le_bits (n : ℕ) : padicValNat 2 (n+1) ≤ bits n := by
  letI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  induction n using Nat.strong_induction_on with
  | h n ih =>
    by_cases hEven : n%2=0
    · rw [padicValNat.eq_zero_of_not_dvd (by omega : ¬ 2 ∣ n+1)]
      exact Nat.zero_le _
    · let m := n/2
      have hm : m < n := by dsimp [m]; omega
      have he : n=1+2*m := by dsimp [m]; omega
      have hv : padicValNat 2 (n+1) = 1+padicValNat 2 (m+1) := by
        rw [show n+1=2*(m+1) by omega,
          padicValNat.mul (by decide : (2 : ℕ) ≠ 0) (by omega), padicValNat_self]
      have hbits : bits n = 1+bits m := by
        unfold bits
        rw [he, Nat.digits_add 2 (by decide) 1 m (by decide) (Or.inl (by decide))]
        rfl
      rw [hv,hbits]
      exact Nat.add_le_add_left (ih m hm) _


end FactorialRatio
namespace FactorialRatio

open Finset

def poweredDivisor (p e x : ℕ) : ℤ := if p^e ∣ x then 1 else 0

theorem sum_poweredDivisor (p x b : ℕ) [Fact p.Prime] (hx : x ≠ 0)
    (hb : padicValNat p x < b) :
    (∑ e ∈ Ico 1 b, poweredDivisor p e x) = (padicValNat p x : ℤ) := by
  have he : (Ico 1 b).filter (fun e => p^e ∣ x) = Ico 1 (padicValNat p x+1) := by
    ext e
    simp only [mem_filter, mem_Ico, padicValNat_dvd_iff_le hx]
    omega
  unfold poweredDivisor
  rw [sum_ite]
  simp [he, Nat.card_Ico]

theorem natural_dvd_by_valuations {a b : ℕ} (ha : a ≠ 0) (hb : b ≠ 0)
    (h : ∀ p : ℕ, p.Prime → padicValNat p a ≤ padicValNat p b) : a ∣ b := by
  apply (Nat.factorization_le_iff_dvd ha hb).mp
  intro p
  by_cases hp : p.Prime
  · simpa only [Nat.factorization_def _ hp] using h p hp
  · rw [Nat.factorization_eq_zero_of_not_prime _ hp, Nat.factorization_eq_zero_of_not_prime _ hp]

theorem single_factor_valuation (p n x c : ℕ) [Fact p.Prime] (hx : x ≠ 0) (hc : c ≠ 0)
    (h : ∀ e : ℕ, 0 < e → poweredDivisor p e x ≤ floorStep (p^e) n + poweredDivisor p e c) :
    padicValNat p x ≤ padicValNat p (num n) - padicValNat p (den n) + padicValNat p c := by
  let b := Nat.log p (6*n) + padicValNat p x + padicValNat p c + 1
  have hlog : Nat.log p (6*n) < b := by dsimp [b]; omega
  have hbx : padicValNat p x < b := by dsimp [b]; omega
  have hbc : padicValNat p c < b := by dsimp [b]; omega
  have hs : (∑ e ∈ Ico 1 b, poweredDivisor p e x) ≤
      ∑ e ∈ Ico 1 b, (floorStep (p^e) n + poweredDivisor p e c) := by
    exact sum_le_sum fun e he => h e (mem_Ico.mp he).1
  rw [sum_add_distrib, sum_poweredDivisor p x b hx hbx, sum_poweredDivisor p c b hc hbc,
    ← valuation_difference p n b hlog] at hs
  omega


end FactorialRatio
namespace FactorialRatio

open Finset

private theorem val_nonneg (p n : ℕ) [Fact p.Prime] :
    padicValNat p (den n) ≤ padicValNat p (num n) := by
  have he := valuation_difference p n (Nat.log p (6*n)+1) (by omega)
  have hp : 0<p := (Fact.out : Nat.Prime p).pos
  have hs : 0 ≤ ∑ e ∈ Ico 1 (Nat.log p (6*n)+1), floorStep (p^e) n :=
    sum_nonneg fun e _ => floorStep_nonneg _ _ (pow_pos hp e)
  omega

private theorem prime_pow_two_le (p e : ℕ) (hp : p.Prime) (he : 0<e) : 2 ≤ p^e :=
  hp.two_le.trans (Nat.le_of_dvd (pow_pos hp.pos e) (dvd_pow_self p he.ne'))

theorem explicit_C (n : ℕ) : den n * (n+1) ∣ 5*num n := by
  apply natural_dvd_by_valuations (by unfold den; positivity) (by unfold num; positivity)
  intro p hp
  letI : Fact p.Prime := ⟨hp⟩
  rw [padicValNat.mul (a := den n) (by unfold den; positivity) (by omega),
    padicValNat.mul (a := 5) (by decide) (by unfold num; positivity)]
  by_cases hp2 : p=2
  · subst p
    have hb := valuation_two n
    have hl := padicVal_two_succ_le_bits n
    omega
  · have hs := single_factor_valuation p n (n+1) 5 (by omega) (by decide) (by
      intro e he
      have hm := prime_pow_two_le p e hp he
      have hn := floorStep_nonneg (p^e) n (by omega)
      unfold poweredDivisor
      split
      · rename_i hd
        by_cases h5 : p^e=5
        · have hf : p^e ∣ 5 := h5 ▸ dvd_refl _
          simp [hf]
          omega
        · have hodd : p^e % 2 = 1 := Nat.odd_iff.mp ((hp.odd_of_ne_two hp2).pow)
          have hpos := floorStep_n_add_one (p^e) n (by omega) hd
          split <;> omega
      · split <;> omega)
    have hx := val_nonneg p n
    omega

theorem explicit_D (n : ℕ) : den n * (4*n+1) ∣ num n := by
  apply natural_dvd_by_valuations (by unfold den; positivity) (by unfold num; positivity)
  intro p hp
  letI : Fact p.Prime := ⟨hp⟩
  rw [padicValNat.mul (a := den n) (by unfold den; positivity) (by omega)]
  have hs := single_factor_valuation p n (4*n+1) 1 (by omega) (by decide) (by
    intro e he
    have hm := prime_pow_two_le p e hp he
    have hf := floorStep_nonneg (p^e) n (by omega)
    unfold poweredDivisor
    split
    · rename_i hd
      have hm3 : 3 ≤ p^e := by
        by_contra hh
        have h2 : p^e=2 := by omega
        rw [h2] at hd
        omega
      have he1 := floorStep_four_shift (m := p^e) (n := n) (d := 1) (by decide) (by omega) hd
      split <;> omega
    · split <;> omega)
  have hx := val_nonneg p n
  simp at hs
  omega

theorem explicit_K (n : ℕ) (hn : 0<n) : den n * (6*n-1) ∣ num n := by
  apply natural_dvd_by_valuations (mul_ne_zero (by unfold den; positivity) (by omega)) (by unfold num; positivity)
  intro p hp
  letI : Fact p.Prime := ⟨hp⟩
  rw [padicValNat.mul (a := den n) (by unfold den; positivity) (by omega)]
  have hs := single_factor_valuation p n (6*n-1) 1 (by omega) (by decide) (by
    intro e he
    have hm := prime_pow_two_le p e hp he
    have hf := floorStep_nonneg (p^e) n (by omega)
    unfold poweredDivisor
    split
    · rename_i hd
      have hm3 : 3 ≤ p^e := by
        by_contra hh
        have h2 : p^e=2 := by omega
        rw [h2] at hd
        omega
      have hdZ : ((p^e : ℕ) : ℤ) ∣ ((6*n-1 : ℕ) : ℤ) := by exact_mod_cast hd
      have he1 := floorStep_six_shift (m := p^e) (n := n) (d := 1) (by decide)
        (by omega) (by simpa [Nat.cast_sub (show 1≤6*n by omega)] using hdZ)
      split <;> omega
    · split <;> omega)
  have hx := val_nonneg p n
  simp at hs
  omega


end FactorialRatio
namespace FactorialRatio

open Finset

theorem uniform_multiplier {ι : Type*} (s : Finset ι) (f : ι → ℕ) (n B : ℕ)
    (hf : ∀ i ∈ s, f i ≠ 0)
    (large : ∀ m > B, ∀ i ∈ s, m ∣ f i → 1 ≤ floorStep m n)
    (unique : ∀ m > B, ∀ i ∈ s, ∀ j ∈ s, m ∣ f i → m ∣ f j → i=j) :
    den n * (∏ i ∈ s, f i) ∣ B.factorial^s.card * num n := by
  classical
  have hprod : (∏ i ∈ s, f i) ≠ 0 := prod_ne_zero_iff.mpr hf
  have hden : den n ≠ 0 := by unfold den; positivity
  have hnum : num n ≠ 0 := by unfold num; positivity
  have hC : B.factorial^s.card ≠ 0 := pow_ne_zero _ (Nat.factorial_ne_zero _)
  apply natural_dvd_by_valuations (mul_ne_zero hden hprod) (mul_ne_zero hC hnum)
  intro p hp
  letI : Fact p.Prime := ⟨hp⟩
  let b := Nat.log p (6*n) + Nat.log p B + (∑ i ∈ s, padicValNat p (f i)) + 1
  have hlog : Nat.log p (6*n) < b := by dsimp [b]; omega
  have hlogB : Nat.log p B < b := by dsimp [b]; omega
  have hb (i : ι) (hi : i ∈ s) : padicValNat p (f i) < b := by
    have hle := single_le_sum (f := fun i => padicValNat p (f i))
      (fun _ _ => Nat.zero_le _) hi
    dsimp [b]
    omega
  have hstep (e : ℕ) :
      (∑ i ∈ s, poweredDivisor p e (f i)) ≤
        floorStep (p^e) n + (s.card : ℤ) * ((B/p^e : ℕ) : ℤ) := by
    have hm : 0 < p^e := pow_pos hp.pos _
    have hfloor := floorStep_nonneg (p^e) n hm
    by_cases hB : p^e ≤ B
    · have hs : (∑ i ∈ s, poweredDivisor p e (f i)) ≤ (s.card : ℤ) := by
        simpa using (sum_le_sum (s := s) (fun i _ => show poweredDivisor p e (f i) ≤ (1 : ℤ) by
          unfold poweredDivisor
          split <;> omega))
      have hq : 1 ≤ ((B/p^e : ℕ) : ℤ) := by
        exact_mod_cast ((Nat.le_div_iff_mul_le hm).mpr (by simpa using hB) : 1 ≤ B/p^e)
      have hmul := mul_le_mul_of_nonneg_left hq (by positivity : (0 : ℤ) ≤ s.card)
      omega
    · by_cases h : ∃ i ∈ s, p^e ∣ f i
      · obtain ⟨i, hi, hdi⟩ := h
        rw [sum_eq_single i]
        · simp only [poweredDivisor, if_pos hdi]
          have hpos := large (p^e) (by omega) i hi hdi
          have hmul : (0 : ℤ) ≤ (s.card : ℤ) * ((B/p^e : ℕ) : ℤ) := by positivity
          omega
        · intro j hj hne
          have hnot : ¬p^e ∣ f j := fun hdj => hne (unique (p^e) (by omega) j hj i hi hdj hdi)
          simp [poweredDivisor,hnot]
        · exact fun hni => (hni hi).elim
      · have hs : (∑ i ∈ s, poweredDivisor p e (f i)) = 0 := by
          exact sum_eq_zero fun i hi => if_neg (fun hd => h ⟨i,hi,hd⟩)
        rw [hs]
        positivity
  have hs := sum_le_sum (s := Ico 1 b) (fun e _ => hstep e)
  rw [sum_comm, sum_add_distrib, ← mul_sum] at hs
  have hpowers : (∑ i ∈ s, ∑ e ∈ Ico 1 b, poweredDivisor p e (f i)) =
      ∑ i ∈ s, (padicValNat p (f i) : ℤ) :=
    sum_congr rfl fun i hi => sum_poweredDivisor p (f i) b (hf i hi) (hb i hi)
  rw [hpowers] at hs
  rw [← valuation_difference p n b hlog] at hs
  have hBsum : (∑ e ∈ Ico 1 b, ((B/p^e : ℕ) : ℤ)) = padicValNat p B.factorial := by
    exact_mod_cast (padicValNat_factorial (p := p) hlogB).symm
  rw [hBsum] at hs
  have hvalprod : padicValNat p (∏ i ∈ s, f i) = ∑ i ∈ s, padicValNat p (f i) := by
    simpa only [Nat.factorization_def _ hp] using
      (Nat.factorization_prod_apply (p := p) hf)
  rw [← Nat.cast_sum, ← hvalprod] at hs
  rw [padicValNat.mul hden hprod, padicValNat.mul hC hnum, padicValNat.pow]
  omega


end FactorialRatio
namespace FactorialRatio

open Finset

theorem floorStep_add_shift {m n d : ℕ} (hd : 0<d) (hm : 6*d ≤ m) (hdiv : m ∣ n+d) :
    1 ≤ floorStep m n := by
  have hm0 : 0 < m := by omega
  let r := n%m
  have hr : r < m := Nat.mod_lt _ hm0
  have hEq : r+d ≡ n+d [MOD m] := (Nat.mod_modEq n m).add (Nat.ModEq.refl d)
  obtain ⟨q,hq⟩ := (hEq.dvd_iff (dvd_refl m)).mpr hdiv
  have hq1 : q=1 := by
    by_contra hnq
    have hq2 : 2≤q := by
      by_contra hnot
      have hzero : q=0 := by omega
      simp [hzero] at hq
      omega
    have hmul := Nat.mul_le_mul_left m hq2
    omega
  rw [hq1, mul_one] at hq
  rw [floorStep_mod m n hm0]
  exact floorStep_pos_regions hm0 hr (Or.inr (Or.inr (by omega)))

theorem uniform_signed (r n B : ℕ) (g : ℕ → ℤ)
    (hf : ∀ i < r, g i ≠ 0)
    (large : ∀ m > B, ∀ i < r, (m : ℤ) ∣ g i → 1 ≤ floorStep m n)
    (sep : ∀ i < r, ∀ j < r, -(B : ℤ) ≤ g i - g j ∧ g i - g j ≤ B)
    (inj : Function.Injective g) :
    (den n : ℤ) * (∏ i ∈ range r, g i) ∣ ((B.factorial^r : ℕ) : ℤ) * (num n : ℤ) := by
  have h := uniform_multiplier (range r) (fun i => (g i).natAbs) n B
    (fun i hi => Int.natAbs_ne_zero.mpr (hf i (mem_range.mp hi)))
    (fun m hm i hi hd => large m hm i (mem_range.mp hi) (Int.natAbs_dvd_natAbs.mp (by simpa using hd)))
    (by
      intro m hm i hi j hj hdi hdj
      have hi' : (m : ℤ) ∣ g i := Int.natAbs_dvd_natAbs.mp (by simpa using hdi)
      have hj' : (m : ℤ) ∣ g j := Int.natAbs_dvd_natAbs.mp (by simpa using hdj)
      have hdiff := dvd_sub hi' hj'
      have hh := sep i (mem_range.mp hi) j (mem_range.mp hj)
      have hz : g i-g j=0 := by
        by_cases he : 0≤g i-g j
        · exact Int.eq_zero_of_dvd_of_nonneg_of_lt he (by omega) hdiff
        · have hh' := Int.eq_zero_of_dvd_of_nonneg_of_lt
            (show 0≤ -(g i-g j) by omega) (show -(g i-g j)<(m : ℤ) by omega)
            (dvd_neg.mpr hdiff)
          omega
      exact inj (sub_eq_zero.mp hz))
  have hp : (∏ i ∈ range r, g i).natAbs = ∏ i ∈ range r, (g i).natAbs :=
    map_prod Int.natAbsHom g (range r)
  apply Int.natAbs_dvd_natAbs.mp
  simpa [Int.natAbs_mul, hp] using h

namespace Families

def bound (r : ℕ) : ℕ := 12*(r+1)

theorem C (r n : ℕ) :
    (den n : ℤ) * (∏ i ∈ range r, ((n : ℤ)+i+1)) ∣
      (((bound r).factorial^r : ℕ) : ℤ)*(num n : ℤ) := by
  apply uniform_signed r n (bound r) (fun i => (n : ℤ)+i+1)
  · intro i hi
    omega
  · intro m hm i hi hd
    apply floorStep_add_shift (d := i+1) (by omega) (by unfold bound at hm; omega)
    exact_mod_cast hd
  · intro i hi j hj
    unfold bound
    omega
  · intro a b h
    dsimp at h
    omega

theorem D (r n : ℕ) :
    (den n : ℤ) * (∏ i ∈ range r, (4*(n : ℤ)+2*i+1)) ∣
      (((bound r).factorial^r : ℕ) : ℤ)*(num n : ℤ) := by
  apply uniform_signed r n (bound r) (fun i => 4*(n : ℤ)+2*i+1)
  · intro i hi
    omega
  · intro m hm i hi hd
    have hd' : m ∣ 4*n+(2*i+1) := by
      exact_mod_cast (show (m : ℤ) ∣ 4*(n : ℤ)+(2*(i : ℤ)+1) from by
        convert hd using 1 <;> ring)
    exact floorStep_four_shift (d := 2*i+1) (by omega) (by unfold bound at hm; omega) hd'
  · intro i hi j hj
    unfold bound
    omega
  · intro a b h
    dsimp at h
    omega

theorem K (r n : ℕ) :
    (den n : ℤ) * (∏ i ∈ range r, (6*(n : ℤ)-(2*i+1))) ∣
      (((bound r).factorial^r : ℕ) : ℤ)*(num n : ℤ) := by
  apply uniform_signed r n (bound r) (fun i => 6*(n : ℤ)-(2*i+1))
  · intro i hi
    omega
  · intro m hm i hi hd
    exact floorStep_six_shift (d := 2*i+1) (by omega) (by unfold bound at hm; omega)
      (by push_cast; exact hd)
  · intro i hi j hj
    unfold bound
    omega
  · intro a b h
    dsimp at h
    omega

end Families
end FactorialRatio

theorem OMA.solution : type_of% @OMA.S_oeis_a211419.main := by
  open OMA.S_oeis_a211419 FactorialRatio in
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro n
    have h : ((den n*(n+1) : ℕ) : ℤ) ∣ ((5*num n : ℕ) : ℤ) := by
      exact_mod_cast explicit_C n
    simpa [den,num,denominator,numerator,mul_assoc] using h
  · intro n
    have h : ((den n*(4*n+1) : ℕ) : ℤ) ∣ (num n : ℤ) := by
      exact_mod_cast explicit_D n
    simpa [den,num,denominator,numerator,mul_assoc] using h
  · intro n
    by_cases h : n=0
    · subst n
      norm_num [denominator,numerator]
    · have hpos : 0<n := by omega
      have hz : ((den n*(6*n-1) : ℕ) : ℤ) ∣ (num n : ℤ) := by
        exact_mod_cast explicit_K n hpos
      simpa [Nat.cast_sub (show 1≤6*n by omega),den,num,denominator,numerator,mul_assoc] using hz
  · intro r _
    refine ⟨((Families.bound r).factorial^r : ℕ), by positivity, ?_⟩
    intro n
    simpa [den,num,numerator,denominator,factorsC] using Families.C r n
  · intro r _
    refine ⟨((Families.bound r).factorial^r : ℕ), by positivity, ?_⟩
    intro n
    simpa [den,num,numerator,denominator,factorsD] using Families.D r n
  · intro r _
    refine ⟨((Families.bound r).factorial^r : ℕ), by positivity, ?_⟩
    intro n
    simpa [den,num,numerator,denominator,factorsK] using Families.K r n
