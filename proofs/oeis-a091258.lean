import OMAStatements.S_oeis_a091258

namespace SigmaRange

open scoped ArithmeticFunction.sigma
open Finset

def quad (x : ℚ) : ℚ := x ^ 2 + x + 1

private theorem geomIdentity (x : ℚ) (n : ℕ) :
    (∑ i ∈ range n, x ^ i) * (x - 1) = x ^ n - 1 := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [sum_range_succ, add_mul, ih, pow_succ]
    ring

theorem sigma_prime_power_quotient (p e : ℕ) (hp : p.Prime) :
    (σ 3 (p ^ e) : ℚ) / (σ 1 (p ^ e) : ℚ) =
      quad ((p : ℚ) ^ (e + 1)) / quad (p : ℚ) := by
  rw [ArithmeticFunction.sigma_apply_prime_pow hp, ArithmeticFunction.sigma_one_apply_prime_pow hp]
  push_cast
  simp only [pow_mul]
  have hpow (i : ℕ) : ((p : ℚ) ^ i) ^ 3 = ((p : ℚ) ^ 3) ^ i := by
    rw [← pow_mul, ← pow_mul, Nat.mul_comm]
  simp_rw [hpow]
  let x : ℚ := p
  change (∑ i ∈ range (e + 1), (x ^ 3) ^ i) / (∑ i ∈ range (e + 1), x ^ i) =
    quad (x ^ (e + 1)) / quad x
  have hx : 1 < x := by
    dsimp [x]
    exact_mod_cast hp.one_lt
  have hden : 0 < ∑ i ∈ range (e + 1), x ^ i :=
    sum_pos (fun i _ => pow_pos (by linarith) i) (by simp)
  have hquad : 0 < quad x := by
    unfold quad
    nlinarith
  apply (div_eq_div_iff hden.ne' hquad.ne').2
  apply mul_right_cancel₀ (show x - 1 ≠ 0 by linarith)
  calc
    (∑ i ∈ range (e + 1), (x ^ 3) ^ i) * quad x * (x - 1) =
        (∑ i ∈ range (e + 1), (x ^ 3) ^ i) * (x ^ 3 - 1) := by
      rw [mul_assoc]
      congr 1
      unfold quad
      ring
    _ = (x ^ (e + 1)) ^ 3 - 1 := by
      rw [geomIdentity, ← pow_mul, ← pow_mul, Nat.mul_comm]
    _ = quad (x ^ (e + 1)) * (x ^ (e + 1) - 1) := by
      unfold quad
      ring
    _ = quad (x ^ (e + 1)) * (∑ i ∈ range (e + 1), x ^ i) * (x - 1) := by
      rw [mul_assoc, geomIdentity]

theorem sigma_quotient_factorization (n : ℕ) (hn : n ≠ 0) :
    (σ 3 n : ℚ) / (σ 1 n : ℚ) =
      ∏ p ∈ n.primeFactors, quad ((p : ℚ) ^ (n.factorization p + 1)) / quad (p : ℚ) := by
  rw [(ArithmeticFunction.isMultiplicative_sigma (k := 3)).multiplicative_factorization _ hn,
    (ArithmeticFunction.isMultiplicative_sigma (k := 1)).multiplicative_factorization _ hn]
  simp only [Finsupp.prod, Nat.support_factorization]
  push_cast
  rw [← Finset.prod_div_distrib]
  apply Finset.prod_congr rfl
  intro p hp
  exact sigma_prime_power_quotient p (n.factorization p) (Nat.prime_of_mem_primeFactors hp)


end SigmaRange

/-!
Forward direction ingredient for OEIS A091258.  For a prime power `p^e`, the
local divisor-sum ratio is `Q (p^(e+1)) / Q p`, where `Q x = x^2 + x + 1`.
Every prime divisor of `Q p`, except possibly 3, is 1 modulo 3; moreover, 3
occurs in both local numerator and denominator exactly when `p = 1 mod 3`.
-/

namespace OMA.SigmaRange

def Q (x : ℕ) : ℕ := x ^ 2 + x + 1

def localFactor (p e : ℕ) : ℚ := (Q (p ^ (e + 1)) : ℚ) / Q p

lemma Q_mod_three (x : ℕ) : Q x % 3 = 0 ↔ x % 3 = 1 := by
  have hx : x % 3 < 3 := Nat.mod_lt _ (by norm_num)
  interval_cases h : x % 3 <;> norm_num [Q, Nat.add_mod, Nat.mul_mod, Nat.pow_mod, h]

lemma Q_power_mod_three (p k : ℕ) (hp : p % 3 = 1) : Q (p ^ k) % 3 = 0 := by
  apply (Q_mod_three _).2
  rw [Nat.pow_mod]
  simp [hp]

/-- If a prime other than 3 divides `x²+x+1`, then it is 1 modulo 3. -/
lemma prime_dvd_Q_mod_three (r x : ℕ) (hr : Nat.Prime r)
    (hxr : r ∣ Q x) (hr3 : r ≠ 3) : r % 3 = 1 := by
  letI : Fact (Nat.Prime r) := ⟨hr⟩
  letI : NeZero r := ⟨hr.ne_zero⟩
  have hpoly : (x : ZMod r) ^ 2 + x + 1 = 0 := by
    have hzero : (Q x : ZMod r) = 0 :=
      (ZMod.natCast_eq_zero_iff (Q x) r).2 hxr
    simpa [Q] using hzero
  have hxne : (x : ZMod r) ≠ 0 := by
    intro hx
    rw [hx] at hpoly
    norm_num at hpoly
  let u : (ZMod r)ˣ := Units.mk0 (x : ZMod r) hxne
  have hu3 : u ^ 3 = 1 := by
    apply Units.ext
    change (x : ZMod r) ^ 3 = 1
    calc
      (x : ZMod r) ^ 3 = (x : ZMod r) * ((x : ZMod r) ^ 2 + x + 1) -
          ((x : ZMod r) ^ 2 + x + 1) + 1 := by ring
      _ = 1 := by rw [hpoly]; ring
  have hu1 : u ≠ 1 := by
    intro h
    have hx1 : (x : ZMod r) = 1 := by
      simpa [u] using congrArg (fun z : (ZMod r)ˣ => (z : ZMod r)) h
    rw [hx1] at hpoly
    have h3zero : (3 : ZMod r) = 0 := by
      norm_num [pow_two] at hpoly
      exact hpoly
    have hdiv : r ∣ 3 := (ZMod.natCast_eq_zero_iff 3 r).1 h3zero
    have hr3' : r = 3 := by
      rcases (Nat.dvd_prime (by norm_num : Nat.Prime 3)).mp hdiv with h | h
      · exact (hr.ne_one h).elim
      · exact h
    exact hr3 hr3'
  have horder : orderOf u = 3 := by
    refine (orderOf_eq_iff (x := u) (n := 3) (by norm_num)).2 ?_
    refine ⟨hu3, ?_⟩
    intro m hm hmpos
    interval_cases m
    · simpa using hu1
    · intro hsq
      have hmul := congrArg (fun z : (ZMod r)ˣ => z * u) hsq
      have : u ^ 3 = u := by simpa [pow_succ] using hmul
      exact hu1 (this.symm.trans hu3)
  have hdiv : 3 ∣ r - 1 := by
    have hcard := orderOf_dvd_natCard u
    rw [Nat.card_eq_fintype_card, ZMod.card_units r] at hcard
    simpa [horder] using hcard
  have hrge : 3 < r := by
    by_contra h
    have hle : r ≤ 3 := by omega
    have hr2 : 2 ≤ r := hr.two_le
    rcases (show r = 2 ∨ r = 3 by omega) with h | h
    · subst r
      norm_num at hdiv
    · exact hr3 h
  have hmod : r % 3 ≠ 0 := by
    intro hzero
    have : 3 ∣ r := Nat.dvd_of_mod_eq_zero hzero
    rcases (Nat.dvd_prime hr).1 this with h | h
    · omega
    · exact hr3 h.symm
  omega

/-- The raw local numerator and denominator share a factor of 3 whenever
3 divides the denominator. This is the local cancellation needed for the
rational denominator statement. -/

lemma Q_pos (x : ℕ) : 0 < Q x := by
  dsimp [Q]
  omega

lemma Q_div_three_mod_three (x : ℕ) (hx : x % 3 = 1) : (Q x / 3) % 3 = 1 := by
  have hx9 : x % 9 = 1 ∨ x % 9 = 4 ∨ x % 9 = 7 := by omega
  rcases hx9 with h | h | h
  · let k := x / 9
    have heq : x = 9 * k + 1 := by dsimp [k]; omega
    have hf : Q x = 3 * (27 * k ^ 2 + 9 * k + 1) := by rw [heq]; dsimp [Q]; ring
    rw [hf, Nat.mul_div_cancel_left _ (by norm_num)]
    simp [Nat.add_mod, Nat.mul_mod]
  · let k := x / 9
    have heq : x = 9 * k + 4 := by dsimp [k]; omega
    have hf : Q x = 3 * (27 * k ^ 2 + 27 * k + 7) := by rw [heq]; dsimp [Q]; ring
    rw [hf, Nat.mul_div_cancel_left _ (by norm_num)]
    simp [Nat.add_mod, Nat.mul_mod]
  · let k := x / 9
    have heq : x = 9 * k + 7 := by dsimp [k]; omega
    have hf : Q x = 3 * (27 * k ^ 2 + 45 * k + 19) := by rw [heq]; dsimp [Q]; ring
    rw [hf, Nat.mul_div_cancel_left _ (by norm_num)]
    simp [Nat.add_mod, Nat.mul_mod]

lemma localFactor_three_common (p e : ℕ) (hp : 3 ∣ Q p) :
    3 ∣ Q (p ^ (e + 1)) := by
  have hpmod : p % 3 = 1 := by
    apply (Q_mod_three p).1
    exact Nat.mod_eq_zero_of_dvd hp
  exact Nat.dvd_of_mod_eq_zero (Q_power_mod_three p (e + 1) hpmod)

lemma localFactor_den_dvd (p e : ℕ) : (localFactor p e).den ∣ Q p := by
  change ((Q (p ^ (e + 1)) : ℚ) / Q p).den ∣ Q p
  have hd : ((Q (p ^ (e + 1)) : ℚ) / Q p).den ∣ Q p := by
    rw [Rat.natCast_div_eq_divInt]
    exact_mod_cast (Rat.den_dvd (Q (p ^ (e + 1)) : ℤ) (Q p : ℤ))
  exact hd

lemma localFactor_three_not_dvd (p e : ℕ) : ¬ 3 ∣ (localFactor p e).den := by
  intro hden
  have hpmod : p % 3 = 1 := by
    apply (Q_mod_three p).1
    exact Nat.mod_eq_zero_of_dvd (Nat.dvd_trans hden (localFactor_den_dvd p e))
  have hBp : 3 ∣ Q p := Nat.dvd_of_mod_eq_zero ((Q_mod_three p).2 hpmod)
  have hAp : 3 ∣ Q (p ^ (e + 1)) := localFactor_three_common p e hBp
  have hBquot : ¬ 3 ∣ Q p / 3 := by
    intro hd
    have hmod := Q_div_three_mod_three p hpmod
    have hmod0 : (Q p / 3) % 3 = 0 := Nat.mod_eq_zero_of_dvd hd
    omega
  have hratio : localFactor p e =
      ((Q (p ^ (e + 1)) / 3 : ℕ) : ℚ) / ((Q p / 3 : ℕ) : ℚ) := by
    dsimp [localFactor]
    have hA : 3 * (Q (p ^ (e + 1)) / 3) = Q (p ^ (e + 1)) := Nat.mul_div_cancel' hAp
    have hB : 3 * (Q p / 3) = Q p := Nat.mul_div_cancel' hBp
    have hB0 : ((Q p / 3 : ℕ) : ℚ) ≠ 0 := by
      have hp1 : 1 ≤ p := by omega
      have hq3 : 3 ≤ Q p := by dsimp [Q]; nlinarith
      have hpos : 0 < Q p / 3 := Nat.div_pos hq3 (by norm_num)
      exact_mod_cast (Nat.ne_of_gt hpos)
    have hA' : (Q (p ^ (e + 1)) : ℚ) = 3 * (Q (p ^ (e + 1)) / 3 : ℕ) := by
      exact_mod_cast hA.symm
    have hB' : (Q p : ℚ) = 3 * (Q p / 3 : ℕ) := by exact_mod_cast hB.symm
    rw [hA', hB']
    field_simp [hB0]
  have hdivAlt : (((Q (p ^ (e + 1)) / 3 : ℕ) : ℚ) / ((Q p / 3 : ℕ) : ℚ)).den ∣ Q p / 3 := by
    rw [Rat.natCast_div_eq_divInt]
    exact_mod_cast (Rat.den_dvd (Q (p ^ (e + 1)) / 3 : ℤ) (Q p / 3 : ℤ))
  have hdenAlt : 3 ∣ (((Q (p ^ (e + 1)) / 3 : ℕ) : ℚ) / ((Q p / 3 : ℕ) : ℚ)).den := by
    rwa [← hratio]
  exact hBquot (Nat.dvd_trans hdenAlt hdivAlt)

lemma localFactor_prime_divisor (p e r : ℕ) (hr : Nat.Prime r)
    (hdiv : r ∣ (localFactor p e).den) : r % 3 = 1 := by
  have hQ : r ∣ Q p := Nat.dvd_trans hdiv (localFactor_den_dvd p e)
  have hr3 : r ≠ 3 := by
    intro h
    subst r
    exact localFactor_three_not_dvd p e hdiv
  exact prime_dvd_Q_mod_three r p hr hQ hr3

lemma prod_den_dvd_prod_local_den {s : Finset ℕ} (f : ℕ → ℚ) :
    (s.prod f).den ∣ s.prod (fun p => (f p).den) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s has ih =>
      simp only [Finset.prod_insert has]
      exact (Rat.mul_den_dvd _ _).trans (Nat.mul_dvd_mul_left _ ih)

lemma prime_dvd_prod_exists {s : Finset ℕ} {r : ℕ} (hr : Nat.Prime r)
    (f : ℕ → ℕ) (h : r ∣ s.prod f) : ∃ p ∈ s, r ∣ f p := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      simp at h
      exact False.elim (hr.ne_one h)
  | @insert a s has ih =>
      simp only [Finset.prod_insert has] at h
      rcases (Nat.Prime.dvd_mul hr).1 h with h₁ | h₂
      · exact ⟨a, Finset.mem_insert_self _ _, h₁⟩
      · obtain ⟨p, hp, hpr⟩ := ih h₂
        exact ⟨p, Finset.mem_insert_of_mem hp, hpr⟩

/-- Every prime dividing the denominator of a finite product of the local
prime-power ratios is congruent to 1 modulo 3. -/
theorem prod_localFactor_den_prime_mod_three
    (s : Finset ℕ) (hs : ∀ p ∈ s, Nat.Prime p) (e : ℕ → ℕ)
    (r : ℕ) (hr : Nat.Prime r)
    (hdiv : r ∣ (s.prod (fun p => localFactor p (e p))).den) : r % 3 = 1 := by
  have hprod : r ∣ s.prod (fun p => (localFactor p (e p)).den) :=
    Nat.dvd_trans hdiv (prod_den_dvd_prod_local_den _)
  obtain ⟨p, hp, hlocal⟩ := prime_dvd_prod_exists hr _ hprod
  exact localFactor_prime_divisor p (e p) r hr hlocal


end OMA.SigmaRange

namespace SigmaRange

def Q (x : ℕ) : ℕ := x ^ 2 + x + 1

/-- A root of `X² + X + 1` modulo a prime other than three has order three. -/
theorem not_dvd_pow_sub_one_of_not_dvd_three (p q t : ℕ) (hq : q.Prime)
    (hq3 : q % 3 = 1) (hQ : q ∣ Q p) (ht : 0 < t) (ht3 : ¬ 3 ∣ t) :
    ¬ q ∣ p ^ t - 1 := by
  letI : Fact q.Prime := ⟨hq⟩
  let a : ZMod q := p
  have hQz : (Q p : ZMod q) = 0 := (ZMod.natCast_eq_zero_iff _ _).2 hQ
  have hp0 : p ≠ 0 := by
    intro hp
    subst p
    norm_num [Q] at hQ
    exact hq.ne_one hQ
  have hpoly : a ^ 2 + a + 1 = 0 := by
    simpa [a, Q] using hQz
  have hcube : a ^ 3 = 1 := by
    calc
      a ^ 3 = a ^ 3 - 1 + 1 := by ring
      _ = (a - 1) * (a ^ 2 + a + 1) + 1 := by ring
      _ = 1 := by rw [hpoly]; ring
  have hqne3 : q ≠ 3 := by intro h; subst q; norm_num at hq3
  have ha1 : a ≠ 1 := by
    intro ha
    have hthree : (3 : ZMod q) = 0 := by
      norm_num [ha] at hpoly ⊢
      exact hpoly
    have hdiv : q ∣ 3 := (ZMod.natCast_eq_zero_iff _ _).mp hthree
    rcases (Nat.dvd_prime Nat.prime_three).mp hdiv with h | h
    · exact hq.ne_one h
    · exact hqne3 h
  have ho : orderOf a = 3 := by
    have hodvd : orderOf a ∣ 3 := orderOf_dvd_iff_pow_eq_one.mpr hcube
    rcases (Nat.dvd_prime Nat.prime_three).mp hodvd with h | h
    · have heq : a = 1 := by
        have hp := pow_orderOf_eq_one a
        simpa [h] using hp
      exact (ha1 heq).elim
    · exact h
  intro hdiv
  have hpPow : 0 < p ^ t := Nat.pow_pos (Nat.pos_of_ne_zero hp0)
  have hcast : ((p ^ t : ℕ) : ZMod q) = 1 := by
    have hz : ((p ^ t - 1 : ℕ) : ZMod q) = 0 :=
      (ZMod.natCast_eq_zero_iff _ _).2 hdiv
    have hsub : p ^ t - 1 + 1 = p ^ t := Nat.sub_add_cancel (by omega)
    rw [← hsub, Nat.cast_add, hz]
    simp
  have hpow : a ^ t = 1 := by simpa [a, Nat.cast_pow] using hcast
  have horder : orderOf a ∣ t := orderOf_dvd_iff_pow_eq_one.mpr hpow
  rw [ho] at horder
  exact ht3 horder

/-- The LTE step used after factoring `Q (p ^ t)` through `p ^ (3 * t) - 1`.
The remaining work in the application is to identify the two factors and show
that `q` does not divide `p ^ t - 1`. -/
theorem padicVal_cube_pow (p q t : ℕ) [Fact q.Prime] (hqOdd : Odd q)
    (hp3 : 1 < p ^ 3) (hqdiv : q ∣ p ^ 3 - 1) (hqnot : ¬ q ∣ p ^ 3)
    (ht : t ≠ 0) :
    padicValNat q ((p ^ 3) ^ t - 1) = padicValNat q (p ^ 3 - 1) + padicValNat q t := by
  simpa only [one_pow] using
    (padicValNat.pow_sub_pow hqOdd hp3 hqdiv hqnot ht)

/-- LTE for `X² + X + 1` at primes whose residue class of `p` has order three. -/
theorem padicVal_Q_pow (p q t : ℕ) (hq : q.Prime) (hq3 : q % 3 = 1)
    (hQ : q ∣ Q p) (ht : 0 < t) (ht3 : ¬ 3 ∣ t) :
    padicValNat q (Q (p ^ t)) = padicValNat q (Q p) + padicValNat q t := by
  letI : Fact q.Prime := ⟨hq⟩
  have hodd : Odd q := hq.odd_of_ne_two (by omega)
  have hp0 : p ≠ 0 := by
    intro hp
    subst p
    norm_num [Q] at hQ
    exact hq.ne_one hQ
  have hpne1 : p ≠ 1 := by
    intro hp
    subst p
    have hq3d : q ∣ 3 := by simpa [Q] using hQ
    have hqne3 : q ≠ 3 := by intro heq; subst q; norm_num at hq3
    rcases (Nat.dvd_prime Nat.prime_three).mp hq3d with heq | heq
    · exact hq.ne_one heq
    · exact hqne3 heq
  have hp2 : 1 < p := by omega
  have hfac (x : ℕ) (hx : 1 ≤ x) : (x - 1) * Q x = x ^ 3 - 1 := by
    have hx3 : 1 ≤ x ^ 3 := Nat.one_le_pow 3 x hx
    have hInt : (((x - 1) * Q x : ℕ) : ℤ) = ((x ^ 3 - 1 : ℕ) : ℤ) := by
      rw [Nat.cast_mul, Nat.cast_sub hx, Nat.cast_sub hx3]
      simp only [Nat.cast_one]
      dsimp [Q]
      ring
    exact_mod_cast hInt
  have hbaseFac : (p - 1) * Q p = p ^ 3 - 1 := hfac p (by omega)
  have hpPowPos : 0 < p ^ t := Nat.pow_pos (Nat.pos_of_ne_zero hp0)
  have hpowFac : (p ^ t - 1) * Q (p ^ t) = p ^ (3 * t) - 1 := by
    simpa [pow_mul, Nat.mul_comm] using hfac (p ^ t) (by omega)
  have hqdiv : q ∣ p ^ 3 - 1 := by
    rw [← hbaseFac]
    exact dvd_mul_of_dvd_right hQ _
  have hpnot : ¬ q ∣ p ^ 3 := by
    intro h
    have hp : q ∣ p := hq.dvd_of_dvd_pow h
    have hp2d : q ∣ p ^ 2 := dvd_pow hp (by norm_num)
    have hsum : q ∣ p ^ 2 + p := dvd_add hp2d hp
    have h1 : q ∣ 1 := by
      have hd : q ∣ (p ^ 2 + p + 1) - (p ^ 2 + p) := by
        apply Nat.dvd_sub hQ hsum
      simpa [Q] using hd
    exact hq.not_dvd_one h1
  have hLTE := padicVal_cube_pow p q t hodd (Nat.one_lt_pow (by norm_num) hp2)
    hqdiv hpnot ht.ne'
  have havoid := not_dvd_pow_sub_one_of_not_dvd_three p q t hq hq3 hQ ht ht3
  have hden0 : padicValNat q (p ^ t - 1) = 0 :=
    padicValNat.eq_zero_of_not_dvd havoid
  have hdenNe : p ^ t - 1 ≠ 0 := by
    intro hz
    exact havoid (hz ▸ dvd_zero q)
  have hpn : ¬ q ∣ p - 1 := by
    have := not_dvd_pow_sub_one_of_not_dvd_three p q 1 hq hq3 hQ (by omega) (by norm_num)
    simpa using this
  have hbase0 : padicValNat q (p - 1) = 0 :=
    padicValNat.eq_zero_of_not_dvd hpn
  have hbaseNe : p - 1 ≠ 0 := by
    intro hz
    exact hpn (hz ▸ dvd_zero q)
  have hvalBase : padicValNat q (p ^ 3 - 1) = padicValNat q (Q p) := by
    rw [← hbaseFac, padicValNat.mul hbaseNe (by simp [Q]), hbase0, zero_add]
  have hpowrewrite : (p ^ 3) ^ t = p ^ (3 * t) := by rw [pow_mul]
  have hvalPow : padicValNat q (p ^ (3 * t) - 1) =
      padicValNat q (p ^ 3 - 1) + padicValNat q t := by
    simpa [hpowrewrite] using hLTE
  have hfacVal := congrArg (padicValNat q) hpowFac
  rw [← hfacVal, padicValNat.mul hdenNe (by simp [Q])] at hvalPow
  rw [hden0, zero_add, hvalBase] at hvalPow
  exact hvalPow

end SigmaRange

namespace SigmaRange

def cubicCyclotomic (x : ℕ) : ℕ := x ^ 2 + x + 1

def cubicCyclotomicZ (x : ℤ) : ℤ := x ^ 2 + x + 1

def cubicCyclotomicZMod (p : ℕ) (x : ZMod p) : ZMod p := x ^ 2 + x + 1

/-- A nontrivial cube root of unity gives a root of `X² + X + 1`. -/
theorem cubic_root_of_order_three {p : ℕ} (hp : Nat.Prime p) (x : (ZMod p)ˣ)
    (hx : orderOf x = 3) : (x : ZMod p) ^ 2 + (x : ZMod p) + 1 = 0 := by
  have hcube : (x : ZMod p) ^ 3 = 1 := by
    have h : x ^ 3 = 1 := by
      apply orderOf_dvd_iff_pow_eq_one.mp
      simpa [hx]
    simpa using congrArg (fun u : (ZMod p)ˣ => (u : ZMod p)) h
  letI : Fact (Nat.Prime p) := ⟨hp⟩
  have hne : (x : ZMod p) ≠ 1 := by
    intro h
    have hu : x = 1 := Units.ext h
    rw [hu, orderOf_one] at hx
    omega
  have hfact : ((x : ZMod p) - 1) * ((x : ZMod p) ^ 2 + (x : ZMod p) + 1) = 0 := by
    calc
      _ = (x : ZMod p) ^ 3 - 1 := by ring
      _ = 0 := by rw [hcube]; ring
  rcases mul_eq_zero.mp hfact with h | h
  · exact False.elim (hne (sub_eq_zero.mp h))
  · exact h

/-- Every prime with `3 ∣ p - 1` has a nontrivial cube root in its residue field. -/
theorem exists_cubic_root_mod_prime {p : ℕ} (hp : Nat.Prime p) (h3 : 3 ∣ p - 1) :
    ∃ x : ZMod p, x ^ 2 + x + 1 = 0 := by
  letI : Fact (Nat.Prime p) := ⟨hp⟩
  letI := ZMod.isCyclic_units_prime hp
  obtain ⟨g, hg⟩ := @IsCyclic.exists_ofOrder_eq_natCard ((ZMod p)ˣ) _ _
  have hcard : orderOf g = p - 1 := by
    simpa [Nat.card_eq_fintype_card, ZMod.card_units, Nat.totient_prime hp] using hg
  let n := (p - 1) / 3
  have hn : 3 * n = p - 1 := Nat.mul_div_cancel' h3
  have hpow : orderOf (g ^ n) = 3 := by
    rw [orderOf_pow, hcard]
    have hd : n ∣ p - 1 := ⟨3, by omega⟩
    have hgcd : Nat.gcd (p - 1) n = n := Nat.gcd_eq_right hd
    rw [hgcd]
    have hnpos : 0 < n := by
      dsimp [n]
      have hp2 := hp.two_le
      have hle : 3 ≤ p - 1 := Nat.le_of_dvd (by omega) h3
      omega
    rw [← hn]
    simpa [Nat.mul_comm] using Nat.mul_div_cancel_left 3 hnpos
  have hroot := cubic_root_of_order_three hp (g ^ n) hpow
  exact ⟨(g ^ n : (ZMod p)ˣ), hroot⟩

/-- Choose the last base-`q` digit which cancels the next quotient of the
cyclotomic value, provided the derivative is nonzero modulo `q`. -/
theorem choose_lift_digit {q : ℕ} (hq : Nat.Prime q) (r : ℕ) (t : ZMod q)
    (hderiv : (2 * (r : ZMod q) + 1) ≠ 0) :
    ∃ c : ZMod q, t + c * (2 * (r : ZMod q) + 1) = 0 := by
  letI : Fact (Nat.Prime q) := ⟨hq⟩
  let d : ZMod q := 2 * (r : ZMod q) + 1
  refine ⟨-t * d⁻¹, ?_⟩
  have hd : d ≠ 0 := hderiv
  change t + (-t * d⁻¹) * d = 0
  calc
    t + (-t * d⁻¹) * d = t + -t * (d⁻¹ * d) := by ring
    _ = t + -t := by
      have hi : d⁻¹ * d = 1 := inv_mul_cancel₀ hd
      rw [hi]
      ring
    _ = 0 := by ring

/-- Natural-number form of `choose_lift_digit`, useful for turning the digit
choice into a divisibility statement about the quotient. -/
theorem choose_lift_digit_nat {q : ℕ} (hq : Nat.Prime q) (r t : ℕ)
    (hderiv : (2 * (r : ZMod q) + 1) ≠ 0) :
    ∃ c < q, q ∣ t + c * (2 * r + 1) := by
  letI : NeZero q := ⟨hq.ne_zero⟩
  obtain ⟨z, hz⟩ := choose_lift_digit hq r (t : ZMod q) hderiv
  refine ⟨z.val, z.val_lt, ?_⟩
  rw [← ZMod.natCast_eq_zero_iff]
  push_cast
  simpa using hz

theorem cubic_root_lift {q r a : ℕ} (hq : q.Prime) (hq3 : q ≠ 3)
    (ha : 0 < a) (hr : q ^ a ∣ cubicCyclotomic r) :
    ∃ v : ℕ, q ^ (a + 1) ∣ cubicCyclotomic v := by
  have hrq : q ∣ cubicCyclotomic r :=
    (dvd_pow_self q (by omega : a ≠ 0)).trans hr
  have hzero : (r : ZMod q) ^ 2 + (r : ZMod q) + 1 = 0 := by
    exact_mod_cast (ZMod.natCast_eq_zero_iff (cubicCyclotomic r) q).mpr hrq
  have hderiv : (2 * (r : ZMod q) + 1) ≠ 0 := by
    intro h
    have h3 : (3 : ZMod q) = 0 := by
      linear_combination (4 : ZMod q) * hzero -
        (2 * (r : ZMod q) + 1) * h
    norm_cast at h3
    have hd : q ∣ 3 := (ZMod.natCast_eq_zero_iff 3 q).mp h3
    exact ((Nat.dvd_prime Nat.prime_three).mp hd).elim hq.ne_one hq3
  obtain ⟨t, ht⟩ := hr
  obtain ⟨c, _, hc⟩ := choose_lift_digit_nat hq r t hderiv
  obtain ⟨k, hk⟩ := hc
  have hqpow : q ∣ q ^ a := dvd_pow_self q (by omega)
  obtain ⟨w, hw⟩ := hqpow
  use r + c * q ^ a
  use k + c ^ 2 * w
  calc
    cubicCyclotomic (r + c * q ^ a) =
        cubicCyclotomic r + q ^ a * (c * (2 * r + 1)) + q ^ a * (c ^ 2 * q ^ a) := by
      unfold cubicCyclotomic
      ring
    _ = q ^ a * (t + c * (2 * r + 1) + c ^ 2 * q ^ a) := by rw [ht]; ring
    _ = q ^ (a + 1) * (k + c ^ 2 * w) := by
      rw [hk, pow_succ q a]
      have hterm : c ^ 2 * q ^ a = q * (c ^ 2 * w) := by rw [hw]; ring
      rw [hterm]
      ring

theorem exists_cubic_root_mod_prime_pow {q : ℕ} (hq : q.Prime) (hmod : q % 3 = 1)
    (a : ℕ) : ∃ r : ℕ, q ^ a ∣ cubicCyclotomic r := by
  have hq3 : q ≠ 3 := by omega
  have h3 : 3 ∣ q - 1 := by omega
  induction a with
  | zero => exact ⟨0, by simp⟩
  | succ a ih =>
    cases a with
    | zero =>
      letI : NeZero q := ⟨hq.ne_zero⟩
      obtain ⟨r, hr⟩ := exists_cubic_root_mod_prime hq h3
      refine ⟨r.val, ?_⟩
      rw [pow_one, ← ZMod.natCast_eq_zero_iff]
      change ((cubicCyclotomic r.val : ℕ) : ZMod q) = 0
      unfold cubicCyclotomic
      push_cast
      simpa using hr
    | succ a =>
      obtain ⟨r, hr⟩ := ih
      exact cubic_root_lift hq hq3 (by omega) hr


end SigmaRange

namespace SigmaRange

def firstQuad (x : ℕ) : ℕ := x ^ 2 + x + 1

theorem firstQuad_not_dvd_three {p : ℕ} (hp : p % 3 = 2) :
    ¬ 3 ∣ firstQuad p := by
  have hcast : (p : ZMod 3) = 2 := by
    calc
      (p : ZMod 3) = ((p % 3 : ℕ) : ZMod 3) := (ZMod.natCast_mod p 3).symm
      _ = 2 := by rw [hp]; rfl
  rw [← ZMod.natCast_eq_zero_iff]
  push_cast [firstQuad]
  rw [hcast]
  decide

theorem firstQuad_coprime_cube {p : ℕ} (h3 : ¬ 3 ∣ firstQuad p) :
    (firstQuad p).Coprime (firstQuad (p ^ 3)) := by
  by_contra h
  obtain ⟨q, hq, hleft, hright⟩ := Nat.Prime.not_coprime_iff_dvd.mp h
  let x : ZMod q := p
  have hQ : x ^ 2 + x + 1 = 0 := by
    change (p : ZMod q) ^ 2 + (p : ZMod q) + 1 = 0
    exact_mod_cast (ZMod.natCast_eq_zero_iff (firstQuad p) q).mpr hleft
  have hcube : x ^ 3 = 1 := by
    calc
      x ^ 3 = (x - 1) * (x ^ 2 + x + 1) + 1 := by ring
      _ = 1 := by rw [hQ, mul_zero, zero_add]
  have hQcube : (x ^ 3) ^ 2 + x ^ 3 + 1 = 0 := by
    change ((p : ZMod q) ^ 3) ^ 2 + (p : ZMod q) ^ 3 + 1 = 0
    exact_mod_cast (ZMod.natCast_eq_zero_iff (firstQuad (p ^ 3)) q).mpr hright
  have hq3 : q ∣ 3 := (ZMod.natCast_eq_zero_iff 3 q).mp (by
    rw [hcube] at hQcube
    norm_num at hQcube ⊢
    convert hQcube using 1)
  rcases (Nat.dvd_prime Nat.prime_three).mp hq3 with he | he
  · exact hq.ne_one he
  · exact h3 (he ▸ hleft)


theorem den_cancel_prescribed_factor {A B d m k : ℕ} (hd : 0 < d)
    (hm : 0 < m) (hB : B = d * m) (hA : A.Coprime B) (hk : k.Coprime d) :
    (((A : ℚ) / B) * (↑(m * k) : ℚ)).den = d := by
  have hc : (A * k).Coprime d := by
    exact (hA.coprime_dvd_right (hB ▸ Nat.dvd_mul_right d m)).mul_left hk
  have heq : ((A : ℚ) / B) * (↑(m * k) : ℚ) = (↑(A * k) : ℚ) / d := by
    rw [hB]
    push_cast
    field_simp
  rw [heq]
  have hcInt : (Int.ofNat (A * k)).natAbs.Coprime (Int.ofNat d).natAbs := hc
  have h : (((((A * k : ℕ) : ℤ) : ℚ) / ((d : ℤ) : ℚ)).den : ℤ) = (d : ℤ) :=
    Rat.den_div_eq_of_coprime (a := Int.ofNat (A * k)) (b := Int.ofNat d)
      (by change (0 : ℤ) < (d : ℤ); exact_mod_cast hd) hcInt
  simp only [Int.cast_natCast] at h
  exact Int.ofNat_inj.mp h


theorem quad_dvd_quad_pow {p t : ℕ} (ht : ¬ 3 ∣ t) :
    firstQuad p ∣ firstQuad (p ^ t) := by
  let x : ZMod (firstQuad p) := p
  have hQ : x ^ 2 + x + 1 = 0 := by
    have h := (ZMod.natCast_eq_zero_iff (firstQuad p) (firstQuad p)).mpr (dvd_refl _)
    change (p : ZMod (firstQuad p)) ^ 2 + (p : ZMod (firstQuad p)) + 1 = 0
    exact_mod_cast h
  have hcube : x ^ 3 = 1 := by
    calc
      x ^ 3 = (x - 1) * (x ^ 2 + x + 1) + 1 := by ring
      _ = 1 := by rw [hQ, mul_zero, zero_add]
  have hpow : x ^ t = x ^ (t % 3) := by
    conv_lhs => rw [← Nat.mod_add_div t 3]
    simp [pow_add, pow_mul, hcube]
  suffices h : (x ^ t) ^ 2 + x ^ t + 1 = 0 by
    apply (ZMod.natCast_eq_zero_iff _ _).mp
    dsimp [x] at h
    exact_mod_cast h
  rw [hpow]
  have hr : t % 3 = 1 ∨ t % 3 = 2 := by
    have hn := Nat.mod_lt t (by decide : 0 < 3)
    have hz : t % 3 ≠ 0 := mt (Nat.dvd_of_mod_eq_zero) ht
    omega
  rcases hr with h | h
  · simpa [h] using hQ
  · rw [h]
    rw [show (x ^ 2) ^ 2 = x by calc
      (x ^ 2) ^ 2 = x ^ 3 * x := by ring
      _ = x := by rw [hcube, one_mul]]
    rw [add_comm x]
    exact hQ


theorem cancel_of_factorizations {d m V : ℕ} (hm : m ≠ 0) (hV : V ≠ 0)
    (hval : ∀ q : ℕ, q.Prime → q ∣ d * m → V.factorization q = m.factorization q) :
    ∃ k : ℕ, V = m * k ∧ k.Coprime d := by
  have hmV : m ∣ V := (Nat.factorization_le_iff_dvd hm hV).mp <| by
    intro q
    by_cases hq : q.Prime
    · by_cases hqm : q ∣ m
      · rw [hval q hq (dvd_mul_of_dvd_right hqm d)]
      · rw [Nat.factorization_eq_zero_of_not_dvd hqm]
        exact Nat.zero_le _
    · rw [Nat.factorization_eq_zero_of_not_prime _ hq]
      exact Nat.zero_le _
  obtain ⟨k, hk⟩ := hmV
  have hk0 : k ≠ 0 := by
    rintro rfl
    apply hV
    simpa using hk
  refine ⟨k, hk, ?_⟩
  by_contra hh
  obtain ⟨q, hq, hqk, hqd⟩ := Nat.Prime.not_coprime_iff_dvd.mp hh
  have he := hval q hq (dvd_mul_of_dvd_left hqd m)
  rw [hk, Nat.factorization_mul hm hk0, Finsupp.add_apply] at he
  have hp := hq.factorization_pos_of_dvd hk0 hqk
  omega


end SigmaRange
namespace SigmaRange

open scoped ArithmeticFunction.sigma

private theorem cast_firstQuad (x : ℕ) : (firstQuad x : ℚ) = quad (x : ℚ) := by
  simp [firstQuad, quad]

theorem range_forward {n q : ℕ} (hn : n ≠ 0) (hq : q.Prime)
    (hd : q ∣ ((σ 3 n : ℚ) / (σ 1 n : ℚ)).den) : q % 3 = 1 := by
  rw [sigma_quotient_factorization n hn] at hd
  have hh : ∀ p : ℕ, quad ((p : ℚ) ^ (n.factorization p + 1)) / quad (p : ℚ) =
      OMA.SigmaRange.localFactor p (n.factorization p) := by
    intro p
    simp [OMA.SigmaRange.localFactor, OMA.SigmaRange.Q, quad]
  simp_rw [hh] at hd
  exact OMA.SigmaRange.prod_localFactor_den_prime_mod_three n.primeFactors
    (fun _ => Nat.prime_of_mem_primeFactors) n.factorization q hq hd

theorem range_reverse_of_prime_construction
    (construction : ∀ D : ℕ, 0 < D → (∀ q : ℕ, q.Prime → q ∣ D → q % 3 = 1) →
      ∀ N : ℕ, ∃ p : ℕ, p.Prime ∧ N < p ∧ p % 3 = 2 ∧ D ∣ firstQuad p)
    {d : ℕ} (hd : 0 < d) (hdgood : ∀ q : ℕ, q.Prime → q ∣ d → q % 3 = 1) :
    ∃ n : ℕ, 0 < n ∧ ((σ 3 n : ℚ) / (σ 1 n : ℚ)).den = d := by
  obtain ⟨p, hp, _, hp3, hdp⟩ := construction d hd hdgood 0
  have hB3 := firstQuad_not_dvd_three hp3
  have hBgood : ∀ q : ℕ, q.Prime → q ∣ firstQuad p → q % 3 = 1 := by
    intro q hq hqB
    exact OMA.SigmaRange.prime_dvd_Q_mod_three q p hq hqB (by
      rintro rfl
      exact hB3 hqB)
  obtain ⟨r, hr, hpr, _, hBr⟩ := construction (firstQuad p) (by unfold firstQuad; omega)
    hBgood p
  obtain ⟨m, hm⟩ := hdp
  have hmpos : 0 < m := by
    by_contra! hh
    have hzero : m = 0 := by omega
    simp [hzero, firstQuad] at hm
  have hm3 : ¬ 3 ∣ m := fun h => hB3 (hm ▸ dvd_mul_of_dvd_right h d)
  obtain ⟨V, hV⟩ := quad_dvd_quad_pow (p := r) hm3
  have hV0 : V ≠ 0 := by
    rintro rfl
    simp [firstQuad] at hV
  have hval : ∀ q : ℕ, q.Prime → q ∣ d * m → V.factorization q = m.factorization q := by
    intro q hq hqdm
    have hqB : q ∣ firstQuad p := hm ▸ hqdm
    have hqR : q ∣ firstQuad r := hqB.trans hBr
    have he := padicVal_Q_pow r q m hq (hBgood q hq hqB) hqR hmpos hm3
    change padicValNat q (firstQuad (r ^ m)) =
      padicValNat q (firstQuad r) + padicValNat q m at he
    simp only [← Nat.factorization_def _ hq] at he
    rw [hV, Nat.factorization_mul (by unfold firstQuad; omega) hV0, Finsupp.add_apply] at he
    omega
  obtain ⟨k, hk, hkd⟩ := cancel_of_factorizations hmpos.ne' hV0 hval
  have hcop : (p ^ 2).Coprime (r ^ (m - 1)) :=
    (Nat.coprime_primes hp hr |>.mpr hpr.ne).pow _ _
  refine ⟨p ^ 2 * r ^ (m - 1), Nat.mul_pos (pow_pos hp.pos _) (pow_pos hr.pos _), ?_⟩
  rw [ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime hcop,
    ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime hcop]
  push_cast
  rw [← div_mul_div_comm, sigma_prime_power_quotient p 2 hp,
    sigma_prime_power_quotient r (m - 1) hr]
  have hmexp : m - 1 + 1 = m := by omega
  rw [hmexp]
  norm_num at *
  rw [← cast_firstQuad p, ← cast_firstQuad r, ← Nat.cast_pow, ← Nat.cast_pow,
    ← cast_firstQuad, ← cast_firstQuad, hV, hk]
  push_cast
  rw [mul_div_cancel_left₀ _ (show (firstQuad r : ℚ) ≠ 0 by
    exact_mod_cast (show firstQuad r ≠ 0 by unfold firstQuad; omega))]
  simpa only [Nat.cast_mul] using den_cancel_prescribed_factor hd hmpos hm
    (firstQuad_coprime_cube hB3).symm hkd


end SigmaRange

namespace SigmaRangeCRT

def Q (n : ℕ) : ℕ := n ^ 2 + n + 1

/-- From a root modulo `d`, choose a residue modulo `3d` that is that root
modulo `d` and is `2` modulo `3`. Dirichlet then supplies large primes in
this residue class. -/
theorem exists_large_prime_with_Q_divisible
    {d N : ℕ} (hd : 0 < d) (hcop : d.Coprime 3)
    (hr : ∃ r, r.Coprime d ∧ d ∣ Q r) :
    ∃ p, N < p ∧ Nat.Prime p ∧ p % 3 = 2 ∧ d ∣ Q p := by
  obtain ⟨r, hrd, hroot⟩ := hr
  let crt := Nat.chineseRemainder hcop r 2
  let x := crt.val
  have hxrd : x ≡ r [MOD d] := crt.property.1
  have hx3 : x ≡ 2 [MOD 3] := crt.property.2
  have hxmodd : x % d = r % d := hxrd
  have hxmod3 : x % 3 = 2 := by
    have := hx3
    simpa [Nat.ModEq] using this
  have hxCoprimed : x.Coprime d := by
    apply (ZMod.coprime_mod_iff_coprime x d).mp
    rw [hxmodd]
    exact (ZMod.coprime_mod_iff_coprime r d).mpr hrd
  have hxCoprime3 : x.Coprime 3 := by
    rw [← ZMod.coprime_mod_iff_coprime x 3, hxmod3]
    norm_num
  have hxCoprime : x.Coprime (3 * d) := by
    exact hxCoprime3.mul_right hxCoprimed
  have hmodulus : 3 * d ≠ 0 := by omega
  obtain ⟨p, hpN, hp, hpx⟩ :=
    Nat.forall_exists_prime_gt_and_modEq N hmodulus hxCoprime
  have hpxd : p ≡ x [MOD d] := by
    apply Nat.ModEq.of_dvd (n := 3 * d)
    · exact ⟨3, by ring⟩
    · exact hpx
  have hprd : p ≡ r [MOD d] := hpxd.trans hxrd
  have hQmod : Q p ≡ Q r [MOD d] := by
    unfold Q
    exact (Nat.ModEq.pow 2 hprd).add hprd |>.add (Nat.ModEq.refl 1)
  have hdvd : d ∣ Q r := hroot
  have hQzero : Q r ≡ 0 [MOD d] := Dvd.dvd.modEq_zero_nat hdvd
  have hQpzero : Q p ≡ 0 [MOD d] := hQmod.trans hQzero
  have hdiv : d ∣ Q p := Nat.modEq_zero_iff_dvd.mp hQpzero
  refine ⟨p, hpN, hp, ?_, hdiv⟩
  have hpx3 : p ≡ x [MOD 3] :=
    Nat.ModEq.of_dvd ⟨d, by ring⟩ hpx
  have hpm : p ≡ 2 [MOD 3] := hpx3.trans hx3
  have : p % 3 = 2 % 3 := by simpa [Nat.ModEq] using hpm
  simpa using this

/-- Combine roots modulo each maximal prime power in `d` into a root modulo d. -/
theorem exists_root_mod_of_prime_power_roots {d : ℕ} (hd : d ≠ 0)
    (hroot : ∀ q ∈ d.primeFactors,
      ∃ r, q ^ d.factorization q ∣ Q r) :
    ∃ r, r.Coprime d ∧ d ∣ Q r := by
  let S := d.primeFactors
  let m (q : ℕ) := q ^ d.factorization q
  let a (q : ℕ) := if hq : q ∈ S then Classical.choose (hroot q hq) else 0
  have hmodpos : ∀ q ∈ S, m q ≠ 0 := by
    intro q hq
    simp only [m]
    exact pow_ne_zero _ (Nat.ne_of_gt (Nat.Prime.pos (Nat.prime_of_mem_primeFactors hq)))
  have hpair : (↑S : Set ℕ).Pairwise (Function.onFun Nat.Coprime m) := by
    intro q hq q' hq' hne
    apply Nat.Coprime.pow
    apply (Nat.coprime_primes (Nat.prime_of_mem_primeFactors hq)
      (Nat.prime_of_mem_primeFactors hq')).mpr
    exact hne
  let crt := Nat.chineseRemainderOfFinset a m S hmodpos hpair
  let r := crt.val
  have hrq : ∀ q ∈ S, r ≡ a q [MOD m q] := crt.property
  have hqdiv : ∀ q ∈ S, m q ∣ Q r := by
    intro q hq
    have haq : m q ∣ Q (a q) := by
      simpa [a, hq] using Classical.choose_spec (hroot q (by simpa [S] using hq))
    have hmod : Q r ≡ Q (a q) [MOD m q] := by
      unfold Q
      exact (Nat.ModEq.pow 2 (hrq q hq)).add (hrq q hq) |>.add (Nat.ModEq.refl 1)
    exact Nat.modEq_zero_iff_dvd.mp (hmod.trans (Dvd.dvd.modEq_zero_nat haq))
  have hprod : (∏ q ∈ S, m q) ∣ Q r := by
    have hprodInt : (∏ q ∈ S, (m q : ℤ)) ∣ (Q r : ℤ) := by
      apply Finset.prod_dvd_of_coprime
      · intro q hq q' hq' hne
        exact (Nat.isCoprime_iff_coprime).2 (hpair hq hq' hne)
      · intro q hq
        exact_mod_cast hqdiv q hq
    exact_mod_cast hprodInt
  have hrootd : d ∣ Q r := by
    have heq : (∏ q ∈ d.primeFactors, q ^ d.factorization q) = d :=
      (Nat.prod_primeFactors_pow_factorization hd).symm
    simpa [S, m, heq] using hprod
  have hcoprime : r.Coprime d := by
    have hself : r.Coprime (Q r) := by
      unfold Q
      rw [Nat.coprime_comm]
      rw [show r ^ 2 + r + 1 = (1 + r * r) + r by ring]
      rw [Nat.coprime_add_self_left]
      rw [Nat.coprime_add_mul_right_left]
      simp
    exact Nat.Coprime.of_dvd_right hrootd hself
  exact ⟨r, hcoprime, hrootd⟩

end SigmaRangeCRT
namespace SigmaRange

theorem prime_construction_of_combined_root
    (root : ∀ D : ℕ, 0 < D → (∀ q : ℕ, q.Prime → q ∣ D → q % 3 = 1) →
      ∃ x : ℕ, D ∣ firstQuad x)
    (D : ℕ) (hD : 0 < D) (hgood : ∀ q : ℕ, q.Prime → q ∣ D → q % 3 = 1)
    (N : ℕ) : ∃ p : ℕ, p.Prime ∧ N < p ∧ p % 3 = 2 ∧ D ∣ firstQuad p := by
  have hD3 : D.Coprime 3 := by
    apply Nat.Coprime.symm
    apply Nat.prime_three.coprime_iff_not_dvd.mpr
    intro h
    have := hgood 3 Nat.prime_three h
    omega
  obtain ⟨x, hx⟩ := root D hD hgood
  have hxD : x.Coprime D := by
    by_contra h
    obtain ⟨q, hq, hqx, hqD⟩ := Nat.Prime.not_coprime_iff_dvd.mp h
    have hqQ := hqD.trans hx
    have hq1 : q ∣ 1 := by
      have hqx2 : q ∣ x ^ 2 := hqx.trans (dvd_pow_self x (by decide))
      have h := Nat.dvd_sub hqQ (Nat.dvd_add hqx2 hqx)
      rwa [firstQuad, Nat.add_sub_cancel_left] at h
    exact hq.not_dvd_one hq1
  obtain ⟨p, hpN, hp, hp3, hdiv⟩ :=
    SigmaRangeCRT.exists_large_prime_with_Q_divisible (N := N) hD hD3 ⟨x, hxD, hx⟩
  exact ⟨p, hp, hpN, hp3, hdiv⟩


end SigmaRange
namespace SigmaRange

theorem prime_construction
    (D : ℕ) (hD : 0 < D) (hgood : ∀ q : ℕ, q.Prime → q ∣ D → q % 3 = 1)
    (N : ℕ) : ∃ p : ℕ, p.Prime ∧ N < p ∧ p % 3 = 2 ∧ D ∣ firstQuad p := by
  apply prime_construction_of_combined_root _ D hD hgood N
  intro d hd hgoodd
  obtain ⟨r, _, hr⟩ := SigmaRangeCRT.exists_root_mod_of_prime_power_roots hd.ne' (by
    intro q hq
    have hqp := Nat.prime_of_mem_primeFactors hq
    exact exists_cubic_root_mod_prime_pow hqp
      (hgoodd q hqp (Nat.dvd_of_mem_primeFactors hq)) (d.factorization q))
  exact ⟨r, hr⟩

end SigmaRange
theorem OMA.solution : type_of% @OMA.S_oeis_a091258.main := by
  ext d
  constructor
  · rintro ⟨n, hn, rfl⟩
    refine ⟨Rat.den_pos _, ?_⟩
    intro q hq hdiv
    exact SigmaRange.range_forward hn.ne' hq hdiv
  · rintro ⟨hd, hgood⟩
    exact SigmaRange.range_reverse_of_prime_construction
      SigmaRange.prime_construction hd hgood
