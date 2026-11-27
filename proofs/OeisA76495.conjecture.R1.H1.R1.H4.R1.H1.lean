import OMAReductions.R_OeisA76495_conjecture_R1_H1_R1_H4_R1
import Mathlib

/-!
Disjoint exponent boxes exclude the four eight-prime supports. The Lean
checker verifies every upper bound, lower bound, and skipped exponent.
-/

open ArithmeticFunction
open scoped BigOperators

namespace SigmaAbundancyBounds
/-- Sum of the powers from zero through the given exponent. -/
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

theorem geometric_product_scaled_mono {ι : Type*}
    (I : Finset ι) (p a b : ι → ℕ) (hexp : ∀ i ∈ I, a i ≤ b i) :
    (∏ i ∈ I, geometric (p i) (a i)) * (∏ i ∈ I, p i ^ b i) ≤
      (∏ i ∈ I, geometric (p i) (b i)) * (∏ i ∈ I, p i ^ a i) := by
  rw [← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]
  exact Finset.prod_le_prod (fun _ _ => Nat.zero_le _)
    (fun i hi => geometric_scaled_mono (p i) (hexp i hi))

theorem prime_power_product_mono {ι : Type*} (I : Finset ι) (p a b : ι → ℕ)
    (hp : ∀ i ∈ I, 1 ≤ p i) (hexp : ∀ i ∈ I, a i ≤ b i) :
    (∏ i ∈ I, p i ^ a i) ≤ ∏ i ∈ I, p i ^ b i := by
  exact Finset.prod_le_prod (fun _ _ => Nat.zero_le _)
    (fun i hi => Nat.pow_le_pow_right (hp i hi) (hexp i hi))

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


end SigmaAbundancyBounds

namespace SigmaEightModThree

def geometric (p e : ℕ) : ℕ := ∑ j ∈ Finset.range (e + 1), p ^ j

def geomModThree (p e : ℕ) : ℕ := geometric p e % 3

theorem geometric_succ (p e : ℕ) :
    geometric p (e + 1) = geometric p e + p ^ (e + 1) := by
  simp [geometric, Finset.sum_range_succ, Nat.add_assoc, Nat.add_left_comm,
    Nat.add_comm]

theorem pow_mod_three_eq_one_of_mod_one (p k : ℕ) (hp : p % 3 = 1) :
    p ^ k % 3 = 1 := by
  induction k with
  | zero => norm_num
  | succ k ih =>
      rw [Nat.pow_succ, Nat.mul_mod, ih, hp]

theorem pow_mod_three_two (p k : ℕ) (hp : p % 3 = 2) :
    p ^ k % 3 = if k % 2 = 0 then 1 else 2 := by
  induction k with
  | zero => norm_num
  | succ k ih =>
      rw [Nat.pow_succ, Nat.mul_mod, ih, hp]
      by_cases hk : k % 2 = 0 <;> simp [hk] <;> omega

theorem geomModThree_eq_succ_mod_three_of_mod_one (p e : ℕ) (hp : p % 3 = 1) :
    geomModThree p e = (e + 1) % 3 := by
  induction e with
  | zero => norm_num [geomModThree, geometric]
  | succ e ih =>
      change geometric p (e + 1) % 3 = (e + 1 + 1) % 3
      rw [geometric_succ, Nat.add_mod,
        pow_mod_three_eq_one_of_mod_one p (e + 1) hp]
      change geometric p e % 3 = (e + 1) % 3 at ih
      rw [ih]
      omega

theorem geomModThree_formula_of_mod_two (p e : ℕ) (hp : p % 3 = 2) :
    geomModThree p e = if e % 2 = 0 then 1 else 0 := by
  induction e with
  | zero => norm_num [geomModThree, geometric]
  | succ e ih =>
      change geometric p (e + 1) % 3 = if (e + 1) % 2 = 0 then 1 else 0
      rw [geometric_succ, Nat.add_mod, pow_mod_three_two p (e + 1) hp]
      change geometric p e % 3 = (if e % 2 = 0 then 1 else 0) at ih
      rw [ih]
      by_cases he : e % 2 = 0
      · have hs : (e + 1) % 2 = 1 := by omega
        simp [he, hs]
      · have he' : e % 2 = 1 := by omega
        have hs : (e + 1) % 2 = 0 := by omega
        simp [he', hs]

theorem geomModThree_eq_zero_of_mod_two_odd (p e : ℕ) (hp : p % 3 = 2)
    (he : e % 2 = 1) : geomModThree p e = 0 := by
  rw [geomModThree_formula_of_mod_two p e hp, if_neg (by omega)]

end SigmaEightModThree

namespace SigmaEightBoxes
open SigmaAbundancyBounds

abbrev Exponents := Fin 8 → ℕ
abbrev Ceiling := Fin 8 → Option ℕ

def value (p e : Exponents) : ℕ := ∏ i, p i ^ e i
def divisorSum (p e : Exponents) : ℕ := ∏ i, geometric (p i) (e i)

def numerator (p : ℕ) (u : Option ℕ) : ℕ :=
  match u with
  | none => p
  | some e => geometric p e

def denominator (p : ℕ) (u : Option ℕ) : ℕ :=
  match u with
  | none => p - 1
  | some e => p ^ e

def upperNum (p : Exponents) (u : Ceiling) : ℕ := ∏ i, numerator (p i) (u i)
def upperDen (p : Exponents) (u : Ceiling) : ℕ := ∏ i, denominator (p i) (u i)

def Bounded (e : Exponents) (u : Ceiling) : Prop :=
  ∀ i b, u i = some b → e i ≤ b

def Above (l e : Exponents) : Prop := ∀ i, l i ≤ e i

theorem upper_excludes {p e : Exponents} {u : Ceiling} (hp : ∀ i, 2 ≤ p i)
    (hu : Bounded e u) (hsmall : upperNum p u ≤ 3 * upperDen p u)
    (heq : divisorSum p e = 3 * value p e + 5) : False := by
  have hb (i : Fin 8) : geometric (p i) (e i) * denominator (p i) (u i) ≤
      numerator (p i) (u i) * p i ^ e i := by
    cases h : u i with
    | none => exact geometric_upper (p i) (e i) (by have := hp i; omega)
    | some b => exact geometric_scaled_mono (p i) (hu i b h)
  have hh : divisorSum p e * upperDen p u ≤ upperNum p u * value p e := by
    unfold divisorSum upperDen upperNum value
    rw [← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]
    exact Finset.prod_le_prod (fun _ _ => Nat.zero_le _) (fun i _ => hb i)
  have hpos : 0 < upperDen p u := by
    apply Finset.prod_pos
    intro i _
    have hi := hp i
    cases h : u i with
    | none => exact Nat.sub_pos_of_lt (by omega)
    | some b => exact pow_pos (by omega) _
  have hmul := Nat.mul_le_mul_right (value p e) hsmall
  nlinarith only [hh, heq, hpos, hmul]

theorem lower_excludes {p e l : Exponents} (hp : ∀ i, 2 ≤ p i)
    (hl : Above l e) (hlarge : 3 * value p l + 5 < divisorSum p l)
    (heq : divisorSum p e = 3 * value p e + 5) : False := by
  have hmono : value p l ≤ value p e :=
    prime_power_product_mono Finset.univ p l e
      (fun i _ => by have := hp i; omega) (fun i _ => hl i)
  have hratio : divisorSum p l * value p e ≤ divisorSum p e * value p l :=
    geometric_product_scaled_mono Finset.univ p l e (fun i _ => hl i)
  have hpos : 0 < value p e := Finset.prod_pos fun i _ => pow_pos (by have := hp i; omega) _
  have hstrict := Nat.mul_lt_mul_of_pos_right hlarge hpos
  nlinarith only [hmono, hratio, heq, hstrict]

theorem lower_update {e l : Exponents} {i : Fin 8} {k : ℕ} (hl : Above l e)
    (hk : k ≤ e i) : Above (Function.update l i k) e := by
  intro j
  by_cases h : j = i
  · subst j
    simpa using hk
  · simpa [Function.update_of_ne h] using hl j

theorem upper_update {e : Exponents} {u : Ceiling} {i : Fin 8} {k : ℕ}
    (hu : Bounded e u) (hk : e i ≤ k) : Bounded e (Function.update u i (some k)) := by
  intro j b hj
  by_cases h : j = i
  · subst j
    have : k = b := by simpa using hj
    simpa [← this] using hk
  · apply hu j b
    simpa [Function.update_of_ne h] using hj

def Allowed (p e : ℕ) : Prop :=
  (p % 3 = 2 → e % 2 = 0) ∧ (p % 3 = 1 → e % 3 ≠ 2)

instance (p e : ℕ) : Decidable (Allowed p e) := inferInstanceAs (Decidable (_ ∧ _))

def skips (p c k : ℕ) : Prop :=
  ∀ a : Fin k, c < a.val → ¬ Allowed p a.val

instance (p c k : ℕ) : Decidable (skips p c k) :=
  inferInstanceAs (Decidable (∀ a : Fin k, c < a.val → ¬ Allowed p a.val))

theorem lower_of_skip {p c k e : ℕ} (hs : skips p c k) (ha : Allowed p e)
    (hc : c < e) : k ≤ e := by
  by_contra! hk
  exact hs ⟨e, hk⟩ hc ha

inductive Certificate
  | overshoot
  | tighten (i : Fin 8) (cut next : ℕ) (child : Certificate)
  | split (i : Fin 8) (cut next : ℕ) (below above : Certificate)

def check (p l : Exponents) (u : Ceiling) : Certificate → Bool
  | .overshoot => decide (3 * value p l + 5 < divisorSum p l)
  | .tighten i cut next child =>
      let bound := Function.update u i (some cut)
      decide (upperNum p bound ≤ 3 * upperDen p bound) &&
      decide (skips (p i) cut next) &&
      check p (Function.update l i next) u child
  | .split i cut next below above =>
      decide (skips (p i) cut next) &&
      check p l (Function.update u i (some cut)) below &&
      check p (Function.update l i next) u above

theorem sound {p e : Exponents} (hp : ∀ i, 2 ≤ p i)
    (ha : ∀ i, Allowed (p i) (e i))
    (heq : divisorSum p e = 3 * value p e + 5)
    (cert : Certificate) {l : Exponents} {u : Ceiling}
    (hl : Above l e) (hu : Bounded e u) (hc : check p l u cert = true) : False := by
  induction cert generalizing l u with
  | overshoot =>
      exact lower_excludes hp hl (of_decide_eq_true hc) heq
  | tighten i cut next child ih =>
      simp only [check, Bool.and_eq_true, decide_eq_true_eq] at hc
      obtain ⟨⟨hupper, hskip⟩, hchild⟩ := hc
      have hcut : cut < e i := by
        by_contra! habove
        exact upper_excludes hp (upper_update hu habove) hupper heq
      exact ih (lower_update hl (lower_of_skip hskip (ha i) hcut)) hu hchild
  | split i cut next below above ihBelow ihAbove =>
      simp only [check, Bool.and_eq_true, decide_eq_true_eq] at hc
      obtain ⟨⟨hskip, hbelow⟩, habove⟩ := hc
      by_cases h : e i ≤ cut
      · exact ihBelow hl (upper_update hu h) hbelow
      · exact ihAbove (lower_update hl (lower_of_skip hskip (ha i) (by omega))) hu habove

theorem allowed_of_equation (p e : Exponents)
    (heq : divisorSum p e = 3 * value p e + 5) : ∀ i, Allowed (p i) (e i) := by
  have hz : (divisorSum p e : ZMod 3) = 2 := by
    rw [heq]
    push_cast
    have h3 : (3 : ZMod 3) = 0 := by decide
    rw [h3, zero_mul, zero_add]
    decide
  rw [divisorSum, Nat.cast_prod] at hz
  intro i
  have hne : (SigmaEightModThree.geometric (p i) (e i) : ZMod 3) ≠ 0 := by
    intro h
    have h' : (SigmaAbundancyBounds.geometric (p i) (e i) : ZMod 3) = 0 := by
      simpa only [SigmaAbundancyBounds.geometric_eq_sum, SigmaEightModThree.geometric] using h
    have hp : (∏ j : Fin 8, (SigmaAbundancyBounds.geometric (p j) (e j) : ZMod 3)) = 0 :=
      Finset.prod_eq_zero (Finset.mem_univ i) h'
    rw [hp] at hz
    exact (by decide : (0 : ZMod 3) ≠ 2) hz
  have hnot : SigmaEightModThree.geomModThree (p i) (e i) ≠ 0 := by
    intro hm
    apply hne
    exact (ZMod.natCast_eq_zero_iff _ _).2 (Nat.dvd_iff_mod_eq_zero.mpr hm)
  constructor
  · intro hi
    by_contra! h
    exact hnot (SigmaEightModThree.geomModThree_eq_zero_of_mod_two_odd
      (p i) (e i) hi (by omega))
  · intro hi h
    have hm := SigmaEightModThree.geomModThree_eq_succ_mod_three_of_mod_one (p i) (e i) hi
    exact hnot (by omega)

def cert23 : Certificate :=
 (.tighten 0 2 3
 (.tighten 2 1 3
 (.split 0 3 4
 (.tighten 1 2 4
 (.split 4 1 3
 (.tighten 1 4 6
 (.tighten 2 3 4
 (.tighten 3 2 4
 (.tighten 6 1 3
 (.split 5 2 4
 (.split 2 4 6
 (.tighten 7 2 4
 (.split 1 6 8
 (.split 6 3 4
 (.tighten 3 4 6
 .overshoot)
 .overshoot)
 .overshoot))
 (.split 7 2 4
 (.tighten 1 6 8
 (.tighten 2 6 7
 (.tighten 3 4 6
 (.tighten 6 3 4
 (.split 1 8 10
 (.tighten 2 7 9
 (.tighten 3 6 8
 (.tighten 6 4 6
 .overshoot)))
 (.split 6 4 6
 (.tighten 2 7 9
 .overshoot)
 .overshoot))))))
 .overshoot))
 .overshoot)))))
 .overshoot))
 (.split 1 2 4
 (.split 4 1 3
 (.split 0 4 5
 (.tighten 3 2 4
 (.tighten 6 1 3
 (.split 2 3 4
 (.tighten 5 2 4
 .overshoot)
 .overshoot)))
 (.split 6 1 3
 (.split 0 5 6
 (.tighten 3 2 4
 (.split 2 3 4
 (.tighten 5 2 4
 .overshoot)
 .overshoot))
 (.split 3 2 4
 (.split 0 6 7
 (.split 2 3 4
 (.split 5 2 4
 (.tighten 7 2 4
 .overshoot)
 .overshoot)
 .overshoot)
 .overshoot)
 .overshoot))
 .overshoot))
 .overshoot)
 .overshoot))))

theorem check23 : check ![3, 5, 7, 11, 13, 17, 19, 23] ![1, 2, 1, 2, 1, 2, 1, 2] (fun _ => none) cert23 = true := by
  decide +kernel

def cert29 : Certificate :=
 (.tighten 0 3 4
 (.tighten 2 1 3
 (.split 1 2 4
 (.tighten 0 5 6
 (.tighten 4 1 3
 (.tighten 6 1 3
 (.split 3 2 4
 (.split 0 6 7
 (.tighten 2 4 6
 (.tighten 5 2 4
 (.split 4 3 4
 (.tighten 6 3 4
 (.tighten 7 2 4
 .overshoot))
 (.split 7 2 4
 (.tighten 2 6 7
 (.tighten 4 4 6
 (.tighten 6 3 4
 (.split 5 4 6
 (.tighten 6 4 6
 .overshoot)
 .overshoot))))
 .overshoot))))
 (.split 2 3 4
 (.tighten 0 7 8
 (.tighten 5 2 4
 (.split 0 8 9
 (.tighten 4 3 4
 (.tighten 7 2 4
 .overshoot))
 (.split 7 2 4
 (.split 4 3 4
 (.tighten 0 9 10
 (.tighten 6 3 4
 (.split 0 10 11
 (.split 5 4 6
 (.tighten 6 4 6
 .overshoot)
 .overshoot)
 .overshoot)))
 .overshoot)
 .overshoot))))
 .overshoot))
 .overshoot))))
 (.split 4 1 3
 (.tighten 0 4 5
 (.split 6 1 3
 (.tighten 0 5 6
 (.tighten 3 2 4
 (.split 0 6 7
 (.tighten 1 4 6
 (.tighten 2 3 4
 (.tighten 5 2 4
 (.split 2 4 6
 (.split 7 2 4
 (.split 1 6 8
 (.tighten 3 4 6
 .overshoot)
 .overshoot)
 .overshoot)
 .overshoot))))
 (.split 1 4 6
 (.tighten 2 3 4
 (.split 0 7 8
 (.tighten 5 2 4
 (.split 2 4 6
 (.split 7 2 4
 (.tighten 3 4 6
 .overshoot)
 .overshoot)
 .overshoot))
 (.split 5 2 4
 (.tighten 2 4 6
 (.split 0 8 9
 (.tighten 2 7 9
 (.tighten 3 6 8
 (.tighten 7 4 6
 .overshoot)))
 (.split 7 2 4
 (.tighten 0 9 10
 (.split 0 10 11
 (.tighten 3 4 6
 .overshoot)
 .overshoot))
 .overshoot)))
 .overshoot)))
 (.split 2 3 4
 (.tighten 5 2 4
 (.split 0 7 8
 (.tighten 1 6 8
 (.tighten 3 4 6
 (.tighten 7 2 4
 .overshoot)))
 .overshoot))
 .overshoot)))))
 .overshoot))
 .overshoot))))

theorem check29 : check ![3, 5, 7, 11, 13, 17, 19, 29] ![1, 2, 1, 2, 1, 2, 1, 2] (fun _ => none) cert29 = true := by
  decide +kernel

def cert31 : Certificate :=
 (.tighten 0 3 4
 (.tighten 1 2 4
 (.tighten 2 1 3
 (.split 0 4 5
 (.tighten 4 1 3
 (.split 6 1 3
 (.tighten 1 4 6
 (.tighten 2 3 4
 (.tighten 3 2 4
 (.tighten 5 2 4
 (.tighten 7 1 3
 (.split 2 4 6
 (.tighten 4 3 4
 .overshoot)
 .overshoot))))))
 .overshoot))
 (.split 4 1 3
 (.tighten 0 5 6
 (.tighten 6 1 3
 (.split 0 6 7
 (.tighten 3 2 4
 (.tighten 7 1 3
 (.split 1 4 6
 (.tighten 2 3 4
 (.split 5 2 4
 (.split 2 4 6
 (.tighten 6 3 4
 (.split 3 4 6
 (.tighten 6 4 6
 (.tighten 7 3 4
 .overshoot))
 .overshoot))
 .overshoot)
 .overshoot))
 (.split 2 3 4
 (.tighten 5 2 4
 .overshoot)
 .overshoot))))
 (.split 2 3 4
 (.tighten 3 2 4
 (.tighten 7 1 3
 (.split 1 4 6
 (.split 0 7 8
 (.tighten 5 2 4
 .overshoot)
 .overshoot)
 .overshoot)))
 (.split 3 2 4
 (.tighten 1 4 6
 (.tighten 7 1 3
 (.split 0 7 8
 (.tighten 5 2 4
 .overshoot)
 (.split 5 2 4
 (.split 0 8 9
 (.tighten 2 4 6
 .overshoot)
 (.split 2 4 6
 (.split 0 9 10
 (.split 1 6 8
 (.tighten 6 3 4
 .overshoot)
 .overshoot)
 .overshoot)
 .overshoot))
 .overshoot))))
 (.split 7 1 3
 (.tighten 0 9 10
 (.tighten 1 6 8
 (.tighten 2 4 6
 (.tighten 3 4 6
 (.tighten 5 2 4
 (.tighten 6 3 4
 (.split 0 10 11
 (.tighten 1 8 10
 (.tighten 2 7 9
 (.tighten 5 4 6
 (.tighten 6 4 6
 .overshoot))))
 .overshoot)))))))
 .overshoot))))))
 .overshoot)))))

theorem check31 : check ![3, 5, 7, 11, 13, 17, 19, 31] ![1, 2, 1, 2, 1, 2, 1, 1] (fun _ => none) cert31 = true := by
  decide +kernel

def cert37 : Certificate :=
 (.tighten 0 4 5
 (.tighten 1 2 4
 (.tighten 2 1 3
 (.tighten 4 1 3
 (.tighten 6 1 3
 (.split 0 5 6
 (.tighten 1 4 6
 (.tighten 2 3 4
 (.tighten 3 2 4
 (.tighten 7 1 3
 (.split 5 2 4
 (.tighten 2 4 6
 (.tighten 4 3 4
 (.split 1 6 8
 (.tighten 3 4 6
 (.tighten 4 4 6
 (.tighten 6 3 4
 (.split 2 6 7
 (.tighten 7 3 4
 .overshoot)
 .overshoot))))
 (.split 6 3 4
 (.split 3 4 6
 (.tighten 2 6 7
 (.tighten 4 4 6
 (.split 1 8 10
 (.tighten 2 7 9
 (.tighten 7 3 4
 .overshoot))
 (.split 7 3 4
 (.tighten 2 7 9
 .overshoot)
 .overshoot))))
 .overshoot)
 .overshoot))))
 .overshoot)))))
 (.split 3 2 4
 (.split 0 6 7
 (.tighten 2 3 4
 (.tighten 7 1 3
 (.split 1 4 6
 (.tighten 5 2 4
 (.split 2 4 6
 (.tighten 4 4 6
 (.tighten 6 3 4
 .overshoot))
 .overshoot))
 .overshoot)))
 (.split 2 3 4
 (.tighten 7 1 3
 (.split 1 4 6
 (.tighten 0 7 8
 (.tighten 5 2 4
 .overshoot))
 .overshoot))
 (.split 7 1 3
 (.tighten 0 7 8
 (.tighten 1 4 6
 (.tighten 5 2 4
 (.split 0 8 9
 (.tighten 2 4 6
 .overshoot)
 (.split 2 4 6
 (.split 4 3 4
 (.tighten 0 9 10
 (.split 0 10 11
 (.tighten 1 6 8
 (.split 6 3 4
 (.tighten 5 4 6
 .overshoot)
 .overshoot))
 (.split 1 6 8
 (.tighten 0 11 12
 (.tighten 6 3 4
 (.split 0 12 13
 (.tighten 5 4 6
 .overshoot)
 (.split 5 4 6
 (.split 6 4 6
 (.tighten 0 15 16
 .overshoot)
 .overshoot)
 .overshoot))))
 .overshoot)))
 .overshoot)
 .overshoot)))))
 .overshoot)))
 (.split 7 1 3
 (.split 0 6 7
 (.tighten 2 3 4
 (.split 1 4 6
 (.tighten 5 2 4
 (.split 2 4 6
 (.tighten 4 3 4
 .overshoot)
 .overshoot))
 .overshoot))
 (.split 2 3 4
 (.split 1 4 6
 (.tighten 0 7 8
 (.tighten 5 2 4
 .overshoot))
 .overshoot)
 .overshoot))
 .overshoot))))))))

theorem check37 : check ![3, 5, 7, 11, 13, 17, 19, 37] ![1, 2, 1, 2, 1, 2, 1, 1] (fun _ => none) cert37 = true := by
  decide +kernel

theorem exponent_bridge {n : ℕ} (hn : Odd n) (p : Exponents)
    (himg : Finset.univ.image p = n.primeFactors) (hinj : Function.Injective p)
    (heq : sigma 1 n = 3 * n + 5) :
    ∃ e : Exponents, (∀ i, 1 ≤ e i) ∧ divisorSum p e = 3 * value p e + 5 := by
  let e : Exponents := fun i => n.factorization (p i)
  have hn0 : n ≠ 0 := by
    obtain ⟨k, hk⟩ := hn
    omega
  have hmem (i : Fin 8) : p i ∈ n.primeFactors :=
    himg ▸ Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩
  have he (i : Fin 8) : 1 ≤ e i := Nat.one_le_iff_ne_zero.mpr
    (Finsupp.mem_support_iff.mp (Nat.support_factorization n ▸ hmem i))
  have hvalue : value p e = n := by
    unfold value
    have hprod := (Nat.prod_primeFactors_pow_factorization hn0).symm
    rw [← himg, Finset.prod_image (fun a _ b _ hab => hinj hab)] at hprod
    exact hprod
  have hsum : divisorSum p e = sigma 1 n := by
    have hfactor : sigma 1 n =
        ∏ q ∈ n.primeFactors, sigma 1 (q ^ n.factorization q) := by
      rw [isMultiplicative_sigma.multiplicative_factorization _ hn0]
      simp [Finsupp.prod, Nat.support_factorization]
    rw [← himg, Finset.prod_image (fun a _ b _ hab => hinj hab)] at hfactor
    rw [hfactor]
    unfold divisorSum
    apply Finset.prod_congr rfl
    intro i _
    rw [sigma_one_apply_prime_pow (Nat.prime_of_mem_primeFactors (hmem i)),
      SigmaAbundancyBounds.geometric_eq_sum]
  exact ⟨e, he, by rw [hvalue, hsum, heq]⟩

theorem exclude_profile {n : ℕ} (hn : Odd n) (p l : Exponents)
    (hp : ∀ i, 2 ≤ p i)
    (himg : Finset.univ.image p = n.primeFactors) (hinj : Function.Injective p)
    (hl : ∀ i, l i = if p i % 3 = 2 then 2 else 1)
    (hAllowed : ∀ e : Exponents, divisorSum p e = 3 * value p e + 5 →
      ∀ i, Allowed (p i) (e i))
    (cert : Certificate) (hc : check p l (fun _ => none) cert = true)
    (heq : sigma 1 n = 3 * n + 5) : False := by
  obtain ⟨e, hpos, hprod⟩ := exponent_bridge hn p himg hinj heq
  have ha := hAllowed e hprod
  have habove : Above l e := by
    intro i
    rw [hl]
    split_ifs with h
    · have he := (ha i).1 h
      have := hpos i
      omega
    · exact hpos i
  exact sound hp ha hprod cert habove (by simp [Bounded]) hc

theorem solve_of_allowed
    (hAllowed : ∀ p e : Exponents, divisorSum p e = 3 * value p e + 5 →
      ∀ i, Allowed (p i) (e i)) : OMA.R_OeisA76495_conjecture_R1_H1_R1_H4_R1.H1 := by
  intro n hn hsupport heq
  obtain ⟨q, hq, hs⟩ := hsupport
  simp only [Finset.mem_insert, Finset.mem_singleton] at hq
  rcases hq with rfl | rfl | rfl | rfl
  · apply exclude_profile hn ![3, 5, 7, 11, 13, 17, 19, 23]
        ![1, 2, 1, 2, 1, 2, 1, 2] _ _ _ _ _ cert23 check23 heq
    · decide +kernel
    · rw [hs]
      decide +kernel
    · change ∀ a b : Fin 8, _ → a = b
      decide +kernel
    · decide +kernel
    · exact hAllowed _
  · apply exclude_profile hn ![3, 5, 7, 11, 13, 17, 19, 29]
        ![1, 2, 1, 2, 1, 2, 1, 2] _ _ _ _ _ cert29 check29 heq
    · decide +kernel
    · rw [hs]
      decide +kernel
    · change ∀ a b : Fin 8, _ → a = b
      decide +kernel
    · decide +kernel
    · exact hAllowed _
  · apply exclude_profile hn ![3, 5, 7, 11, 13, 17, 19, 31]
        ![1, 2, 1, 2, 1, 2, 1, 1] _ _ _ _ _ cert31 check31 heq
    · decide +kernel
    · rw [hs]
      decide +kernel
    · change ∀ a b : Fin 8, _ → a = b
      decide +kernel
    · decide +kernel
    · exact hAllowed _
  · apply exclude_profile hn ![3, 5, 7, 11, 13, 17, 19, 37]
        ![1, 2, 1, 2, 1, 2, 1, 1] _ _ _ _ _ cert37 check37 heq
    · decide +kernel
    · rw [hs]
      decide +kernel
    · change ∀ a b : Fin 8, _ → a = b
      decide +kernel
    · decide +kernel
    · exact hAllowed _

end SigmaEightBoxes

theorem OMA.solution : OMA.R_OeisA76495_conjecture_R1_H1_R1_H4_R1.H1 :=
  SigmaEightBoxes.solve_of_allowed SigmaEightBoxes.allowed_of_equation
