import OMAReductions.R_OeisA76495_conjecture_R1_H1_R1_H4_R1_H2_R1_H2_R1
import Mathlib

/-!
The eight-prime prefix either already exceeds abundancy three, or its
checked upper abundancy bounds the ninth prime. The four certificates
partition the allowed exponent tuples using only modulo-three exclusions.
-/

open scoped BigOperators

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

theorem geometric_product_scaled_mono {ι : Type*}
    (I : Finset ι) (p a b : ι → ℕ) (hexp : ∀ i ∈ I, a i ≤ b i) :
    (∏ i ∈ I, geometric (p i) (a i)) * (∏ i ∈ I, p i ^ b i) ≤
      (∏ i ∈ I, geometric (p i) (b i)) * (∏ i ∈ I, p i ^ a i) := by
  rw [← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]
  exact Finset.prod_le_prod (fun _ _ => Nat.zero_le _)
    (fun i hi => geometric_scaled_mono (p i) (hexp i hi))

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

end SigmaEightBoxes

open SigmaAbundancyBounds SigmaEightBoxes

namespace SigmaNineTailBoxes
open SigmaAbundancyBounds SigmaEightBoxes

private theorem positive_value (p e : Exponents) (hp : ∀ i, 2 ≤ p i) :
    0 < value p e := Finset.prod_pos (fun i _ => pow_pos (by have := hp i; omega) _)

private theorem positive_den (p : Exponents) (u : Ceiling) (hp : ∀ i, 2 ≤ p i) :
    0 < upperDen p u := by
  apply Finset.prod_pos
  intro i _
  have hi := hp i
  cases h : u i with
  | none => exact Nat.sub_pos_of_lt (by omega)
  | some b => exact pow_pos (by omega) _

private theorem upper_limit {p e : Exponents} {u : Ceiling} (hp : ∀ i, 2 ≤ p i)
    (hu : Bounded e u) :
    divisorSum p e * upperDen p u ≤ upperNum p u * value p e := by
  have hb (i : Fin 8) : geometric (p i) (e i) * denominator (p i) (u i) ≤
      numerator (p i) (u i) * p i ^ e i := by
    cases h : u i with
    | none => exact geometric_upper (p i) (e i) (by have := hp i; omega)
    | some b => exact geometric_scaled_mono (p i) (hu i b h)
  unfold divisorSum upperDen upperNum value
  rw [← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]
  exact Finset.prod_le_prod (fun _ _ => Nat.zero_le _) (fun i _ => hb i)

private theorem geo_ge_pow (q t : ℕ) : q^t ≤ geometric q t := by
  rw [geometric_eq_sum]
  exact Finset.single_le_sum (fun _ _ => Nat.zero_le _)
    (Finset.mem_range.mpr (Nat.lt_succ_self _))

private theorem overshoot_tail {p e l : Exponents} {q t : ℕ}
    (hp : ∀ i, 2 ≤ p i) (hq : 5 < q) (ht : 1 ≤ t)
    (hl : Above l e) (hlarge : 3 * value p l < divisorSum p l)
    (heq : divisorSum p e * geometric q t = 3 * (value p e * q^t) + 5) : False := by
  have hratio : divisorSum p l * value p e ≤ divisorSum p e * value p l :=
    geometric_product_scaled_mono Finset.univ p l e (fun i _ => hl i)
  have hscaled := Nat.mul_lt_mul_of_pos_right hlarge (positive_value p e hp)
  have hpos := positive_value p l hp
  have hstrict : 3 * value p e < divisorSum p e := by
    by_contra! h
    have hh := Nat.mul_le_mul_right (value p l) h
    nlinarith only [hratio, hscaled, hh]
  have hnext : 3 * value p e + 1 ≤ divisorSum p e := by omega
  have hq1 : 1 ≤ q := by omega
  have hqPow : q ≤ q^t := by
    simpa only [pow_one] using Nat.pow_le_pow_right hq1 ht
  have hprod := Nat.mul_le_mul hnext (geo_ge_pow q t)
  nlinarith only [hprod, heq, hqPow, hq]

private theorem cap_tail {p e : Exponents} {u : Ceiling} {q t c : ℕ}
    (hp : ∀ i, 2 ≤ p i) (hq : 5 < q)
    (hu : Bounded e u) (hcap : upperNum p u * (c+1) ≤ 3 * upperDen p u * c)
    (heq : divisorSum p e * geometric q t = 3 * (value p e * q^t) + 5) : q ≤ c := by
  by_contra! hqGt
  let X := upperNum p u
  let Y := upperDen p u
  let S := divisorSum p e
  let N := value p e
  let R := geometric q t
  let P := q ^ t
  change X * (c+1) ≤ 3*Y*c at hcap
  have hXY : X ≤ 3*Y := by
    by_contra! h
    have hs := Nat.mul_lt_mul_of_pos_right h (Nat.succ_pos c)
    have hm := Nat.mul_le_mul_left (3*Y) (show c ≤ c+1 by omega)
    nlinarith only [hs, hm, hcap]
  have hc : X*q ≤ 3*Y*(q-1) := by
    obtain ⟨d, hd⟩ := Nat.exists_eq_add_of_le (show c+1 ≤ q by omega)
    rw [hd, show (c+1+d)-1 = c+d by omega]
    have hAdd := Nat.add_le_add hcap (Nat.mul_le_mul_right d hXY)
    nlinarith only [hAdd]
  have hN : S*Y ≤ X*N := upper_limit hp hu
  have hQ : R*(q-1) ≤ q*P := geometric_upper q t (by omega)
  have hY : 0 < Y := positive_den p u hp
  have hden : 0 < Y*(q-1) := mul_pos hY (by omega)
  have hprod := Nat.mul_le_mul hN hQ
  have hr := Nat.mul_le_mul_right (N*P) hc
  change S*R = 3*(N*P)+5 at heq
  have he := congrArg (fun a : ℕ => a*(Y*(q-1))) heq
  nlinarith only [hprod, hr, he, hden]

inductive BoundCertificate
  | overshoot
  | cap
  | split (i : Fin 8) (cut next : ℕ) (below above : BoundCertificate)

def checkBound (p l : Exponents) (u : Ceiling) (c : ℕ) : BoundCertificate → Bool
  | .overshoot => decide (3 * value p l < divisorSum p l)
  | .cap => decide (upperNum p u * (c+1) ≤ 3 * upperDen p u * c)
  | .split i cut next below above =>
      decide (skips (p i) cut next) &&
      checkBound p l (Function.update u i (some cut)) c below &&
      checkBound p (Function.update l i next) u c above

theorem bound_sound {p e : Exponents} {q t : ℕ} (hp : ∀ i, 2 ≤ p i)
    (ha : ∀ i, Allowed (p i) (e i)) (hq : 5 < q) (ht : 1 ≤ t)
    (heq : divisorSum p e * geometric q t = 3 * (value p e * q^t) + 5)
    (cert : BoundCertificate) {l : Exponents} {u : Ceiling} {c : ℕ}
    (hl : Above l e) (hu : Bounded e u) (hc : checkBound p l u c cert = true) : q ≤ c := by
  induction cert generalizing l u with
  | overshoot => exact (overshoot_tail hp hq ht hl (of_decide_eq_true hc) heq).elim
  | cap => exact cap_tail hp hq hu (of_decide_eq_true hc) heq
  | split i cut next below above ihBelow ihAbove =>
      simp only [checkBound, Bool.and_eq_true, decide_eq_true_eq] at hc
      obtain ⟨⟨hskip, hbelow⟩, habove⟩ := hc
      by_cases h : e i ≤ cut
      · exact ihBelow hl (upper_update hu h) hbelow
      · exact ihAbove (lower_update hl (lower_of_skip hskip (ha i) (by omega))) hu habove

def cert23 : BoundCertificate :=
 (.split 0 3 4
  (.split 0 2 3
   .cap
   (.split 1 2 4
    .cap
    (.split 2 1 3
     .cap
     (.split 4 1 3
      (.split 1 4 6
       .cap
       (.split 2 3 4
        .cap
        (.split 3 2 4
         .cap
         (.split 5 2 4
          (.split 2 4 6
           (.split 1 6 8
            (.split 6 3 4
             (.split 3 4 6
              .cap
              (.split 6 1 3
               .cap
               (.split 7 2 4
                .cap
                .overshoot)))
             (.split 7 2 4
              .cap
              .overshoot))
            (.split 6 1 3
             .cap
             (.split 7 2 4
              .cap
              .overshoot)))
           (.split 6 1 3
            .cap
            (.split 7 2 4
             (.split 1 8 10
              (.split 1 6 8
               .cap
               (.split 2 7 9
                .cap
                (.split 3 6 8
                 .cap
                 (.split 6 4 6
                  .cap
                  .overshoot))))
              (.split 2 6 7
               .cap
               (.split 3 4 6
                .cap
                (.split 6 4 6
                 (.split 2 7 9
                  .cap
                  (.split 6 3 4
                   .cap
                   .overshoot))
                 .overshoot))))
             .overshoot)))
          (.split 6 1 3
           .cap
           .overshoot)))))
      .overshoot))))
  (.split 1 2 4
   (.split 2 1 3
    .cap
    (.split 4 1 3
     (.split 0 4 5
      (.split 2 3 4
       (.split 3 2 4
        .cap
        (.split 5 2 4
         .cap
         (.split 6 1 3
          .cap
          .overshoot)))
       (.split 3 2 4
        .cap
        (.split 6 1 3
         .cap
         .overshoot)))
      (.split 6 1 3
       (.split 0 5 6
        (.split 2 3 4
         (.split 3 2 4
          .cap
          (.split 5 2 4
           .cap
           .overshoot))
         (.split 3 2 4
          .cap
          .overshoot))
        (.split 3 2 4
         (.split 0 6 7
          (.split 2 3 4
           (.split 5 2 4
            (.split 7 2 4
             .cap
             .overshoot)
            .overshoot)
           .overshoot)
          .overshoot)
         .overshoot))
       .overshoot))
     .overshoot))
   (.split 2 1 3
    .cap
    .overshoot)))

set_option maxHeartbeats 3000000 in
theorem check23 : checkBound ![3, 5, 7, 11, 13, 17, 19, 23] ![1, 2, 1, 2, 1, 2, 1, 2] (fun _ => none) 32931725 cert23 = true := by
  decide +kernel


def cert29 : BoundCertificate :=
 (.split 0 3 4
  .cap
  (.split 1 2 4
   (.split 0 5 6
    .cap
    (.split 2 1 3
     .cap
     (.split 3 2 4
      (.split 0 6 7
       (.split 2 4 6
        .cap
        (.split 4 3 4
         (.split 4 1 3
          .cap
          (.split 5 2 4
           .cap
           (.split 6 3 4
            .cap
            (.split 7 2 4
             .cap
             .overshoot))))
         (.split 5 2 4
          .cap
          (.split 6 1 3
           .cap
           (.split 7 2 4
            (.split 2 6 7
             .cap
             (.split 4 4 6
              .cap
              (.split 5 4 6
               (.split 6 4 6
                .cap
                .overshoot)
               (.split 6 3 4
                .cap
                .overshoot))))
            .overshoot)))))
       (.split 2 3 4
        (.split 0 8 9
         (.split 0 7 8
          .cap
          (.split 4 3 4
           .cap
           (.split 5 2 4
            .cap
            (.split 6 1 3
             .cap
             (.split 7 2 4
              .cap
              .overshoot)))))
         (.split 4 1 3
          .cap
          (.split 5 2 4
           .cap
           (.split 6 1 3
            .cap
            (.split 7 2 4
             (.split 4 3 4
              (.split 0 10 11
               (.split 0 9 10
                .cap
                (.split 5 4 6
                 (.split 6 4 6
                  .cap
                  .overshoot)
                 (.split 6 3 4
                  .cap
                  .overshoot)))
               (.split 6 3 4
                .cap
                .overshoot))
              .overshoot)
             .overshoot)))))
        (.split 4 1 3
         .cap
         (.split 6 1 3
          .cap
          .overshoot))))
      (.split 4 1 3
       .cap
       (.split 6 1 3
        .cap
        .overshoot)))))
   (.split 2 1 3
    .cap
    (.split 4 1 3
     (.split 0 4 5
      .cap
      (.split 6 1 3
       (.split 0 6 7
        (.split 0 5 6
         .cap
         (.split 1 4 6
          .cap
          (.split 2 4 6
           (.split 2 3 4
            .cap
            (.split 3 2 4
             .cap
             (.split 5 2 4
              .cap
              (.split 7 2 4
               (.split 1 6 8
                (.split 3 4 6
                 .cap
                 .overshoot)
                .overshoot)
               .overshoot))))
           (.split 3 2 4
            .cap
            (.split 5 2 4
             .cap
             .overshoot)))))
        (.split 1 4 6
         (.split 0 7 8
          (.split 2 4 6
           (.split 2 3 4
            .cap
            (.split 3 2 4
             .cap
             (.split 5 2 4
              .cap
              (.split 7 2 4
               (.split 3 4 6
                .cap
                .overshoot)
               .overshoot))))
           (.split 3 2 4
            .cap
            (.split 5 2 4
             .cap
             .overshoot)))
          (.split 2 3 4
           .cap
           (.split 3 2 4
            .cap
            (.split 5 2 4
             (.split 0 8 9
              (.split 2 7 9
               .cap
               (.split 3 6 8
                .cap
                (.split 7 4 6
                 .cap
                 .overshoot)))
              (.split 2 4 6
               .cap
               (.split 7 2 4
                (.split 0 10 11
                 (.split 0 9 10
                  .cap
                  (.split 3 4 6
                   .cap
                   .overshoot))
                 .overshoot)
                .overshoot)))
             .overshoot))))
         (.split 2 3 4
          (.split 0 7 8
           (.split 1 6 8
            .cap
            (.split 3 4 6
             .cap
             (.split 5 2 4
              .cap
              (.split 7 2 4
               .cap
               .overshoot))))
           (.split 3 2 4
            .cap
            (.split 5 2 4
             .cap
             .overshoot)))
          (.split 3 2 4
           .cap
           .overshoot))))
       .overshoot))
     .overshoot))))

set_option maxHeartbeats 3000000 in
theorem check29 : checkBound ![3, 5, 7, 11, 13, 17, 19, 29] ![1, 2, 1, 2, 1, 2, 1, 2] (fun _ => none) 57697901 cert29 = true := by
  decide +kernel


def cert31 : BoundCertificate :=
 (.split 0 4 5
  (.split 0 3 4
   .cap
   (.split 1 2 4
    .cap
    (.split 2 1 3
     .cap
     (.split 4 1 3
      .cap
      (.split 6 1 3
       (.split 1 4 6
        .cap
        (.split 2 4 6
         (.split 2 3 4
          .cap
          (.split 3 2 4
           .cap
           (.split 4 3 4
            .cap
            (.split 5 2 4
             .cap
             (.split 7 1 3
              .cap
              .overshoot)))))
         (.split 3 2 4
          .cap
          (.split 5 2 4
           .cap
           (.split 7 1 3
            .cap
            .overshoot)))))
       .overshoot)))))
  (.split 1 2 4
   .cap
   (.split 2 1 3
    .cap
    (.split 4 1 3
     (.split 0 6 7
      (.split 0 5 6
       .cap
       (.split 1 4 6
        (.split 2 3 4
         .cap
         (.split 3 2 4
          .cap
          (.split 5 2 4
           (.split 2 4 6
            (.split 3 4 6
             (.split 6 4 6
              .cap
              (.split 7 3 4
               .cap
               .overshoot))
             (.split 6 3 4
              .cap
              (.split 7 1 3
               .cap
               .overshoot)))
            (.split 6 1 3
             .cap
             (.split 7 1 3
              .cap
              .overshoot)))
           (.split 6 1 3
            .cap
            (.split 7 1 3
             .cap
             .overshoot)))))
        (.split 2 3 4
         (.split 3 2 4
          .cap
          (.split 5 2 4
           .cap
           (.split 6 1 3
            .cap
            (.split 7 1 3
             .cap
             .overshoot))))
         (.split 3 2 4
          .cap
          (.split 6 1 3
           .cap
           (.split 7 1 3
            .cap
            .overshoot))))))
      (.split 2 3 4
       (.split 1 4 6
        (.split 0 7 8
         (.split 3 2 4
          .cap
          (.split 5 2 4
           .cap
           (.split 6 1 3
            .cap
            (.split 7 1 3
             .cap
             .overshoot))))
         (.split 3 2 4
          .cap
          (.split 6 1 3
           .cap
           (.split 7 1 3
            .cap
            .overshoot))))
        (.split 3 2 4
         .cap
         (.split 6 1 3
          .cap
          (.split 7 1 3
           .cap
           .overshoot))))
       (.split 3 2 4
        (.split 0 7 8
         (.split 1 4 6
          .cap
          (.split 5 2 4
           .cap
           (.split 6 1 3
            .cap
            (.split 7 1 3
             .cap
             .overshoot))))
         (.split 1 4 6
          .cap
          (.split 5 2 4
           (.split 0 8 9
            (.split 2 4 6
             .cap
             (.split 6 1 3
              .cap
              (.split 7 1 3
               .cap
               .overshoot)))
            (.split 2 4 6
             (.split 0 9 10
              (.split 1 6 8
               (.split 6 3 4
                .cap
                (.split 7 1 3
                 .cap
                 .overshoot))
               (.split 6 1 3
                .cap
                (.split 7 1 3
                 .cap
                 .overshoot)))
              (.split 6 1 3
               .cap
               (.split 7 1 3
                .cap
                .overshoot)))
             (.split 6 1 3
              .cap
              (.split 7 1 3
               .cap
               .overshoot))))
           (.split 6 1 3
            .cap
            (.split 7 1 3
             .cap
             .overshoot)))))
        (.split 6 1 3
         .cap
         (.split 7 1 3
          (.split 0 10 11
           (.split 0 9 10
            .cap
            (.split 1 8 10
             .cap
             (.split 2 7 9
              .cap
              (.split 3 4 6
               .cap
               (.split 5 4 6
                .cap
                (.split 6 4 6
                 .cap
                 .overshoot))))))
           (.split 1 6 8
            .cap
            (.split 2 4 6
             .cap
             (.split 3 4 6
              .cap
              (.split 5 2 4
               .cap
               (.split 6 3 4
                .cap
                .overshoot))))))
          .overshoot)))))
     .overshoot))))

set_option maxHeartbeats 3000000 in
theorem check31 : checkBound ![3, 5, 7, 11, 13, 17, 19, 31] ![1, 2, 1, 2, 1, 2, 1, 1] (fun _ => none) 13410060 cert31 = true := by
  decide +kernel


def cert37 : BoundCertificate :=
 (.split 0 5 6
  (.split 0 4 5
   .cap
   (.split 1 4 6
    .cap
    (.split 2 3 4
     .cap
     (.split 3 2 4
      .cap
      (.split 4 1 3
       .cap
       (.split 5 2 4
        (.split 1 6 8
         (.split 2 6 7
          (.split 2 4 6
           .cap
           (.split 3 4 6
            .cap
            (.split 4 4 6
             .cap
             (.split 6 3 4
              .cap
              (.split 7 3 4
               .cap
               .overshoot)))))
          (.split 3 4 6
           .cap
           (.split 4 4 6
            .cap
            (.split 6 3 4
             .cap
             (.split 7 1 3
              .cap
              .overshoot)))))
         (.split 2 4 6
          .cap
          (.split 4 3 4
           .cap
           (.split 6 3 4
            (.split 3 4 6
             (.split 1 8 10
              (.split 2 7 9
               .cap
               (.split 4 4 6
                .cap
                (.split 6 1 3
                 .cap
                 (.split 7 3 4
                  .cap
                  .overshoot))))
              (.split 2 6 7
               .cap
               (.split 4 4 6
                .cap
                (.split 6 1 3
                 .cap
                 (.split 7 3 4
                  (.split 2 7 9
                   .cap
                   (.split 7 1 3
                    .cap
                    .overshoot))
                  .overshoot)))))
             (.split 6 1 3
              .cap
              (.split 7 1 3
               .cap
               .overshoot)))
            (.split 7 1 3
             .cap
             .overshoot)))))
        (.split 6 1 3
         .cap
         (.split 7 1 3
          .cap
          .overshoot))))))))
  (.split 1 2 4
   .cap
   (.split 2 1 3
    .cap
    (.split 3 2 4
     (.split 0 6 7
      (.split 1 4 6
       (.split 2 4 6
        (.split 2 3 4
         .cap
         (.split 4 4 6
          .cap
          (.split 5 2 4
           .cap
           (.split 6 3 4
            .cap
            (.split 7 1 3
             .cap
             .overshoot)))))
        (.split 4 1 3
         .cap
         (.split 5 2 4
          .cap
          (.split 6 1 3
           .cap
           (.split 7 1 3
            .cap
            .overshoot)))))
       (.split 2 3 4
        .cap
        (.split 4 1 3
         .cap
         (.split 6 1 3
          .cap
          (.split 7 1 3
           .cap
           .overshoot)))))
      (.split 2 3 4
       (.split 1 4 6
        (.split 0 7 8
         .cap
         (.split 4 1 3
          .cap
          (.split 5 2 4
           .cap
           (.split 6 1 3
            .cap
            (.split 7 1 3
             .cap
             .overshoot)))))
        (.split 4 1 3
         .cap
         (.split 6 1 3
          .cap
          (.split 7 1 3
           .cap
           .overshoot))))
       (.split 4 1 3
        .cap
        (.split 6 1 3
         .cap
         (.split 7 1 3
          (.split 0 8 9
           (.split 0 7 8
            .cap
            (.split 1 4 6
             .cap
             (.split 2 4 6
              .cap
              (.split 5 2 4
               .cap
               .overshoot))))
           (.split 1 4 6
            .cap
            (.split 2 4 6
             (.split 4 3 4
              (.split 0 10 11
               (.split 0 9 10
                .cap
                (.split 1 6 8
                 .cap
                 (.split 5 2 4
                  .cap
                  (.split 6 3 4
                   (.split 5 4 6
                    .cap
                    .overshoot)
                   .overshoot))))
               (.split 1 6 8
                (.split 0 12 13
                 (.split 0 11 12
                  .cap
                  (.split 5 4 6
                   .cap
                   (.split 6 3 4
                    .cap
                    .overshoot)))
                 (.split 5 4 6
                  (.split 5 2 4
                   .cap
                   (.split 6 4 6
                    (.split 0 15 16
                     .cap
                     (.split 6 3 4
                      .cap
                      .overshoot))
                    .overshoot))
                  (.split 6 3 4
                   .cap
                   .overshoot)))
                (.split 5 2 4
                 .cap
                 .overshoot)))
              (.split 5 2 4
               .cap
               .overshoot))
             (.split 5 2 4
              .cap
              .overshoot))))
          .overshoot)))))
     (.split 4 1 3
      .cap
      (.split 6 1 3
       .cap
       (.split 7 1 3
        (.split 0 6 7
         (.split 1 4 6
          (.split 2 4 6
           (.split 2 3 4
            .cap
            (.split 4 3 4
             .cap
             (.split 5 2 4
              .cap
              .overshoot)))
           (.split 5 2 4
            .cap
            .overshoot))
          (.split 2 3 4
           .cap
           .overshoot))
         (.split 2 3 4
          (.split 1 4 6
           (.split 0 7 8
            .cap
            (.split 5 2 4
             .cap
             .overshoot))
           .overshoot)
          .overshoot))
        .overshoot)))))))

set_option maxHeartbeats 3000000 in
theorem check37 : checkBound ![3, 5, 7, 11, 13, 17, 19, 37] ![1, 2, 1, 2, 1, 2, 1, 1] (fun _ => none) 68482549 cert37 = true := by
  decide +kernel

private theorem consistent_prefix_exponents (p e : Exponents) {q t : ℕ}
    (heq : divisorSum p e * geometric q t = 3 * (value p e * q^t) + 5) :
    ∀ i, Allowed (p i) (e i) := by
  have hz : (↑(divisorSum p e * geometric q t) : ZMod 3) = 2 := by
    rw [heq]
    push_cast
    have h3 : (3 : ZMod 3) = 0 := by decide
    rw [h3, zero_mul, zero_add]
    decide
  rw [Nat.cast_mul, divisorSum, Nat.cast_prod] at hz
  intro i
  have hne : (SigmaEightModThree.geometric (p i) (e i) : ZMod 3) ≠ 0 := by
    intro h
    have h' : (geometric (p i) (e i) : ZMod 3) = 0 := by
      simpa only [geometric_eq_sum, SigmaEightModThree.geometric] using h
    have hp : (∏ j : Fin 8, (geometric (p j) (e j) : ZMod 3)) = 0 :=
      Finset.prod_eq_zero (Finset.mem_univ i) h'
    rw [hp, zero_mul] at hz
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

private theorem apply_profile {p e : Fin 9 → ℕ} (hs : StrictMono p)
    (hp : ∀ i, (p i).Prime ∧ 3 ≤ p i) (he : ∀ i, 1 ≤ e i)
    (heq : (∏ i, ∑ j ∈ Finset.range (e i + 1), p i ^ j) = 3 * (∏ i, p i ^ e i) + 5)
    (r l : Exponents) (hr : (fun i : Fin 8 => p i.castSucc) = r) (hr7 : 5 < r 7)
    (hl : ∀ i, l i = if r i % 3 = 2 then 2 else 1) (c : ℕ) (cert : BoundCertificate)
    (hc : checkBound r l (fun _ => none) c cert = true) : p 8 ≤ c := by
  let f : Exponents := fun i => e i.castSucc
  have h5 : 5 < p 8 := by
    have h := congrFun hr (7 : Fin 8)
    have h7 : (7 : Fin 8).castSucc = (7 : Fin 9) := by decide
    change p ((7 : Fin 8).castSucc) = r 7 at h
    rw [h7] at h
    exact (h.symm ▸ hr7).trans (hs (by decide : (7 : Fin 9) < 8))
  have hr2 (i : Fin 8) : 2 ≤ r i := by
    rw [← hr]
    exact (hp i.castSucc).1.two_le
  have hlast : Fin.last 8 = (8 : Fin 9) := by decide
  have heq' : divisorSum r f * geometric (p 8) (e 8) =
      3 * (value r f * p 8 ^ e 8) + 5 := by
    have h := heq
    simp_rw [← geometric_eq_sum] at h
    rw [Fin.prod_univ_castSucc (fun i : Fin 9 => geometric (p i) (e i)),
      Fin.prod_univ_castSucc (fun i : Fin 9 => p i ^ e i), hlast] at h
    rw [← hr]
    exact h
  have ha := consistent_prefix_exponents r f heq'
  have hAbove : Above l f := by
    intro i
    rw [hl]
    split_ifs with h
    · have h2 := (ha i).1 h
      have h1 : 1 ≤ f i := he i.castSucc
      omega
    · exact he i.castSucc
  exact bound_sound hr2 ha h5 (he 8) heq' cert hAbove (by simp [Bounded]) hc

theorem solve : OMA.R_OeisA76495_conjecture_R1_H1_R1_H4_R1_H2_R1_H2_R1.H1 := by
  intro p e hs hp he hprefix hbig heq
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hprefix
  rcases hprefix with h | h | h | h
  · have hr : (fun i : Fin 8 => p i.castSucc) = (![3, 5, 7, 11, 13, 17, 19, 23] : Exponents) :=
      List.ofFn_injective (h.trans (by decide : List.ofFn (![3, 5, 7, 11, 13, 17, 19, 23] : Exponents) = [3, 5, 7, 11, 13, 17, 19, 23]).symm)
    have hb := apply_profile hs hp he heq ![3, 5, 7, 11, 13, 17, 19, 23] ![1, 2, 1, 2, 1, 2, 1, 2] hr (by decide)
      (by decide +kernel) 32931725 cert23 check23
    omega
  · have hr : (fun i : Fin 8 => p i.castSucc) = (![3, 5, 7, 11, 13, 17, 19, 29] : Exponents) :=
      List.ofFn_injective (h.trans (by decide : List.ofFn (![3, 5, 7, 11, 13, 17, 19, 29] : Exponents) = [3, 5, 7, 11, 13, 17, 19, 29]).symm)
    have hb := apply_profile hs hp he heq ![3, 5, 7, 11, 13, 17, 19, 29] ![1, 2, 1, 2, 1, 2, 1, 2] hr (by decide)
      (by decide +kernel) 57697901 cert29 check29
    omega
  · have hr : (fun i : Fin 8 => p i.castSucc) = (![3, 5, 7, 11, 13, 17, 19, 31] : Exponents) :=
      List.ofFn_injective (h.trans (by decide : List.ofFn (![3, 5, 7, 11, 13, 17, 19, 31] : Exponents) = [3, 5, 7, 11, 13, 17, 19, 31]).symm)
    have hb := apply_profile hs hp he heq ![3, 5, 7, 11, 13, 17, 19, 31] ![1, 2, 1, 2, 1, 2, 1, 1] hr (by decide)
      (by decide +kernel) 13410060 cert31 check31
    omega
  · have hr : (fun i : Fin 8 => p i.castSucc) = (![3, 5, 7, 11, 13, 17, 19, 37] : Exponents) :=
      List.ofFn_injective (h.trans (by decide : List.ofFn (![3, 5, 7, 11, 13, 17, 19, 37] : Exponents) = [3, 5, 7, 11, 13, 17, 19, 37]).symm)
    have hb := apply_profile hs hp he heq ![3, 5, 7, 11, 13, 17, 19, 37] ![1, 2, 1, 2, 1, 2, 1, 1] hr (by decide)
      (by decide +kernel) 68482549 cert37 check37
    omega

end SigmaNineTailBoxes

theorem OMA.solution : OMA.R_OeisA76495_conjecture_R1_H1_R1_H4_R1_H2_R1_H2_R1.H1 :=
  SigmaNineTailBoxes.solve
