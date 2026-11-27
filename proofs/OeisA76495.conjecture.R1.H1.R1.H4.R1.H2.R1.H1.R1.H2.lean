import OMAReductions.R_OeisA76495_conjecture_R1_H1_R1_H4_R1_H2_R1_H1_R1
import Mathlib

/-!
Every bounded nine-prime support is enumerated using checked limiting
abundancy inequalities. For each support the packed certificate partitions
the allowed exponent tuples into disjoint boxes and checks exclusion of
every box by exact arithmetic. Digits are base 32, least significant first.
The first nine digits are the lower exponent bounds. They are followed by
the certificate digits, whose tags are 0 for overshoot, 1 for tightening,
and 2 for a split. The checker verifies each skipped exponent by divisibility
against every support prime other than five.
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

/-- Lower bounds on each ordered prime give an upper bound on the full
abundancy product. -/
theorem product_profile_bound {ι : Type*} (I : Finset ι) (p q e : ι → ℕ)
    (hq : ∀ i ∈ I, 2 ≤ q i) (hp : ∀ i ∈ I, q i ≤ p i) :
    (∏ i ∈ I, geometric (p i) (e i))*(∏ i ∈ I, (q i-1)) ≤
      (∏ i ∈ I, q i)*(∏ i ∈ I, p i ^ e i) := by
  rw [← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]
  exact Finset.prod_le_prod (fun _ _ => Nat.zero_le _)
    (fun i hi => geometric_lower_base_bound (hq i hi) (hp i hi))

end SigmaAbundancyBounds

namespace SigmaLocalModuliFast
open SigmaAbundancyBounds

def Allowed {k : ℕ} (p : Fin k → ℕ) (q e : ℕ) : Prop :=
  ∀ j, p j ≠ 5 → ¬ p j ∣ geometric q e

instance {k : ℕ} (p : Fin k → ℕ) (q e : ℕ) : Decidable (Allowed p q e) :=
  inferInstanceAs (Decidable (∀ j, p j ≠ 5 → ¬ p j ∣ geometric q e))

def skipped {k : ℕ} (p : Fin k → ℕ) (q c u : ℕ) : Prop :=
  ∀ i : Fin u, c < i.val → ¬ Allowed p q i.val

instance {k : ℕ} (p : Fin k → ℕ) (q c u : ℕ) : Decidable (skipped p q c u) :=
  inferInstanceAs (Decidable (∀ i : Fin u, c < i.val → ¬ Allowed p q i.val))

def allowedB {k : ℕ} (p : Fin k → ℕ) (q e : ℕ) : Bool :=
  let sum := geometric q e
  (List.ofFn p).all (fun r => r == 5 || sum % r != 0)

theorem allowedB_true {k : ℕ} (p : Fin k → ℕ) (q e : ℕ)
    (h : Allowed p q e) : allowedB p q e = true := by
  apply List.all_eq_true.mpr
  intro r hr
  obtain ⟨j, rfl⟩ := List.mem_ofFn.mp hr
  by_cases h5 : p j = 5
  · simp [h5]
  · have hd := h j h5
    have hn : geometric q e % p j ≠ 0 := fun hz =>
      hd (Nat.dvd_iff_mod_eq_zero.mpr hz)
    simp [h5, hn]

def skippedB {k : ℕ} (p : Fin k → ℕ) (q c u : ℕ) : Bool :=
  (List.range' (c+1) (u-(c+1))).all (fun e => !allowedB p q e)

theorem skippedB_sound {k : ℕ} {p : Fin k → ℕ} {q c u : ℕ}
    (hs : skippedB p q c u = true) : skipped p q c u := by
  intro a hc ha
  have hm : a.val ∈ List.range' (c+1) (u-(c+1)) := List.mem_range'_1.mpr
    ⟨by omega, by have := a.isLt; omega⟩
  have htest := List.all_eq_true.mp hs _ hm
  rw [allowedB_true p q a.val ha] at htest
  contradiction

theorem lower_of_skipped {k : ℕ} {p : Fin k → ℕ} {q c u e : ℕ}
    (hs : skipped p q c u) (ha : Allowed p q e) (hc : c < e) : u ≤ e := by
  by_contra! hn
  exact hs ⟨e, hn⟩ hc ha

theorem allowed_of_equation {k : ℕ} (p e : Fin k → ℕ)
    (hp : ∀ i, (p i).Prime) (he : ∀ i, 1 ≤ e i)
    {v s : ℕ}
    (heq : (∏ i, geometric (p i) (e i)) * s =
      3 * ((∏ i, p i ^ e i) * v) + 5) : ∀ i, Allowed p (p i) (e i) := by
  intro i j hj hdiv
  have hpN : p j ∣ ∏ i, p i ^ e i := by
    have hdvd : p j ∣ p j ^ e j := dvd_pow_self _ (by have := he j; omega)
    exact hdvd.trans (Finset.dvd_prod_of_mem _ (Finset.mem_univ _))
  have hpS : p j ∣ ∏ i, geometric (p i) (e i) :=
    hdiv.trans (Finset.dvd_prod_of_mem _ (Finset.mem_univ _))
  have hk : p j ∣ 3 * ((∏ i, p i ^ e i) * v) :=
    dvd_mul_of_dvd_right (dvd_mul_of_dvd_left hpN _) _
  have hwhole := dvd_mul_of_dvd_left hpS s
  rw [heq] at hwhole
  have h5 : p j ∣ 5 := (Nat.dvd_add_iff_right hk).mpr hwhole
  rcases (Nat.dvd_prime Nat.prime_five).mp h5 with h | h
  · exact (hp j).ne_one h
  · exact hj h

end SigmaLocalModuliFast

namespace SigmaNineBoxesFast
open SigmaAbundancyBounds SigmaLocalModuliFast

abbrev Exponents := Fin 9 → ℕ
abbrev Ceiling := Fin 9 → Option ℕ

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
  have hb (i : Fin 9) : geometric (p i) (e i) * denominator (p i) (u i) ≤
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

theorem lower_update {e l : Exponents} {i : Fin 9} {k : ℕ} (hl : Above l e)
    (hk : k ≤ e i) : Above (Function.update l i k) e := by
  intro j
  by_cases h : j = i
  · subst j
    simpa using hk
  · simpa [Function.update_of_ne h] using hl j

theorem upper_update {e : Exponents} {u : Ceiling} {i : Fin 9} {k : ℕ}
    (hu : Bounded e u) (hk : e i ≤ k) : Bounded e (Function.update u i (some k)) := by
  intro j b hj
  by_cases h : j = i
  · subst j
    have : k = b := by simpa using hj
    simpa [← this] using hk
  · apply hu j b
    simpa [Function.update_of_ne h] using hj

inductive Certificate
  | overshoot
  | tighten (i : Fin 9) (cut next : ℕ) (child : Certificate)
  | split (i : Fin 9) (cut next : ℕ) (below above : Certificate)

def check (p l : Exponents) (u : Ceiling) : Certificate → Bool
  | .overshoot => decide (3 * value p l + 5 < divisorSum p l)
  | .tighten i cut next child =>
      let bound := Function.update u i (some cut)
      decide (upperNum p bound ≤ 3 * upperDen p bound) &&
      skippedB p (p i) cut next &&
      check p (Function.update l i next) u child
  | .split i cut next below above =>
      skippedB p (p i) cut next &&
      check p l (Function.update u i (some cut)) below &&
      check p (Function.update l i next) u above

theorem sound {p e : Exponents} (hp : ∀ i, 2 ≤ p i)
    (ha : ∀ i, Allowed p (p i) (e i))
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
      exact ih (lower_update hl (lower_of_skipped (skippedB_sound hskip) (ha i) hcut)) hu hchild
  | split i cut next below above ihBelow ihAbove =>
      simp only [check, Bool.and_eq_true] at hc
      obtain ⟨⟨hskip, hbelow⟩, habove⟩ := hc
      by_cases h : e i ≤ cut
      · exact ihBelow hl (upper_update hu h) hbelow
      · exact ihAbove (lower_update hl (lower_of_skipped (skippedB_sound hskip) (ha i) (by omega))) hu habove


def decode : ℕ → ℕ → Option (Certificate × ℕ)
  | 0, _ => none
  | fuel + 1, n =>
      let tag := n % 32
      if tag = 0 then some (.overshoot, n / 32)
      else if tag = 1 ∨ tag = 2 then do
        let axis := (n / 32) % 32
        let cut := (n / 1024) % 32
        let next := (n / 32768) % 32
        if h : axis < 9 then
          let (below, rest) ← decode fuel (n / 1048576)
          if tag = 1 then some (.tighten ⟨axis,h⟩ cut next below, rest)
          else do
            let (above, tail) ← decode fuel rest
            pure (.split ⟨axis,h⟩ cut next below above, tail)
        else none
      else none

def profileOf (ps : List ℕ) (i : Fin 9) : ℕ := ps[i.val]?.getD 0

def initial (n : ℕ) : Exponents := fun i => (n / 32^i.val) % 32

def verifyPacked (ps : List ℕ) (n : ℕ) : Bool :=
  let p := profileOf ps
  let l := initial n
  match decode 128 (n / 32^9) with
  | some (cert, _) =>
      (List.ofFn fun i : Fin 9 => skippedB p (p i) 0 (l i)).all id &&
      check p l (fun _ => none) cert
  | none => false

theorem packed_sound {ps : List ℕ} {w : ℕ}
    (hc : verifyPacked ps w = true) (e : Exponents)
    (hp : ∀ i, (profileOf ps i).Prime) (he : ∀ i, 1 ≤ e i)
    (hs : divisorSum (profileOf ps) e = 3 * value (profileOf ps) e + 5) : False := by
  unfold verifyPacked at hc
  split at hc
  next cert rest h =>
    simp only [Bool.and_eq_true] at hc
    have ha := SigmaLocalModuliFast.allowed_of_equation (profileOf ps) e hp he
      (s := 1) (v := 1) (by simpa only [divisorSum, value, Nat.mul_one] using hs)
    have habove : Above (initial w) e := by
      intro i
      have hm : skippedB (profileOf ps) (profileOf ps i) 0 (initial w i) ∈
          List.ofFn (fun j : Fin 9 => skippedB (profileOf ps) (profileOf ps j) 0 (initial w j)) :=
        List.mem_ofFn.mpr ⟨i, rfl⟩
      have ht := List.all_eq_true.mp hc.1 _ hm
      exact lower_of_skipped (skippedB_sound ht) (ha i) (he i)
    exact sound (fun i => (hp i).two_le) ha hs cert habove (by simp [Bounded]) hc.2
  next => contradiction

end SigmaNineBoxesFast

open SigmaAbundancyBounds SigmaNineBoxesFast

namespace SigmaNine

def caps : Fin 8 → ℕ := ![8, 12, 15, 19, 23, 28, 38, 77]

def prefixes (prev : ℕ) : List ℕ → List (List ℕ)
  | [] => [[]]
  | cap :: caps =>
      ((List.range (cap + 1)).filter (fun p => decide (prev < p ∧ p.Prime))).flatMap
        (fun p => (prefixes p caps).map (p :: ·))

def den (ps : List ℕ) : ℕ := (ps.map (· - 1)).prod

private theorem mem_prefixes {s caps : List ℕ} {prev : ℕ}
    (hs : List.Forall₂ (fun p c => p ≤ c ∧ p.Prime) s caps)
    (hp : (prev :: s).Pairwise (· < ·)) : s ∈ prefixes prev caps := by
  induction hs generalizing prev with
  | nil => simp [prefixes]
  | @cons p cap s caps hc tail ih =>
      obtain ⟨hbefore, hafter⟩ := List.pairwise_cons.mp hp
      apply List.mem_flatMap.mpr
      have hlt : prev < p := hbefore p (by simp)
      refine ⟨p, ?_, List.mem_map.mpr ⟨s, ih hafter, rfl⟩⟩
      exact List.mem_filter.mpr ⟨List.mem_range.mpr (Nat.lt_succ_of_le hc.1),
        decide_eq_true ⟨hlt, hc.2⟩⟩

theorem profile_prefix_mem (p : Fin 9 → ℕ) (hs : StrictMono p)
    (hp : ∀ i, (p i).Prime) (hlo : ∀ i, 3 ≤ p i)
    (hc : ∀ i : Fin 8, p i.castSucc ≤ caps i) :
    List.ofFn (fun i : Fin 8 => p i.castSucc) ∈ prefixes 2 (List.ofFn caps) := by
  apply mem_prefixes
  · rw [List.forall₂_iff_get]
    refine ⟨by simp, ?_⟩
    intro i hi hj
    have h8 : i < 8 := by simpa using hi
    simpa only [List.get_eq_getElem, List.getElem_ofFn] using And.intro (hc ⟨i,h8⟩) (hp (Fin.castSucc ⟨i,h8⟩))
  · apply List.pairwise_cons.mpr
    constructor
    · intro a ha
      obtain ⟨i, rfl⟩ := List.mem_ofFn.mp ha
      exact hlo i.castSucc
    · rw [List.pairwise_ofFn]
      intro i j hij
      exact hs (show i.castSucc < j.castSucc from hij)

def start (ps : List ℕ) : ℕ := ps.getLastD 2 + 1

def lastCap (ps : List ℕ) : ℕ :=
  min 3009 ((3 * den ps) / (3 * den ps - ps.prod))

def viablePrefixes : List (List ℕ) :=
  (prefixes 2 (List.ofFn caps)).filter fun ps =>
    decide (ps.prod < 3 * den ps ∧
      3 * den ps * (start ps - 1) < ps.prod * start ps)

theorem qualify_prefix {ps : List ℕ} (hm : ps ∈ prefixes 2 (List.ofFn caps))
    {q : ℕ} (hp : q.Prime) (hq : q ≤ 3009) (hq2 : 2 < q) (hs : ∀ a ∈ ps, a < q)
    (hsmall : ps.prod < 3 * den ps)
    (hlarge : 3 * den ps * (q-1) < ps.prod * q) :
    ps ∈ viablePrefixes ∧ start ps ≤ q ∧ q ≤ lastCap ps := by
  have hstart : start ps ≤ q := by
    unfold start
    rcases List.mem_cons.mp (List.getLastD_mem_cons (a := 2) (l := ps)) with h | h
    · omega
    · exact hs _ h
  let D := 3 * den ps
  let M := ps.prod
  let δ := D - M
  have hδpos : 0 < δ := Nat.sub_pos_of_lt hsmall
  have hδ : δ + M = D := Nat.sub_add_cancel hsmall.le
  have hqsub : q - 1 + 1 = q := Nat.sub_add_cancel hp.pos
  have hlo := congrArg (fun t : ℕ => t * q) hδ
  have hhi := congrArg (fun t : ℕ => D * t) hqsub
  change D * (q-1) < M * q at hlarge
  have hcut : δ * q < D := by nlinarith only [hlo, hhi, hlarge]
  have hqBound : q ≤ D / δ := by
    apply (Nat.le_div_iff_mul_le hδpos).mpr
    nlinarith only [hcut]
  have hcap := le_min hq hqBound
  have hpos : 0 < start ps := Nat.succ_pos _
  have hsub : start ps - 1 + 1 = start ps := Nat.sub_add_cancel hpos
  have hdelta := congrArg (fun t : ℕ => t * start ps) hδ
  have hrest := congrArg (fun t : ℕ => D * t) hsub
  have hsl := Nat.mul_le_mul_left δ hstart
  have hfirst : D * (start ps - 1) < M * start ps := by
    nlinarith only [hdelta, hrest, hcut, hsl]
  exact ⟨List.mem_filter.mpr ⟨hm, decide_eq_true ⟨hsmall,hfirst⟩⟩, hstart, hcap⟩

def candidateFinals (ps : List ℕ) (low count : ℕ) : List ℕ :=
  let D := 3 * den ps
  let M := ps.prod
  (List.range' low count).filter
    (fun q => decide (q.Prime ∧ D * (q-1) < M * q))

theorem checked_window {ps : List ℕ} {lo count q : ℕ}
    {rows : List (ℕ × ℕ)}
    (hrows : rows.map Prod.fst = candidateFinals ps lo count)
    (hcheck : rows.all (fun x => verifyPacked (ps ++ [x.1]) x.2) = true)
    (hlo : lo ≤ q) (hhi : q < lo + count) (hp : q.Prime)
    (hlarge : 3 * den ps * (q-1) < ps.prod * q) :
    ∃ w, verifyPacked (ps ++ [q]) w = true := by
  have hm : q ∈ candidateFinals ps lo count :=
    List.mem_filter.mpr ⟨List.mem_range'_1.mpr ⟨hlo,hhi⟩, decide_eq_true ⟨hp,hlarge⟩⟩
  rw [← hrows] at hm
  obtain ⟨⟨q', w⟩, hr, eq⟩ := List.mem_map.mp hm
  change q' = q at eq
  subst q'
  exact ⟨w, List.all_eq_true.mp hcheck _ hr⟩
def ps10 : List ℕ := [3, 5, 7, 11, 13, 17, 23, 31]

def window10_0g0 : List (ℕ × ℕ) := [
  (37, 0x618023088430802109044204c1),
  (41, 0xc3002609c4618023088430802209044204c1),
  (43, 0x41142c3804609c2730023088430802409044204c1),
  (47, 0x3088230802209044204c1),
  (53, 0x3088230802609044204c1),
  (59, 0x3088230802209044204c1),
  (61, 0x62102620c2a30444114241884609c4618043088230802409044204c1),
  (67, 0x3088261802409044204c1),
  (71, 0x3088261802209044204c1),
  (73, 0x3088261802109044204c1),
  (79, 0x3088261802109044204c1),
  (83, 0x3088261802209044204c1),
  (89, 0x3088261802209044204c1)
]

set_option maxHeartbeats 6000000 in
theorem window10_0g0_valid : window10_0g0.all (fun x => verifyPacked (ps10 ++ [x.1]) x.2) = true := by
  decide +kernel

def window10_0g1 : List (ℕ × ℕ) := [
  (97, 0x3088261802609044204c1),
  (101, 0x3088261802209044204c1),
  (103, 0x3088261802609044204c1),
  (107, 0x3088261802409044204c1),
  (109, 0x3088261802609044204c1),
  (113, 0x3088261802a09044204c1),
  (127, 0x3088261802109044204c1)
]

set_option maxHeartbeats 6000000 in
theorem window10_0g1_valid : window10_0g1.all (fun x => verifyPacked (ps10 ++ [x.1]) x.2) = true := by
  decide +kernel

def window10_0 : List (ℕ × ℕ) := window10_0g0 ++ window10_0g1

set_option maxHeartbeats 1500000 in
theorem window10_0_prime_values : window10_0.map Prod.fst = candidateFinals ps10 32 96 := by
  decide +kernel

theorem window10_0_valid : window10_0.all (fun x => verifyPacked (ps10 ++ [x.1]) x.2) = true := by
  simp only [window10_0, List.all_append, window10_0g0_valid, window10_0g1_valid, Bool.and_self]

def window10_1g0 : List (ℕ × ℕ) := [
  (131, 0x3088261802209044204c1),
  (137, 0x3088261802609044204c1),
  (139, 0x3088261802409044204c1),
  (149, 0x3088261802409044204c1),
  (151, 0x3088261802109044204c1),
  (157, 0x3088261802109044204c1),
  (163, 0x3088261802109044204c1),
  (167, 0x3088261802209044204c1),
  (173, 0x3088261802209044204c1),
  (179, 0x3088261802609044204c1),
  (181, 0x3088261802609044204c1),
  (191, 0x3088261802609044204c1),
  (193, 0x3088261802109044204c1)
]

set_option maxHeartbeats 6000000 in
theorem window10_1g0_valid : window10_1g0.all (fun x => verifyPacked (ps10 ++ [x.1]) x.2) = true := by
  decide +kernel

def window10_1g1 : List (ℕ × ℕ) := [
  (197, 0x3088261802209044204c1),
  (199, 0x3088261802109044204c1),
  (211, 0x411424188473004609c43088261802109044204c1),
  (223, 0x4188273004609c43088261802609044204c1)
]

set_option maxHeartbeats 6000000 in
theorem window10_1g1_valid : window10_1g1.all (fun x => verifyPacked (ps10 ++ [x.1]) x.2) = true := by
  decide +kernel

def window10_1 : List (ℕ × ℕ) := window10_1g0 ++ window10_1g1

set_option maxHeartbeats 1500000 in
theorem window10_1_prime_values : window10_1.map Prod.fst = candidateFinals ps10 128 96 := by
  decide +kernel

theorem window10_1_valid : window10_1.all (fun x => verifyPacked (ps10 ++ [x.1]) x.2) = true := by
  simp only [window10_1, List.all_append, window10_1g0_valid, window10_1g1_valid, Bool.and_self]

def window10_2g0 : List (ℕ × ℕ) := [
  (227, 0x82285870088310800000062102620c4a304462084411444188273004609c43088261802209044204c1),
  (229, 0x10450b0e011062100062082411444188273004609c43088261802609044204c1),
  (233, 0x18830a8c1090451008228587008831080411424188273004609c43088261802609044204c1),
  (239, 0x10450b0e009062100062102620c2a304262084411424188273004609c43088261802209044204c1),
  (241, 0x8228587004831080411426208273004609c43088261802409044204c1),
  (251, 0x41142c38044188273002609c43088261802209044204c1),
  (257, 0x188409cc209883128c111882090451000a30426208441142c38044188273002609c43088261802209044204c1),
  (263, 0x4114241882c3802609c43088261802409044204c1),
  (269, 0x4114262082c3802609c40000062102620c2a30444114441884609c2730043088261802609044204c1),
  (271, 0x18860ca000a8e21188509cc20c1a00988411883128c111045098820b0e00982710004114241884609c2730043088261802409044204c1),
  (277, 0x411424188473004609c23088261802109044204c1),
  (281, 0x411424188473004609c23088261802209044204c1),
  (283, 0x6214262102620c430a04a3044411424188473004609c23088261802109044204c1)
]

set_option maxHeartbeats 6000000 in
theorem window10_2g0_valid : window10_2g0.all (fun x => verifyPacked (ps10 ++ [x.1]) x.2) = true := by
  decide +kernel

def window10_2g1 : List (ℕ × ℕ) := [
  (293, 0x14608482289870088310804188273004609c23088261802209044204c1),
  (307, 0x4188273004609c23088261802409084204c1),
  (311, 0xc4185460898700882284831080411424188273004609c23088261802209044204c1),
  (313, 0x8228587004831080411424188273004609c23088261802109044204c1),
  (317, 0x208a161c0120c42000062102620c4a304262084411424188273004609c23088261802609044204c1)
]

set_option maxHeartbeats 6000000 in
theorem window10_2g1_valid : window10_2g1.all (fun x => verifyPacked (ps10 ++ [x.1]) x.2) = true := by
  decide +kernel

def window10_2 : List (ℕ × ℕ) := window10_2g0 ++ window10_2g1

set_option maxHeartbeats 1500000 in
theorem window10_2_prime_values : window10_2.map Prod.fst = candidateFinals ps10 224 96 := by
  decide +kernel

theorem window10_2_valid : window10_2.all (fun x => verifyPacked (ps10 ++ [x.1]) x.2) = true := by
  simp only [window10_2, List.all_append, window10_2g0_valid, window10_2g1_valid, Bool.and_self]

def window10_3g0 : List (ℕ × ℕ) := [
  (331, 0x6208241144c3804609c24188273002109044204c1),
  (337, 0x41142c3804609c24188273002409044204c1),
  (347, 0xc410482288041142c3804609c24188273002409044204c1),
  (349, 0xc410482288041142c3804609c24188273002609044204c1),
  (353, 0x62082c3804609c2411424188273002209044204c1),
  (359, 0x621427308262104620c262082a3042c3804609c2411424188273002409044204c1),
  (367, 0x609c24114241882c3802609044204c1),
  (373, 0x609c24114262082c3802409044204c1),
  (379, 0x18860a8e2141a011885100c4285ac008c4204e6104614080000186206500058a088c43060d004c428806218262142d60047308430a0262102620c4609c24114262082a3042c3802109044204c1)
]

set_option maxHeartbeats 6000000 in
theorem window10_3g0_valid : window10_3g0.all (fun x => verifyPacked (ps10 ++ [x.1]) x.2) = true := by
  decide +kernel

def window10_3 : List (ℕ × ℕ) := window10_3g0

set_option maxHeartbeats 1500000 in
theorem window10_3_prime_values : window10_3.map Prod.fst = candidateFinals ps10 320 61 := by
  decide +kernel

theorem window10_3_valid : window10_3.all (fun x => verifyPacked (ps10 ++ [x.1]) x.2) = true := by
  exact window10_3g0_valid

theorem prefix10_verified {q : ℕ} (hlo : start ps10 ≤ q) (hhi : q ≤ lastCap ps10)
    (hp : q.Prime) (hlarge : 3 * den ps10 * (q-1) < ps10.prod * q) :
    ∃ w, verifyPacked (ps10 ++ [q]) w = true := by
  change 32 ≤ q at hlo
  change q ≤ 380 at hhi

  by_cases h0 : q < 128
  · exact checked_window window10_0_prime_values window10_0_valid (by omega) (by omega) hp hlarge

  by_cases h1 : q < 224
  · exact checked_window window10_1_prime_values window10_1_valid (by omega) (by omega) hp hlarge

  by_cases h2 : q < 320
  · exact checked_window window10_2_prime_values window10_2_valid (by omega) (by omega) hp hlarge

  exact checked_window window10_3_prime_values window10_3_valid (by omega) (by omega) hp hlarge

def ps11 : List ℕ := [3, 5, 7, 11, 13, 17, 23, 37]

def window11_0g0 : List (ℕ × ℕ) := [
  (41, 0x6104261804308823080220904420441),
  (43, 0x6104261804308823080240904420441),
  (47, 0x41882309c46104261804308823080260904420441),
  (53, 0x308826180260904420441),
  (59, 0x10450b0e01106208c2710004114241884309c27300461044308826180220904420441),
  (61, 0x30ce1310c1310813106151c4183401208a201045098820b0e010c2810061404822858700483108030a02411426208273004309c261044308826180210904420441),
  (67, 0x30882610426180240904420441),
  (71, 0x30882610426180220904420441),
  (73, 0x30882610426180240904420441),
  (79, 0x30882610426180210904420441),
  (83, 0x30882610426180220904420441),
  (89, 0x30882610426180220904420441),
  (97, 0x30882610426180260904420441)
]

set_option maxHeartbeats 6000000 in
theorem window11_0g0_valid : window11_0g0.all (fun x => verifyPacked (ps11 ++ [x.1]) x.2) = true := by
  decide +kernel

def window11_0g1 : List (ℕ × ℕ) := [
  (101, 0x30882610426180220904420441),
  (103, 0x411424188473004309c430882610426180260904420441),
  (107, 0x1884098830a0c1110451008228587008831080411424188273004309c430882610426180240904420441),
  (109, 0x208a161c0120c420000a404262144730826210441142620c2620828304273004309c430882610426180240904420441),
  (113, 0x822848310587004613880309c24188273004308826104261802a0904420441)
]

set_option maxHeartbeats 6000000 in
theorem window11_0g1_valid : window11_0g1.all (fun x => verifyPacked (ps11 ++ [x.1]) x.2) = true := by
  decide +kernel

def window11_0 : List (ℕ × ℕ) := window11_0g0 ++ window11_0g1

set_option maxHeartbeats 1500000 in
theorem window11_0_prime_values : window11_0.map Prod.fst = candidateFinals ps11 38 88 := by
  decide +kernel

theorem window11_0_valid : window11_0.all (fun x => verifyPacked (ps11 ++ [x.1]) x.2) = true := by
  simp only [window11_0, List.all_append, window11_0g0_valid, window11_0g1_valid, Bool.and_self]

theorem prefix11_verified {q : ℕ} (hlo : start ps11 ≤ q) (hhi : q ≤ lastCap ps11)
    (hp : q.Prime) (hlarge : 3 * den ps11 * (q-1) < ps11.prod * q) :
    ∃ w, verifyPacked (ps11 ++ [q]) w = true := by
  change 38 ≤ q at hlo
  change q ≤ 125 at hhi

  exact checked_window window11_0_prime_values window11_0_valid (by omega) (by omega) hp hlarge

def ps16 : List ℕ := [3, 5, 7, 11, 13, 17, 29, 31]

def window16_0g0 : List (ℕ × ℕ) := [
  (37, 0x3088230802109044204c1),
  (41, 0x41202a30427208441144609c241882618043088230802209044204c1),
  (43, 0x3088261802409044204c1),
  (47, 0x3088261802209044204c1),
  (53, 0x3088261802a09044204c1),
  (59, 0x3088261802209044204c1),
  (61, 0x3088261802409044204c1),
  (67, 0x3088261802409044204c1),
  (71, 0x3088261802209044204c1),
  (73, 0x40a0241144001884098830a8c109028110450a8e011062100040a02411444188273004609c43088261802109044204c1),
  (79, 0x61404822880001884098830a8c110c28110450a8e011062100030a02411444188273004609c23088261802109044204c1),
  (83, 0x609c24114241882a3802209044204c1)
]

set_option maxHeartbeats 6000000 in
theorem window16_0g0_valid : window16_0g0.all (fun x => verifyPacked (ps16 ++ [x.1]) x.2) = true := by
  decide +kernel

def window16_0 : List (ℕ × ℕ) := window16_0g0

set_option maxHeartbeats 1500000 in
theorem window16_0_prime_values : window16_0.map Prod.fst = candidateFinals ps16 32 52 := by
  decide +kernel

theorem window16_0_valid : window16_0.all (fun x => verifyPacked (ps16 ++ [x.1]) x.2) = true := by
  exact window16_0g0_valid

theorem prefix16_verified {q : ℕ} (hlo : start ps16 ≤ q) (hhi : q ≤ lastCap ps16)
    (hp : q.Prime) (hlarge : 3 * den ps16 * (q-1) < ps16.prod * q) :
    ∃ w, verifyPacked (ps16 ++ [q]) w = true := by
  change 32 ≤ q at hlo
  change q ≤ 83 at hhi

  exact checked_window window16_0_prime_values window16_0_valid (by omega) (by omega) hp hlarge

def ps17 : List ℕ := [3, 5, 7, 11, 13, 17, 29, 37]

def window17_0g0 : List (ℕ × ℕ) := [
  (41, 0x30882610426180220904420441),
  (43, 0x30882610426180240904420441),
  (47, 0x30882610426180260904420441),
  (53, 0x411424188473004309c4308826104261802a0904420441)
]

set_option maxHeartbeats 6000000 in
theorem window17_0g0_valid : window17_0g0.all (fun x => verifyPacked (ps17 ++ [x.1]) x.2) = true := by
  decide +kernel

def window17_0 : List (ℕ × ℕ) := window17_0g0

set_option maxHeartbeats 1500000 in
theorem window17_0_prime_values : window17_0.map Prod.fst = candidateFinals ps17 38 21 := by
  decide +kernel

theorem window17_0_valid : window17_0.all (fun x => verifyPacked (ps17 ++ [x.1]) x.2) = true := by
  exact window17_0g0_valid

theorem prefix17_verified {q : ℕ} (hlo : start ps17 ≤ q) (hhi : q ≤ lastCap ps17)
    (hp : q.Prime) (hlarge : 3 * den ps17 * (q-1) < ps17.prod * q) :
    ∃ w, verifyPacked (ps17 ++ [q]) w = true := by
  change 38 ≤ q at hlo
  change q ≤ 58 at hhi

  exact checked_window window17_0_prime_values window17_0_valid (by omega) (by omega) hp hlarge

def ps20 : List ℕ := [3, 5, 7, 11, 13, 17, 31, 37]

def window20_0g0 : List (ℕ × ℕ) := [
  (41, 0x3088261802208444204c1),
  (43, 0x3088261802408444204c1),
  (47, 0x28c1090451106211cc010c2710004114262082a3802309c40000c418546084822894700861384831080309c24188273004609843088261802608444204c1)
]

set_option maxHeartbeats 6000000 in
theorem window20_0g0_valid : window20_0g0.all (fun x => verifyPacked (ps20 ++ [x.1]) x.2) = true := by
  decide +kernel

def window20_0 : List (ℕ × ℕ) := window20_0g0

set_option maxHeartbeats 1500000 in
theorem window20_0_prime_values : window20_0.map Prod.fst = candidateFinals ps20 38 14 := by
  decide +kernel

theorem window20_0_valid : window20_0.all (fun x => verifyPacked (ps20 ++ [x.1]) x.2) = true := by
  exact window20_0g0_valid

theorem prefix20_verified {q : ℕ} (hlo : start ps20 ≤ q) (hhi : q ≤ lastCap ps20)
    (hp : q.Prime) (hlarge : 3 * den ps20 * (q-1) < ps20.prod * q) :
    ∃ w, verifyPacked (ps20 ++ [q]) w = true := by
  change 38 ≤ q at hlo
  change q ≤ 51 at hhi

  exact checked_window window20_0_prime_values window20_0_valid (by omega) (by omega) hp hlarge

def ps23 : List ℕ := [3, 5, 7, 11, 13, 19, 23, 31]

def window23_0g0 : List (ℕ × ℕ) := [
  (37, 0x3088230802609024204c1),
  (41, 0x609c24188230944618043088230802209024204c1),
  (43, 0x30942618043088230802409024204c1),
  (47, 0x3088261802209024204c1),
  (53, 0x3088261802609024204c1),
  (59, 0x3088261802209024204c1),
  (61, 0x3088261802409024204c1),
  (67, 0x3088261802109024204c1),
  (71, 0x3088261802209024204c1),
  (73, 0x4188273004609c4309443088261802109024204c1),
  (79, 0x4188273004609c2309443088261802109024204c1),
  (83, 0x7308262104620c262082a3042c3804609c24188273002309443088261802409024204c1),
  (89, 0x309423088261802209024204c1)
]

set_option maxHeartbeats 6000000 in
theorem window23_0g0_valid : window23_0g0.all (fun x => verifyPacked (ps23 ++ [x.1]) x.2) = true := by
  decide +kernel

def window23_0g1 : List (ℕ × ℕ) := [
  (97, 0x41882c3802609c4309423088261802609024204c1),
  (101, 0x4188273004609c2309423088261802209024204c1),
  (103, 0x1870048310804188273004609c2309423088261802609024204c1),
  (107, 0x62082c3804609c2309424188273002409024204c1),
  (109, 0x620c241944a3044609c23094262082c3802609024204c1)
]

set_option maxHeartbeats 6000000 in
theorem window23_0g1_valid : window23_0g1.all (fun x => verifyPacked (ps23 ++ [x.1]) x.2) = true := by
  decide +kernel

def window23_0 : List (ℕ × ℕ) := window23_0g0 ++ window23_0g1

set_option maxHeartbeats 1500000 in
theorem window23_0_prime_values : window23_0.map Prod.fst = candidateFinals ps23 32 78 := by
  decide +kernel

theorem window23_0_valid : window23_0.all (fun x => verifyPacked (ps23 ++ [x.1]) x.2) = true := by
  simp only [window23_0, List.all_append, window23_0g0_valid, window23_0g1_valid, Bool.and_self]

theorem prefix23_verified {q : ℕ} (hlo : start ps23 ≤ q) (hhi : q ≤ lastCap ps23)
    (hp : q.Prime) (hlarge : 3 * den ps23 * (q-1) < ps23.prod * q) :
    ∃ w, verifyPacked (ps23 ++ [q]) w = true := by
  change 32 ≤ q at hlo
  change q ≤ 109 at hhi

  exact checked_window window23_0_prime_values window23_0_valid (by omega) (by omega) hp hlarge

def ps24 : List ℕ := [3, 5, 7, 11, 13, 19, 23, 37]

def window24_0g0 : List (ℕ × ℕ) := [
  (41, 0x3094261044308826180223102420441),
  (43, 0x3094261044308826180243102420441),
  (47, 0x30882610426180263102420441),
  (53, 0x30882610426180263102420441),
  (59, 0x3094230882610426180223102420441),
  (61, 0x3094230882610426180213102420441),
  (67, 0xc280906210000000c42048328804194262102620c4a30446208430a0441882c38043094230882610427300213102420441)
]

set_option maxHeartbeats 6000000 in
theorem window24_0g0_valid : window24_0g0.all (fun x => verifyPacked (ps24 ++ [x.1]) x.2) = true := by
  decide +kernel

def window24_0 : List (ℕ × ℕ) := window24_0g0

set_option maxHeartbeats 1500000 in
theorem window24_0_prime_values : window24_0.map Prod.fst = candidateFinals ps24 38 32 := by
  decide +kernel

theorem window24_0_valid : window24_0.all (fun x => verifyPacked (ps24 ++ [x.1]) x.2) = true := by
  exact window24_0g0_valid

theorem prefix24_verified {q : ℕ} (hlo : start ps24 ≤ q) (hhi : q ≤ lastCap ps24)
    (hp : q.Prime) (hlarge : 3 * den ps24 * (q-1) < ps24.prod * q) :
    ∃ w, verifyPacked (ps24 ++ [q]) w = true := by
  change 38 ≤ q at hlo
  change q ≤ 69 at hhi

  exact checked_window window24_0_prime_values window24_0_valid (by omega) (by omega) hp hlarge

def ps28 : List ℕ := [3, 5, 7, 11, 13, 19, 29, 31]

def window28_0g0 : List (ℕ × ℕ) := [
  (37, 0x3088261802609024204c1),
  (41, 0x3088261802209024204c1),
  (43, 0x3088261802409024204c1),
  (47, 0x620c261204a304472082a3804609c24188273002309443088261802209024204c1),
  (53, 0x1470048310807208273004609c2309423088261802a09024204c1)
]

set_option maxHeartbeats 6000000 in
theorem window28_0g0_valid : window28_0g0.all (fun x => verifyPacked (ps28 ++ [x.1]) x.2) = true := by
  decide +kernel

def window28_0 : List (ℕ × ℕ) := window28_0g0

set_option maxHeartbeats 1500000 in
theorem window28_0_prime_values : window28_0.map Prod.fst = candidateFinals ps28 32 23 := by
  decide +kernel

theorem window28_0_valid : window28_0.all (fun x => verifyPacked (ps28 ++ [x.1]) x.2) = true := by
  exact window28_0g0_valid

theorem prefix28_verified {q : ℕ} (hlo : start ps28 ≤ q) (hhi : q ≤ lastCap ps28)
    (hp : q.Prime) (hlarge : 3 * den ps28 * (q-1) < ps28.prod * q) :
    ∃ w, verifyPacked (ps28 ++ [q]) w = true := by
  change 32 ≤ q at hlo
  change q ≤ 54 at hhi

  exact checked_window window28_0_prime_values window28_0_valid (by omega) (by omega) hp hlarge

def ps29 : List ℕ := [3, 5, 7, 11, 13, 19, 29, 37]

def window29_0g0 : List (ℕ × ℕ) := [
  (41, 0x41882a30043094230882610426180223102420441)
]

set_option maxHeartbeats 6000000 in
theorem window29_0g0_valid : window29_0g0.all (fun x => verifyPacked (ps29 ++ [x.1]) x.2) = true := by
  decide +kernel

def window29_0 : List (ℕ × ℕ) := window29_0g0

set_option maxHeartbeats 1500000 in
theorem window29_0_prime_values : window29_0.map Prod.fst = candidateFinals ps29 38 5 := by
  decide +kernel

theorem window29_0_valid : window29_0.all (fun x => verifyPacked (ps29 ++ [x.1]) x.2) = true := by
  exact window29_0g0_valid

theorem prefix29_verified {q : ℕ} (hlo : start ps29 ≤ q) (hhi : q ≤ lastCap ps29)
    (hp : q.Prime) (hlarge : 3 * den ps29 * (q-1) < ps29.prod * q) :
    ∃ w, verifyPacked (ps29 ++ [q]) w = true := by
  change 38 ≤ q at hlo
  change q ≤ 42 at hhi

  exact checked_window window29_0_prime_values window29_0_valid (by omega) (by omega) hp hlarge

def ps30 : List ℕ := [3, 5, 7, 11, 13, 19, 31, 37]

def window30_0g0 : List (ℕ × ℕ) := []

set_option maxHeartbeats 6000000 in
theorem window30_0g0_valid : window30_0g0.all (fun x => verifyPacked (ps30 ++ [x.1]) x.2) = true := by
  decide +kernel

def window30_0 : List (ℕ × ℕ) := window30_0g0

set_option maxHeartbeats 1500000 in
theorem window30_0_prime_values : window30_0.map Prod.fst = candidateFinals ps30 38 1 := by
  decide +kernel

theorem window30_0_valid : window30_0.all (fun x => verifyPacked (ps30 ++ [x.1]) x.2) = true := by
  exact window30_0g0_valid

theorem prefix30_verified {q : ℕ} (hlo : start ps30 ≤ q) (hhi : q ≤ lastCap ps30)
    (hp : q.Prime) (hlarge : 3 * den ps30 * (q-1) < ps30.prod * q) :
    ∃ w, verifyPacked (ps30 ++ [q]) w = true := by
  change 38 ≤ q at hlo
  change q ≤ 38 at hhi

  exact checked_window window30_0_prime_values window30_0_valid (by omega) (by omega) hp hlarge

def ps31 : List ℕ := [3, 5, 7, 11, 13, 23, 29, 31]

def window31_0g0 : List (ℕ × ℕ) := []

set_option maxHeartbeats 6000000 in
theorem window31_0g0_valid : window31_0g0.all (fun x => verifyPacked (ps31 ++ [x.1]) x.2) = true := by
  decide +kernel

def window31_0 : List (ℕ × ℕ) := window31_0g0

set_option maxHeartbeats 1500000 in
theorem window31_0_prime_values : window31_0.map Prod.fst = candidateFinals ps31 32 5 := by
  decide +kernel

theorem window31_0_valid : window31_0.all (fun x => verifyPacked (ps31 ++ [x.1]) x.2) = true := by
  exact window31_0g0_valid

theorem prefix31_verified {q : ℕ} (hlo : start ps31 ≤ q) (hhi : q ≤ lastCap ps31)
    (hp : q.Prime) (hlarge : 3 * den ps31 * (q-1) < ps31.prod * q) :
    ∃ w, verifyPacked (ps31 ++ [q]) w = true := by
  change 32 ≤ q at hlo
  change q ≤ 36 at hhi

  exact checked_window window31_0_prime_values window31_0_valid (by omega) (by omega) hp hlarge

def ps33 : List ℕ := [3, 5, 7, 11, 17, 19, 23, 31]

def window33_0g0 : List (ℕ × ℕ) := []

set_option maxHeartbeats 6000000 in
theorem window33_0g0_valid : window33_0g0.all (fun x => verifyPacked (ps33 ++ [x.1]) x.2) = true := by
  decide +kernel

def window33_0 : List (ℕ × ℕ) := window33_0g0

set_option maxHeartbeats 1500000 in
theorem window33_0_prime_values : window33_0.map Prod.fst = candidateFinals ps33 32 4 := by
  decide +kernel

theorem window33_0_valid : window33_0.all (fun x => verifyPacked (ps33 ++ [x.1]) x.2) = true := by
  exact window33_0g0_valid

theorem prefix33_verified {q : ℕ} (hlo : start ps33 ≤ q) (hhi : q ≤ lastCap ps33)
    (hp : q.Prime) (hlarge : 3 * den ps33 * (q-1) < ps33.prod * q) :
    ∃ w, verifyPacked (ps33 ++ [q]) w = true := by
  change 32 ≤ q at hlo
  change q ≤ 35 at hhi

  exact checked_window window33_0_prime_values window33_0_valid (by omega) (by omega) hp hlarge

set_option maxHeartbeats 2000000 in
theorem viable_prefixes_exact : viablePrefixes = [[3, 5, 7, 11, 13, 17, 19, 41], [3, 5, 7, 11, 13, 17, 19, 43], [3, 5, 7, 11, 13, 17, 19, 47], [3, 5, 7, 11, 13, 17, 19, 53], [3, 5, 7, 11, 13, 17, 19, 59], [3, 5, 7, 11, 13, 17, 19, 61], [3, 5, 7, 11, 13, 17, 19, 67], [3, 5, 7, 11, 13, 17, 19, 71], [3, 5, 7, 11, 13, 17, 19, 73], [3, 5, 7, 11, 13, 17, 23, 29], [3, 5, 7, 11, 13, 17, 23, 31], [3, 5, 7, 11, 13, 17, 23, 37], [3, 5, 7, 11, 13, 17, 23, 41], [3, 5, 7, 11, 13, 17, 23, 43], [3, 5, 7, 11, 13, 17, 23, 47], [3, 5, 7, 11, 13, 17, 23, 53], [3, 5, 7, 11, 13, 17, 29, 31], [3, 5, 7, 11, 13, 17, 29, 37], [3, 5, 7, 11, 13, 17, 29, 41], [3, 5, 7, 11, 13, 17, 29, 43], [3, 5, 7, 11, 13, 17, 31, 37], [3, 5, 7, 11, 13, 17, 31, 41], [3, 5, 7, 11, 13, 19, 23, 29], [3, 5, 7, 11, 13, 19, 23, 31], [3, 5, 7, 11, 13, 19, 23, 37], [3, 5, 7, 11, 13, 19, 23, 41], [3, 5, 7, 11, 13, 19, 23, 43], [3, 5, 7, 11, 13, 19, 23, 47], [3, 5, 7, 11, 13, 19, 29, 31], [3, 5, 7, 11, 13, 19, 29, 37], [3, 5, 7, 11, 13, 19, 31, 37], [3, 5, 7, 11, 13, 23, 29, 31], [3, 5, 7, 11, 17, 19, 23, 29], [3, 5, 7, 11, 17, 19, 23, 31]] := by
  decide +kernel

theorem word_exists_of_viable {ps : List ℕ} (hm : ps ∈ viablePrefixes)
    (hinterval : 30 ≤ (ps[7]?).getD 0 ∧ (ps[7]?).getD 0 ≤ 37)
    {q : ℕ} (hlo : start ps ≤ q) (hhi : q ≤ lastCap ps)
    (hp : q.Prime) (hlarge : 3 * den ps * (q-1) < ps.prod * q) :
    ∃ w, verifyPacked (ps ++ [q]) w = true := by
  rw [viable_prefixes_exact] at hm
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
  rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · norm_num at hinterval
  · norm_num at hinterval
  · norm_num at hinterval
  · norm_num at hinterval
  · norm_num at hinterval
  · norm_num at hinterval
  · norm_num at hinterval
  · norm_num at hinterval
  · norm_num at hinterval
  · norm_num at hinterval
  · exact prefix10_verified hlo hhi hp hlarge
  · exact prefix11_verified hlo hhi hp hlarge
  · norm_num at hinterval
  · norm_num at hinterval
  · norm_num at hinterval
  · norm_num at hinterval
  · exact prefix16_verified hlo hhi hp hlarge
  · exact prefix17_verified hlo hhi hp hlarge
  · norm_num at hinterval
  · norm_num at hinterval
  · exact prefix20_verified hlo hhi hp hlarge
  · norm_num at hinterval
  · norm_num at hinterval
  · exact prefix23_verified hlo hhi hp hlarge
  · exact prefix24_verified hlo hhi hp hlarge
  · norm_num at hinterval
  · norm_num at hinterval
  · norm_num at hinterval
  · exact prefix28_verified hlo hhi hp hlarge
  · exact prefix29_verified hlo hhi hp hlarge
  · exact prefix30_verified hlo hhi hp hlarge
  · exact prefix31_verified hlo hhi hp hlarge
  · norm_num at hinterval
  · exact prefix33_verified hlo hhi hp hlarge

theorem exclude_bounded
    (checkedWord : ∀ ps ∈ viablePrefixes, 30 ≤ (ps[7]?).getD 0 ∧ (ps[7]?).getD 0 ≤ 37 → ∀ q : ℕ, start ps ≤ q → q ≤ lastCap ps →
      q.Prime → 3 * den ps * (q-1) < ps.prod * q →
      ∃ w, verifyPacked (ps ++ [q]) w = true) :
    OMA.R_OeisA76495_conjecture_R1_H1_R1_H4_R1_H2_R1_H1_R1.H2 := by
  intro p e hcommon hq hinterval hsmall heq
  obtain ⟨hstrict, hp, he, hcap⟩ := hcommon
  let ps := List.ofFn (fun i : Fin 8 => p i.castSucc)
  have hmem : ps ∈ prefixes 2 (List.ofFn caps) :=
    profile_prefix_mem p hstrict (fun i => (hp i).1) (fun i => (hp i).2) hcap
  have hvalue : 0 < value p e := Finset.prod_pos (fun i _ => pow_pos (hp i).1.pos _)
  have hsigma : divisorSum p e = 3 * value p e + 5 := by
    simpa only [divisorSum, value, geometric_eq_sum] using heq
  let D := ∏ i : Fin 9, (p i - 1)
  let Q := ∏ i : Fin 9, p i
  have hD : 0 < D := Finset.prod_pos fun i _ => by have := (hp i).2; omega
  have H := product_profile_bound Finset.univ p p e (fun i _ => (hp i).1.two_le)
    (fun _ _ => le_rfl)
  change divisorSum p e * D ≤ Q * value p e at H
  rw [hsigma] at H
  have hlarge : 3 * D < Q := by
    by_contra! h
    have hh := Nat.mul_le_mul_right (value p e) h
    nlinarith only [hh, H, hD]
  change 3 * (∏ i : Fin 9, (p i - 1)) < (∏ i : Fin 9, p i) at hlarge
  rw [Fin.prod_univ_castSucc (fun i : Fin 9 => p i - 1),
    Fin.prod_univ_castSucc (fun i : Fin 9 => p i)] at hlarge
  have h8 : Fin.last 8 = (8 : Fin 9) := by decide
  have hpsNum : ps.prod = ∏ i : Fin 8, p i.castSucc := List.prod_ofFn
  have hpsDen : den ps = ∏ i : Fin 8, (p i.castSucc - 1) := by
    rw [den, show ps = List.ofFn (fun i : Fin 8 => p i.castSucc) by rfl,
      List.map_ofFn, List.prod_ofFn]
    rfl
  change (∏ i : Fin 8, p i.castSucc) < 3 * (∏ i : Fin 8, (p i.castSucc - 1)) at hsmall
  have hbound : ps.prod < 3 * den ps := by simpa only [hpsNum, hpsDen] using hsmall
  have hcross : 3 * den ps * (p 8 - 1) < ps.prod * p 8 := by
    simpa only [hpsNum, hpsDen, h8, mul_assoc] using hlarge
  have hall (r : ℕ) (hr : r ∈ ps) : r < p 8 := by
    obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hr
    apply hstrict
    change i.val < (8 : Fin 9).val
    exact i.isLt
  obtain ⟨hqualified, hlo, hhi⟩ := qualify_prefix hmem (hp 8).1 hq (hp 8).2 hall hbound hcross
  have hfull : List.ofFn p = ps ++ [p 8] := by
    rw [List.ofFn_succ', List.concat_eq_append, h8]
  have hps7 : (ps[7]?).getD 0 = p 7 := by
    have hlt : 7 < 8 := by decide
    simp only [ps, List.getElem?_ofFn, hlt, dite_true, Option.getD_some]
    rfl
  have hinter : 30 ≤ (ps[7]?).getD 0 ∧ (ps[7]?).getD 0 ≤ 37 := by
    rw [hps7]
    omega
  obtain ⟨w, hw⟩ := checkedWord ps hqualified hinter (p 8) hlo hhi (hp 8).1 hcross
  rw [← hfull] at hw
  have hprofile : profileOf (List.ofFn p) = p := by
    funext i
    simp only [profileOf, List.getElem?_ofFn, i.isLt, dite_true, Option.getD_some]
  exact packed_sound hw e (by rw [hprofile]; exact fun i => (hp i).1) he
    (by simpa only [hprofile] using hsigma)

end SigmaNine

theorem OMA.solution : OMA.R_OeisA76495_conjecture_R1_H1_R1_H4_R1_H2_R1_H1_R1.H2 :=
  SigmaNine.exclude_bounded (fun _ hm hi _ hlo hhi hp hc =>
    SigmaNine.word_exists_of_viable hm hi hlo hhi hp hc)
