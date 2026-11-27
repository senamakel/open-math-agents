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
def ps0 : List ℕ := [3, 5, 7, 11, 13, 17, 19, 41]

def window0_0g0 : List (ℕ × ℕ) := [
  (43, 0xc260984108c221000309826104430882618043080241044420441),
  (47, 0x6104261804308823080221044420441),
  (53, 0x6104261804308823080261044420441),
  (59, 0x6104261804308823080221044420441),
  (61, 0x62102620c273082a3044411c2620824114430a0241882309846104261804308823080211044420441),
  (67, 0x309826104261804308823080241044420441),
  (71, 0x102404c42088330800018860a048118841106609883110471000620c241984411c2a30444114441884309826104261804308823080221044420441),
  (73, 0x1885098840906610083304c4204c41888238546084c410881408040a02620824114430982418826104261804308823080211044420441),
  (79, 0x30a024114441882a30043098461044308826180211044420441),
  (83, 0x4114241882a30023098461044308826180241044420441),
  (89, 0x3098261044308826180221044420441),
  (97, 0x3098261044308826180261044420441),
  (101, 0x41882a30043098261044308826180221044420441)
]

set_option maxHeartbeats 6000000 in
theorem window0_0g0_valid : window0_0g0.all (fun x => verifyPacked (ps0 ++ [x.1]) x.2) = true := by
  decide +kernel

def window0_0g1 : List (ℕ × ℕ) := [
  (103, 0x822848310804114241882a30043098261044308826180261044420441),
  (107, 0x62082411443098241882a300261044308826180241044420441),
  (109, 0x1884090661000083401310c2310a16b0013108220cc131062000062182621446210441982620c2c5004411c262084309824114241882a300261044308826180241044420441),
  (113, 0x308826104261802a1044420441),
  (127, 0x30882610426180211044420441),
  (131, 0x30882610426180221044420441),
  (137, 0x30882610426180261044420441)
]

set_option maxHeartbeats 6000000 in
theorem window0_0g1_valid : window0_0g1.all (fun x => verifyPacked (ps0 ++ [x.1]) x.2) = true := by
  decide +kernel

def window0_0 : List (ℕ × ℕ) := window0_0g0 ++ window0_0g1

set_option maxHeartbeats 1500000 in
theorem window0_0_prime_values : window0_0.map Prod.fst = candidateFinals ps0 42 96 := by
  decide +kernel

theorem window0_0_valid : window0_0.all (fun x => verifyPacked (ps0 ++ [x.1]) x.2) = true := by
  simp only [window0_0, List.all_append, window0_0g0_valid, window0_0g1_valid, Bool.and_self]

def window0_1g0 : List (ℕ × ℕ) := [
  (139, 0x30882610426180261044420441),
  (149, 0x30882610426180241044420441),
  (151, 0x30882610426180241044420441),
  (157, 0x30882610426180211044420441),
  (163, 0x30882610426180261044420441),
  (167, 0x30882610426180221044420441),
  (173, 0x30882610426180221044420441),
  (179, 0x30882610426180261044420441),
  (181, 0x30882610426180261044420441),
  (191, 0x30882610426180261044420441),
  (193, 0x30882610426180211044420441),
  (197, 0x30882610426180241044420441),
  (199, 0x30882610426180211044420441)
]

set_option maxHeartbeats 6000000 in
theorem window0_1g0_valid : window0_1g0.all (fun x => verifyPacked (ps0 ++ [x.1]) x.2) = true := by
  decide +kernel

def window0_1g1 : List (ℕ × ℕ) := [
  (211, 0x41882a30043098430882610426180211044420441),
  (223, 0x822848310804114241882a30043098430882610426180261044420441),
  (227, 0x208a120c42000062102620c4411c2a3042620844114241882a30043098430882610426180221044420441),
  (229, 0x208a120c42000000188509cc211884118831104709828100062102620c2411c460a02a30444114262082a30043098430882610426180211044420441),
  (233, 0x41882a30023098430882610426180241044420441)
]

set_option maxHeartbeats 6000000 in
theorem window0_1g1_valid : window0_1g1.all (fun x => verifyPacked (ps0 ++ [x.1]) x.2) = true := by
  decide +kernel

def window0_1 : List (ℕ × ℕ) := window0_1g0 ++ window0_1g1

set_option maxHeartbeats 1500000 in
theorem window0_1_prime_values : window0_1.map Prod.fst = candidateFinals ps0 138 96 := by
  decide +kernel

theorem window0_1_valid : window0_1.all (fun x => verifyPacked (ps0 ++ [x.1]) x.2) = true := by
  simp only [window0_1, List.all_append, window0_1g0_valid, window0_1g1_valid, Bool.and_self]

def window0_2g0 : List (ℕ × ℕ) := [
  (239, 0x62102620c4c5004411c4a3044620844114441882a30023098430882610426180241044420441),
  (241, 0x411c2620c2a3042c5002620844114441882a30023098430882610426180241044420441),
  (251, 0x4114241882a30023098430882610426180221044420441),
  (257, 0x28c509887100c4386500098a088c240547108c4284e61060d004c4208c418800000c43858a084c2408061202c5042a30c4a3882621447308262104620c2c5004411c24114262082a3042a30023098430882610426180221044420441),
  (263, 0x3098230882610426180241044420441),
  (269, 0x3098230882610426180261044420441),
  (271, 0x3098230882610426180241044420441),
  (277, 0x3098230882610426180211044420441),
  (281, 0x3098230882610426180221044420441),
  (283, 0x3098230882610426180211044420441),
  (293, 0x3098230882610426180221044420441),
  (307, 0x3098230882610426180241048420441),
  (311, 0x3098230882610426180261044420441)
]

set_option maxHeartbeats 6000000 in
theorem window0_2g0_valid : window0_2g0.all (fun x => verifyPacked (ps0 ++ [x.1]) x.2) = true := by
  decide +kernel

def window0_2g1 : List (ℕ × ℕ) := [
  (313, 0x3098230882610426180211044420441),
  (317, 0x3098230882610426180261044420441)
]

set_option maxHeartbeats 6000000 in
theorem window0_2g1_valid : window0_2g1.all (fun x => verifyPacked (ps0 ++ [x.1]) x.2) = true := by
  decide +kernel

def window0_2 : List (ℕ × ℕ) := window0_2g0 ++ window0_2g1

set_option maxHeartbeats 1500000 in
theorem window0_2_prime_values : window0_2.map Prod.fst = candidateFinals ps0 234 96 := by
  decide +kernel

theorem window0_2_valid : window0_2.all (fun x => verifyPacked (ps0 ++ [x.1]) x.2) = true := by
  simp only [window0_2, List.all_append, window0_2g0_valid, window0_2g1_valid, Bool.and_self]

def window0_3g0 : List (ℕ × ℕ) := [
  (331, 0x3098230882610426180211044420441),
  (337, 0x3098230882610426180241044420441),
  (347, 0x3098230882610426180241044420441),
  (349, 0x3098230882610426180241044420441),
  (353, 0x3098230882610426180241044420441),
  (359, 0x3098230882610426180241044420441),
  (367, 0x3098230882610426180211044420441),
  (373, 0x3098230882610426180241044420441),
  (379, 0x30982308826104261802a1044420441),
  (383, 0x3098230882610426180221044420441),
  (389, 0x3098230882610426180261044420441),
  (397, 0x3098230882610426180211044420441),
  (401, 0x3098230882610426180261044420441)
]

set_option maxHeartbeats 6000000 in
theorem window0_3g0_valid : window0_3g0.all (fun x => verifyPacked (ps0 ++ [x.1]) x.2) = true := by
  decide +kernel

def window0_3g1 : List (ℕ × ℕ) := [
  (409, 0x3098230882610426180241044420441),
  (419, 0x3098230882610426180241044420441),
  (421, 0x3098230882610426180211044420441)
]

set_option maxHeartbeats 6000000 in
theorem window0_3g1_valid : window0_3g1.all (fun x => verifyPacked (ps0 ++ [x.1]) x.2) = true := by
  decide +kernel

def window0_3 : List (ℕ × ℕ) := window0_3g0 ++ window0_3g1

set_option maxHeartbeats 1500000 in
theorem window0_3_prime_values : window0_3.map Prod.fst = candidateFinals ps0 330 96 := by
  decide +kernel

theorem window0_3_valid : window0_3.all (fun x => verifyPacked (ps0 ++ [x.1]) x.2) = true := by
  simp only [window0_3, List.all_append, window0_3g0_valid, window0_3g1_valid, Bool.and_self]

def window0_4g0 : List (ℕ × ℕ) := [
  (431, 0x3098230882610426180241044420441),
  (433, 0x3098230882610426180261044420441),
  (439, 0x3098230882610426180241044420441),
  (443, 0x3098230882610426180261044420441),
  (449, 0x1884090661000621826210441982620c4411c4a30444114441884a30043098230882610426180221044420441),
  (457, 0x4114241884a30043098230882610426180211044420441),
  (461, 0x4114241884a30043098230882610426180221044420441),
  (463, 0x4114241884a30043098230882610426180211044420441),
  (467, 0x4114241884a30043098230882610426180261044420441),
  (479, 0x4114241884a30043098230882610426180221044420441),
  (487, 0x4114241884a30043098230882610426180211044420441),
  (491, 0x4114241884a30043098230882610426180221044420441),
  (499, 0xc1404c4204c41848238800305013108131062208e120cc2000062182621446210460a02411c241982620c2a30444114241884a30043098230882610426180211044420441)
]

set_option maxHeartbeats 6000000 in
theorem window0_4g0_valid : window0_4g0.all (fun x => verifyPacked (ps0 ++ [x.1]) x.2) = true := by
  decide +kernel

def window0_4g1 : List (ℕ × ℕ) := [
  (503, 0x411c2419826214262102620c2a304241884a30043098230882610426180241044420441),
  (509, 0x41882a30043098230882610426180221044420441),
  (521, 0x41882a30043098230882610426180221044420441)
]

set_option maxHeartbeats 6000000 in
theorem window0_4g1_valid : window0_4g1.all (fun x => verifyPacked (ps0 ++ [x.1]) x.2) = true := by
  decide +kernel

def window0_4 : List (ℕ × ℕ) := window0_4g0 ++ window0_4g1

set_option maxHeartbeats 1500000 in
theorem window0_4_prime_values : window0_4.map Prod.fst = candidateFinals ps0 426 96 := by
  decide +kernel

theorem window0_4_valid : window0_4.all (fun x => verifyPacked (ps0 ++ [x.1]) x.2) = true := by
  simp only [window0_4, List.all_append, window0_4g0_valid, window0_4g1_valid, Bool.and_self]

def window0_5g0 : List (ℕ × ℕ) := [
  (523, 0x41882a30043098230882610426180211044420441),
  (541, 0x81404c4204c418883308040a024198262102620c2a3044411c2620844114441882a30043098230882610426180211044420441),
  (547, 0x620824114441882a30043098230882610426180211044420441),
  (557, 0x20cc131061208e20000621827308462102620c4411c241982a3044620824114441882a30043098230882610426180241044420441),
  (563, 0xc4204c418883308003108120cc2000c4304c420883304c41898a00882389460888228883108000000621c2a3104c504462182a30c273084411c24198262102620c262082a30424114441882a30043098230882610426180221044420441),
  (569, 0xc42048330804198262102620c40001461858a084c4308c420883304c41858a0088238800041a009884118830906610083304c41858a0088238546088822888310804114241882a30043098230882610426180241044420441),
  (571, 0x3108131061208e20000d600262104620c4411c2419840208e120cc13106151822000c41848330882385460858a008822888310804114241882a30043098230882610426180241044420441),
  (577, 0x822848310804114241882a30043098230882610426180261044420441),
  (587, 0x822848310804114241882a30043098230882610426180221044420441),
  (593, 0x822848310804114241882a30043098230882610426180221044420441),
  (599, 0x208a120c42000000000a30c26214462104620c241984411c4a3044620844114241882a30043098230882610426180261044420441),
  (601, 0x41142418840000041982620c2411c4a3044620844114241882a30043098230882610426180241044420441),
  (607, 0x41142418840000c4204c418482388003108131062208e120cc20000621826214462104411c241982620c2a3044620844114241882a30043098230882610426180241044420441)
]

set_option maxHeartbeats 6000000 in
theorem window0_5g0_valid : window0_5g0.all (fun x => verifyPacked (ps0 ++ [x.1]) x.2) = true := by
  decide +kernel

def window0_5g1 : List (ℕ × ℕ) := [
  (613, 0x104509062100030a02411c2621826214262102620c2a3042620844114241882a30043098230882610426180211044420441),
  (617, 0x822848310804114262082a30043098230882610426180221044420441)
]

set_option maxHeartbeats 6000000 in
theorem window0_5g1_valid : window0_5g1.all (fun x => verifyPacked (ps0 ++ [x.1]) x.2) = true := by
  decide +kernel

def window0_5 : List (ℕ × ℕ) := window0_5g0 ++ window0_5g1

set_option maxHeartbeats 1500000 in
theorem window0_5_prime_values : window0_5.map Prod.fst = candidateFinals ps0 522 96 := by
  decide +kernel

theorem window0_5_valid : window0_5.all (fun x => verifyPacked (ps0 ++ [x.1]) x.2) = true := by
  simp only [window0_5, List.all_append, window0_5g0_valid, window0_5g1_valid, Bool.and_self]

def window0_6g0 : List (ℕ × ℕ) := [
  (619, 0x10450906210000000062142a388260a0462102620c441984411c4a30444114262082a30043098230882610426180211044420441),
  (631, 0x104509062100000014618547108c4284e610461408c42088330800000c4284e610861408c420883304c4188030a02621826214262102620c273082a3044411c24114262082a30043098230882610426180211044420441),
  (641, 0x1885098840988311066100062102419840018860988509884110660988313140110471000000146184c4308c4289ac008c4204c418482388003108131062208e120cc200006214262104620c241984411c2c5004a30444114241884309823088261042a300261044420441),
  (643, 0x18840906610000310c183401310a201886098850b58011884110660988310083304c41858a0088238800000c4285ac008c4208c418483308041982620c2c5004411c2a30444114241884309823088261042a300261044420441),
  (647, 0x146306b200946288c240a50005462098a08946188c4304c4284c4204c41860d0048238800000c2404c4385462080030901310e251881940026282183401310a2018850b5801188409883110470906610000000061202621c2a3104a30c46218462144d6004411c24198262102620c2a304400188409066100062182621426210441982620c4411c2a3042c50044114241884309823088261042a300221044420441),
  (653, 0x411c2621826214262102620c2a3042d600241884309823088261042a300261044420441),
  (659, 0x309824188261042a300241044420441),
  (661, 0x309824188261042a300211044420441),
  (673, 0x309824188261042a300211044420441),
  (677, 0x309824188261042a300221044420441),
  (683, 0x309824188261042a300241044420441),
  (691, 0x309824188261042a300211044420441),
  (701, 0x62102620c441984c5004411c4a30446208441144309824188261042a300221044420441)
]

set_option maxHeartbeats 6000000 in
theorem window0_6g0_valid : window0_6g0.all (fun x => verifyPacked (ps0 ++ [x.1]) x.2) = true := by
  decide +kernel

def window0_6g1 : List (ℕ × ℕ) := [
  (709, 0xc280988411883110661000620c241984c5004411c4000000310c16b002185023108220cc131061208e2000030a0262102620c441984411c2c5004a30446208441144309824188261042a300211044420441)
]

set_option maxHeartbeats 6000000 in
theorem window0_6g1_valid : window0_6g1.all (fun x => verifyPacked (ps0 ++ [x.1]) x.2) = true := by
  decide +kernel

def window0_6 : List (ℕ × ℕ) := window0_6g0 ++ window0_6g1

set_option maxHeartbeats 1500000 in
theorem window0_6_prime_values : window0_6.map Prod.fst = candidateFinals ps0 618 96 := by
  decide +kernel

theorem window0_6_valid : window0_6.all (fun x => verifyPacked (ps0 ++ [x.1]) x.2) = true := by
  simp only [window0_6, List.all_append, window0_6g0_valid, window0_6g1_valid, Bool.and_self]

def window0_7g0 : List (ℕ × ℕ) := [
  (719, 0x3106120cc20188609884098830b5800a8c1100062102620c441982a3042c5004411c26208441144309824188261042a300221044420441),
  (727, 0x6208241144309824188261042a300241044420441),
  (733, 0xa38830680473082d600240a0462104620c441984000007308240a0462104620c241984c5004411c4a30446208241144309824188261042a300211044420441),
  (739, 0xc280988409cc20988311066131401104710000018860c1a009cc210c280988409883110660904710000310c151c41185023108131061208e200007308230a0462102620c4411c241984c5004a30446208241144309824188261042a300211044420441),
  (743, 0x620c2419840000c4304e6108c4204c4188833058a0088238800028e20c1a011886098840988309cc20b5800904710006210273082620c4411c24198400188409066100062182730826210441982620c4411c2c5004a30446208241144309824188261042a300221044420441),
  (751, 0x3984118502310823106120cc200000310e194001518825186251c4183401310c21850120cc13108131061398416b001518220000621827308430a0262102620c441982a3042c5004411c26208241144309824188261042a300211044420441),
  (757, 0x18860b58011cc208c281000621c32800430a0262182a30c2a3882c50430680262104411c241982620c262082a3042c500241144309824188261042a300211044420441),
  (761, 0x30982411424188261042a300221044420441),
  (769, 0x30982411424188261042a300241044420441),
  (773, 0x30982411424188261042a300221044420441),
  (787, 0x30982411424188261042a300211044420441),
  (797, 0x30982411424188261042a300221044420441),
  (809, 0x30982411424188261042a300241044420441)
]

set_option maxHeartbeats 6000000 in
theorem window0_7g0_valid : window0_7g0.all (fun x => verifyPacked (ps0 ++ [x.1]) x.2) = true := by
  decide +kernel

def window0_7 : List (ℕ × ℕ) := window0_7g0

set_option maxHeartbeats 1500000 in
theorem window0_7_prime_values : window0_7.map Prod.fst = candidateFinals ps0 714 96 := by
  decide +kernel

theorem window0_7_valid : window0_7.all (fun x => verifyPacked (ps0 ++ [x.1]) x.2) = true := by
  exact window0_7g0_valid

def window0_8g0 : List (ℕ × ℕ) := [
  (811, 0x30982411424188261042a300241044420441),
  (821, 0x310813106220cc200006214262104620c241984c5004411c4a30446208430982411424188261042a300241044420441),
  (823, 0x620c241984000c280988509884090661000621826214230a044198262102620c4c5004411c4a30446208430982411424188261042a300211044420441),
  (827, 0x188409883110661314011047100000020d004c4308c4288062142d600462102620c441982411c40018840988309047100062102620c4411c241984c5004a30446208430982411424188261042a300221044420441),
  (829, 0x106802621440310a16b00230501310823106220cc2000060a0262104620c241984c5004411c40000005186183401310c2310a16b001305023108231061208e200000018850b58011828118841188311047090661000620c241984411c2c5004a30446208430982411424188261042a300211044420441),
  (839, 0x1886098850b58009884118830904710000000061202621c4c504306804621440310a16b0023108231062208e120cc20104709066098830a8c11000620c241984411c2a3042c50046208430982411424188261042a300221044420441),
  (853, 0x30982411426208261042a300241044420441),
  (857, 0x30982411426208261042a300221044420441),
  (859, 0x30a027308462102620c441984c5004411c4a304430982411426208261042a300211044420441),
  (863, 0x310813106220cc2000062142730826210441984000006218262144730846210441982620c4c5004411c4a304430982411426208261042a300261044420441),
  (877, 0x5186151c428340218501310a16b00131082000c4285ac00461408c4204e610883308000000c504328002a388506802621846214230a04018501310a1398420000a388262184621440310c1310a139842185016b0023108220cc131062208e200000028e20c1a0098851000a30c2a388462142d600430a040000c4385461860d008c4288062142d600430a02730846210441984000000310c1310a2018850b58010c2811cc2118841106609883110470a8c1100000000a30c2a3882621846214430a04018501398423108231061208e2000000188508c2811cc211884118831104709066100030a02621426210273082620c4411c241982a3044c500430982411426208261042a300211044420441),
  (881, 0x1886098851358011cc211884110660988309047100000000621c2a3182a3104a38850680462182621440028e209886118850b5801188409cc20988311047090660a8c110000310a131081398413106220cc20000a30c26218462142730844198262102620c2a3044411c2c500430982411426208261042a300241044420441),
  (883, 0x1471060d008c4304c4285ac004c42080000000518816282251862310c2310a26b002310813984231061208e200000028e20c1a011885100c4285ac008e6104c4208c4188823848330800000c43060d004c428806218262142d60047308462104411c241982620c2a304400000621427308462104620c241984411c2a3042c500430982411426208261042a3002a1044420441)
]

set_option maxHeartbeats 6000000 in
theorem window0_8g0_valid : window0_8g0.all (fun x => verifyPacked (ps0 ++ [x.1]) x.2) = true := by
  decide +kernel

def window0_8g1 : List (ℕ × ℕ) := [
  (887, 0x106802621440310a16b00239842310823106120cc20000a388262184621426210273082620c441982c5004411c2309824114262082a3042a300241044420441)
]

set_option maxHeartbeats 6000000 in
theorem window0_8g1_valid : window0_8g1.all (fun x => verifyPacked (ps0 ++ [x.1]) x.2) = true := by
  decide +kernel

def window0_8 : List (ℕ × ℕ) := window0_8g0 ++ window0_8g1

set_option maxHeartbeats 1500000 in
theorem window0_8_prime_values : window0_8.map Prod.fst = candidateFinals ps0 810 87 := by
  decide +kernel

theorem window0_8_valid : window0_8.all (fun x => verifyPacked (ps0 ++ [x.1]) x.2) = true := by
  simp only [window0_8, List.all_append, window0_8g0_valid, window0_8g1_valid, Bool.and_self]

theorem prefix0_verified {q : ℕ} (hlo : start ps0 ≤ q) (hhi : q ≤ lastCap ps0)
    (hp : q.Prime) (hlarge : 3 * den ps0 * (q-1) < ps0.prod * q) :
    ∃ w, verifyPacked (ps0 ++ [q]) w = true := by
  change 42 ≤ q at hlo
  change q ≤ 896 at hhi

  by_cases h0 : q < 138
  · exact checked_window window0_0_prime_values window0_0_valid (by omega) (by omega) hp hlarge

  by_cases h1 : q < 234
  · exact checked_window window0_1_prime_values window0_1_valid (by omega) (by omega) hp hlarge

  by_cases h2 : q < 330
  · exact checked_window window0_2_prime_values window0_2_valid (by omega) (by omega) hp hlarge

  by_cases h3 : q < 426
  · exact checked_window window0_3_prime_values window0_3_valid (by omega) (by omega) hp hlarge

  by_cases h4 : q < 522
  · exact checked_window window0_4_prime_values window0_4_valid (by omega) (by omega) hp hlarge

  by_cases h5 : q < 618
  · exact checked_window window0_5_prime_values window0_5_valid (by omega) (by omega) hp hlarge

  by_cases h6 : q < 714
  · exact checked_window window0_6_prime_values window0_6_valid (by omega) (by omega) hp hlarge

  by_cases h7 : q < 810
  · exact checked_window window0_7_prime_values window0_7_valid (by omega) (by omega) hp hlarge

  exact checked_window window0_8_prime_values window0_8_valid (by omega) (by omega) hp hlarge

def ps12 : List ℕ := [3, 5, 7, 11, 13, 17, 23, 41]

def window12_0g0 : List (ℕ × ℕ) := [
  (43, 0x418826104261804308823080241104420441),
  (47, 0x308826180221104420441),
  (53, 0x62102620c4411c4620844114441882c300261044308826180261104420441),
  (59, 0x30882610426180221104420441),
  (61, 0x30882610426180211104420441),
  (67, 0x30882610426180241104420441),
  (71, 0x30882610426180221104420441),
  (73, 0x30882610426180211104420441),
  (79, 0x30882610426180211104420441),
  (83, 0x30882610426180221104420441),
  (89, 0x822848310804114241882c300430882610426180221104420441)
]

set_option maxHeartbeats 6000000 in
theorem window12_0g0_valid : window12_0g0.all (fun x => verifyPacked (ps12 ++ [x.1]) x.2) = true := by
  decide +kernel

def window12_0 : List (ℕ × ℕ) := window12_0g0

set_option maxHeartbeats 1500000 in
theorem window12_0_prime_values : window12_0.map Prod.fst = candidateFinals ps12 42 52 := by
  decide +kernel

theorem window12_0_valid : window12_0.all (fun x => verifyPacked (ps12 ++ [x.1]) x.2) = true := by
  exact window12_0g0_valid

theorem prefix12_verified {q : ℕ} (hlo : start ps12 ≤ q) (hhi : q ≤ lastCap ps12)
    (hp : q.Prime) (hlarge : 3 * den ps12 * (q-1) < ps12.prod * q) :
    ∃ w, verifyPacked (ps12 ++ [q]) w = true := by
  change 42 ≤ q at hlo
  change q ≤ 93 at hhi

  exact checked_window window12_0_prime_values window12_0_valid (by omega) (by omega) hp hlarge

def ps18 : List ℕ := [3, 5, 7, 11, 13, 17, 29, 41]

def window18_0g0 : List (ℕ × ℕ) := [
  (43, 0x30882610426180241104420441),
  (47, 0x30882610426180221104420441)
]

set_option maxHeartbeats 6000000 in
theorem window18_0g0_valid : window18_0g0.all (fun x => verifyPacked (ps18 ++ [x.1]) x.2) = true := by
  decide +kernel

def window18_0 : List (ℕ × ℕ) := window18_0g0

set_option maxHeartbeats 1500000 in
theorem window18_0_prime_values : window18_0.map Prod.fst = candidateFinals ps18 42 9 := by
  decide +kernel

theorem window18_0_valid : window18_0.all (fun x => verifyPacked (ps18 ++ [x.1]) x.2) = true := by
  exact window18_0g0_valid

theorem prefix18_verified {q : ℕ} (hlo : start ps18 ≤ q) (hhi : q ≤ lastCap ps18)
    (hp : q.Prime) (hlarge : 3 * den ps18 * (q-1) < ps18.prod * q) :
    ∃ w, verifyPacked (ps18 ++ [q]) w = true := by
  change 42 ≤ q at hlo
  change q ≤ 50 at hhi

  exact checked_window window18_0_prime_values window18_0_valid (by omega) (by omega) hp hlarge

def ps21 : List ℕ := [3, 5, 7, 11, 13, 17, 31, 41]

def window21_0g0 : List (ℕ × ℕ) := [
  (43, 0xc4284c4209441880a20c2c5004411c4a3044620844114241882a3002609843088261802410444204c1)
]

set_option maxHeartbeats 6000000 in
theorem window21_0g0_valid : window21_0g0.all (fun x => verifyPacked (ps21 ++ [x.1]) x.2) = true := by
  decide +kernel

def window21_0 : List (ℕ × ℕ) := window21_0g0

set_option maxHeartbeats 1500000 in
theorem window21_0_prime_values : window21_0.map Prod.fst = candidateFinals ps21 42 4 := by
  decide +kernel

theorem window21_0_valid : window21_0.all (fun x => verifyPacked (ps21 ++ [x.1]) x.2) = true := by
  exact window21_0g0_valid

theorem prefix21_verified {q : ℕ} (hlo : start ps21 ≤ q) (hhi : q ≤ lastCap ps21)
    (hp : q.Prime) (hlarge : 3 * den ps21 * (q-1) < ps21.prod * q) :
    ∃ w, verifyPacked (ps21 ++ [q]) w = true := by
  change 42 ≤ q at hlo
  change q ≤ 45 at hhi

  exact checked_window window21_0_prime_values window21_0_valid (by omega) (by omega) hp hlarge

def ps25 : List ℕ := [3, 5, 7, 11, 13, 19, 23, 41]

def window25_0g0 : List (ℕ × ℕ) := [
  (43, 0x30882610426180241102420441),
  (47, 0x30882610426180221102420441),
  (53, 0x3094230882610426180261102420441)
]

set_option maxHeartbeats 6000000 in
theorem window25_0g0_valid : window25_0g0.all (fun x => verifyPacked (ps25 ++ [x.1]) x.2) = true := by
  decide +kernel

def window25_0 : List (ℕ × ℕ) := window25_0g0

set_option maxHeartbeats 1500000 in
theorem window25_0_prime_values : window25_0.map Prod.fst = candidateFinals ps25 42 17 := by
  decide +kernel

theorem window25_0_valid : window25_0.all (fun x => verifyPacked (ps25 ++ [x.1]) x.2) = true := by
  exact window25_0g0_valid

theorem prefix25_verified {q : ℕ} (hlo : start ps25 ≤ q) (hhi : q ≤ lastCap ps25)
    (hp : q.Prime) (hlarge : 3 * den ps25 * (q-1) < ps25.prod * q) :
    ∃ w, verifyPacked (ps25 ++ [q]) w = true := by
  change 42 ≤ q at hlo
  change q ≤ 58 at hhi

  exact checked_window window25_0_prime_values window25_0_valid (by omega) (by omega) hp hlarge

set_option maxHeartbeats 2000000 in
theorem viable_prefixes_exact : viablePrefixes = [[3, 5, 7, 11, 13, 17, 19, 41], [3, 5, 7, 11, 13, 17, 19, 43], [3, 5, 7, 11, 13, 17, 19, 47], [3, 5, 7, 11, 13, 17, 19, 53], [3, 5, 7, 11, 13, 17, 19, 59], [3, 5, 7, 11, 13, 17, 19, 61], [3, 5, 7, 11, 13, 17, 19, 67], [3, 5, 7, 11, 13, 17, 19, 71], [3, 5, 7, 11, 13, 17, 19, 73], [3, 5, 7, 11, 13, 17, 23, 29], [3, 5, 7, 11, 13, 17, 23, 31], [3, 5, 7, 11, 13, 17, 23, 37], [3, 5, 7, 11, 13, 17, 23, 41], [3, 5, 7, 11, 13, 17, 23, 43], [3, 5, 7, 11, 13, 17, 23, 47], [3, 5, 7, 11, 13, 17, 23, 53], [3, 5, 7, 11, 13, 17, 29, 31], [3, 5, 7, 11, 13, 17, 29, 37], [3, 5, 7, 11, 13, 17, 29, 41], [3, 5, 7, 11, 13, 17, 29, 43], [3, 5, 7, 11, 13, 17, 31, 37], [3, 5, 7, 11, 13, 17, 31, 41], [3, 5, 7, 11, 13, 19, 23, 29], [3, 5, 7, 11, 13, 19, 23, 31], [3, 5, 7, 11, 13, 19, 23, 37], [3, 5, 7, 11, 13, 19, 23, 41], [3, 5, 7, 11, 13, 19, 23, 43], [3, 5, 7, 11, 13, 19, 23, 47], [3, 5, 7, 11, 13, 19, 29, 31], [3, 5, 7, 11, 13, 19, 29, 37], [3, 5, 7, 11, 13, 19, 31, 37], [3, 5, 7, 11, 13, 23, 29, 31], [3, 5, 7, 11, 17, 19, 23, 29], [3, 5, 7, 11, 17, 19, 23, 31]] := by
  decide +kernel

theorem word_exists_of_viable {ps : List ℕ} (hm : ps ∈ viablePrefixes)
    (hinterval : 38 ≤ (ps[7]?).getD 0 ∧ (ps[7]?).getD 0 ≤ 41)
    {q : ℕ} (hlo : start ps ≤ q) (hhi : q ≤ lastCap ps)
    (hp : q.Prime) (hlarge : 3 * den ps * (q-1) < ps.prod * q) :
    ∃ w, verifyPacked (ps ++ [q]) w = true := by
  rw [viable_prefixes_exact] at hm
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
  rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact prefix0_verified hlo hhi hp hlarge
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
  · norm_num at hinterval
  · exact prefix12_verified hlo hhi hp hlarge
  · norm_num at hinterval
  · norm_num at hinterval
  · norm_num at hinterval
  · norm_num at hinterval
  · norm_num at hinterval
  · exact prefix18_verified hlo hhi hp hlarge
  · norm_num at hinterval
  · norm_num at hinterval
  · exact prefix21_verified hlo hhi hp hlarge
  · norm_num at hinterval
  · norm_num at hinterval
  · norm_num at hinterval
  · exact prefix25_verified hlo hhi hp hlarge
  · norm_num at hinterval
  · norm_num at hinterval
  · norm_num at hinterval
  · norm_num at hinterval
  · norm_num at hinterval
  · norm_num at hinterval
  · norm_num at hinterval
  · norm_num at hinterval

theorem exclude_bounded
    (checkedWord : ∀ ps ∈ viablePrefixes, 38 ≤ (ps[7]?).getD 0 ∧ (ps[7]?).getD 0 ≤ 41 → ∀ q : ℕ, start ps ≤ q → q ≤ lastCap ps →
      q.Prime → 3 * den ps * (q-1) < ps.prod * q →
      ∃ w, verifyPacked (ps ++ [q]) w = true) :
    OMA.R_OeisA76495_conjecture_R1_H1_R1_H4_R1_H2_R1_H1_R1.H3 := by
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
  have hinter : 38 ≤ (ps[7]?).getD 0 ∧ (ps[7]?).getD 0 ≤ 41 := by
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

theorem OMA.solution : OMA.R_OeisA76495_conjecture_R1_H1_R1_H4_R1_H2_R1_H1_R1.H3 :=
  SigmaNine.exclude_bounded (fun _ hm hi _ hlo hhi hp hc =>
    SigmaNine.word_exists_of_viable hm hi hlo hhi hp hc)
