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
def ps1 : List ℕ := [3, 5, 7, 11, 13, 17, 19, 43]

def window1_0g0 : List (ℕ × ℕ) := [
  (47, 0x6104261804308823080222044420441),
  (53, 0x6104261804308823080262044420441),
  (59, 0x309826104261804308823080222044420441),
  (61, 0x309826104261804308823080212044420441),
  (67, 0x30982418826104261804308823080242044420441),
  (71, 0x308826180222044420441),
  (73, 0x8140482288040a0241142a380441884000144184c410881408040a02620824114441882730043098461044308826180212044420441),
  (79, 0x3098261044308826180212044420441),
  (83, 0x3098261044308826180242044420441),
  (89, 0x4114241884730043098261044308826180222044420441),
  (97, 0x309824114262082a3802610443088261802a2044420441),
  (101, 0x30882610426180222044420441),
  (103, 0x30882610426180262044420441)
]

set_option maxHeartbeats 6000000 in
theorem window1_0g0_valid : window1_0g0.all (fun x => verifyPacked (ps1 ++ [x.1]) x.2) = true := by
  decide +kernel

def window1_0g1 : List (ℕ × ℕ) := [
  (107, 0x30882610426180242044420441),
  (109, 0x30882610426180242044420441),
  (113, 0x308826104261802a2044420441),
  (127, 0x30882610426180212044420441),
  (131, 0x30882610426180222044420441),
  (137, 0x30882610426180262044420441),
  (139, 0x30882610426180242044420441)
]

set_option maxHeartbeats 6000000 in
theorem window1_0g1_valid : window1_0g1.all (fun x => verifyPacked (ps1 ++ [x.1]) x.2) = true := by
  decide +kernel

def window1_0 : List (ℕ × ℕ) := window1_0g0 ++ window1_0g1

set_option maxHeartbeats 1500000 in
theorem window1_0_prime_values : window1_0.map Prod.fst = candidateFinals ps1 44 96 := by
  decide +kernel

theorem window1_0_valid : window1_0.all (fun x => verifyPacked (ps1 ++ [x.1]) x.2) = true := by
  simp only [window1_0, List.all_append, window1_0g0_valid, window1_0g1_valid, Bool.and_self]

def window1_1g0 : List (ℕ × ℕ) := [
  (149, 0x30882610426180242044420441),
  (151, 0x30882610426180242044420441),
  (157, 0x30882610426180212044420441),
  (163, 0x30a024114441884730043098430882610426180212044420441),
  (167, 0x4114241884730043098430882610426180222044420441),
  (173, 0x822854700883108041882730043098430882610426180222044420441),
  (179, 0x82285470048310804114241882730043098430882610426180262044420441),
  (181, 0x82285470048310804114262082730044098430882610426180262044420441),
  (191, 0x62082a38044114241882730023098430882610426180262044420441),
  (193, 0x4114241882a38023098430882610426180212044420441),
  (197, 0x4114262082a38023098430882610426180242044420441),
  (199, 0x3098230882610426180212044420441),
  (211, 0x3098230882610426180212044420441)
]

set_option maxHeartbeats 6000000 in
theorem window1_1g0_valid : window1_1g0.all (fun x => verifyPacked (ps1 ++ [x.1]) x.2) = true := by
  decide +kernel

def window1_1g1 : List (ℕ × ℕ) := [
  (223, 0x3098230882610426180262044420441),
  (227, 0x3098230882610426180222044420441),
  (229, 0x3098230882610426180212044420441),
  (233, 0x3098230882610426180242044420441)
]

set_option maxHeartbeats 6000000 in
theorem window1_1g1_valid : window1_1g1.all (fun x => verifyPacked (ps1 ++ [x.1]) x.2) = true := by
  decide +kernel

def window1_1 : List (ℕ × ℕ) := window1_1g0 ++ window1_1g1

set_option maxHeartbeats 1500000 in
theorem window1_1_prime_values : window1_1.map Prod.fst = candidateFinals ps1 140 96 := by
  decide +kernel

theorem window1_1_valid : window1_1.all (fun x => verifyPacked (ps1 ++ [x.1]) x.2) = true := by
  simp only [window1_1, List.all_append, window1_1g0_valid, window1_1g1_valid, Bool.and_self]

def window1_2g0 : List (ℕ × ℕ) := [
  (239, 0x3098230882610426180242044420441),
  (241, 0x3098230882610426180242044420441),
  (251, 0x3098230882610426180262044420441),
  (257, 0x3098230882610426180222044420441),
  (263, 0x3098230882610426180242044420441),
  (269, 0x30982308826104261802a2044420441),
  (271, 0x3098230882610426180242044420441),
  (277, 0x3098230882610426180212044420441),
  (281, 0x3098230882610426180222044420441),
  (283, 0x3098230882610426180212044420441),
  (293, 0x3098230882610426180222044420441),
  (307, 0x3098230882610426180242048420441),
  (311, 0x4114241884730043098230882610426180262044420441)
]

set_option maxHeartbeats 6000000 in
theorem window1_2g0_valid : window1_2g0.all (fun x => verifyPacked (ps1 ++ [x.1]) x.2) = true := by
  decide +kernel

def window1_2g1 : List (ℕ × ℕ) := [
  (313, 0x4114241884730043098230882610426180212044420441),
  (317, 0xc4284c42048330804198262102a20c441142a3042418847300430982308826104261802a2044420441),
  (331, 0x208a151c0220c42000000288308c28100062102a20c430a0241984a3044620844114441882730043098230882610426180212044420441)
]

set_option maxHeartbeats 6000000 in
theorem window1_2g1_valid : window1_2g1.all (fun x => verifyPacked (ps1 ++ [x.1]) x.2) = true := by
  decide +kernel

def window1_2 : List (ℕ × ℕ) := window1_2g0 ++ window1_2g1

set_option maxHeartbeats 1500000 in
theorem window1_2_prime_values : window1_2.map Prod.fst = candidateFinals ps1 236 96 := by
  decide +kernel

theorem window1_2_valid : window1_2.all (fun x => verifyPacked (ps1 ++ [x.1]) x.2) = true := by
  simp only [window1_2, List.all_append, window1_2g0_valid, window1_2g1_valid, Bool.and_self]

def window1_3g0 : List (ℕ × ℕ) := [
  (337, 0x10450a8e0110621000620824114441882730043098230882610426180242044420441),
  (347, 0x822848310804114241882730043098230882610426180242044420441),
  (349, 0x62102419840000c4304c4288c420883305441894608947008822848310804114241882730043098230882610426180242044420441),
  (353, 0x82285470048310804114241882730043098230882610426180242044420441),
  (359, 0x82285470048310804114262082730043098230882610426180242044420441),
  (367, 0xc4284c42060d00544188614088330800018840a88310c281000621426210230a04018501310815106220cc26280251822208a120c4200000000062102a20c430a0441984a3044620844114441882a38043098230882610427300212044420441),
  (373, 0x6208241144a38043098241882610427300242044420441),
  (379, 0xc4204e61048330804198262102a20c462082a304241144a380430982418826104273002a2044420441),
  (383, 0x41142a38043098241882610427300222044420441),
  (389, 0xc420544188833098a00946088c410882288041142a38043098241882610427300262044420441),
  (397, 0xc42046140944188833098a00946088c41048228800000030a02a20c441984a30446208441142a38043098241882610427300212044420441),
  (401, 0x358009cc2118840a88311066100062182a3883068026210441982a20c2a3044001884090661000730826210441982a20c4a3042c5004620824114400000621826214462102a20c441982a30426208441142a38043098241882610427300262044420441),
  (409, 0x62142730846210430a040000c4284e6108c4208614054418883308030a0241982a20c2a304462082a3804309824114241882610427300212044420441)
]

set_option maxHeartbeats 6000000 in
theorem window1_3g0_valid : window1_3g0.all (fun x => verifyPacked (ps1 ++ [x.1]) x.2) = true := by
  decide +kernel

def window1_3g1 : List (ℕ × ℕ) := [
  (419, 0x30982411424188261042a380242044420441),
  (421, 0x6214262104a0a04a20c441984c5004a30446208430982411424188261042a380212044420441)
]

set_option maxHeartbeats 6000000 in
theorem window1_3g1_valid : window1_3g1.all (fun x => verifyPacked (ps1 ++ [x.1]) x.2) = true := by
  decide +kernel

def window1_3 : List (ℕ × ℕ) := window1_3g0 ++ window1_3g1

set_option maxHeartbeats 1500000 in
theorem window1_3_prime_values : window1_3.map Prod.fst = candidateFinals ps1 332 96 := by
  decide +kernel

theorem window1_3_valid : window1_3.all (fun x => verifyPacked (ps1 ++ [x.1]) x.2) = true := by
  simp only [window1_3, List.all_append, window1_3g0_valid, window1_3g1_valid, Bool.and_self]

def window1_4g0 : List (ℕ × ℕ) := [
  (431, 0x30982411426208261042a380242044420441),
  (433, 0x62102a20c441984c5004a304430982411426208261042a380262044420441),
  (439, 0x310c1310a151c41834013108200006218262144d600462102730844198241142a20c262082a3042c500242044420441)
]

set_option maxHeartbeats 6000000 in
theorem window1_4g0_valid : window1_4g0.all (fun x => verifyPacked (ps1 ++ [x.1]) x.2) = true := by
  decide +kernel

def window1_4 : List (ℕ × ℕ) := window1_4g0

set_option maxHeartbeats 1500000 in
theorem window1_4_prime_values : window1_4.map Prod.fst = candidateFinals ps1 428 12 := by
  decide +kernel

theorem window1_4_valid : window1_4.all (fun x => verifyPacked (ps1 ++ [x.1]) x.2) = true := by
  exact window1_4g0_valid

theorem prefix1_verified {q : ℕ} (hlo : start ps1 ≤ q) (hhi : q ≤ lastCap ps1)
    (hp : q.Prime) (hlarge : 3 * den ps1 * (q-1) < ps1.prod * q) :
    ∃ w, verifyPacked (ps1 ++ [q]) w = true := by
  change 44 ≤ q at hlo
  change q ≤ 439 at hhi

  by_cases h0 : q < 140
  · exact checked_window window1_0_prime_values window1_0_valid (by omega) (by omega) hp hlarge

  by_cases h1 : q < 236
  · exact checked_window window1_1_prime_values window1_1_valid (by omega) (by omega) hp hlarge

  by_cases h2 : q < 332
  · exact checked_window window1_2_prime_values window1_2_valid (by omega) (by omega) hp hlarge

  by_cases h3 : q < 428
  · exact checked_window window1_3_prime_values window1_3_valid (by omega) (by omega) hp hlarge

  exact checked_window window1_4_prime_values window1_4_valid (by omega) (by omega) hp hlarge

def ps2 : List ℕ := [3, 5, 7, 11, 13, 17, 19, 47]

def window2_0g0 : List (ℕ × ℕ) := [
  (53, 0x309826104261804308823080261044420441),
  (59, 0x30982418826104261804308823080221044420441),
  (61, 0x308826180213044420441),
  (67, 0x3098261044308826180241044420441),
  (71, 0x3098261044308826180221044420441),
  (73, 0x3098261044308826180211044420441),
  (79, 0x188208c2811045100030a026208241144a380430982418827300261044308826180211044420441),
  (83, 0x30882610426180241044420441),
  (89, 0x30882610426180221044420441),
  (97, 0x30882610426180261044420441),
  (101, 0x30882610426180221044420441),
  (103, 0x30882610426180261044420441),
  (107, 0x30882610426180241044420441)
]

set_option maxHeartbeats 6000000 in
theorem window2_0g0_valid : window2_0g0.all (fun x => verifyPacked (ps2 ++ [x.1]) x.2) = true := by
  decide +kernel

def window2_0g1 : List (ℕ × ℕ) := [
  (109, 0x30882610426180241044420441),
  (113, 0x308826104261802a1044420441),
  (127, 0x61404822894700883108041882730043098430882610426180211044420441),
  (131, 0x18840988311847100c2384c41854608947008822848310804114241882730043098430882610426180221044420441),
  (137, 0xc410482288041142a380441882730023098430882610426180261044420441),
  (139, 0x4114241882a38023098430882610426180241044420441)
]

set_option maxHeartbeats 6000000 in
theorem window2_0g1_valid : window2_0g1.all (fun x => verifyPacked (ps2 ++ [x.1]) x.2) = true := by
  decide +kernel

def window2_0 : List (ℕ × ℕ) := window2_0g0 ++ window2_0g1

set_option maxHeartbeats 1500000 in
theorem window2_0_prime_values : window2_0.map Prod.fst = candidateFinals ps2 48 96 := by
  decide +kernel

theorem window2_0_valid : window2_0.all (fun x => verifyPacked (ps2 ++ [x.1]) x.2) = true := by
  simp only [window2_0, List.all_append, window2_0g0_valid, window2_0g1_valid, Bool.and_self]

def window2_1g0 : List (ℕ × ℕ) := [
  (149, 0x3098230882610426180241044420441),
  (151, 0x3098230882610426180241044420441),
  (157, 0x3098230882610426180211044420441),
  (163, 0x3098230882610426180211044420441),
  (167, 0x3098230882610426180221044420441),
  (173, 0x3098230882610426180221044420441),
  (179, 0x3098230882610426180261044420441),
  (181, 0x4098230882610426180261044420441),
  (191, 0x4114241884730043098230882610426180261044420441),
  (193, 0x3108120cc2000c4304c4284c420883304c4188c23880611c241982620c2a304430a024114241884730043098230882610426180211044420441),
  (197, 0x620c2611c4001884098831184709066100c238483304c4204c418546088822894700883108041882730043098230882610426180241044420441),
  (199, 0x208a151c0220c420000031061308e2000c4204c4188c2384833080611c24198262102620c2a304430a02620844114441882730043098230882610426180211044420441),
  (211, 0x3108120cc2000062182c5042d6004621426210441982620c4020cc131061628021850200000018850988411883110661314010c2809847100003108120cc2000062182d6004621426210441982620c4611c400188309847100c2384c4184833098a0086140546088822848310800000062102620c2611c40308e13106120cc2185020000620c241984611c430a02a3044620844114441882a38043098230882610427300211044420441)
]

set_option maxHeartbeats 6000000 in
theorem window2_1g0_valid : window2_1g0.all (fun x => verifyPacked (ps2 ++ [x.1]) x.2) = true := by
  decide +kernel

def window2_1g1 : List (ℕ × ℕ) := [
  (223, 0x7308262104620c441984611c4a304462082a3804309824114241882610427300261044420441),
  (227, 0x30982411424188261042a380221044420441),
  (229, 0x620c2611c40000c4285ac008c4204c4188c2384833080611c24198262102620c2a304400188409066100062182621426210441982620c4611c2a3042c500460a026208430982411424188261042a380211044420441)
]

set_option maxHeartbeats 6000000 in
theorem window2_1g1_valid : window2_1g1.all (fun x => verifyPacked (ps2 ++ [x.1]) x.2) = true := by
  decide +kernel

def window2_1 : List (ℕ × ℕ) := window2_1g0 ++ window2_1g1

set_option maxHeartbeats 1500000 in
theorem window2_1_prime_values : window2_1.map Prod.fst = candidateFinals ps2 144 89 := by
  decide +kernel

theorem window2_1_valid : window2_1.all (fun x => verifyPacked (ps2 ++ [x.1]) x.2) = true := by
  simp only [window2_1, List.all_append, window2_1g0_valid, window2_1g1_valid, Bool.and_self]

theorem prefix2_verified {q : ℕ} (hlo : start ps2 ≤ q) (hhi : q ≤ lastCap ps2)
    (hp : q.Prime) (hlarge : 3 * den ps2 * (q-1) < ps2.prod * q) :
    ∃ w, verifyPacked (ps2 ++ [q]) w = true := by
  change 48 ≤ q at hlo
  change q ≤ 232 at hhi

  by_cases h0 : q < 144
  · exact checked_window window2_0_prime_values window2_0_valid (by omega) (by omega) hp hlarge

  exact checked_window window2_1_prime_values window2_1_valid (by omega) (by omega) hp hlarge

def ps3 : List ℕ := [3, 5, 7, 11, 13, 17, 19, 53]

def window3_0g0 : List (ℕ × ℕ) := [
  (59, 0x3098261044308826180223044420441),
  (61, 0x3098261044308826180213044420441),
  (67, 0xc410482288041142a380430982418827300261044308826180243044420441),
  (71, 0x30882610426180223044420441),
  (73, 0x30882610426180213044420441),
  (79, 0x30882610426180213044420441),
  (83, 0x30882610426180243044420441),
  (89, 0x30882610426180223044420441),
  (97, 0x41882730043098430882610426180263044420441),
  (101, 0x4120262102620c2a30426208441144a380441882730023098430882610426180223044420441),
  (103, 0x28c30a8e21188409cc20b140118830a8c111882090451000a30426208441142a380441882730023098430882610426180263044420441),
  (107, 0x3098230882610426180243044420441),
  (109, 0x3098230882610426180243044420441)
]

set_option maxHeartbeats 6000000 in
theorem window3_0g0_valid : window3_0g0.all (fun x => verifyPacked (ps3 ++ [x.1]) x.2) = true := by
  decide +kernel

def window3_0g1 : List (ℕ × ℕ) := [
  (113, 0x30982308826104261802a3044420441),
  (127, 0x41982620c2a304230a044114441884730043098230882610426180213044420441),
  (131, 0x62102620c441984a30444114241884730043098230882610426180223044420441),
  (137, 0x82285470048310804114241882730043098230882610426180263044420441),
  (139, 0x208a151c0120c420000a30c2c5042a3884621826214273082621044198241142620c262082a3042730043098230882610426180243044420441)
]

set_option maxHeartbeats 6000000 in
theorem window3_0g1_valid : window3_0g1.all (fun x => verifyPacked (ps3 ++ [x.1]) x.2) = true := by
  decide +kernel

def window3_0 : List (ℕ × ℕ) := window3_0g0 ++ window3_0g1

set_option maxHeartbeats 1500000 in
theorem window3_0_prime_values : window3_0.map Prod.fst = candidateFinals ps3 54 95 := by
  decide +kernel

theorem window3_0_valid : window3_0.all (fun x => verifyPacked (ps3 ++ [x.1]) x.2) = true := by
  simp only [window3_0, List.all_append, window3_0g0_valid, window3_0g1_valid, Bool.and_self]

theorem prefix3_verified {q : ℕ} (hlo : start ps3 ≤ q) (hhi : q ≤ lastCap ps3)
    (hp : q.Prime) (hlarge : 3 * den ps3 * (q-1) < ps3.prod * q) :
    ∃ w, verifyPacked (ps3 ++ [q]) w = true := by
  change 54 ≤ q at hlo
  change q ≤ 148 at hhi

  exact checked_window window3_0_prime_values window3_0_valid (by omega) (by omega) hp hlarge

def ps4 : List ℕ := [3, 5, 7, 11, 13, 17, 19, 59]

def window4_0g0 : List (ℕ × ℕ) := [
  (61, 0x30882610426180211044420441),
  (67, 0x30882610426180241044420441),
  (71, 0x30882610426180221044420441),
  (73, 0x30882610426180211044420441),
  (79, 0xc4204c2388c41880611c262102620c2a304430a044114441884730043098430882610426180211044420441),
  (83, 0xc4204c2388c41880611c262102620c2a30440018470988409883128c10b1401104510082285470088310804114241882730043098430882610426180241044420441),
  (89, 0x3098230882610426180221044420441),
  (97, 0x3098230882610426180261044420441),
  (101, 0x3098230882610426180221044420441),
  (103, 0x4114241884730043098230882610426180261044420441),
  (107, 0x10450a8e01106210000018840984711066100000188609cc21188411847100c2384c4204e610483308c41880611c24198262102620c2a3044620824114441882730043098230882610426180241044420441),
  (109, 0x82285470048310804114262082730043098230882610426180241044420441),
  (113, 0x188509cc211884118471188311066100000000a30c262184621447308462104611c40308e13108120cc2000062182621447308262104611c241982620c4a304462082a38043098241142418826104273002a1044420441)
]

set_option maxHeartbeats 6000000 in
theorem window4_0g0_valid : window4_0g0.all (fun x => verifyPacked (ps4 ++ [x.1]) x.2) = true := by
  decide +kernel

def window4_0 : List (ℕ × ℕ) := window4_0g0

set_option maxHeartbeats 1500000 in
theorem window4_0_prime_values : window4_0.map Prod.fst = candidateFinals ps4 60 56 := by
  decide +kernel

theorem window4_0_valid : window4_0.all (fun x => verifyPacked (ps4 ++ [x.1]) x.2) = true := by
  exact window4_0g0_valid

theorem prefix4_verified {q : ℕ} (hlo : start ps4 ≤ q) (hhi : q ≤ lastCap ps4)
    (hp : q.Prime) (hlarge : 3 * den ps4 * (q-1) < ps4.prod * q) :
    ∃ w, verifyPacked (ps4 ++ [q]) w = true := by
  change 60 ≤ q at hlo
  change q ≤ 115 at hhi

  exact checked_window window4_0_prime_values window4_0_valid (by omega) (by omega) hp hlarge

def ps5 : List ℕ := [3, 5, 7, 11, 13, 17, 19, 61]

def window5_0g0 : List (ℕ × ℕ) := [
  (67, 0x30882610426180240844420441),
  (71, 0x30882610426180220844420441),
  (73, 0x30882610426180210844420441),
  (79, 0x3104118502208a2000062102620c2a30426208430a0241144a3804309c400000000250005462098a088834094618a0d004c4288062142d600430a0262102620c2a3042c5002309c4018501184e1208a200c2808c27090450a8e01106210000000c4284c4208c418946084c410861408030a026208241144309c241882730043098430882610426180210844420441),
  (83, 0x18850c1a0098841188310006214262104620c2c5004a304262084309c24114241882a38023098430882610426180240844420441),
  (89, 0x3098230882610426180220844420441),
  (97, 0x6218262102620c441982a304241144309c241884730043098230882610426180260844420441),
  (101, 0x188209045128e010c27100041142a3804309c241884000000031410a8c311067110480a8e20988411066100000008338547108c43088240804120262182730846210441982620c462082a304241144309c241882730043098230882610426180220844420441),
  (103, 0x310c16b002398423108220cc131061310415182162801208a201045098820a8e010c2710061384822854700483108000000419c2a388462182621446210273082620c441982a3044309c24114262082730043098230882610426180260844420441),
  (107, 0x309c230982411424188261042a380240844420441)
]

set_option maxHeartbeats 6000000 in
theorem window5_0g0_valid : window5_0g0.all (fun x => verifyPacked (ps5 ++ [x.1]) x.2) = true := by
  decide +kernel

def window5_0 : List (ℕ × ℕ) := window5_0g0

set_option maxHeartbeats 1500000 in
theorem window5_0_prime_values : window5_0.map Prod.fst = candidateFinals ps5 62 47 := by
  decide +kernel

theorem window5_0_valid : window5_0.all (fun x => verifyPacked (ps5 ++ [x.1]) x.2) = true := by
  exact window5_0g0_valid

theorem prefix5_verified {q : ℕ} (hlo : start ps5 ≤ q) (hhi : q ≤ lastCap ps5)
    (hp : q.Prime) (hlarge : 3 * den ps5 * (q-1) < ps5.prod * q) :
    ∃ w, verifyPacked (ps5 ++ [q]) w = true := by
  change 62 ≤ q at hlo
  change q ≤ 108 at hhi

  exact checked_window window5_0_prime_values window5_0_valid (by omega) (by omega) hp hlarge

def ps6 : List ℕ := [3, 5, 7, 11, 13, 17, 19, 67]

def window6_0g0 : List (ℕ × ℕ) := [
  (71, 0x4090131081310620204809884098830b140128c11104510082285470088310804114241882730043098430882610426180222044420441),
  (73, 0x1884098830a8c10b140098821102810081404c410482288040a0241142a380441882730023098430882610426180212044420441),
  (79, 0x3098230882610426180212044420441),
  (83, 0x3098230882610426180242044420441),
  (89, 0x822854700483108000000621424120462104620c241984a3042620844114241882730043098230882610426180222044420441)
]

set_option maxHeartbeats 6000000 in
theorem window6_0g0_valid : window6_0g0.all (fun x => verifyPacked (ps6 ++ [x.1]) x.2) = true := by
  decide +kernel

def window6_0 : List (ℕ × ℕ) := window6_0g0

set_option maxHeartbeats 1500000 in
theorem window6_0_prime_values : window6_0.map Prod.fst = candidateFinals ps6 68 26 := by
  decide +kernel

theorem window6_0_valid : window6_0.all (fun x => verifyPacked (ps6 ++ [x.1]) x.2) = true := by
  exact window6_0g0_valid

theorem prefix6_verified {q : ℕ} (hlo : start ps6 ≤ q) (hhi : q ≤ lastCap ps6)
    (hp : q.Prime) (hlarge : 3 * den ps6 * (q-1) < ps6.prod * q) :
    ∃ w, verifyPacked (ps6 ++ [q]) w = true := by
  change 68 ≤ q at hlo
  change q ≤ 93 at hhi

  exact checked_window window6_0_prime_values window6_0_valid (by omega) (by omega) hp hlarge

def ps7 : List ℕ := [3, 5, 7, 11, 13, 17, 19, 71]

def window7_0g0 : List (ℕ × ℕ) := [
  (73, 0x3098230882610426180211044420441),
  (79, 0x30a024114441884730043098230882610426180211044420441),
  (83, 0x82285470048310804114262082730043098230882610426180241044420441)
]

set_option maxHeartbeats 6000000 in
theorem window7_0g0_valid : window7_0g0.all (fun x => verifyPacked (ps7 ++ [x.1]) x.2) = true := by
  decide +kernel

def window7_0 : List (ℕ × ℕ) := window7_0g0

set_option maxHeartbeats 1500000 in
theorem window7_0_prime_values : window7_0.map Prod.fst = candidateFinals ps7 72 15 := by
  decide +kernel

theorem window7_0_valid : window7_0.all (fun x => verifyPacked (ps7 ++ [x.1]) x.2) = true := by
  exact window7_0g0_valid

theorem prefix7_verified {q : ℕ} (hlo : start ps7 ≤ q) (hhi : q ≤ lastCap ps7)
    (hp : q.Prime) (hlarge : 3 * den ps7 * (q-1) < ps7.prod * q) :
    ∃ w, verifyPacked (ps7 ++ [q]) w = true := by
  change 72 ≤ q at hlo
  change q ≤ 86 at hhi

  exact checked_window window7_0_prime_values window7_0_valid (by omega) (by omega) hp hlarge

def ps8 : List ℕ := [3, 5, 7, 11, 13, 17, 19, 73]

def window8_0g0 : List (ℕ × ℕ) := [
  (79, 0x30a02409c4018501204e1208a220c4200000000062182a31027308462102620c441982a30446208230a04409c441144018501204e1208a120c4200000018850988409883110660a8c11188210c2809027100041982620c2a30426208430a02409c2411444188273004a38043098230882610426180210844420441),
  (83, 0x409c230982411424188261042a380240844420441)
]

set_option maxHeartbeats 6000000 in
theorem window8_0g0_valid : window8_0g0.all (fun x => verifyPacked (ps8 ++ [x.1]) x.2) = true := by
  decide +kernel

def window8_0 : List (ℕ × ℕ) := window8_0g0

set_option maxHeartbeats 1500000 in
theorem window8_0_prime_values : window8_0.map Prod.fst = candidateFinals ps8 74 10 := by
  decide +kernel

theorem window8_0_valid : window8_0.all (fun x => verifyPacked (ps8 ++ [x.1]) x.2) = true := by
  exact window8_0g0_valid

theorem prefix8_verified {q : ℕ} (hlo : start ps8 ≤ q) (hhi : q ≤ lastCap ps8)
    (hp : q.Prime) (hlarge : 3 * den ps8 * (q-1) < ps8.prod * q) :
    ∃ w, verifyPacked (ps8 ++ [q]) w = true := by
  change 74 ≤ q at hlo
  change q ≤ 83 at hhi

  exact checked_window window8_0_prime_values window8_0_valid (by omega) (by omega) hp hlarge

def ps13 : List ℕ := [3, 5, 7, 11, 13, 17, 23, 43]

def window13_0g0 : List (ℕ × ℕ) := [
  (47, 0x308826180222104420441),
  (53, 0x30882610426180262104420441),
  (59, 0x30882610426180222104420441),
  (61, 0x30882610426180212104420441),
  (67, 0x30882610426180242104420441),
  (71, 0x30882610426180222104420441),
  (73, 0x30882610426180212104420441),
  (79, 0x18501208a261c0220c4200006208230a0441144418827300430882610426180212104420441),
  (83, 0xe610482408c42094418906088c41048228800000062182621444120262104a20c2830446208441142c380441882610427300222104420441)
]

set_option maxHeartbeats 6000000 in
theorem window13_0g0_valid : window13_0g0.all (fun x => verifyPacked (ps13 ++ [x.1]) x.2) = true := by
  decide +kernel

def window13_0 : List (ℕ × ℕ) := window13_0g0

set_option maxHeartbeats 1500000 in
theorem window13_0_prime_values : window13_0.map Prod.fst = candidateFinals ps13 44 41 := by
  decide +kernel

theorem window13_0_valid : window13_0.all (fun x => verifyPacked (ps13 ++ [x.1]) x.2) = true := by
  exact window13_0g0_valid

theorem prefix13_verified {q : ℕ} (hlo : start ps13 ≤ q) (hhi : q ≤ lastCap ps13)
    (hp : q.Prime) (hlarge : 3 * den ps13 * (q-1) < ps13.prod * q) :
    ∃ w, verifyPacked (ps13 ++ [q]) w = true := by
  change 44 ≤ q at hlo
  change q ≤ 84 at hhi

  exact checked_window window13_0_prime_values window13_0_valid (by omega) (by omega) hp hlarge

def ps14 : List ℕ := [3, 5, 7, 11, 13, 17, 23, 47]

def window14_0g0 : List (ℕ × ℕ) := [
  (53, 0x30882610426180261104420441),
  (59, 0x30882610426180221104420441),
  (61, 0x30882610426180213104420441),
  (67, 0x30882610426180241104420441),
  (71, 0x30c40a8c30988612901135801204810102404c4208c2384c418506084c410882288041142c380441882610427300221104420441)
]

set_option maxHeartbeats 6000000 in
theorem window14_0g0_valid : window14_0g0.all (fun x => verifyPacked (ps14 ++ [x.1]) x.2) = true := by
  decide +kernel

def window14_0 : List (ℕ × ℕ) := window14_0g0

set_option maxHeartbeats 1500000 in
theorem window14_0_prime_values : window14_0.map Prod.fst = candidateFinals ps14 48 25 := by
  decide +kernel

theorem window14_0_valid : window14_0.all (fun x => verifyPacked (ps14 ++ [x.1]) x.2) = true := by
  exact window14_0g0_valid

theorem prefix14_verified {q : ℕ} (hlo : start ps14 ≤ q) (hhi : q ≤ lastCap ps14)
    (hp : q.Prime) (hlarge : 3 * den ps14 * (q-1) < ps14.prod * q) :
    ∃ w, verifyPacked (ps14 ++ [q]) w = true := by
  change 48 ≤ q at hlo
  change q ≤ 72 at hhi

  exact checked_window window14_0_prime_values window14_0_valid (by omega) (by omega) hp hlarge

def ps15 : List ℕ := [3, 5, 7, 11, 13, 17, 23, 53]

def window15_0g0 : List (ℕ × ℕ) := [
  (59, 0x10450b0e01106210006208241144418827300430882610426180223104420441),
  (61, 0x41a02a30c262184020d01310c1818815186151c4252022310a200008314303102c504441a02a30c26218462142a40427308462102620c26208283042c380430a024114241882610427300213104420441)
]

set_option maxHeartbeats 6000000 in
theorem window15_0g0_valid : window15_0g0.all (fun x => verifyPacked (ps15 ++ [x.1]) x.2) = true := by
  decide +kernel

def window15_0 : List (ℕ × ℕ) := window15_0g0

set_option maxHeartbeats 1500000 in
theorem window15_0_prime_values : window15_0.map Prod.fst = candidateFinals ps15 54 8 := by
  decide +kernel

theorem window15_0_valid : window15_0.all (fun x => verifyPacked (ps15 ++ [x.1]) x.2) = true := by
  exact window15_0g0_valid

theorem prefix15_verified {q : ℕ} (hlo : start ps15 ≤ q) (hhi : q ≤ lastCap ps15)
    (hp : q.Prime) (hlarge : 3 * den ps15 * (q-1) < ps15.prod * q) :
    ∃ w, verifyPacked (ps15 ++ [q]) w = true := by
  change 54 ≤ q at hlo
  change q ≤ 61 at hhi

  exact checked_window window15_0_prime_values window15_0_valid (by omega) (by omega) hp hlarge

def ps19 : List ℕ := [3, 5, 7, 11, 13, 17, 29, 43]

def window19_0g0 : List (ℕ × ℕ) := [
  (47, 0xe410482288041142a380441882610427300222104420441)
]

set_option maxHeartbeats 6000000 in
theorem window19_0g0_valid : window19_0g0.all (fun x => verifyPacked (ps19 ++ [x.1]) x.2) = true := by
  decide +kernel

def window19_0 : List (ℕ × ℕ) := window19_0g0

set_option maxHeartbeats 1500000 in
theorem window19_0_prime_values : window19_0.map Prod.fst = candidateFinals ps19 44 4 := by
  decide +kernel

theorem window19_0_valid : window19_0.all (fun x => verifyPacked (ps19 ++ [x.1]) x.2) = true := by
  exact window19_0g0_valid

theorem prefix19_verified {q : ℕ} (hlo : start ps19 ≤ q) (hhi : q ≤ lastCap ps19)
    (hp : q.Prime) (hlarge : 3 * den ps19 * (q-1) < ps19.prod * q) :
    ∃ w, verifyPacked (ps19 ++ [q]) w = true := by
  change 44 ≤ q at hlo
  change q ≤ 47 at hhi

  exact checked_window window19_0_prime_values window19_0_valid (by omega) (by omega) hp hlarge

def ps26 : List ℕ := [3, 5, 7, 11, 13, 19, 23, 43]

def window26_0g0 : List (ℕ × ℕ) := [
  (47, 0x41882730023094430882610426180222102420441),
  (53, 0xc42054418883289460898700883108041882730043094230882610426180262102420441)
]

set_option maxHeartbeats 6000000 in
theorem window26_0g0_valid : window26_0g0.all (fun x => verifyPacked (ps26 ++ [x.1]) x.2) = true := by
  decide +kernel

def window26_0 : List (ℕ × ℕ) := window26_0g0

set_option maxHeartbeats 1500000 in
theorem window26_0_prime_values : window26_0.map Prod.fst = candidateFinals ps26 44 11 := by
  decide +kernel

theorem window26_0_valid : window26_0.all (fun x => verifyPacked (ps26 ++ [x.1]) x.2) = true := by
  exact window26_0g0_valid

theorem prefix26_verified {q : ℕ} (hlo : start ps26 ≤ q) (hhi : q ≤ lastCap ps26)
    (hp : q.Prime) (hlarge : 3 * den ps26 * (q-1) < ps26.prod * q) :
    ∃ w, verifyPacked (ps26 ++ [q]) w = true := by
  change 44 ≤ q at hlo
  change q ≤ 54 at hhi

  exact checked_window window26_0_prime_values window26_0_valid (by omega) (by omega) hp hlarge

def ps27 : List ℕ := [3, 5, 7, 11, 13, 19, 23, 47]

def window27_0g0 : List (ℕ × ℕ) := []

set_option maxHeartbeats 6000000 in
theorem window27_0g0_valid : window27_0g0.all (fun x => verifyPacked (ps27 ++ [x.1]) x.2) = true := by
  decide +kernel

def window27_0 : List (ℕ × ℕ) := window27_0g0

set_option maxHeartbeats 1500000 in
theorem window27_0_prime_values : window27_0.map Prod.fst = candidateFinals ps27 48 2 := by
  decide +kernel

theorem window27_0_valid : window27_0.all (fun x => verifyPacked (ps27 ++ [x.1]) x.2) = true := by
  exact window27_0g0_valid

theorem prefix27_verified {q : ℕ} (hlo : start ps27 ≤ q) (hhi : q ≤ lastCap ps27)
    (hp : q.Prime) (hlarge : 3 * den ps27 * (q-1) < ps27.prod * q) :
    ∃ w, verifyPacked (ps27 ++ [q]) w = true := by
  change 48 ≤ q at hlo
  change q ≤ 49 at hhi

  exact checked_window window27_0_prime_values window27_0_valid (by omega) (by omega) hp hlarge

set_option maxHeartbeats 2000000 in
theorem viable_prefixes_exact : viablePrefixes = [[3, 5, 7, 11, 13, 17, 19, 41], [3, 5, 7, 11, 13, 17, 19, 43], [3, 5, 7, 11, 13, 17, 19, 47], [3, 5, 7, 11, 13, 17, 19, 53], [3, 5, 7, 11, 13, 17, 19, 59], [3, 5, 7, 11, 13, 17, 19, 61], [3, 5, 7, 11, 13, 17, 19, 67], [3, 5, 7, 11, 13, 17, 19, 71], [3, 5, 7, 11, 13, 17, 19, 73], [3, 5, 7, 11, 13, 17, 23, 29], [3, 5, 7, 11, 13, 17, 23, 31], [3, 5, 7, 11, 13, 17, 23, 37], [3, 5, 7, 11, 13, 17, 23, 41], [3, 5, 7, 11, 13, 17, 23, 43], [3, 5, 7, 11, 13, 17, 23, 47], [3, 5, 7, 11, 13, 17, 23, 53], [3, 5, 7, 11, 13, 17, 29, 31], [3, 5, 7, 11, 13, 17, 29, 37], [3, 5, 7, 11, 13, 17, 29, 41], [3, 5, 7, 11, 13, 17, 29, 43], [3, 5, 7, 11, 13, 17, 31, 37], [3, 5, 7, 11, 13, 17, 31, 41], [3, 5, 7, 11, 13, 19, 23, 29], [3, 5, 7, 11, 13, 19, 23, 31], [3, 5, 7, 11, 13, 19, 23, 37], [3, 5, 7, 11, 13, 19, 23, 41], [3, 5, 7, 11, 13, 19, 23, 43], [3, 5, 7, 11, 13, 19, 23, 47], [3, 5, 7, 11, 13, 19, 29, 31], [3, 5, 7, 11, 13, 19, 29, 37], [3, 5, 7, 11, 13, 19, 31, 37], [3, 5, 7, 11, 13, 23, 29, 31], [3, 5, 7, 11, 17, 19, 23, 29], [3, 5, 7, 11, 17, 19, 23, 31]] := by
  decide +kernel

theorem word_exists_of_viable {ps : List ℕ} (hm : ps ∈ viablePrefixes)
    (hinterval : 42 ≤ (ps[7]?).getD 0)
    {q : ℕ} (hlo : start ps ≤ q) (hhi : q ≤ lastCap ps)
    (hp : q.Prime) (hlarge : 3 * den ps * (q-1) < ps.prod * q) :
    ∃ w, verifyPacked (ps ++ [q]) w = true := by
  rw [viable_prefixes_exact] at hm
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
  rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · norm_num at hinterval
  · exact prefix1_verified hlo hhi hp hlarge
  · exact prefix2_verified hlo hhi hp hlarge
  · exact prefix3_verified hlo hhi hp hlarge
  · exact prefix4_verified hlo hhi hp hlarge
  · exact prefix5_verified hlo hhi hp hlarge
  · exact prefix6_verified hlo hhi hp hlarge
  · exact prefix7_verified hlo hhi hp hlarge
  · exact prefix8_verified hlo hhi hp hlarge
  · norm_num at hinterval
  · norm_num at hinterval
  · norm_num at hinterval
  · norm_num at hinterval
  · exact prefix13_verified hlo hhi hp hlarge
  · exact prefix14_verified hlo hhi hp hlarge
  · exact prefix15_verified hlo hhi hp hlarge
  · norm_num at hinterval
  · norm_num at hinterval
  · norm_num at hinterval
  · exact prefix19_verified hlo hhi hp hlarge
  · norm_num at hinterval
  · norm_num at hinterval
  · norm_num at hinterval
  · norm_num at hinterval
  · norm_num at hinterval
  · norm_num at hinterval
  · exact prefix26_verified hlo hhi hp hlarge
  · exact prefix27_verified hlo hhi hp hlarge
  · norm_num at hinterval
  · norm_num at hinterval
  · norm_num at hinterval
  · norm_num at hinterval
  · norm_num at hinterval
  · norm_num at hinterval

theorem exclude_bounded
    (checkedWord : ∀ ps ∈ viablePrefixes, 42 ≤ (ps[7]?).getD 0 → ∀ q : ℕ, start ps ≤ q → q ≤ lastCap ps →
      q.Prime → 3 * den ps * (q-1) < ps.prod * q →
      ∃ w, verifyPacked (ps ++ [q]) w = true) :
    OMA.R_OeisA76495_conjecture_R1_H1_R1_H4_R1_H2_R1_H1_R1.H4 := by
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
  have hinter : 42 ≤ (ps[7]?).getD 0 := by
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

theorem OMA.solution : OMA.R_OeisA76495_conjecture_R1_H1_R1_H4_R1_H2_R1_H1_R1.H4 :=
  SigmaNine.exclude_bounded (fun _ hm hi _ hlo hhi hp hc =>
    SigmaNine.word_exists_of_viable hm hi hlo hhi hp hc)
