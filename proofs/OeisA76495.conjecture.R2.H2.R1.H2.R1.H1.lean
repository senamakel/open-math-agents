import OMAReductions.R_OeisA76495_conjecture_R2_H2_R1_H2_R1
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

namespace R2SigmaAbundancyProof

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

end R2SigmaAbundancyProof

namespace SigmaLocalModuliFast
open R2SigmaAbundancyProof

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
open R2SigmaAbundancyProof SigmaLocalModuliFast

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

private def valueB (p e : Exponents) : ℕ :=
  (List.ofFn fun i => p i ^ e i).prod

private def divisorSumB (p e : Exponents) : ℕ :=
  (List.ofFn fun i => geometric (p i) (e i)).prod

private def upperNumB (p : Exponents) (u : Ceiling) : ℕ :=
  (List.ofFn fun i => numerator (p i) (u i)).prod

private def upperDenB (p : Exponents) (u : Ceiling) : ℕ :=
  (List.ofFn fun i => denominator (p i) (u i)).prod

private theorem valueB_eq (p e : Exponents) : valueB p e = value p e :=
  List.prod_ofFn

private theorem divisorSumB_eq (p e : Exponents) : divisorSumB p e = divisorSum p e :=
  List.prod_ofFn

private theorem upperNumB_eq (p : Exponents) (u : Ceiling) : upperNumB p u = upperNum p u :=
  List.prod_ofFn

private theorem upperDenB_eq (p : Exponents) (u : Ceiling) : upperDenB p u = upperDen p u :=
  List.prod_ofFn

def check (p l : Exponents) (u : Ceiling) : Certificate → Bool
  | .overshoot => decide (3 * valueB p l + 5 < divisorSumB p l)
  | .tighten i cut next child =>
      let bound := Function.update u i (some cut)
      decide (upperNumB p bound ≤ 3 * upperDenB p bound) &&
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
      simp only [check, valueB_eq, divisorSumB_eq, decide_eq_true_eq] at hc
      exact lower_excludes hp hl hc heq
  | tighten i cut next child ih =>
      simp only [check, upperNumB_eq, upperDenB_eq, Bool.and_eq_true, decide_eq_true_eq] at hc
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

open R2SigmaAbundancyProof SigmaNineBoxesFast

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

private def primeWindowCandidate (q : ℕ) : Bool :=
  decide (2 ≤ q) &&
    (List.range' 2 (Nat.sqrt q - 1)).all (fun d => decide (q % d ≠ 0))

private theorem primeWindowCandidate_of_prime {q : ℕ} (hp : q.Prime) :
    primeWindowCandidate q = true := by
  simp only [primeWindowCandidate, Bool.and_eq_true, decide_eq_true_eq]
  refine ⟨hp.two_le, List.all_eq_true.mpr ?_⟩
  intro d hd
  obtain ⟨hle, hlt⟩ := List.mem_range'_1.mp hd
  apply decide_eq_true
  intro hz
  exact (Nat.prime_def_le_sqrt.mp hp).2 d hle (by omega) (Nat.dvd_iff_mod_eq_zero.mpr hz)

def candidateFinals (ps : List ℕ) (low count : ℕ) : List ℕ :=
  let D := 3 * den ps
  let M := ps.prod
  (List.range' low count).filter
    (fun q => primeWindowCandidate q && decide (D * (q-1) < M * q))

theorem checked_window {ps : List ℕ} {lo count q : ℕ}
    {rows : List (ℕ × ℕ)}
    (hrows : rows.map Prod.fst = candidateFinals ps lo count)
    (hcheck : rows.all (fun x => verifyPacked (ps ++ [x.1]) x.2) = true)
    (hlo : lo ≤ q) (hhi : q < lo + count) (hp : q.Prime)
    (hlarge : 3 * den ps * (q-1) < ps.prod * q) :
    ∃ w, verifyPacked (ps ++ [q]) w = true := by
  have hm : q ∈ candidateFinals ps lo count :=
    List.mem_filter.mpr ⟨List.mem_range'_1.mpr ⟨hlo,hhi⟩,
      by simp [primeWindowCandidate_of_prime hp, hlarge]⟩
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

set_option maxRecDepth 8000 in
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

set_option maxRecDepth 8000 in
set_option maxHeartbeats 6000000 in
theorem window0_0g1_valid : window0_0g1.all (fun x => verifyPacked (ps0 ++ [x.1]) x.2) = true := by
  decide +kernel

def window0_0 : List (ℕ × ℕ) := window0_0g0 ++ window0_0g1

set_option maxRecDepth 8000 in
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

set_option maxRecDepth 8000 in
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

set_option maxRecDepth 8000 in
set_option maxHeartbeats 6000000 in
theorem window0_1g1_valid : window0_1g1.all (fun x => verifyPacked (ps0 ++ [x.1]) x.2) = true := by
  decide +kernel

def window0_1 : List (ℕ × ℕ) := window0_1g0 ++ window0_1g1

set_option maxRecDepth 8000 in
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

set_option maxRecDepth 8000 in
set_option maxHeartbeats 6000000 in
theorem window0_2g0_valid : window0_2g0.all (fun x => verifyPacked (ps0 ++ [x.1]) x.2) = true := by
  decide +kernel

def window0_2g1 : List (ℕ × ℕ) := [
  (313, 0x3098230882610426180211044420441),
  (317, 0x3098230882610426180261044420441)
]

set_option maxRecDepth 8000 in
set_option maxHeartbeats 6000000 in
theorem window0_2g1_valid : window0_2g1.all (fun x => verifyPacked (ps0 ++ [x.1]) x.2) = true := by
  decide +kernel

def window0_2 : List (ℕ × ℕ) := window0_2g0 ++ window0_2g1

set_option maxRecDepth 8000 in
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

set_option maxRecDepth 8000 in
set_option maxHeartbeats 6000000 in
theorem window0_3g0_valid : window0_3g0.all (fun x => verifyPacked (ps0 ++ [x.1]) x.2) = true := by
  decide +kernel

def window0_3g1 : List (ℕ × ℕ) := [
  (409, 0x3098230882610426180241044420441),
  (419, 0x3098230882610426180241044420441),
  (421, 0x3098230882610426180211044420441)
]

set_option maxRecDepth 8000 in
set_option maxHeartbeats 6000000 in
theorem window0_3g1_valid : window0_3g1.all (fun x => verifyPacked (ps0 ++ [x.1]) x.2) = true := by
  decide +kernel

def window0_3 : List (ℕ × ℕ) := window0_3g0 ++ window0_3g1

set_option maxRecDepth 8000 in
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

set_option maxRecDepth 8000 in
set_option maxHeartbeats 6000000 in
theorem window0_4g0_valid : window0_4g0.all (fun x => verifyPacked (ps0 ++ [x.1]) x.2) = true := by
  decide +kernel

def window0_4g1 : List (ℕ × ℕ) := [
  (503, 0x411c2419826214262102620c2a304241884a30043098230882610426180241044420441),
  (509, 0x41882a30043098230882610426180221044420441),
  (521, 0x41882a30043098230882610426180221044420441)
]

set_option maxRecDepth 8000 in
set_option maxHeartbeats 6000000 in
theorem window0_4g1_valid : window0_4g1.all (fun x => verifyPacked (ps0 ++ [x.1]) x.2) = true := by
  decide +kernel

def window0_4 : List (ℕ × ℕ) := window0_4g0 ++ window0_4g1

set_option maxRecDepth 8000 in
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

set_option maxRecDepth 8000 in
set_option maxHeartbeats 6000000 in
theorem window0_5g0_valid : window0_5g0.all (fun x => verifyPacked (ps0 ++ [x.1]) x.2) = true := by
  decide +kernel

def window0_5g1 : List (ℕ × ℕ) := [
  (613, 0x104509062100030a02411c2621826214262102620c2a3042620844114241882a30043098230882610426180211044420441),
  (617, 0x822848310804114262082a30043098230882610426180221044420441)
]

set_option maxRecDepth 8000 in
set_option maxHeartbeats 6000000 in
theorem window0_5g1_valid : window0_5g1.all (fun x => verifyPacked (ps0 ++ [x.1]) x.2) = true := by
  decide +kernel

def window0_5 : List (ℕ × ℕ) := window0_5g0 ++ window0_5g1

set_option maxRecDepth 8000 in
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

set_option maxRecDepth 8000 in
set_option maxHeartbeats 6000000 in
theorem window0_6g0_valid : window0_6g0.all (fun x => verifyPacked (ps0 ++ [x.1]) x.2) = true := by
  decide +kernel

def window0_6g1 : List (ℕ × ℕ) := [
  (709, 0xc280988411883110661000620c241984c5004411c4000000310c16b002185023108220cc131061208e2000030a0262102620c441984411c2c5004a30446208441144309824188261042a300211044420441)
]

set_option maxRecDepth 8000 in
set_option maxHeartbeats 6000000 in
theorem window0_6g1_valid : window0_6g1.all (fun x => verifyPacked (ps0 ++ [x.1]) x.2) = true := by
  decide +kernel

def window0_6 : List (ℕ × ℕ) := window0_6g0 ++ window0_6g1

set_option maxRecDepth 8000 in
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

set_option maxRecDepth 8000 in
set_option maxHeartbeats 6000000 in
theorem window0_7g0_valid : window0_7g0.all (fun x => verifyPacked (ps0 ++ [x.1]) x.2) = true := by
  decide +kernel

def window0_7 : List (ℕ × ℕ) := window0_7g0

set_option maxRecDepth 8000 in
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

set_option maxRecDepth 8000 in
set_option maxHeartbeats 6000000 in
theorem window0_8g0_valid : window0_8g0.all (fun x => verifyPacked (ps0 ++ [x.1]) x.2) = true := by
  decide +kernel

def window0_8g1 : List (ℕ × ℕ) := [
  (887, 0x106802621440310a16b00239842310823106120cc20000a388262184621426210273082620c441982c5004411c2309824114262082a3042a300241044420441)
]

set_option maxRecDepth 8000 in
set_option maxHeartbeats 6000000 in
theorem window0_8g1_valid : window0_8g1.all (fun x => verifyPacked (ps0 ++ [x.1]) x.2) = true := by
  decide +kernel

def window0_8 : List (ℕ × ℕ) := window0_8g0 ++ window0_8g1

set_option maxRecDepth 8000 in
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

set_option maxRecDepth 8000 in
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

set_option maxRecDepth 8000 in
set_option maxHeartbeats 6000000 in
theorem window1_0g1_valid : window1_0g1.all (fun x => verifyPacked (ps1 ++ [x.1]) x.2) = true := by
  decide +kernel

def window1_0 : List (ℕ × ℕ) := window1_0g0 ++ window1_0g1

set_option maxRecDepth 8000 in
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

set_option maxRecDepth 8000 in
set_option maxHeartbeats 6000000 in
theorem window1_1g0_valid : window1_1g0.all (fun x => verifyPacked (ps1 ++ [x.1]) x.2) = true := by
  decide +kernel

def window1_1g1 : List (ℕ × ℕ) := [
  (223, 0x3098230882610426180262044420441),
  (227, 0x3098230882610426180222044420441),
  (229, 0x3098230882610426180212044420441),
  (233, 0x3098230882610426180242044420441)
]

set_option maxRecDepth 8000 in
set_option maxHeartbeats 6000000 in
theorem window1_1g1_valid : window1_1g1.all (fun x => verifyPacked (ps1 ++ [x.1]) x.2) = true := by
  decide +kernel

def window1_1 : List (ℕ × ℕ) := window1_1g0 ++ window1_1g1

set_option maxRecDepth 8000 in
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

set_option maxRecDepth 8000 in
set_option maxHeartbeats 6000000 in
theorem window1_2g0_valid : window1_2g0.all (fun x => verifyPacked (ps1 ++ [x.1]) x.2) = true := by
  decide +kernel

def window1_2g1 : List (ℕ × ℕ) := [
  (313, 0x4114241884730043098230882610426180212044420441),
  (317, 0xc4284c42048330804198262102a20c441142a3042418847300430982308826104261802a2044420441),
  (331, 0x208a151c0220c42000000288308c28100062102a20c430a0241984a3044620844114441882730043098230882610426180212044420441)
]

set_option maxRecDepth 8000 in
set_option maxHeartbeats 6000000 in
theorem window1_2g1_valid : window1_2g1.all (fun x => verifyPacked (ps1 ++ [x.1]) x.2) = true := by
  decide +kernel

def window1_2 : List (ℕ × ℕ) := window1_2g0 ++ window1_2g1

set_option maxRecDepth 8000 in
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

set_option maxRecDepth 8000 in
set_option maxHeartbeats 6000000 in
theorem window1_3g0_valid : window1_3g0.all (fun x => verifyPacked (ps1 ++ [x.1]) x.2) = true := by
  decide +kernel

def window1_3g1 : List (ℕ × ℕ) := [
  (419, 0x30982411424188261042a380242044420441),
  (421, 0x6214262104a0a04a20c441984c5004a30446208430982411424188261042a380212044420441)
]

set_option maxRecDepth 8000 in
set_option maxHeartbeats 6000000 in
theorem window1_3g1_valid : window1_3g1.all (fun x => verifyPacked (ps1 ++ [x.1]) x.2) = true := by
  decide +kernel

def window1_3 : List (ℕ × ℕ) := window1_3g0 ++ window1_3g1

set_option maxRecDepth 8000 in
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

set_option maxRecDepth 8000 in
set_option maxHeartbeats 6000000 in
theorem window1_4g0_valid : window1_4g0.all (fun x => verifyPacked (ps1 ++ [x.1]) x.2) = true := by
  decide +kernel

def window1_4 : List (ℕ × ℕ) := window1_4g0

set_option maxRecDepth 8000 in
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

set_option maxRecDepth 8000 in
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

set_option maxRecDepth 8000 in
set_option maxHeartbeats 6000000 in
theorem window2_0g1_valid : window2_0g1.all (fun x => verifyPacked (ps2 ++ [x.1]) x.2) = true := by
  decide +kernel

def window2_0 : List (ℕ × ℕ) := window2_0g0 ++ window2_0g1

set_option maxRecDepth 8000 in
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

set_option maxRecDepth 8000 in
set_option maxHeartbeats 6000000 in
theorem window2_1g0_valid : window2_1g0.all (fun x => verifyPacked (ps2 ++ [x.1]) x.2) = true := by
  decide +kernel

def window2_1g1 : List (ℕ × ℕ) := [
  (223, 0x7308262104620c441984611c4a304462082a3804309824114241882610427300261044420441),
  (227, 0x30982411424188261042a380221044420441),
  (229, 0x620c2611c40000c4285ac008c4204c4188c2384833080611c24198262102620c2a304400188409066100062182621426210441982620c4611c2a3042c500460a026208430982411424188261042a380211044420441)
]

set_option maxRecDepth 8000 in
set_option maxHeartbeats 6000000 in
theorem window2_1g1_valid : window2_1g1.all (fun x => verifyPacked (ps2 ++ [x.1]) x.2) = true := by
  decide +kernel

def window2_1 : List (ℕ × ℕ) := window2_1g0 ++ window2_1g1

set_option maxRecDepth 8000 in
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

set_option maxRecDepth 8000 in
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

set_option maxRecDepth 8000 in
set_option maxHeartbeats 6000000 in
theorem window3_0g1_valid : window3_0g1.all (fun x => verifyPacked (ps3 ++ [x.1]) x.2) = true := by
  decide +kernel

def window3_0 : List (ℕ × ℕ) := window3_0g0 ++ window3_0g1

set_option maxRecDepth 8000 in
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

set_option maxRecDepth 8000 in
set_option maxHeartbeats 6000000 in
theorem window4_0g0_valid : window4_0g0.all (fun x => verifyPacked (ps4 ++ [x.1]) x.2) = true := by
  decide +kernel

def window4_0 : List (ℕ × ℕ) := window4_0g0

set_option maxRecDepth 8000 in
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

set_option maxRecDepth 8000 in
set_option maxHeartbeats 6000000 in
theorem window5_0g0_valid : window5_0g0.all (fun x => verifyPacked (ps5 ++ [x.1]) x.2) = true := by
  decide +kernel

def window5_0 : List (ℕ × ℕ) := window5_0g0

set_option maxRecDepth 8000 in
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

set_option maxRecDepth 8000 in
set_option maxHeartbeats 6000000 in
theorem window6_0g0_valid : window6_0g0.all (fun x => verifyPacked (ps6 ++ [x.1]) x.2) = true := by
  decide +kernel

def window6_0 : List (ℕ × ℕ) := window6_0g0

set_option maxRecDepth 8000 in
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

set_option maxRecDepth 8000 in
set_option maxHeartbeats 6000000 in
theorem window7_0g0_valid : window7_0g0.all (fun x => verifyPacked (ps7 ++ [x.1]) x.2) = true := by
  decide +kernel

def window7_0 : List (ℕ × ℕ) := window7_0g0

set_option maxRecDepth 8000 in
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

set_option maxRecDepth 8000 in
set_option maxHeartbeats 6000000 in
theorem window8_0g0_valid : window8_0g0.all (fun x => verifyPacked (ps8 ++ [x.1]) x.2) = true := by
  decide +kernel

def window8_0 : List (ℕ × ℕ) := window8_0g0

set_option maxRecDepth 8000 in
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

def ps9 : List ℕ := [3, 5, 7, 11, 13, 17, 23, 29]

def window9_0g0 : List (ℕ × ℕ) := [
  (31, 0x618023088430802121044204c1),
  (37, 0x6104261802308843080212104420441),
  (41, 0x6104261802308843080222104420441),
  (43, 0x6104261802308843080242104420441),
  (47, 0x41142730046104261802308843080222104420441),
  (53, 0x61042618043088230802a2104420441),
  (59, 0x6104261804308823080222104420441),
  (61, 0x6104261804308823080212104420441),
  (67, 0x6104261804308823080242104420441),
  (71, 0x6104261804308823080222104420441),
  (73, 0x6104261804308823080212104420441),
  (79, 0x308826180212104420441),
  (83, 0x308826180222104420441)
]

set_option maxRecDepth 8000 in
set_option maxHeartbeats 6000000 in
theorem window9_0g0_valid : window9_0g0.all (fun x => verifyPacked (ps9 ++ [x.1]) x.2) = true := by
  decide +kernel

def window9_0g1 : List (ℕ × ℕ) := [
  (89, 0x308826180222104420441),
  (97, 0x308826180262104420441),
  (101, 0x308826180222104420441),
  (103, 0x3088261802a2104420441),
  (107, 0x41142418847300461044308826180242104420441),
  (109, 0x418827300461044308826180242104420441),
  (113, 0x208a161c0120c42000062102620c472084411424188273004610443088261802a2104420441)
]

set_option maxRecDepth 8000 in
set_option maxHeartbeats 6000000 in
theorem window9_0g1_valid : window9_0g1.all (fun x => verifyPacked (ps9 ++ [x.1]) x.2) = true := by
  decide +kernel

def window9_0 : List (ℕ × ℕ) := window9_0g0 ++ window9_0g1

set_option maxRecDepth 8000 in
set_option maxHeartbeats 1500000 in
theorem window9_0_prime_values : window9_0.map Prod.fst = candidateFinals ps9 30 96 := by
  decide +kernel

theorem window9_0_valid : window9_0.all (fun x => verifyPacked (ps9 ++ [x.1]) x.2) = true := by
  simp only [window9_0, List.all_append, window9_0g0_valid, window9_0g1_valid, Bool.and_self]

def window9_1g0 : List (ℕ × ℕ) := [
  (127, 0x30882610426180212104420441),
  (131, 0x30882610426180222104420441),
  (137, 0x30882610426180262104420441),
  (139, 0x30882610426180242104420441),
  (149, 0x30882610426180242104420441),
  (151, 0x30882610426180212104420441),
  (157, 0x30882610426180212104420441),
  (163, 0x30882610426180212104420441),
  (167, 0x30882610426180222104420441),
  (173, 0x30882610426180222104420441),
  (179, 0x30882610426180262104420441),
  (181, 0x308826104261802a2104420441),
  (191, 0x30882610426180262104420441)
]

set_option maxRecDepth 8000 in
set_option maxHeartbeats 6000000 in
theorem window9_1g0_valid : window9_1g0.all (fun x => verifyPacked (ps9 ++ [x.1]) x.2) = true := by
  decide +kernel

def window9_1g1 : List (ℕ × ℕ) := [
  (193, 0x30882610426180212104420441),
  (197, 0x30882610426180222104420441),
  (199, 0x30882610426180212104420441),
  (211, 0x30882610426180212104420441)
]

set_option maxRecDepth 8000 in
set_option maxHeartbeats 6000000 in
theorem window9_1g1_valid : window9_1g1.all (fun x => verifyPacked (ps9 ++ [x.1]) x.2) = true := by
  decide +kernel

def window9_1 : List (ℕ × ℕ) := window9_1g0 ++ window9_1g1

set_option maxRecDepth 8000 in
set_option maxHeartbeats 1500000 in
theorem window9_1_prime_values : window9_1.map Prod.fst = candidateFinals ps9 126 96 := by
  decide +kernel

theorem window9_1_valid : window9_1.all (fun x => verifyPacked (ps9 ++ [x.1]) x.2) = true := by
  simp only [window9_1, List.all_append, window9_1g0_valid, window9_1g1_valid, Bool.and_self]

def window9_2g0 : List (ℕ × ℕ) := [
  (223, 0x308826104261802c2104420441),
  (227, 0x30882610426180222104420441),
  (229, 0x30882610426180262104420441),
  (233, 0x30882610426180242104420441),
  (239, 0x30882610426180222104420441),
  (241, 0x30882610426180242104420441),
  (251, 0x30882610426180222104420441),
  (257, 0x30882610426180222104420441),
  (263, 0x30882610426180242104420441),
  (269, 0x30882610426180262104420441),
  (271, 0x30882610426180242104420441),
  (277, 0x30882610426180212104420441),
  (281, 0x30882610426180222104420441)
]

set_option maxRecDepth 8000 in
set_option maxHeartbeats 6000000 in
theorem window9_2g0_valid : window9_2g0.all (fun x => verifyPacked (ps9 ++ [x.1]) x.2) = true := by
  decide +kernel

def window9_2g1 : List (ℕ × ℕ) := [
  (283, 0x30882610426180212104420441),
  (293, 0x30882610426180222104420441),
  (307, 0x30882610426180242108420441),
  (311, 0x30882610426180222104420441),
  (313, 0x30882610426180212104420441),
  (317, 0x30882610426180262104420441)
]

set_option maxRecDepth 8000 in
set_option maxHeartbeats 6000000 in
theorem window9_2g1_valid : window9_2g1.all (fun x => verifyPacked (ps9 ++ [x.1]) x.2) = true := by
  decide +kernel

def window9_2 : List (ℕ × ℕ) := window9_2g0 ++ window9_2g1

set_option maxRecDepth 8000 in
set_option maxHeartbeats 1500000 in
theorem window9_2_prime_values : window9_2.map Prod.fst = candidateFinals ps9 222 96 := by
  decide +kernel

theorem window9_2_valid : window9_2.all (fun x => verifyPacked (ps9 ++ [x.1]) x.2) = true := by
  simp only [window9_2, List.all_append, window9_2g0_valid, window9_2g1_valid, Bool.and_self]

def window9_3g0 : List (ℕ × ℕ) := [
  (331, 0x30882610426180212104420441),
  (337, 0x30882610426180242104420441),
  (347, 0x30882610426180242104420441),
  (349, 0x30882610426180242104420441),
  (353, 0x30882610426180222104420441),
  (359, 0x30882610426180242104420441),
  (367, 0x30882610426180262104420441),
  (373, 0x30882610426180242104420441),
  (379, 0x30882610426180212104420441),
  (383, 0x30882610426180222104420441),
  (389, 0x30882610426180262104420441),
  (397, 0x30882610426180212104420441),
  (401, 0x308826104261802a2104420441)
]

set_option maxRecDepth 8000 in
set_option maxHeartbeats 6000000 in
theorem window9_3g0_valid : window9_3g0.all (fun x => verifyPacked (ps9 ++ [x.1]) x.2) = true := by
  decide +kernel

def window9_3g1 : List (ℕ × ℕ) := [
  (409, 0x30882610426180212104420441)
]

set_option maxRecDepth 8000 in
set_option maxHeartbeats 6000000 in
theorem window9_3g1_valid : window9_3g1.all (fun x => verifyPacked (ps9 ++ [x.1]) x.2) = true := by
  decide +kernel

def window9_3 : List (ℕ × ℕ) := window9_3g0 ++ window9_3g1

set_option maxRecDepth 8000 in
set_option maxHeartbeats 1500000 in
theorem window9_3_prime_values : window9_3.map Prod.fst = candidateFinals ps9 318 96 := by
  decide +kernel

theorem window9_3_valid : window9_3.all (fun x => verifyPacked (ps9 ++ [x.1]) x.2) = true := by
  simp only [window9_3, List.all_append, window9_3g0_valid, window9_3g1_valid, Bool.and_self]

def window9_4g0 : List (ℕ × ℕ) := [
  (419, 0x30882610426180242104420441),
  (421, 0x30882610426180212104420441),
  (431, 0x30882610426180242104420441),
  (433, 0x30882610426180262104420441),
  (439, 0x30882610426180242104420441),
  (443, 0x30882610426180262104420441),
  (449, 0x30882610426180222104420441),
  (457, 0x30882610426180212104420441),
  (461, 0x30882610426180222104420441),
  (463, 0x30882610426180242104420441),
  (467, 0x30882610426180222104420441),
  (479, 0x30882610426180222104420441),
  (487, 0x30882610426180212104420441)
]

set_option maxRecDepth 8000 in
set_option maxHeartbeats 6000000 in
theorem window9_4g0_valid : window9_4g0.all (fun x => verifyPacked (ps9 ++ [x.1]) x.2) = true := by
  decide +kernel

def window9_4g1 : List (ℕ × ℕ) := [
  (491, 0x30882610426180222104420441),
  (499, 0x30882610426180212104420441),
  (503, 0x30882610426180242104420441),
  (509, 0x30882610426180222104420441)
]

set_option maxRecDepth 8000 in
set_option maxHeartbeats 6000000 in
theorem window9_4g1_valid : window9_4g1.all (fun x => verifyPacked (ps9 ++ [x.1]) x.2) = true := by
  decide +kernel

def window9_4 : List (ℕ × ℕ) := window9_4g0 ++ window9_4g1

set_option maxRecDepth 8000 in
set_option maxHeartbeats 1500000 in
theorem window9_4_prime_values : window9_4.map Prod.fst = candidateFinals ps9 414 96 := by
  decide +kernel

theorem window9_4_valid : window9_4.all (fun x => verifyPacked (ps9 ++ [x.1]) x.2) = true := by
  simp only [window9_4, List.all_append, window9_4g0_valid, window9_4g1_valid, Bool.and_self]

def window9_5g0 : List (ℕ × ℕ) := [
  (521, 0x30882610426180222104420441),
  (523, 0x30882610426180212104420441),
  (541, 0x30882610426180212104420441),
  (547, 0x30882610426180212104420441),
  (557, 0x30882610426180242104420441),
  (563, 0x30882610426180222104420441),
  (569, 0x30882610426180242104420441),
  (571, 0x30882610426180242104420441),
  (577, 0x30882610426180262104420441),
  (587, 0x30882610426180222104420441),
  (593, 0x30882610426180222104420441),
  (599, 0x30882610426180262104420441),
  (601, 0x30882610426180242104420441)
]

set_option maxRecDepth 8000 in
set_option maxHeartbeats 6000000 in
theorem window9_5g0_valid : window9_5g0.all (fun x => verifyPacked (ps9 ++ [x.1]) x.2) = true := by
  decide +kernel

def window9_5 : List (ℕ × ℕ) := window9_5g0

set_option maxRecDepth 8000 in
set_option maxHeartbeats 1500000 in
theorem window9_5_prime_values : window9_5.map Prod.fst = candidateFinals ps9 510 96 := by
  decide +kernel

theorem window9_5_valid : window9_5.all (fun x => verifyPacked (ps9 ++ [x.1]) x.2) = true := by
  exact window9_5g0_valid

def window9_6g0 : List (ℕ × ℕ) := [
  (607, 0x30882610426180212104420441),
  (613, 0x30882610426180212104420441),
  (617, 0x30882610426180222104420441),
  (619, 0x30882610426180212104420441),
  (631, 0x30882610426180212104420441),
  (641, 0x30882610426180262104420441),
  (643, 0x30882610426180262104420441),
  (647, 0x30882610426180222104420441),
  (653, 0x30882610426180262104420441),
  (659, 0x30882610426180242104420441),
  (661, 0x30882610426180212104420441),
  (673, 0x30882610426180212104420441),
  (677, 0x30882610426180222104420441)
]

set_option maxRecDepth 8000 in
set_option maxHeartbeats 6000000 in
theorem window9_6g0_valid : window9_6g0.all (fun x => verifyPacked (ps9 ++ [x.1]) x.2) = true := by
  decide +kernel

def window9_6g1 : List (ℕ × ℕ) := [
  (683, 0x30882610426180242104420441),
  (691, 0x30882610426180212104420441),
  (701, 0x620c28304441144418847300430882610426180222104420441)
]

set_option maxRecDepth 8000 in
set_option maxHeartbeats 6000000 in
theorem window9_6g1_valid : window9_6g1.all (fun x => verifyPacked (ps9 ++ [x.1]) x.2) = true := by
  decide +kernel

def window9_6 : List (ℕ × ℕ) := window9_6g0 ++ window9_6g1

set_option maxRecDepth 8000 in
set_option maxHeartbeats 1500000 in
theorem window9_6_prime_values : window9_6.map Prod.fst = candidateFinals ps9 606 96 := by
  decide +kernel

theorem window9_6_valid : window9_6.all (fun x => verifyPacked (ps9 ++ [x.1]) x.2) = true := by
  simp only [window9_6, List.all_append, window9_6g0_valid, window9_6g1_valid, Bool.and_self]

def window9_7g0 : List (ℕ × ℕ) := [
  (709, 0x30a0262102620c28304241144418847300430882610426180212104420441),
  (719, 0x41142418847300430882610426180222104420441),
  (727, 0x41142418847300430882610426180242104420441),
  (733, 0x41142418847300430882610426180212104420441),
  (739, 0x41142418847300430882610426180212104420441),
  (743, 0x41142418847300430882610426180222104420441),
  (751, 0x41142418847300430882610426180212104420441),
  (757, 0x41142418847300430882610426180212104420441),
  (761, 0x41142418847300430882610426180222104420441),
  (769, 0x41142418847300430882610426180242104420441),
  (773, 0x41142418847300430882610426180222104420441),
  (787, 0x41142418847300430882610426180212104420441),
  (797, 0x41142418847300430882610426180222104420441)
]

set_option maxRecDepth 8000 in
set_option maxHeartbeats 6000000 in
theorem window9_7g0_valid : window9_7g0.all (fun x => verifyPacked (ps9 ++ [x.1]) x.2) = true := by
  decide +kernel

def window9_7 : List (ℕ × ℕ) := window9_7g0

set_option maxRecDepth 8000 in
set_option maxHeartbeats 1500000 in
theorem window9_7_prime_values : window9_7.map Prod.fst = candidateFinals ps9 702 96 := by
  decide +kernel

theorem window9_7_valid : window9_7.all (fun x => verifyPacked (ps9 ++ [x.1]) x.2) = true := by
  exact window9_7g0_valid

def window9_8g0 : List (ℕ × ℕ) := [
  (809, 0x41142418847300430882610426180242104420441),
  (811, 0x41142418847300430882610426180242104420441),
  (821, 0x4114283042418847300430882610426180242104420441),
  (823, 0xc2182a404430a026214262104620c44114283042418847300430882610426180212104420441),
  (827, 0xc21c2a30c4c2184a4042621446210441142620c283042418847300430882610426180222104420441),
  (829, 0xc21c2c2182c3102a30c2c50426214460a024114262102620c2a3042418847300430882610426180212104420441),
  (839, 0x418827300430882610426180222104420441),
  (853, 0x418827300430882610426180242104420441),
  (857, 0x418827300430882610426180222104420441),
  (859, 0x418827300430882610426180212104420441),
  (863, 0x418827300430882610426180262104420441),
  (877, 0x418827300430882610426180212104420441),
  (881, 0x418827300430882610426180222104420441)
]

set_option maxRecDepth 8000 in
set_option maxHeartbeats 6000000 in
theorem window9_8g0_valid : window9_8g0.all (fun x => verifyPacked (ps9 ++ [x.1]) x.2) = true := by
  decide +kernel

def window9_8g1 : List (ℕ × ℕ) := [
  (883, 0x4188273004308826104261802c2104420441),
  (887, 0x418827300430882610426180242104420441)
]

set_option maxRecDepth 8000 in
set_option maxHeartbeats 6000000 in
theorem window9_8g1_valid : window9_8g1.all (fun x => verifyPacked (ps9 ++ [x.1]) x.2) = true := by
  decide +kernel

def window9_8 : List (ℕ × ℕ) := window9_8g0 ++ window9_8g1

set_option maxRecDepth 8000 in
set_option maxHeartbeats 1500000 in
theorem window9_8_prime_values : window9_8.map Prod.fst = candidateFinals ps9 798 96 := by
  decide +kernel

theorem window9_8_valid : window9_8.all (fun x => verifyPacked (ps9 ++ [x.1]) x.2) = true := by
  simp only [window9_8, List.all_append, window9_8g0_valid, window9_8g1_valid, Bool.and_self]

def window9_9g0 : List (ℕ × ℕ) := [
  (907, 0x8228587008831080418827300430882610426180212104420441),
  (911, 0x8228587008831080418827300430882610426180222104420441),
  (919, 0x8228587008831080418827300430882610426180242104420441),
  (929, 0x8228587008831080418827300430882610426180222104420441),
  (937, 0x41142c3804418840000062102620c2830447208441144418827300430882610426180242104420441),
  (941, 0x208a161c0220c420000830427208441144418827300430882610426180222104420441),
  (947, 0x208a161c0220c420000620c2830427208441144418827300430882610426180242104420441),
  (953, 0x10450b0e01106210007208241144418827300430882610426180222104420441),
  (967, 0x10450b0e01106210007208241144418827300430882610426180242104420441),
  (971, 0x10450b0e01106210007208241144418827300430882610426180262104420441),
  (977, 0x10450b0e011062100072082411444188273004308826104261802a2104420441),
  (983, 0x10450b0e01106210007208241144418827300430882610426180222104420441)
]

set_option maxRecDepth 8000 in
set_option maxHeartbeats 6000000 in
theorem window9_9g0_valid : window9_9g0.all (fun x => verifyPacked (ps9 ++ [x.1]) x.2) = true := by
  decide +kernel

def window9_9 : List (ℕ × ℕ) := window9_9g0

set_option maxRecDepth 8000 in
set_option maxHeartbeats 1500000 in
theorem window9_9_prime_values : window9_9.map Prod.fst = candidateFinals ps9 894 96 := by
  decide +kernel

theorem window9_9_valid : window9_9.all (fun x => verifyPacked (ps9 ++ [x.1]) x.2) = true := by
  exact window9_9g0_valid

def window9_10g0 : List (ℕ × ℕ) := [
  (991, 0x41142c3804418840000030a0262104620c2830447208241144418827300430882610426180212104420441),
  (997, 0x208a161c0220c42000000000c21c2c5042c2184a3884a404230a0462104620c4720828304241144418827300430882610426180212104420441),
  (1009, 0x822858700883108041142418827300430882610426180212104420441),
  (1013, 0x822858700883108041142418827300430882610426180222104420441),
  (1019, 0x822858700883108041142418827300430882610426180242104420441),
  (1021, 0x822858700883108041142418827300430882610426180262104420441),
  (1031, 0x18830a0c111045100822858700883108041142418827300430882610426180242104420441),
  (1033, 0x358009884118830a0c111045100822858700883108041142418827300430882610426180242104420441),
  (1039, 0x20c1090451008228587008831080411424188273004308826104261802c2104420441),
  (1049, 0x30c40b087128c3130860a9011358011884098830a0c109045100822858700883108041142418827300430882610426180262104420441),
  (1051, 0x8228483108041142418827300430882610426180212104420441),
  (1061, 0x8228483108041142418827300430882610426180262104420441),
  (1063, 0x8228483108041142418827300430882610426180242104420441)
]

set_option maxRecDepth 8000 in
set_option maxHeartbeats 6000000 in
theorem window9_10g0_valid : window9_10g0.all (fun x => verifyPacked (ps9 ++ [x.1]) x.2) = true := by
  decide +kernel

def window9_10g1 : List (ℕ × ℕ) := [
  (1069, 0x8228483108041142418827300430882610426180212104420441)
]

set_option maxRecDepth 8000 in
set_option maxHeartbeats 6000000 in
theorem window9_10g1_valid : window9_10g1.all (fun x => verifyPacked (ps9 ++ [x.1]) x.2) = true := by
  decide +kernel

def window9_10 : List (ℕ × ℕ) := window9_10g0 ++ window9_10g1

set_option maxRecDepth 8000 in
set_option maxHeartbeats 1500000 in
theorem window9_10_prime_values : window9_10.map Prod.fst = candidateFinals ps9 990 96 := by
  decide +kernel

theorem window9_10_valid : window9_10.all (fun x => verifyPacked (ps9 ++ [x.1]) x.2) = true := by
  simp only [window9_10, List.all_append, window9_10g0_valid, window9_10g1_valid, Bool.and_self]

def window9_11g0 : List (ℕ × ℕ) := [
  (1087, 0x18438584304c428586204c418906089870088228483108041142418827300430882610426180262104420441),
  (1091, 0x184304c4284c4208c418506089870088228483108041142418827300430882610426180222104420441),
  (1093, 0x6214230a0462102620c283044c3804411424188430882610427180212104420441),
  (1097, 0x106085870088228483108041142418827300430882610426180222104420441),
  (1103, 0xc418506085870088228483108041142418827300430882610426180262104420441),
  (1109, 0xc3102c5042c21c4c2182a30c2621440001843854618984308c428548088c4204c418506085870088228483108041142418827300430882610426180222104420441),
  (1117, 0x822858700483108041142418827300430882610426180242104420441),
  (1123, 0x822858700483108041142418827300430882610426180212104420441),
  (1129, 0x822858700483108041142418827300430882610426180212104420441),
  (1151, 0x41142c3802418840000062102620c4830447208441142418827300430882610426180222104420441),
  (1153, 0x208a161c0120c420000620c2830447208441142418827300430882610426180212104420441),
  (1163, 0x10450b0e0090621000830427208441142418827300430882610426180222104420441),
  (1171, 0x10450b0e0090621000620c2830427208441142418827300430882610426180212104420441)
]

set_option maxRecDepth 8000 in
set_option maxHeartbeats 6000000 in
theorem window9_11g0_valid : window9_11g0.all (fun x => verifyPacked (ps9 ++ [x.1]) x.2) = true := by
  decide +kernel

def window9_11g1 : List (ℕ × ℕ) := [
  (1181, 0x822858700483108041142720827300430882610426180222104420441)
]

set_option maxRecDepth 8000 in
set_option maxHeartbeats 6000000 in
theorem window9_11g1_valid : window9_11g1.all (fun x => verifyPacked (ps9 ++ [x.1]) x.2) = true := by
  decide +kernel

def window9_11 : List (ℕ × ℕ) := window9_11g0 ++ window9_11g1

set_option maxRecDepth 8000 in
set_option maxHeartbeats 1500000 in
theorem window9_11_prime_values : window9_11.map Prod.fst = candidateFinals ps9 1086 96 := by
  decide +kernel

theorem window9_11_valid : window9_11.all (fun x => verifyPacked (ps9 ++ [x.1]) x.2) = true := by
  simp only [window9_11, List.all_append, window9_11g0_valid, window9_11g1_valid, Bool.and_self]

def window9_12g0 : List (ℕ × ℕ) := [
  (1187, 0x822858700483108041142720827300430882610426180242104420441),
  (1193, 0x822858700483108041142720827300430882610426180222104420441),
  (1201, 0x822858700483108041142a20827300430882610426180212104420441),
  (1213, 0x822858700483108041142720827300430882610426180212104420441),
  (1217, 0x822858700483108041142720827300430882610426180222104420441),
  (1223, 0x822858700483108041142720827300430882610426180222104420441),
  (1229, 0x822858700483108041142720827300430882610426180242104420441),
  (1231, 0x822858700483108041142720827300430882610426180242104420441),
  (1237, 0x208a161c0120c42000060a02c21c2c218262142c3102a3882620c48304441142720827300430882610426180212104420441),
  (1249, 0x82285870048310804114272082830427300430882610426180212104420441),
  (1259, 0x822858700483108041142620c272082830427300430882610426180222104420441),
  (1277, 0x41142c38024188430882610427300242104420441)
]

set_option maxRecDepth 8000 in
set_option maxHeartbeats 6000000 in
theorem window9_12g0_valid : window9_12g0.all (fun x => verifyPacked (ps9 ++ [x.1]) x.2) = true := by
  decide +kernel

def window9_12 : List (ℕ × ℕ) := window9_12g0

set_option maxRecDepth 8000 in
set_option maxHeartbeats 1500000 in
theorem window9_12_prime_values : window9_12.map Prod.fst = candidateFinals ps9 1182 96 := by
  decide +kernel

theorem window9_12_valid : window9_12.all (fun x => verifyPacked (ps9 ++ [x.1]) x.2) = true := by
  exact window9_12g0_valid

def window9_13g0 : List (ℕ × ℕ) := [
  (1279, 0x41142c38024188430882610427300212104420441),
  (1283, 0x41142c38024188430882610427300242104420441),
  (1289, 0x41142c38024188430882610427300222104420441),
  (1291, 0x41142c38024188430882610427300262104420441),
  (1297, 0xc21c2c2182d60046214262104620c48304441142c38024188430882610427300242104420441),
  (1301, 0x30860c1a011885100c4285ac008c4204c418906088822848310800000062102620c483044720844114441882c380430882610427300222104420441),
  (1303, 0xc418506088822848310800000062102620c483044720844114441882c380430882610427300212104420441),
  (1307, 0x18438546189843060d008c4288062142d600462104620c283044411424188400000620c283044720844114441882c380430882610427300222104420441),
  (1319, 0x610c18340152022310a16b0013108231062208a14182120c42000083042720844114441882c380430882610427300222104420441),
  (1321, 0x1843060d0088140948088c428800000006188162822610e2610c220502010280a90111885135801188409883110450a0c109062100000000c21c2c2182a404440a0262104620c483042720844114441882c380430882610427300212104420441),
  (1327, 0x30870a8c313086141a010c281290111885100001850152022310a26b00231082208a1310614182120c420000620c283042720844114441882c380430882610427300212104420441),
  (1361, 0x7208241144c380441882610427300242104420441),
  (1367, 0x7208241144c380441882610427300262104420441)
]

set_option maxRecDepth 8000 in
set_option maxHeartbeats 6000000 in
theorem window9_13g0_valid : window9_13g0.all (fun x => verifyPacked (ps9 ++ [x.1]) x.2) = true := by
  decide +kernel

def window9_13g1 : List (ℕ × ℕ) := [
  (1373, 0x7208241144c380441882610427300222104420441)
]

set_option maxRecDepth 8000 in
set_option maxHeartbeats 6000000 in
theorem window9_13g1_valid : window9_13g1.all (fun x => verifyPacked (ps9 ++ [x.1]) x.2) = true := by
  decide +kernel

def window9_13 : List (ℕ × ℕ) := window9_13g0 ++ window9_13g1

set_option maxRecDepth 8000 in
set_option maxHeartbeats 1500000 in
theorem window9_13_prime_values : window9_13.map Prod.fst = candidateFinals ps9 1278 96 := by
  decide +kernel

theorem window9_13_valid : window9_13.all (fun x => verifyPacked (ps9 ++ [x.1]) x.2) = true := by
  simp only [window9_13, List.all_append, window9_13g0_valid, window9_13g1_valid, Bool.and_self]

def window9_14g0 : List (ℕ × ℕ) := [
  (1381, 0x7208241144c380441882610427300212104420441),
  (1399, 0x7208241144c380441882610427300242104420441),
  (1409, 0x62102620c4830447208241144c380441882610427300242104420441),
  (1423, 0x62102620c2830447208241144c380441882610427300212104420441),
  (1427, 0x720828304241144c380441882610427300222104420441),
  (1429, 0x720828304241144c380441882610427300242104420441),
  (1433, 0xc2182a3884a404462104620c4720828304241144c380441882610427300262104420441),
  (1439, 0xc2182a3882a404462102620c4720828304241144c380441882610427300262104420441),
  (1447, 0xc5042c21c4a30c4c2182a388430a02a404262104620c2720828304241144c380441882610427300212104420441),
  (1451, 0x62102620c2720828304241144c380441882610427300242104420441),
  (1453, 0xc3102c5082c5044c21c4a30c430a02c218262102620c2a3882a404241144c380441882610427300212104420441),
  (1459, 0x41142c380441882610427300212104420441)
]

set_option maxRecDepth 8000 in
set_option maxHeartbeats 6000000 in
theorem window9_14g0_valid : window9_14g0.all (fun x => verifyPacked (ps9 ++ [x.1]) x.2) = true := by
  decide +kernel

def window9_14 : List (ℕ × ℕ) := window9_14g0

set_option maxRecDepth 8000 in
set_option maxHeartbeats 1500000 in
theorem window9_14_prime_values : window9_14.map Prod.fst = candidateFinals ps9 1374 96 := by
  decide +kernel

theorem window9_14_valid : window9_14.all (fun x => verifyPacked (ps9 ++ [x.1]) x.2) = true := by
  exact window9_14g0_valid

def window9_15g0 : List (ℕ × ℕ) := [
  (1471, 0x41142c380441882610427300242104420441),
  (1481, 0x41142c380441882610427300242104420441),
  (1483, 0x41142c380441882610427300262104420441),
  (1487, 0x41142c380441882610427300222104420441),
  (1489, 0x41142c380441882610427300212104420441),
  (1493, 0x41142c380441882610427300242104420441),
  (1499, 0x41142c380441882610427300222104420441),
  (1511, 0x41142c380441882610427300262104420441),
  (1523, 0x41142c380441882610427300262104420441),
  (1531, 0x41142c380441882610427300212104420441),
  (1543, 0x41142c380441882610427300212104420441),
  (1549, 0x41142c380441882610427300212104420441),
  (1553, 0x41142c380441882610427300222104420441)
]

set_option maxRecDepth 8000 in
set_option maxHeartbeats 6000000 in
theorem window9_15g0_valid : window9_15g0.all (fun x => verifyPacked (ps9 ++ [x.1]) x.2) = true := by
  decide +kernel

def window9_15g1 : List (ℕ × ℕ) := [
  (1559, 0x41142c380441882610427300222104420441)
]

set_option maxRecDepth 8000 in
set_option maxHeartbeats 6000000 in
theorem window9_15g1_valid : window9_15g1.all (fun x => verifyPacked (ps9 ++ [x.1]) x.2) = true := by
  decide +kernel

def window9_15 : List (ℕ × ℕ) := window9_15g0 ++ window9_15g1

set_option maxRecDepth 8000 in
set_option maxHeartbeats 1500000 in
theorem window9_15_prime_values : window9_15.map Prod.fst = candidateFinals ps9 1470 96 := by
  decide +kernel

theorem window9_15_valid : window9_15.all (fun x => verifyPacked (ps9 ++ [x.1]) x.2) = true := by
  simp only [window9_15, List.all_append, window9_15g0_valid, window9_15g1_valid, Bool.and_self]

def window9_16g0 : List (ℕ × ℕ) := [
  (1567, 0x41142c380441882610427300262104420441),
  (1571, 0x41142c380441882610427300222104420441),
  (1579, 0x41142c380441882610427300212104420441),
  (1583, 0x41142c380441882610427300222104420441),
  (1597, 0x41142c380441882610427300242104420441),
  (1601, 0x41142c380441882610427300222104420441),
  (1607, 0x41142c380441882610427300242104420441),
  (1609, 0x41142c380441882610427300262104420441),
  (1613, 0x41142c380441882610427300222104420441),
  (1619, 0x184305ac008c4208c418906088e410882288041142c380441882610427300242104420441),
  (1621, 0xc4204c418906088e410882288041142c380441882610427300212104420441),
  (1627, 0x1843858430a0d008c4205ac004c418906088e410882288041142c380441882610427300242104420441),
  (1637, 0x1843060d004c4208c418506088e410882288041142c380441882610427300222104420441)
]

set_option maxRecDepth 8000 in
set_option maxHeartbeats 6000000 in
theorem window9_16g0_valid : window9_16g0.all (fun x => verifyPacked (ps9 ++ [x.1]) x.2) = true := by
  decide +kernel

def window9_16g1 : List (ℕ × ℕ) := [
  (1657, 0xc4204c418906084e410882288041142c380441882610427300212104420441)
]

set_option maxRecDepth 8000 in
set_option maxHeartbeats 6000000 in
theorem window9_16g1_valid : window9_16g1.all (fun x => verifyPacked (ps9 ++ [x.1]) x.2) = true := by
  decide +kernel

def window9_16 : List (ℕ × ℕ) := window9_16g0 ++ window9_16g1

set_option maxRecDepth 8000 in
set_option maxHeartbeats 1500000 in
theorem window9_16_prime_values : window9_16.map Prod.fst = candidateFinals ps9 1566 96 := by
  decide +kernel

theorem window9_16_valid : window9_16.all (fun x => verifyPacked (ps9 ++ [x.1]) x.2) = true := by
  simp only [window9_16, List.all_append, window9_16g0_valid, window9_16g1_valid, Bool.and_self]

def window9_17g0 : List (ℕ × ℕ) := [
  (1663, 0xc418506084e410882288041142c380441882610427300242104420441),
  (1667, 0xc418506084e410882288041142c380441882610427300242104420441),
  (1669, 0x610c183402205025202200000610e151862610c2205020018438546188814058430548089ac008c4208c418506084e410882288041142c380441882610427300212104420441),
  (1693, 0xe410482288041142c380441882610427300242104420441),
  (1697, 0xe410482288041142c380441882610427300222104420441),
  (1699, 0xe410482288041142c380441882610427300262104420441),
  (1709, 0xe410482288041142c380441882610427300222104420441),
  (1721, 0xe410482288041142c380441882610427300222104420441),
  (1723, 0xe410482288041142c380441882610427300212104420441),
  (1733, 0xe410482288041142c380441882610427300242104420441),
  (1741, 0xe410482288041142c380441882610427300262104420441),
  (1747, 0xe410482288041142c3804418826104273002a2104420441),
  (1753, 0xe410482288041142c380441882610427300212104420441)
]

set_option maxRecDepth 8000 in
set_option maxHeartbeats 6000000 in
theorem window9_17g0_valid : window9_17g0.all (fun x => verifyPacked (ps9 ++ [x.1]) x.2) = true := by
  decide +kernel

def window9_17 : List (ℕ × ℕ) := window9_17g0

set_option maxRecDepth 8000 in
set_option maxHeartbeats 1500000 in
theorem window9_17_prime_values : window9_17.map Prod.fst = candidateFinals ps9 1662 96 := by
  decide +kernel

theorem window9_17_valid : window9_17.all (fun x => verifyPacked (ps9 ++ [x.1]) x.2) = true := by
  exact window9_17g0_valid

def window9_18g0 : List (ℕ × ℕ) := [
  (1759, 0xe410482288041142c380441882610427300242104420441),
  (1777, 0x39041208a20000620c2830447208441142c380441882610427300242104420441),
  (1783, 0x72082411440000000000c21c2a30c4c218430a046214462104620c2830447208441142c380441882610427300212104420441),
  (1787, 0x39041208a2000062102620c2830447208441142c380441882610427300262104420441),
  (1789, 0x39041208a2000062102620c2830447208441142c380441882610427300212104420441),
  (1801, 0x30860a8e2141a0118840b58009883120c111c82090451000830427208441142c380441882610427300242104420441),
  (1811, 0x610c151c426b00231082310614182239041208a2000062102620c4830427208441142c380441882610427300222104420441),
  (1823, 0x1c820a0c1090451000620c2830427208441142c380441882610427300242104420441),
  (1831, 0xc21c2c218230a040030870b08610c280a8e21290113580118841188311c820a0c109045100062102620c2830427208441142c380441882610427300212104420441),
  (1847, 0xc4184e4105060848228804114272082c380441882610427300222104420441)
]

set_option maxRecDepth 8000 in
set_option maxHeartbeats 6000000 in
theorem window9_18g0_valid : window9_18g0.all (fun x => verifyPacked (ps9 ++ [x.1]) x.2) = true := by
  decide +kernel

def window9_18 : List (ℕ × ℕ) := window9_18g0

set_option maxRecDepth 8000 in
set_option maxHeartbeats 1500000 in
theorem window9_18_prime_values : window9_18.map Prod.fst = candidateFinals ps9 1758 96 := by
  decide +kernel

theorem window9_18_valid : window9_18.all (fun x => verifyPacked (ps9 ++ [x.1]) x.2) = true := by
  exact window9_18g0_valid

def window9_19g0 : List (ℕ × ℕ) := [
  (1861, 0x1862058438946189843094710948089ac008c4204c4184e4105060848228804114272082c380441882610427300242104420441),
  (1867, 0x72082c38044114241882610427300212104420441),
  (1871, 0x72082c38044114241882610427300242104420441),
  (1873, 0x72082c38044114241882610427300212104420441),
  (1877, 0x72082c38044114241882610427300222104420441),
  (1879, 0x72082c38044114241882610427300212104420441),
  (1889, 0x72082c38044114241882610427300222104420441),
  (1901, 0x72082c380441142418826104273002a2104420441),
  (1907, 0x72082c38044114241882610427300262104420441),
  (1913, 0x72082c38044114241882610427300242104420441),
  (1931, 0x72082c38044114241882610427300222104420441),
  (1933, 0x72082c38044114241882610427300212104420441),
  (1949, 0x72082c38044114241882610427300222104420441)
]

set_option maxRecDepth 8000 in
set_option maxHeartbeats 6000000 in
theorem window9_19g0_valid : window9_19g0.all (fun x => verifyPacked (ps9 ++ [x.1]) x.2) = true := by
  decide +kernel

def window9_19 : List (ℕ × ℕ) := window9_19g0

set_option maxRecDepth 8000 in
set_option maxHeartbeats 1500000 in
theorem window9_19_prime_values : window9_19.map Prod.fst = candidateFinals ps9 1854 96 := by
  decide +kernel

theorem window9_19_valid : window9_19.all (fun x => verifyPacked (ps9 ++ [x.1]) x.2) = true := by
  exact window9_19g0_valid

def window9_20g0 : List (ℕ × ℕ) := [
  (1951, 0x72082c38044114241882610427300212104420441),
  (1973, 0x6214262104620c48304472082c38044114241882610427300222104420441),
  (1979, 0x62102620c48304472082c38044114241882610427300242104420441),
  (1987, 0x620c28304472082c38044114241882610427300242104420441),
  (1993, 0x620c28304472082c38044114241882610427300212104420441),
  (1997, 0x6214262104620c28304472082c38044114241882610427300242104420441),
  (1999, 0xc21c2a30c430a02c218262142a388262104620c28304472082c38044114241882610427300212104420441),
  (2003, 0x62102620c28304472082c38044114241882610427300222104420441),
  (2011, 0x7208283042c38044114241882610427300212104420441),
  (2017, 0x7208283042c38044114241882610427300212104420441),
  (2027, 0x62102620c47208283042c38044114241882610427300262104420441),
  (2029, 0x62102620c47208283042c38044114241882610427300262104420441),
  (2039, 0x620c27208283042c38044114241882610427300262104420441)
]

set_option maxRecDepth 8000 in
set_option maxHeartbeats 6000000 in
theorem window9_20g0_valid : window9_20g0.all (fun x => verifyPacked (ps9 ++ [x.1]) x.2) = true := by
  decide +kernel

def window9_20 : List (ℕ × ℕ) := window9_20g0

set_option maxRecDepth 8000 in
set_option maxHeartbeats 1500000 in
theorem window9_20_prime_values : window9_20.map Prod.fst = candidateFinals ps9 1950 96 := by
  decide +kernel

theorem window9_20_valid : window9_20.all (fun x => verifyPacked (ps9 ++ [x.1]) x.2) = true := by
  exact window9_20g0_valid

def window9_21g0 : List (ℕ × ℕ) := [
  (2053, 0x62102620c27208283042c38044114241882610427300242104420441),
  (2063, 0x1862058a085843880c21c2c3102c5042a30c4c21826214262102620c2a3882a4042c38044114241882610427300242104420441),
  (2069, 0x411424188261042c380242104420441),
  (2081, 0x411424188261042c380242104420441),
  (2083, 0x411424188261042c380212104420441),
  (2087, 0x411424188261042c380222104420441),
  (2089, 0x411424188261042c380242104420441),
  (2099, 0x411424188261042c380222104420441),
  (2111, 0x411424188261042c380242104420441),
  (2113, 0x411424188261042c380242104420441),
  (2129, 0x411424188261042c380222104420441),
  (2131, 0x411424188261042c380242104420441),
  (2137, 0x411424188261042c380212104420441)
]

set_option maxRecDepth 8000 in
set_option maxHeartbeats 6000000 in
theorem window9_21g0_valid : window9_21g0.all (fun x => verifyPacked (ps9 ++ [x.1]) x.2) = true := by
  decide +kernel

def window9_21g1 : List (ℕ × ℕ) := [
  (2141, 0x411424188261042c380242104420441)
]

set_option maxRecDepth 8000 in
set_option maxHeartbeats 6000000 in
theorem window9_21g1_valid : window9_21g1.all (fun x => verifyPacked (ps9 ++ [x.1]) x.2) = true := by
  decide +kernel

def window9_21 : List (ℕ × ℕ) := window9_21g0 ++ window9_21g1

set_option maxRecDepth 8000 in
set_option maxHeartbeats 1500000 in
theorem window9_21_prime_values : window9_21.map Prod.fst = candidateFinals ps9 2046 96 := by
  decide +kernel

theorem window9_21_valid : window9_21.all (fun x => verifyPacked (ps9 ++ [x.1]) x.2) = true := by
  simp only [window9_21, List.all_append, window9_21g0_valid, window9_21g1_valid, Bool.and_self]

def window9_22g0 : List (ℕ × ℕ) := [
  (2143, 0x411424188261042c380212104420441),
  (2153, 0x411424188261042c380242104420441),
  (2161, 0x411424188261042c380262104420441),
  (2179, 0x411424188261042c380212104420441),
  (2203, 0x411424188261042c380262104420441),
  (2207, 0x411424188261042c380242104420441),
  (2213, 0x411424188261042c380242104420441),
  (2221, 0x411424188261042c380242104420441),
  (2237, 0x411424188261042c380262104420441)
]

set_option maxRecDepth 8000 in
set_option maxHeartbeats 6000000 in
theorem window9_22g0_valid : window9_22g0.all (fun x => verifyPacked (ps9 ++ [x.1]) x.2) = true := by
  decide +kernel

def window9_22 : List (ℕ × ℕ) := window9_22g0

set_option maxRecDepth 8000 in
set_option maxHeartbeats 1500000 in
theorem window9_22_prime_values : window9_22.map Prod.fst = candidateFinals ps9 2142 96 := by
  decide +kernel

theorem window9_22_valid : window9_22.all (fun x => verifyPacked (ps9 ++ [x.1]) x.2) = true := by
  exact window9_22g0_valid

def window9_23g0 : List (ℕ × ℕ) := [
  (2239, 0x411424188261042c380242104420441),
  (2243, 0x411424188261042c380222104420441),
  (2251, 0x411424188261042c380212104420441),
  (2267, 0x411424188261042c380222104420441),
  (2269, 0x411424188261042c380212104420441),
  (2273, 0x411424188261042c380222104420441),
  (2281, 0x411424188261042c380262104420441),
  (2287, 0x411424188261042c380242104420441),
  (2293, 0x411424188261042c380212104420441),
  (2297, 0x411424188261042c3802a2104420441),
  (2309, 0x411424188261042c380222104420441),
  (2311, 0x411424188261042c380242104420441),
  (2333, 0x411424188261042c380242104420441)
]

set_option maxRecDepth 8000 in
set_option maxHeartbeats 6000000 in
theorem window9_23g0_valid : window9_23g0.all (fun x => verifyPacked (ps9 ++ [x.1]) x.2) = true := by
  decide +kernel

def window9_23 : List (ℕ × ℕ) := window9_23g0

set_option maxRecDepth 8000 in
set_option maxHeartbeats 1500000 in
theorem window9_23_prime_values : window9_23.map Prod.fst = candidateFinals ps9 2238 96 := by
  decide +kernel

theorem window9_23_valid : window9_23.all (fun x => verifyPacked (ps9 ++ [x.1]) x.2) = true := by
  exact window9_23g0_valid

def window9_24g0 : List (ℕ × ℕ) := [
  (2339, 0x411424188261042c380222104420441),
  (2341, 0x411424188261042c380212104420441),
  (2347, 0x411424188261042c380212104420441),
  (2351, 0x411424188261042c380222104420441),
  (2357, 0x411424188261042c380222104420441),
  (2371, 0x411424188261042c380212104420441),
  (2377, 0x411424188261042c380242104420441),
  (2381, 0x411424188261042c380222104420441),
  (2383, 0x411424188261042c380212104420441),
  (2389, 0x411424188261042c380212104420441),
  (2393, 0x411424188261042c380222104420441),
  (2399, 0x411424188261042c380222104420441),
  (2411, 0x62142d600462104620c48304472084411424188261042c380222104420441)
]

set_option maxRecDepth 8000 in
set_option maxHeartbeats 6000000 in
theorem window9_24g0_valid : window9_24g0.all (fun x => verifyPacked (ps9 ++ [x.1]) x.2) = true := by
  decide +kernel

def window9_24g1 : List (ℕ × ℕ) := [
  (2417, 0xc21830680462142d600262104620c48304472084411424188261042c380242104420441),
  (2423, 0x62102620c48304472084411424188261042c380222104420441)
]

set_option maxRecDepth 8000 in
set_option maxHeartbeats 6000000 in
theorem window9_24g1_valid : window9_24g1.all (fun x => verifyPacked (ps9 ++ [x.1]) x.2) = true := by
  decide +kernel

def window9_24 : List (ℕ × ℕ) := window9_24g0 ++ window9_24g1

set_option maxRecDepth 8000 in
set_option maxHeartbeats 1500000 in
theorem window9_24_prime_values : window9_24.map Prod.fst = candidateFinals ps9 2334 96 := by
  decide +kernel

theorem window9_24_valid : window9_24.all (fun x => verifyPacked (ps9 ++ [x.1]) x.2) = true := by
  simp only [window9_24, List.all_append, window9_24g0_valid, window9_24g1_valid, Bool.and_self]

def window9_25g0 : List (ℕ × ℕ) := [
  (2437, 0x620c28304472084411424188261042c380242104420441),
  (2441, 0x620c28304472084411424188261042c380222104420441),
  (2447, 0xc21c2a30c4c218262144d600462104620c28304472084411424188261042c380262104420441),
  (2459, 0x62102620c28304472084411424188261042c380242104420441),
  (2467, 0x9400161882610e20025000586209843854618861405843060d004c4288030a02c218262142d600462102620c28304472084411424188261042c380212104420441),
  (2473, 0x8304272084411424188261042c380212104420441),
  (2477, 0x8304272084411424188261042c380222104420441),
  (2503, 0x18438586206500048140984308040a02c218306804a40446214400018438481408040a02c21c2c2184a404262144d600462102620c48304272084411424188261042c380212104420441),
  (2521, 0x620c28304272084411424188261042c380242104420441)
]

set_option maxRecDepth 8000 in
set_option maxHeartbeats 6000000 in
theorem window9_25g0_valid : window9_25g0.all (fun x => verifyPacked (ps9 ++ [x.1]) x.2) = true := by
  decide +kernel

def window9_25 : List (ℕ × ℕ) := window9_25g0

set_option maxRecDepth 8000 in
set_option maxHeartbeats 1500000 in
theorem window9_25_prime_values : window9_25.map Prod.fst = candidateFinals ps9 2430 96 := by
  decide +kernel

theorem window9_25_valid : window9_25.all (fun x => verifyPacked (ps9 ++ [x.1]) x.2) = true := by
  exact window9_25g0_valid

def window9_26g0 : List (ℕ × ℕ) := [
  (2531, 0xc218306802a404462142d600262104620c28304272084411424188261042c380242104420441),
  (2539, 0x30870a8c310c281000c21c2a30c430a02c2184a404462144d600462102620c28304272084411424188261042c380212104420441),
  (2543, 0x30870a8c3130861018438584305461860d00948088c4288000000c3102c5044c21c4a30c4c2182a404262144d600462102620c28304272084411424188261042c380242104420441),
  (2549, 0x8314328002c3104c21c2c2182a30c306802a40446214262102620c283042d600272084411424188261042c380222104420441),
  (2551, 0x41810da40120c50ca000b0c4131410b08710184385862058a08546189843080c21c2c2182c3102a30c2c5043068046214262102620c2a4042d600272084411424188261042c380242104420441),
  (2557, 0x411427208261042c380212104420441),
  (2579, 0x411427208261042c380222104420441),
  (2591, 0x411427208261042c380222104420441),
  (2593, 0x411427208261042c380212104420441),
  (2609, 0x411427208261042c380242104420441),
  (2617, 0x411427208261042c380242104420441),
  (2621, 0x411427208261042c380222104420441)
]

set_option maxRecDepth 8000 in
set_option maxHeartbeats 6000000 in
theorem window9_26g0_valid : window9_26g0.all (fun x => verifyPacked (ps9 ++ [x.1]) x.2) = true := by
  decide +kernel

def window9_26 : List (ℕ × ℕ) := window9_26g0

set_option maxRecDepth 8000 in
set_option maxHeartbeats 1500000 in
theorem window9_26_prime_values : window9_26.map Prod.fst = candidateFinals ps9 2526 96 := by
  decide +kernel

theorem window9_26_valid : window9_26.all (fun x => verifyPacked (ps9 ++ [x.1]) x.2) = true := by
  exact window9_26g0_valid

def window9_27g0 : List (ℕ × ℕ) := [
  (2633, 0x411427208261042c380222104420441),
  (2647, 0x411427208261042c380212104420441),
  (2657, 0x411427208261042c380242104420441),
  (2659, 0x411427208261042c380242104420441),
  (2663, 0x411427208261042c380222104420441),
  (2671, 0x411427208261042c380212104420441),
  (2677, 0x411427208261042c380262104420441),
  (2683, 0x411427208261042c380242104420441),
  (2687, 0x411427208261042c380262104420441),
  (2689, 0x411427208261042c380212104420441),
  (2693, 0x411427208261042c380222104420441),
  (2699, 0x411427208261042c380262104420441),
  (2707, 0x411427208261042c380212104420441)
]

set_option maxRecDepth 8000 in
set_option maxHeartbeats 6000000 in
theorem window9_27g0_valid : window9_27g0.all (fun x => verifyPacked (ps9 ++ [x.1]) x.2) = true := by
  decide +kernel

def window9_27g1 : List (ℕ × ℕ) := [
  (2711, 0x411427208261042c380262104420441),
  (2713, 0x411427208261042c380242104420441)
]

set_option maxRecDepth 8000 in
set_option maxHeartbeats 6000000 in
theorem window9_27g1_valid : window9_27g1.all (fun x => verifyPacked (ps9 ++ [x.1]) x.2) = true := by
  decide +kernel

def window9_27 : List (ℕ × ℕ) := window9_27g0 ++ window9_27g1

set_option maxRecDepth 8000 in
set_option maxHeartbeats 1500000 in
theorem window9_27_prime_values : window9_27.map Prod.fst = candidateFinals ps9 2622 96 := by
  decide +kernel

theorem window9_27_valid : window9_27.all (fun x => verifyPacked (ps9 ++ [x.1]) x.2) = true := by
  simp only [window9_27, List.all_append, window9_27g0_valid, window9_27g1_valid, Bool.and_self]

def window9_28g0 : List (ℕ × ℕ) := [
  (2719, 0x411427208261042c380242104420441),
  (2729, 0x411427208261042c380222104420441),
  (2731, 0x411427208261042c380212104420441),
  (2741, 0x411427208261042c380242104420441),
  (2749, 0x411427208261042c380242104420441),
  (2753, 0x411427208261042c380262104420441),
  (2767, 0x411427208261042c380212104420441),
  (2777, 0x411427208261042c380222104420441),
  (2789, 0x411427208261042c380222104420441),
  (2791, 0x411427208261042c380212104420441),
  (2797, 0x411427208261042c380212104420441),
  (2801, 0x411427188261042c380222104420441),
  (2803, 0x411427208261042c380212104420441)
]

set_option maxRecDepth 8000 in
set_option maxHeartbeats 6000000 in
theorem window9_28g0_valid : window9_28g0.all (fun x => verifyPacked (ps9 ++ [x.1]) x.2) = true := by
  decide +kernel

def window9_28 : List (ℕ × ℕ) := window9_28g0

set_option maxRecDepth 8000 in
set_option maxHeartbeats 1500000 in
theorem window9_28_prime_values : window9_28.map Prod.fst = candidateFinals ps9 2718 96 := by
  decide +kernel

theorem window9_28_valid : window9_28.all (fun x => verifyPacked (ps9 ++ [x.1]) x.2) = true := by
  exact window9_28g0_valid

def window9_29g0 : List (ℕ × ℕ) := [
  (2819, 0x18438584305471060d004c42880c218262142a3882d600462104620c483044411427208261042c380222104420441),
  (2833, 0xc21c2c2184a388462144d600462102620c483044411427208261042c380242104420441),
  (2837, 0x1843054710a0d008c4288062142d600462102620c483044411427208261042c380242104420441),
  (2843, 0xc3102c21c4c2182a3885068046214262102d6002620c483044411427208261042c3802a2104420441),
  (2851, 0x620c283044411427208261042c380242104420441),
  (2857, 0x620c283044411427208261042c380212104420441),
  (2861, 0xc21c2a30c4c2184a388462144d600462104620c283044411427208261042c380222104420441),
  (2879, 0x62102620c283044411427208261042c380242104420441),
  (2887, 0x18438546188614098430800030870a8c310c28100614058438546185843094710a0d008c4288062142d600462102620c283044411427208261042c380212104420441),
  (2897, 0xc21c2a30c4c21826214262102620c2a38830680283044411427208261042c380222104420441),
  (2903, 0x411427208283042c380222104420441),
  (2909, 0x411427208283042c380262104420441)
]

set_option maxRecDepth 8000 in
set_option maxHeartbeats 6000000 in
theorem window9_29g0_valid : window9_29g0.all (fun x => verifyPacked (ps9 ++ [x.1]) x.2) = true := by
  decide +kernel

def window9_29 : List (ℕ × ℕ) := window9_29g0

set_option maxRecDepth 8000 in
set_option maxHeartbeats 1500000 in
theorem window9_29_prime_values : window9_29.map Prod.fst = candidateFinals ps9 2814 96 := by
  decide +kernel

theorem window9_29_valid : window9_29.all (fun x => verifyPacked (ps9 ++ [x.1]) x.2) = true := by
  exact window9_29g0_valid

def window9_30g0 : List (ℕ × ℕ) := [
  (2917, 0x40a02c2184a38840010280b0870b0861008140584385843054710a0d00948088c428800001843858a0848140984308040a02c2182a38846214400000c21c240a04c2184a388462142a4044d600462104620c4411427208283042c380212104420441),
  (2927, 0xc5042c21c4c2182a38850680462142a4042d600262104620c4411427208283042c380222104420441),
  (2939, 0x30860a8e2141a01290111885100000000c3102c5044c21c4c2184a3884a404262144d600462102620c4411427208283042c380222104420441),
  (2953, 0xc21826214262102a3882a404306802620c4411427208283042c3802c2104420441),
  (2957, 0x41142620c27208283042c380222104420441),
  (2963, 0x41142620c27208283042c380262104420441),
  (2969, 0x30870a8c313086128e2141a012901118851000a404262144d60046210441142620c27208283042c380222104420441),
  (2971, 0x94001610e25186220502610c20000c21c2a30c440a04020501610e151861610c251c420000c21c2a30c440a04020501610e151861610c251c418340252022310a200000031410b087128c3110280b0861000c21c2a30c440a02c2182a38846214400000c21c2a30c240a04c2184a388462142a4044d60046210441142620c27208283042c380212104420441),
  (2999, 0xc3102c5042c21c4a30c4c2184a388400000c3102c5044c21c40030c40b141130870a8c3130861000c3102c5042c21c40610e1618816282151862610c151c4283402310a200000030870a8c313086128e2141a0118850a9011000c21c2c2182c3102a30c2a3882a404462142d60044114262102620c27208283042c380242104420441),
  (3001, 0x30c40b1410ca000b087128c310c281000c3102c5042c21c400018a1060c08a5000984385862058a0854618861405843080004a000b0c41314110c280b0870b0860a8c30a8e21006140584385843058620546185471058a0860d008c428800000009400161882610e25186218502001843854618861405843094710800030870a8c310c2810061405843854618584308030a02c21c2c2182a30c2a38850680462142a404400000c3102c5044c21c230a040000083142c3104c5044c21c430a02a30c4c21840030870b0c40b14108c281000c5042c21c430a02a30c4c2182a388462142a4042d60044114262102620c27208283042c380212104420441)
]

set_option maxRecDepth 8000 in
set_option maxHeartbeats 6000000 in
theorem window9_30g0_valid : window9_30g0.all (fun x => verifyPacked (ps9 ++ [x.1]) x.2) = true := by
  decide +kernel

def window9_30 : List (ℕ × ℕ) := window9_30g0

set_option maxRecDepth 8000 in
set_option maxHeartbeats 1500000 in
theorem window9_30_prime_values : window9_30.map Prod.fst = candidateFinals ps9 2910 96 := by
  decide +kernel

theorem window9_30_valid : window9_30.all (fun x => verifyPacked (ps9 ++ [x.1]) x.2) = true := by
  exact window9_30g0_valid

def window9_31g0 : List (ℕ × ℕ) := []

set_option maxRecDepth 8000 in
set_option maxHeartbeats 6000000 in
theorem window9_31g0_valid : window9_31g0.all (fun x => verifyPacked (ps9 ++ [x.1]) x.2) = true := by
  decide +kernel

def window9_31 : List (ℕ × ℕ) := window9_31g0

set_option maxRecDepth 8000 in
set_option maxHeartbeats 1500000 in
theorem window9_31_prime_values : window9_31.map Prod.fst = candidateFinals ps9 3006 4 := by
  decide +kernel

theorem window9_31_valid : window9_31.all (fun x => verifyPacked (ps9 ++ [x.1]) x.2) = true := by
  exact window9_31g0_valid

theorem prefix9_verified {q : ℕ} (hlo : start ps9 ≤ q) (hhi : q ≤ lastCap ps9)
    (hp : q.Prime) (hlarge : 3 * den ps9 * (q-1) < ps9.prod * q) :
    ∃ w, verifyPacked (ps9 ++ [q]) w = true := by
  change 30 ≤ q at hlo
  change q ≤ 3009 at hhi

  by_cases h0 : q < 126
  · exact checked_window window9_0_prime_values window9_0_valid (by omega) (by omega) hp hlarge

  by_cases h1 : q < 222
  · exact checked_window window9_1_prime_values window9_1_valid (by omega) (by omega) hp hlarge

  by_cases h2 : q < 318
  · exact checked_window window9_2_prime_values window9_2_valid (by omega) (by omega) hp hlarge

  by_cases h3 : q < 414
  · exact checked_window window9_3_prime_values window9_3_valid (by omega) (by omega) hp hlarge

  by_cases h4 : q < 510
  · exact checked_window window9_4_prime_values window9_4_valid (by omega) (by omega) hp hlarge

  by_cases h5 : q < 606
  · exact checked_window window9_5_prime_values window9_5_valid (by omega) (by omega) hp hlarge

  by_cases h6 : q < 702
  · exact checked_window window9_6_prime_values window9_6_valid (by omega) (by omega) hp hlarge

  by_cases h7 : q < 798
  · exact checked_window window9_7_prime_values window9_7_valid (by omega) (by omega) hp hlarge

  by_cases h8 : q < 894
  · exact checked_window window9_8_prime_values window9_8_valid (by omega) (by omega) hp hlarge

  by_cases h9 : q < 990
  · exact checked_window window9_9_prime_values window9_9_valid (by omega) (by omega) hp hlarge

  by_cases h10 : q < 1086
  · exact checked_window window9_10_prime_values window9_10_valid (by omega) (by omega) hp hlarge

  by_cases h11 : q < 1182
  · exact checked_window window9_11_prime_values window9_11_valid (by omega) (by omega) hp hlarge

  by_cases h12 : q < 1278
  · exact checked_window window9_12_prime_values window9_12_valid (by omega) (by omega) hp hlarge

  by_cases h13 : q < 1374
  · exact checked_window window9_13_prime_values window9_13_valid (by omega) (by omega) hp hlarge

  by_cases h14 : q < 1470
  · exact checked_window window9_14_prime_values window9_14_valid (by omega) (by omega) hp hlarge

  by_cases h15 : q < 1566
  · exact checked_window window9_15_prime_values window9_15_valid (by omega) (by omega) hp hlarge

  by_cases h16 : q < 1662
  · exact checked_window window9_16_prime_values window9_16_valid (by omega) (by omega) hp hlarge

  by_cases h17 : q < 1758
  · exact checked_window window9_17_prime_values window9_17_valid (by omega) (by omega) hp hlarge

  by_cases h18 : q < 1854
  · exact checked_window window9_18_prime_values window9_18_valid (by omega) (by omega) hp hlarge

  by_cases h19 : q < 1950
  · exact checked_window window9_19_prime_values window9_19_valid (by omega) (by omega) hp hlarge

  by_cases h20 : q < 2046
  · exact checked_window window9_20_prime_values window9_20_valid (by omega) (by omega) hp hlarge

  by_cases h21 : q < 2142
  · exact checked_window window9_21_prime_values window9_21_valid (by omega) (by omega) hp hlarge

  by_cases h22 : q < 2238
  · exact checked_window window9_22_prime_values window9_22_valid (by omega) (by omega) hp hlarge

  by_cases h23 : q < 2334
  · exact checked_window window9_23_prime_values window9_23_valid (by omega) (by omega) hp hlarge

  by_cases h24 : q < 2430
  · exact checked_window window9_24_prime_values window9_24_valid (by omega) (by omega) hp hlarge

  by_cases h25 : q < 2526
  · exact checked_window window9_25_prime_values window9_25_valid (by omega) (by omega) hp hlarge

  by_cases h26 : q < 2622
  · exact checked_window window9_26_prime_values window9_26_valid (by omega) (by omega) hp hlarge

  by_cases h27 : q < 2718
  · exact checked_window window9_27_prime_values window9_27_valid (by omega) (by omega) hp hlarge

  by_cases h28 : q < 2814
  · exact checked_window window9_28_prime_values window9_28_valid (by omega) (by omega) hp hlarge

  by_cases h29 : q < 2910
  · exact checked_window window9_29_prime_values window9_29_valid (by omega) (by omega) hp hlarge

  by_cases h30 : q < 3006
  · exact checked_window window9_30_prime_values window9_30_valid (by omega) (by omega) hp hlarge

  exact checked_window window9_31_prime_values window9_31_valid (by omega) (by omega) hp hlarge

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

set_option maxRecDepth 8000 in
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

set_option maxRecDepth 8000 in
set_option maxHeartbeats 6000000 in
theorem window10_0g1_valid : window10_0g1.all (fun x => verifyPacked (ps10 ++ [x.1]) x.2) = true := by
  decide +kernel

def window10_0 : List (ℕ × ℕ) := window10_0g0 ++ window10_0g1

set_option maxRecDepth 8000 in
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

set_option maxRecDepth 8000 in
set_option maxHeartbeats 6000000 in
theorem window10_1g0_valid : window10_1g0.all (fun x => verifyPacked (ps10 ++ [x.1]) x.2) = true := by
  decide +kernel

def window10_1g1 : List (ℕ × ℕ) := [
  (197, 0x3088261802209044204c1),
  (199, 0x3088261802109044204c1),
  (211, 0x411424188473004609c43088261802109044204c1),
  (223, 0x4188273004609c43088261802609044204c1)
]

set_option maxRecDepth 8000 in
set_option maxHeartbeats 6000000 in
theorem window10_1g1_valid : window10_1g1.all (fun x => verifyPacked (ps10 ++ [x.1]) x.2) = true := by
  decide +kernel

def window10_1 : List (ℕ × ℕ) := window10_1g0 ++ window10_1g1

set_option maxRecDepth 8000 in
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

set_option maxRecDepth 8000 in
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

set_option maxRecDepth 8000 in
set_option maxHeartbeats 6000000 in
theorem window10_2g1_valid : window10_2g1.all (fun x => verifyPacked (ps10 ++ [x.1]) x.2) = true := by
  decide +kernel

def window10_2 : List (ℕ × ℕ) := window10_2g0 ++ window10_2g1

set_option maxRecDepth 8000 in
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

set_option maxRecDepth 8000 in
set_option maxHeartbeats 6000000 in
theorem window10_3g0_valid : window10_3g0.all (fun x => verifyPacked (ps10 ++ [x.1]) x.2) = true := by
  decide +kernel

def window10_3 : List (ℕ × ℕ) := window10_3g0

set_option maxRecDepth 8000 in
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

set_option maxRecDepth 8000 in
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

set_option maxRecDepth 8000 in
set_option maxHeartbeats 6000000 in
theorem window11_0g1_valid : window11_0g1.all (fun x => verifyPacked (ps11 ++ [x.1]) x.2) = true := by
  decide +kernel

def window11_0 : List (ℕ × ℕ) := window11_0g0 ++ window11_0g1

set_option maxRecDepth 8000 in
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

set_option maxRecDepth 8000 in
set_option maxHeartbeats 6000000 in
theorem window12_0g0_valid : window12_0g0.all (fun x => verifyPacked (ps12 ++ [x.1]) x.2) = true := by
  decide +kernel

def window12_0 : List (ℕ × ℕ) := window12_0g0

set_option maxRecDepth 8000 in
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

set_option maxRecDepth 8000 in
set_option maxHeartbeats 6000000 in
theorem window13_0g0_valid : window13_0g0.all (fun x => verifyPacked (ps13 ++ [x.1]) x.2) = true := by
  decide +kernel

def window13_0 : List (ℕ × ℕ) := window13_0g0

set_option maxRecDepth 8000 in
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

set_option maxRecDepth 8000 in
set_option maxHeartbeats 6000000 in
theorem window14_0g0_valid : window14_0g0.all (fun x => verifyPacked (ps14 ++ [x.1]) x.2) = true := by
  decide +kernel

def window14_0 : List (ℕ × ℕ) := window14_0g0

set_option maxRecDepth 8000 in
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

set_option maxRecDepth 8000 in
set_option maxHeartbeats 6000000 in
theorem window15_0g0_valid : window15_0g0.all (fun x => verifyPacked (ps15 ++ [x.1]) x.2) = true := by
  decide +kernel

def window15_0 : List (ℕ × ℕ) := window15_0g0

set_option maxRecDepth 8000 in
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

set_option maxRecDepth 8000 in
set_option maxHeartbeats 6000000 in
theorem window16_0g0_valid : window16_0g0.all (fun x => verifyPacked (ps16 ++ [x.1]) x.2) = true := by
  decide +kernel

def window16_0 : List (ℕ × ℕ) := window16_0g0

set_option maxRecDepth 8000 in
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

set_option maxRecDepth 8000 in
set_option maxHeartbeats 6000000 in
theorem window17_0g0_valid : window17_0g0.all (fun x => verifyPacked (ps17 ++ [x.1]) x.2) = true := by
  decide +kernel

def window17_0 : List (ℕ × ℕ) := window17_0g0

set_option maxRecDepth 8000 in
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

def ps18 : List ℕ := [3, 5, 7, 11, 13, 17, 29, 41]

def window18_0g0 : List (ℕ × ℕ) := [
  (43, 0x30882610426180241104420441),
  (47, 0x30882610426180221104420441)
]

set_option maxRecDepth 8000 in
set_option maxHeartbeats 6000000 in
theorem window18_0g0_valid : window18_0g0.all (fun x => verifyPacked (ps18 ++ [x.1]) x.2) = true := by
  decide +kernel

def window18_0 : List (ℕ × ℕ) := window18_0g0

set_option maxRecDepth 8000 in
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

def ps19 : List ℕ := [3, 5, 7, 11, 13, 17, 29, 43]

def window19_0g0 : List (ℕ × ℕ) := [
  (47, 0xe410482288041142a380441882610427300222104420441)
]

set_option maxRecDepth 8000 in
set_option maxHeartbeats 6000000 in
theorem window19_0g0_valid : window19_0g0.all (fun x => verifyPacked (ps19 ++ [x.1]) x.2) = true := by
  decide +kernel

def window19_0 : List (ℕ × ℕ) := window19_0g0

set_option maxRecDepth 8000 in
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

def ps20 : List ℕ := [3, 5, 7, 11, 13, 17, 31, 37]

def window20_0g0 : List (ℕ × ℕ) := [
  (41, 0x3088261802208444204c1),
  (43, 0x3088261802408444204c1),
  (47, 0x28c1090451106211cc010c2710004114262082a3802309c40000c418546084822894700861384831080309c24188273004609843088261802608444204c1)
]

set_option maxRecDepth 8000 in
set_option maxHeartbeats 6000000 in
theorem window20_0g0_valid : window20_0g0.all (fun x => verifyPacked (ps20 ++ [x.1]) x.2) = true := by
  decide +kernel

def window20_0 : List (ℕ × ℕ) := window20_0g0

set_option maxRecDepth 8000 in
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

def ps21 : List ℕ := [3, 5, 7, 11, 13, 17, 31, 41]

def window21_0g0 : List (ℕ × ℕ) := [
  (43, 0xc4284c4209441880a20c2c5004411c4a3044620844114241882a3002609843088261802410444204c1)
]

set_option maxRecDepth 8000 in
set_option maxHeartbeats 6000000 in
theorem window21_0g0_valid : window21_0g0.all (fun x => verifyPacked (ps21 ++ [x.1]) x.2) = true := by
  decide +kernel

def window21_0 : List (ℕ × ℕ) := window21_0g0

set_option maxRecDepth 8000 in
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

def ps22 : List ℕ := [3, 5, 7, 11, 13, 19, 23, 29]

def window22_0g0 : List (ℕ × ℕ) := [
  (31, 0x618023088430802121024204c1),
  (37, 0x30942720826104461804308823080262102420441),
  (41, 0x6104261804308823080222102420441),
  (43, 0x6104261804308823080242102420441),
  (47, 0x309426104261804308823080222102420441),
  (53, 0x3088261802a2102420441),
  (59, 0x3094261044308826180222102420441),
  (61, 0x3094261044308826180212102420441),
  (67, 0x30a023094241882c380261044308826180212102420441),
  (71, 0x30882610426180222102420441),
  (73, 0x30882610426180212102420441),
  (79, 0x30882610426180212102420441),
  (83, 0x30882610426180242102420441)
]

set_option maxRecDepth 8000 in
set_option maxHeartbeats 6000000 in
theorem window22_0g0_valid : window22_0g0.all (fun x => verifyPacked (ps22 ++ [x.1]) x.2) = true := by
  decide +kernel

def window22_0g1 : List (ℕ × ℕ) := [
  (89, 0x30882610426180222102420441),
  (97, 0x41882730043094430882610426180262102420441),
  (101, 0x41882730023094430882610426180222102420441),
  (103, 0x41882c380230944308826104261802a2102420441),
  (107, 0x3094230882610426180242102420441),
  (109, 0x3094230882610426180242102420441),
  (113, 0x30942308826104261802a2102420441)
]

set_option maxRecDepth 8000 in
set_option maxHeartbeats 6000000 in
theorem window22_0g1_valid : window22_0g1.all (fun x => verifyPacked (ps22 ++ [x.1]) x.2) = true := by
  decide +kernel

def window22_0 : List (ℕ × ℕ) := window22_0g0 ++ window22_0g1

set_option maxRecDepth 8000 in
set_option maxHeartbeats 1500000 in
theorem window22_0_prime_values : window22_0.map Prod.fst = candidateFinals ps22 30 96 := by
  decide +kernel

theorem window22_0_valid : window22_0.all (fun x => verifyPacked (ps22 ++ [x.1]) x.2) = true := by
  simp only [window22_0, List.all_append, window22_0g0_valid, window22_0g1_valid, Bool.and_self]

def window22_1g0 : List (ℕ × ℕ) := [
  (127, 0x3094230882610426180212102420441),
  (131, 0x41882730043094230882610426180222102420441),
  (137, 0x610c17b402310a2000073142c3104c21c4c218262142d600462102620c441942a3044c3802418843094230882610427300262102420441),
  (139, 0x3094241882610427300242102420441)
]

set_option maxRecDepth 8000 in
set_option maxHeartbeats 6000000 in
theorem window22_1g0_valid : window22_1g0.all (fun x => verifyPacked (ps22 ++ [x.1]) x.2) = true := by
  decide +kernel

def window22_1 : List (ℕ × ℕ) := window22_1g0

set_option maxRecDepth 8000 in
set_option maxHeartbeats 1500000 in
theorem window22_1_prime_values : window22_1.map Prod.fst = candidateFinals ps22 126 20 := by
  decide +kernel

theorem window22_1_valid : window22_1.all (fun x => verifyPacked (ps22 ++ [x.1]) x.2) = true := by
  exact window22_1g0_valid

theorem prefix22_verified {q : ℕ} (hlo : start ps22 ≤ q) (hhi : q ≤ lastCap ps22)
    (hp : q.Prime) (hlarge : 3 * den ps22 * (q-1) < ps22.prod * q) :
    ∃ w, verifyPacked (ps22 ++ [q]) w = true := by
  change 30 ≤ q at hlo
  change q ≤ 145 at hhi

  by_cases h0 : q < 126
  · exact checked_window window22_0_prime_values window22_0_valid (by omega) (by omega) hp hlarge

  exact checked_window window22_1_prime_values window22_1_valid (by omega) (by omega) hp hlarge

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

set_option maxRecDepth 8000 in
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

set_option maxRecDepth 8000 in
set_option maxHeartbeats 6000000 in
theorem window23_0g1_valid : window23_0g1.all (fun x => verifyPacked (ps23 ++ [x.1]) x.2) = true := by
  decide +kernel

def window23_0 : List (ℕ × ℕ) := window23_0g0 ++ window23_0g1

set_option maxRecDepth 8000 in
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

set_option maxRecDepth 8000 in
set_option maxHeartbeats 6000000 in
theorem window24_0g0_valid : window24_0g0.all (fun x => verifyPacked (ps24 ++ [x.1]) x.2) = true := by
  decide +kernel

def window24_0 : List (ℕ × ℕ) := window24_0g0

set_option maxRecDepth 8000 in
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

def ps25 : List ℕ := [3, 5, 7, 11, 13, 19, 23, 41]

def window25_0g0 : List (ℕ × ℕ) := [
  (43, 0x30882610426180241102420441),
  (47, 0x30882610426180221102420441),
  (53, 0x3094230882610426180261102420441)
]

set_option maxRecDepth 8000 in
set_option maxHeartbeats 6000000 in
theorem window25_0g0_valid : window25_0g0.all (fun x => verifyPacked (ps25 ++ [x.1]) x.2) = true := by
  decide +kernel

def window25_0 : List (ℕ × ℕ) := window25_0g0

set_option maxRecDepth 8000 in
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

def ps26 : List ℕ := [3, 5, 7, 11, 13, 19, 23, 43]

def window26_0g0 : List (ℕ × ℕ) := [
  (47, 0x41882730023094430882610426180222102420441),
  (53, 0xc42054418883289460898700883108041882730043094230882610426180262102420441)
]

set_option maxRecDepth 8000 in
set_option maxHeartbeats 6000000 in
theorem window26_0g0_valid : window26_0g0.all (fun x => verifyPacked (ps26 ++ [x.1]) x.2) = true := by
  decide +kernel

def window26_0 : List (ℕ × ℕ) := window26_0g0

set_option maxRecDepth 8000 in
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

set_option maxRecDepth 8000 in
set_option maxHeartbeats 6000000 in
theorem window27_0g0_valid : window27_0g0.all (fun x => verifyPacked (ps27 ++ [x.1]) x.2) = true := by
  decide +kernel

def window27_0 : List (ℕ × ℕ) := window27_0g0

set_option maxRecDepth 8000 in
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

def ps28 : List ℕ := [3, 5, 7, 11, 13, 19, 29, 31]

def window28_0g0 : List (ℕ × ℕ) := [
  (37, 0x3088261802609024204c1),
  (41, 0x3088261802209024204c1),
  (43, 0x3088261802409024204c1),
  (47, 0x620c261204a304472082a3804609c24188273002309443088261802209024204c1),
  (53, 0x1470048310807208273004609c2309423088261802a09024204c1)
]

set_option maxRecDepth 8000 in
set_option maxHeartbeats 6000000 in
theorem window28_0g0_valid : window28_0g0.all (fun x => verifyPacked (ps28 ++ [x.1]) x.2) = true := by
  decide +kernel

def window28_0 : List (ℕ × ℕ) := window28_0g0

set_option maxRecDepth 8000 in
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

set_option maxRecDepth 8000 in
set_option maxHeartbeats 6000000 in
theorem window29_0g0_valid : window29_0g0.all (fun x => verifyPacked (ps29 ++ [x.1]) x.2) = true := by
  decide +kernel

def window29_0 : List (ℕ × ℕ) := window29_0g0

set_option maxRecDepth 8000 in
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

set_option maxRecDepth 8000 in
set_option maxHeartbeats 6000000 in
theorem window30_0g0_valid : window30_0g0.all (fun x => verifyPacked (ps30 ++ [x.1]) x.2) = true := by
  decide +kernel

def window30_0 : List (ℕ × ℕ) := window30_0g0

set_option maxRecDepth 8000 in
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

set_option maxRecDepth 8000 in
set_option maxHeartbeats 6000000 in
theorem window31_0g0_valid : window31_0g0.all (fun x => verifyPacked (ps31 ++ [x.1]) x.2) = true := by
  decide +kernel

def window31_0 : List (ℕ × ℕ) := window31_0g0

set_option maxRecDepth 8000 in
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

def ps32 : List ℕ := [3, 5, 7, 11, 17, 19, 23, 29]

def window32_0g0 : List (ℕ × ℕ) := [
  (31, 0x3088261802111022204c1),
  (37, 0xc418483288041942620c2a3044411c24110441884730043094230882610426180261102220441)
]

set_option maxRecDepth 8000 in
set_option maxHeartbeats 6000000 in
theorem window32_0g0_valid : window32_0g0.all (fun x => verifyPacked (ps32 ++ [x.1]) x.2) = true := by
  decide +kernel

def window32_0 : List (ℕ × ℕ) := window32_0g0

set_option maxRecDepth 8000 in
set_option maxHeartbeats 1500000 in
theorem window32_0_prime_values : window32_0.map Prod.fst = candidateFinals ps32 30 9 := by
  decide +kernel

theorem window32_0_valid : window32_0.all (fun x => verifyPacked (ps32 ++ [x.1]) x.2) = true := by
  exact window32_0g0_valid

theorem prefix32_verified {q : ℕ} (hlo : start ps32 ≤ q) (hhi : q ≤ lastCap ps32)
    (hp : q.Prime) (hlarge : 3 * den ps32 * (q-1) < ps32.prod * q) :
    ∃ w, verifyPacked (ps32 ++ [q]) w = true := by
  change 30 ≤ q at hlo
  change q ≤ 38 at hhi

  exact checked_window window32_0_prime_values window32_0_valid (by omega) (by omega) hp hlarge

def ps33 : List ℕ := [3, 5, 7, 11, 17, 19, 23, 31]

def window33_0g0 : List (ℕ × ℕ) := []

set_option maxRecDepth 8000 in
set_option maxHeartbeats 6000000 in
theorem window33_0g0_valid : window33_0g0.all (fun x => verifyPacked (ps33 ++ [x.1]) x.2) = true := by
  decide +kernel

def window33_0 : List (ℕ × ℕ) := window33_0g0

set_option maxRecDepth 8000 in
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
    {q : ℕ} (hlo : start ps ≤ q) (hhi : q ≤ lastCap ps)
    (hp : q.Prime) (hlarge : 3 * den ps * (q-1) < ps.prod * q) :
    ∃ w, verifyPacked (ps ++ [q]) w = true := by
  rw [viable_prefixes_exact] at hm
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
  rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact prefix0_verified hlo hhi hp hlarge
  · exact prefix1_verified hlo hhi hp hlarge
  · exact prefix2_verified hlo hhi hp hlarge
  · exact prefix3_verified hlo hhi hp hlarge
  · exact prefix4_verified hlo hhi hp hlarge
  · exact prefix5_verified hlo hhi hp hlarge
  · exact prefix6_verified hlo hhi hp hlarge
  · exact prefix7_verified hlo hhi hp hlarge
  · exact prefix8_verified hlo hhi hp hlarge
  · exact prefix9_verified hlo hhi hp hlarge
  · exact prefix10_verified hlo hhi hp hlarge
  · exact prefix11_verified hlo hhi hp hlarge
  · exact prefix12_verified hlo hhi hp hlarge
  · exact prefix13_verified hlo hhi hp hlarge
  · exact prefix14_verified hlo hhi hp hlarge
  · exact prefix15_verified hlo hhi hp hlarge
  · exact prefix16_verified hlo hhi hp hlarge
  · exact prefix17_verified hlo hhi hp hlarge
  · exact prefix18_verified hlo hhi hp hlarge
  · exact prefix19_verified hlo hhi hp hlarge
  · exact prefix20_verified hlo hhi hp hlarge
  · exact prefix21_verified hlo hhi hp hlarge
  · exact prefix22_verified hlo hhi hp hlarge
  · exact prefix23_verified hlo hhi hp hlarge
  · exact prefix24_verified hlo hhi hp hlarge
  · exact prefix25_verified hlo hhi hp hlarge
  · exact prefix26_verified hlo hhi hp hlarge
  · exact prefix27_verified hlo hhi hp hlarge
  · exact prefix28_verified hlo hhi hp hlarge
  · exact prefix29_verified hlo hhi hp hlarge
  · exact prefix30_verified hlo hhi hp hlarge
  · exact prefix31_verified hlo hhi hp hlarge
  · exact prefix32_verified hlo hhi hp hlarge
  · exact prefix33_verified hlo hhi hp hlarge

theorem exclude_bounded
    (checkedWord : ∀ ps ∈ viablePrefixes, ∀ q : ℕ, start ps ≤ q → q ≤ lastCap ps →
      q.Prime → 3 * den ps * (q-1) < ps.prod * q →
      ∃ w, verifyPacked (ps ++ [q]) w = true) :
    OMA.R_OeisA76495_conjecture_R2_H2_R1_H2_R1.H1 := by
  intro p e hstrict hp he hcap hq hsmall heq
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
  obtain ⟨w, hw⟩ := checkedWord ps hqualified (p 8) hlo hhi (hp 8).1 hcross
  rw [← hfull] at hw
  have hprofile : profileOf (List.ofFn p) = p := by
    funext i
    simp only [profileOf, List.getElem?_ofFn, i.isLt, dite_true, Option.getD_some]
  exact packed_sound hw e (by rw [hprofile]; exact fun i => (hp i).1) he
    (by simpa only [hprofile] using hsigma)

end SigmaNine

theorem OMA.solution : OMA.R_OeisA76495_conjecture_R2_H2_R1_H2_R1.H1 :=
  SigmaNine.exclude_bounded (fun _ hm _ hlo hhi hp hc =>
    SigmaNine.word_exists_of_viable hm hlo hhi hp hc)
