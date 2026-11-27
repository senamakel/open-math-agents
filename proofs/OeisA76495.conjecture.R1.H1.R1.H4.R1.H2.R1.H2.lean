import OMAReductions.R_OeisA76495_conjecture_R1_H1_R1_H4_R1_H2_R1
import Mathlib

/-!
First bound the ninth prime for each exceptional prefix. Then verify the
complete finite support lists and their disjoint exponent-box certificates.
Each packed word stores nine initial exponent bounds followed by the
certificate in base 32. The checker validates each skipped exponent by
divisibility against every support prime other than five.
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

end SigmaAbundancyBounds

namespace SigmaLocalModuli
open SigmaAbundancyBounds

def Allowed {k : ℕ} (p : Fin k → ℕ) (q e : ℕ) : Prop :=
  ∀ j, p j ≠ 5 → ¬ p j ∣ geometric q e

instance {k : ℕ} (p : Fin k → ℕ) (q e : ℕ) : Decidable (Allowed p q e) :=
  inferInstanceAs (Decidable (∀ j, p j ≠ 5 → ¬ p j ∣ geometric q e))

def skipped {k : ℕ} (p : Fin k → ℕ) (q c u : ℕ) : Prop :=
  ∀ i : Fin u, c < i.val → ¬ Allowed p q i.val

instance {k : ℕ} (p : Fin k → ℕ) (q c u : ℕ) : Decidable (skipped p q c u) :=
  inferInstanceAs (Decidable (∀ i : Fin u, c < i.val → ¬ Allowed p q i.val))

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

end SigmaLocalModuli

namespace SigmaNineBoxesLocal
open SigmaAbundancyBounds SigmaLocalModuli

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
      decide (skipped p (p i) cut next) &&
      check p (Function.update l i next) u child
  | .split i cut next below above =>
      decide (skipped p (p i) cut next) &&
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
      exact ih (lower_update hl (lower_of_skipped hskip (ha i) hcut)) hu hchild
  | split i cut next below above ihBelow ihAbove =>
      simp only [check, Bool.and_eq_true, decide_eq_true_eq] at hc
      obtain ⟨⟨hskip, hbelow⟩, habove⟩ := hc
      by_cases h : e i ≤ cut
      · exact ihBelow hl (upper_update hu h) hbelow
      · exact ihAbove (lower_update hl (lower_of_skipped hskip (ha i) (by omega))) hu habove


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
      decide (∀ i, skipped p (p i) 0 (l i)) &&
      check p l (fun _ => none) cert
  | none => false

theorem packed_sound {ps : List ℕ} {w : ℕ}
    (hc : verifyPacked ps w = true) (e : Exponents)
    (hp : ∀ i, (profileOf ps i).Prime) (he : ∀ i, 1 ≤ e i)
    (hs : divisorSum (profileOf ps) e = 3 * value (profileOf ps) e + 5) : False := by
  unfold verifyPacked at hc
  split at hc
  next cert rest h =>
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hc
    have ha := SigmaLocalModuli.allowed_of_equation (profileOf ps) e hp he
      (s := 1) (v := 1) (by simpa only [divisorSum, value, Nat.mul_one] using hs)
    have habove : Above (initial w) e := fun i => lower_of_skipped (hc.1 i) (ha i) (he i)
    exact sound (fun i => (hp i).two_le) ha hs cert habove (by simp [Bounded]) hc.2
  next => contradiction

end SigmaNineBoxesLocal

open SigmaNineBoxesLocal

namespace SigmaTailWindows

private def primesBetween (low count : ℕ) : List ℕ :=
  (List.range' low count).filter fun q => decide q.Prime

private theorem checked_window {ps : List ℕ} {lo count q : ℕ}
    {rows : List (ℕ × ℕ)}
    (hrows : rows.map Prod.fst = primesBetween lo count)
    (hcheck : rows.all (fun x => verifyPacked (ps ++ [x.1]) x.2) = true)
    (hlo : lo ≤ q) (hhi : q < lo + count) (hp : q.Prime) :
    ∃ w, verifyPacked (ps ++ [q]) w = true := by
  have hm : q ∈ primesBetween lo count :=
    List.mem_filter.mpr ⟨List.mem_range'_1.mpr ⟨hlo,hhi⟩, decide_eq_true hp⟩
  rw [← hrows] at hm
  obtain ⟨⟨q', w⟩, hr, eq⟩ := List.mem_map.mp hm
  change q' = q at eq
  subst q'
  exact ⟨w, List.all_eq_true.mp hcheck _ hr⟩


def ps23 : List ℕ := [3, 5, 7, 11, 13, 17, 19, 23]

private def window23_0 : List (ℕ × ℕ) := [
  (29, 0x3080242044420441),
  (31, 0x30802120444204c1),
  (37, 0x3080262044420441),
  (41, 0x309826104461804308843080222044420441),
  (43, 0x309826104461804308843080242044420441),
  (47, 0x6104261804308843080222044420441),
  (53, 0x6104261804308843080262044420441),
  (59, 0x309826104261804308843080222044420441),
  (61, 0x309826104261804308843080212044420441),
  (67, 0x309826104261804308843080242044420441),
  (71, 0x61802308843080222044420441),
  (73, 0x61802308843080212044420441),
  (79, 0x309826104461802308843080212044420441),
  (83, 0x309826104461802308843080242044420441),
  (89, 0x309826104461802308843080222044420441),
  (97, 0x41142c380430982730026104461802308843080262044420441),
  (101, 0x6104261802308843080222044420441),
  (103, 0x6104261802308843080262044420441),
  (107, 0x6104261802308843080242044420441),
  (109, 0x6104261802308843080242044420441),
  (113, 0x61042618023088430802a2044420441)
]

set_option maxHeartbeats 3000000 in
private theorem window23_0_valid :
    window23_0.all (fun x => verifyPacked (ps23 ++ [x.1]) x.2) = true := by
  decide +kernel

set_option maxHeartbeats 1000000 in
private theorem window23_0_eq : window23_0.map Prod.fst = primesBetween 24 96 := by
  decide +kernel


private def window23_1 : List (ℕ × ℕ) := [
  (127, 0x6104261802308843080212044420441),
  (131, 0x6104261802308843080222044420441),
  (137, 0x6104261802308843080262044420441),
  (139, 0x6104261802308843080242044420441),
  (149, 0x6104261802308843080242044420441),
  (151, 0x6104261802308843080242044420441),
  (157, 0x6104261802308843080212044420441),
  (163, 0x6104261802308843080212044420441),
  (167, 0x6104261802308843080222044420441),
  (173, 0x6104261802308843080222044420441),
  (179, 0x6104261802308843080262044420441),
  (181, 0x6104261802308843080262044420441),
  (191, 0x4114273004309846104261802308843080262044420441),
  (193, 0x73002309846104230884000004114241884309846104430882618043080212044420441),
  (197, 0x41142c380473002309846104230884000004114241884309846104430882618043080242044420441),
  (199, 0x41142c380473002309846104230884000004114241884309846104430882618043080212044420441),
  (211, 0x940016188200083406d200986206500058a08946188c43880621c2a30c2c504306804621440310a16b00218501208a131081310615182161c01184c2308211844200004114241882309846104430882618043080212044420441)
]

set_option maxHeartbeats 3000000 in
private theorem window23_1_valid :
    window23_1.all (fun x => verifyPacked (ps23 ++ [x.1]) x.2) = true := by
  decide +kernel

set_option maxHeartbeats 1000000 in
private theorem window23_1_eq : window23_1.map Prod.fst = primesBetween 120 96 := by
  decide +kernel


private def window23_2 : List (ℕ × ℕ) := [
  (223, 0xc260984108c221000309826104430882618043080262044420441),
  (227, 0xc260984108c221000309826104430882618043080222044420441),
  (229, 0xc260984108c221000309826104430882618043080262044420441),
  (233, 0xc260984108c221000309826104430882618043080242044420441),
  (239, 0xc260984108c221000309826104430882618043080242044420441),
  (241, 0xc260984108c221000309826104430882618043080242044420441),
  (251, 0xc260984108c221000309826104430882618043080222044420441),
  (257, 0xc260984108c221000309826104430882618043080222044420441),
  (263, 0xc260984108c221000309826104430882618043080242044420441),
  (269, 0xc260984108c221000309826104430882618043080262044420441),
  (271, 0xc260984108c221000309826104430882618043080242044420441),
  (277, 0xc260984108c221000309826104430882618043080212044420441),
  (281, 0xc260984108c221000309826104430882618043080222044420441),
  (283, 0xc260984108c221000309826104430882618043080212044420441),
  (293, 0xc260984108c221000309826104430882618043080222044420441),
  (307, 0xc260984108c221000309826104430882618043080242048420441),
  (311, 0xc260984108c221000309826104430882618043080262044420441)
]

set_option maxHeartbeats 3000000 in
private theorem window23_2_valid :
    window23_2.all (fun x => verifyPacked (ps23 ++ [x.1]) x.2) = true := by
  decide +kernel

set_option maxHeartbeats 1000000 in
private theorem window23_2_eq : window23_2.map Prod.fst = primesBetween 216 96 := by
  decide +kernel


private def window23_3 : List (ℕ × ℕ) := [
  (313, 0xc260984108c221000309826104430882618043080212044420441),
  (317, 0xc260984108c221000309826104430882618043080262044420441),
  (331, 0xc260984108c221000309826104430882618043080212044420441),
  (337, 0xc260984108c221000309826104430882618043080242044420441),
  (347, 0xc260984108c221000309826104430882618043080242044420441),
  (349, 0xc260984108c221000309826104430882618043080242044420441),
  (353, 0xc260984108c221000309826104430882618043080242044420441),
  (359, 0xc260984108c221000309826104430882618043080242044420441),
  (367, 0xc260984108c221000309826104430882618043080262044420441),
  (373, 0xc260984108c221000309826104430882618043080242044420441),
  (379, 0x1066098830a8c10904511cc010c260984108c2210003098261044308826180430802a2044420441),
  (383, 0x104509cc010c260984108c221000309826104430882618043080222044420441),
  (389, 0x104509cc010c260984108c221000309826104430882618043080262044420441),
  (397, 0x104509cc010c260984108c221000309826104430882618043080212044420441),
  (401, 0x104509cc010c260984108c221000309826104430882618043080262044420441)
]

set_option maxHeartbeats 3000000 in
private theorem window23_3_valid :
    window23_3.all (fun x => verifyPacked (ps23 ++ [x.1]) x.2) = true := by
  decide +kernel

set_option maxHeartbeats 1000000 in
private theorem window23_3_eq : window23_3.map Prod.fst = primesBetween 312 96 := by
  decide +kernel


private def window23_4 : List (ℕ × ℕ) := [
  (409, 0x6210230a04419840000c4384c4304c42858a084c420861408030a026210241984620c401850120cc1310813106151822208a139802184c13082118442000000000621c26210430a02620c4419844114441884309826104430882618043080212044420441),
  (419, 0x184c130821398011844200004114241884309826104430882618043080242044420441),
  (421, 0x184c130821398011844200004114241884309826104430882618043080212044420441),
  (431, 0x208a161c02184c130821398011844200004114241884309826104430882618043080242044420441),
  (433, 0x208a161c02184c130821398011844200004114241884309826104430882618043080262044420441),
  (439, 0x208a161c02184c130821398011844200004114241884309826104430882618043080242044420441),
  (443, 0x208a161c02184c130821398011844200004114241884309826104430882618043080262044420441),
  (449, 0x208a161c02184c13082139801184420000419824114262102620c241884309826104430882618043080222044420441),
  (457, 0xc280906610000310e183402310c1310816b0011850220cc13106251821208a2010450b0e010c260984109cc008c22100030982418826104430882618043080212044420441),
  (461, 0xc26090450984109cc008c22100030982418826104430882618043080222044420441),
  (463, 0x1884090281188311066128c1130e010c26090450984109cc008c22100030982418826104430882618043080212044420441),
  (467, 0x310813106220cc20106609884098830a8c1130e010c26090450984109cc008c22100030982418826104430882618043080262044420441),
  (479, 0xc2609045098410b0e008c2210000000062102620c441984620844114430982418826104430882618043080222044420441),
  (487, 0x184c1208a13082161c01184420000620824114430982418826104430882618043080212044420441),
  (491, 0x184c1208a13082161c01184420000620824114430982418826104430882618043080222044420441),
  (499, 0x83401310a2018850b58011884118280988311066128c110c2609045098410b0e008c2210003098241142418826104430882618043080212044420441),
  (503, 0x1885098840b58009883110661000000146184c438a0d008c4308c428800028c3098871188609885135801106609884098830a8c110c2609045098410b0e008c2210003098241142418826104430882618043080242044420441)
]

set_option maxHeartbeats 3000000 in
private theorem window23_4_valid :
    window23_4.all (fun x => verifyPacked (ps23 ++ [x.1]) x.2) = true := by
  decide +kernel

set_option maxHeartbeats 1000000 in
private theorem window23_4_eq : window23_4.map Prod.fst = primesBetween 408 96 := by
  decide +kernel


private def window23_5 : List (ℕ × ℕ) := [
  (509, 0x3098241142418826104461804308823080222044420441),
  (521, 0x3098241142418826104461804308823080222044420441),
  (523, 0x3098241142418826104461804308823080212044420441),
  (541, 0x3098241142620826104461804308823080212044420441),
  (547, 0x62142730846210230a04620c4419843098241142620826104461804308823080212044420441)
]

set_option maxHeartbeats 3000000 in
private theorem window23_5_valid :
    window23_5.all (fun x => verifyPacked (ps23 ++ [x.1]) x.2) = true := by
  decide +kernel

set_option maxHeartbeats 1000000 in
private theorem window23_5_eq : window23_5.map Prod.fst = primesBetween 504 49 := by
  decide +kernel


theorem cover23 {q : ℕ} (hlo : 24 ≤ q) (hhi : q ≤ 552) (hp : q.Prime) :
    ∃ w, verifyPacked (ps23 ++ [q]) w = true := by
  by_cases h0 : q < 120
  · exact checked_window window23_0_eq window23_0_valid (by omega) (by omega) hp
  by_cases h1 : q < 216
  · exact checked_window window23_1_eq window23_1_valid (by omega) (by omega) hp
  by_cases h2 : q < 312
  · exact checked_window window23_2_eq window23_2_valid (by omega) (by omega) hp
  by_cases h3 : q < 408
  · exact checked_window window23_3_eq window23_3_valid (by omega) (by omega) hp
  by_cases h4 : q < 504
  · exact checked_window window23_4_eq window23_4_valid (by omega) (by omega) hp
  exact checked_window window23_5_eq window23_5_valid (by omega) (by omega) hp


def ps29 : List ℕ := [3, 5, 7, 11, 13, 17, 19, 29]

private def window29_0 : List (ℕ × ℕ) := [
  (31, 0x30802120444204c1),
  (37, 0x6104261804308843080262044420441),
  (41, 0x309826104261804308843080222044420441),
  (43, 0x61802308843080242044420441),
  (47, 0x309826104461802308843080222044420441),
  (53, 0x61042618023088430802a2044420441),
  (59, 0x6104261802308843080222044420441),
  (61, 0x6104261802308843080212044420441),
  (67, 0x6104261802308843080242044420441),
  (71, 0x41142a380230984610423088400000720824114441882309846104430882618043080222044420441),
  (73, 0xc260984108c221000309826104430882618043080212044420441),
  (79, 0xc260984108c221000309826104430882618043080212044420441),
  (83, 0xc260984108c221000309826104430882618043080242044420441),
  (89, 0x3098241142418826104461804308823080222044420441),
  (97, 0x6104261804308823080262044420441),
  (101, 0x6104261804308823080222044420441),
  (103, 0x61042618043088230802a2044420441),
  (107, 0x6104261804308823080242044420441),
  (109, 0x6104261804308823080242044420441),
  (113, 0x61042618043088230802a2044420441)
]

set_option maxHeartbeats 3000000 in
private theorem window29_0_valid :
    window29_0.all (fun x => verifyPacked (ps29 ++ [x.1]) x.2) = true := by
  decide +kernel

set_option maxHeartbeats 1000000 in
private theorem window29_0_eq : window29_0.map Prod.fst = primesBetween 30 96 := by
  decide +kernel


private def window29_1 : List (ℕ × ℕ) := [
  (127, 0x6104261804308823080212044420441),
  (131, 0x6104261804308823080222044420441),
  (137, 0x6104261804308823080262044420441),
  (139, 0x6104261804308823080242044420441),
  (149, 0x6104261804308823080242044420441),
  (151, 0x6104261804308823080242044420441),
  (157, 0x6214262102620c4a304460a044114241884309846104261804308823080212044420441),
  (163, 0x30a02720824114441882309846104261804308823080212044420441),
  (167, 0x4114241882309846104261804308823080222044420441),
  (173, 0x309826104261804308823080222044420441),
  (179, 0x309826104261804308823080262044420441),
  (181, 0x4098261042618043088230802a2044420441),
  (191, 0x309826104261804308823080262044420441),
  (193, 0x309826104261804308823080212044420441),
  (197, 0x309826104261804308823080242044420441),
  (199, 0x309826104261804308823080212044420441),
  (211, 0x309826104261804308823080212044420441)
]

set_option maxHeartbeats 3000000 in
private theorem window29_1_valid :
    window29_1.all (fun x => verifyPacked (ps29 ++ [x.1]) x.2) = true := by
  decide +kernel

set_option maxHeartbeats 1000000 in
private theorem window29_1_eq : window29_1.map Prod.fst = primesBetween 126 96 := by
  decide +kernel


private def window29_2 : List (ℕ × ℕ) := [
  (223, 0x3098261042618043088230802a2044420441),
  (227, 0x309826104261804308823080222044420441),
  (229, 0x309826104261804308823080212044420441),
  (233, 0x309826104261804308823080242044420441),
  (239, 0x309826104261804308823080242044420441),
  (241, 0x309826104261804308823080242044420441),
  (251, 0x309826104261804308823080222044420441),
  (257, 0x309826104261804308823080222044420441),
  (263, 0x309826104261804308823080242044420441),
  (269, 0x4114241884309826104261804308823080262044420441),
  (271, 0x4114241884309826104261804308823080242044420441),
  (277, 0x4114241884309826104261804308823080212044420441),
  (281, 0x188409066100062182621426210441982620c441142a304241884309826104261804308823080222044420441),
  (283, 0x30982418826104261804308823080212044420441),
  (293, 0xc4204c418883308041982620c2a3044720844114430982418826104261804308823080222044420441),
  (307, 0x30982418826104261804308823080242048420441),
  (311, 0xc42048330804198262102620c4a3044720843098241142418826104261804308823080262044420441),
  (313, 0x621826214430a024198262102620c2a3042720843098241142418826104261804308823080212044420441),
  (317, 0xa21c2a3882621846214462102620c441982a30443098241142720826104261804308823080262044420441)
]

set_option maxHeartbeats 3000000 in
private theorem window29_2_valid :
    window29_2.all (fun x => verifyPacked (ps29 ++ [x.1]) x.2) = true := by
  decide +kernel

set_option maxHeartbeats 1000000 in
private theorem window29_2_eq : window29_2.map Prod.fst = primesBetween 222 96 := by
  decide +kernel


private def window29_3 : List (ℕ × ℕ) := [
  (331, 0x308826180212044420441),
  (337, 0x308826180242044420441),
  (347, 0x308826180242044420441),
  (349, 0x308826180242044420441),
  (353, 0x308826180242044420441),
  (359, 0x308826180242044420441),
  (367, 0x308826180212044420441),
  (373, 0x308826180242044420441),
  (379, 0x3088261802a2044420441),
  (383, 0x308826180222044420441),
  (389, 0x4114241884730043098461044308826180262044420441),
  (397, 0x4114241884730043098461044308826180212044420441),
  (401, 0x41142418847300430984610443088261802a2044420441),
  (409, 0x4114241884730043098461044308826180212044420441)
]

set_option maxHeartbeats 3000000 in
private theorem window29_3_valid :
    window29_3.all (fun x => verifyPacked (ps29 ++ [x.1]) x.2) = true := by
  decide +kernel

set_option maxHeartbeats 1000000 in
private theorem window29_3_eq : window29_3.map Prod.fst = primesBetween 318 96 := by
  decide +kernel


private def window29_4 : List (ℕ × ℕ) := [
  (419, 0x41882730043098461044308826180242044420441),
  (421, 0x41882730043098461044308826180212044420441),
  (431, 0x41882730043098461044308826180242044420441),
  (433, 0x41882730043098461044308826180262044420441),
  (439, 0x822854700883108041882730043098461044308826180242044420441),
  (443, 0x822854700883108041882730043098461044308826180262044420441),
  (449, 0x10450a8e0110621000720824114441882730043098461044308826180222044420441),
  (457, 0x41142a3804418840000c420461408030a0262102620c4720824114441882730043098461044308826180212044420441),
  (461, 0x82285470088310804114241882730043098461044308826180222044420441),
  (463, 0x82285470088310804114241882730043098461044308826180242044420441),
  (467, 0x1884098830b5800904510082285470088310804114241882730043098461044308826180262044420441),
  (479, 0x82285470048310804114241882730043098461044308826180222044420441),
  (487, 0x82285470048310804114241882730043098461044308826180212044420441),
  (491, 0x82285470048310804114272082730043098461044308826180222044420441),
  (499, 0x82285470048310804114272082730043098461044308826180212044420441),
  (503, 0x41142a38024188400000a38826214462104620c44114272082730043098461044308826180242044420441),
  (509, 0x41142a380241884730023098461044308826180222044420441)
]

set_option maxHeartbeats 3000000 in
private theorem window29_4_valid :
    window29_4.all (fun x => verifyPacked (ps29 ++ [x.1]) x.2) = true := by
  decide +kernel

set_option maxHeartbeats 1000000 in
private theorem window29_4_eq : window29_4.map Prod.fst = primesBetween 414 96 := by
  decide +kernel


private def window29_5 : List (ℕ × ℕ) := [
  (521, 0x7208241144a380441882730023098461044308826180222044420441),
  (523, 0x7208241144a380441882730023098461044308826180212044420441),
  (541, 0x41142a380441882730023098461044308826180212044420441),
  (547, 0x41142a380441882730023098461044308826180212044420441),
  (557, 0xc41858a008e410882288041142a380441882730023098461044308826180242044420441),
  (563, 0xe410482288041142a380441882730023098461044308826180222044420441),
  (569, 0xe410482288041142a380441882730023098461044308826180242044420441),
  (571, 0xe410482288041142a380441882730023098461044308826180242044420441),
  (577, 0x188409883100c4204c41858a008e41048228804114272082a380441882730023098461044308826180262044420441),
  (587, 0x72082a38044114241882730023098461044308826180222044420441),
  (593, 0x72082a38044114241882730023098461044308826180222044420441),
  (599, 0x4114241882a38023098461044308826180262044420441),
  (601, 0x4114241882a38023098461044308826180242044420441)
]

set_option maxHeartbeats 3000000 in
private theorem window29_5_valid :
    window29_5.all (fun x => verifyPacked (ps29 ++ [x.1]) x.2) = true := by
  decide +kernel

set_option maxHeartbeats 1000000 in
private theorem window29_5_eq : window29_5.map Prod.fst = primesBetween 510 96 := by
  decide +kernel


private def window29_6 : List (ℕ × ℕ) := [
  (607, 0x4114241882a38023098461044308826180242044420441),
  (613, 0x4114241882a38023098461044308826180212044420441),
  (617, 0x4114241882a38023098461044308826180222044420441),
  (619, 0x4114241882a38023098461044308826180212044420441),
  (631, 0x310a16b002185020020d004c4288062142d600430a0262104620c2c5002720844114241882a38023098461044308826180212044420441),
  (641, 0x4114272082a38023098461044308826180262044420441),
  (643, 0x4114272082a38023098461044308826180262044420441),
  (647, 0x4114272082a38023098461044308826180222044420441),
  (653, 0x14438547105ac008c4284c4208c41880620c2c50044114272082a38023098461044308826180262044420441)
]

set_option maxHeartbeats 3000000 in
private theorem window29_6_valid :
    window29_6.all (fun x => verifyPacked (ps29 ++ [x.1]) x.2) = true := by
  decide +kernel

set_option maxHeartbeats 1000000 in
private theorem window29_6_eq : window29_6.map Prod.fst = primesBetween 606 52 := by
  decide +kernel


theorem cover29 {q : ℕ} (hlo : 30 ≤ q) (hhi : q ≤ 657) (hp : q.Prime) :
    ∃ w, verifyPacked (ps29 ++ [q]) w = true := by
  by_cases h0 : q < 126
  · exact checked_window window29_0_eq window29_0_valid (by omega) (by omega) hp
  by_cases h1 : q < 222
  · exact checked_window window29_1_eq window29_1_valid (by omega) (by omega) hp
  by_cases h2 : q < 318
  · exact checked_window window29_2_eq window29_2_valid (by omega) (by omega) hp
  by_cases h3 : q < 414
  · exact checked_window window29_3_eq window29_3_valid (by omega) (by omega) hp
  by_cases h4 : q < 510
  · exact checked_window window29_4_eq window29_4_valid (by omega) (by omega) hp
  by_cases h5 : q < 606
  · exact checked_window window29_5_eq window29_5_valid (by omega) (by omega) hp
  exact checked_window window29_6_eq window29_6_valid (by omega) (by omega) hp


def ps31 : List ℕ := [3, 5, 7, 11, 13, 17, 19, 31]

private def window31_0 : List (ℕ × ℕ) := [
  (37, 0x30982618043088430802608444204c1),
  (41, 0x618023088430802208444204c1),
  (43, 0x618023088430802408444204c1),
  (47, 0x618023088430802208444204c1),
  (53, 0x618023088430802608444204c1),
  (59, 0x61202620c4a30444114473004609c230984618023088430802208444204c1),
  (61, 0x609c241142a380230984618023088430802408444204c1),
  (67, 0x621826210441982620c2a304241144a380473002609c430982618023088430802408444204c1),
  (71, 0x4114273004609c230982618023088430802208444204c1),
  (73, 0x621426210441982620c2a3042a380440a02609c23098241142730023088430802108444204c1),
  (79, 0x3088230802108444204c1),
  (83, 0x3088230802408444204c1),
  (89, 0x3088230802208444204c1),
  (97, 0x3088230802608444204c1),
  (101, 0x3088230802208444204c1),
  (103, 0x4114241884609c430984618043088230802608444204c1),
  (107, 0x4114241882609c430984618043088230802408444204c1),
  (109, 0x609c230984618043088230802608444204c1),
  (113, 0x609c230984618043088230802a08444204c1),
  (127, 0x30982618043088230802108444204c1)
]

set_option maxHeartbeats 3000000 in
private theorem window31_0_valid :
    window31_0.all (fun x => verifyPacked (ps31 ++ [x.1]) x.2) = true := by
  decide +kernel

set_option maxHeartbeats 1000000 in
private theorem window31_0_eq : window31_0.map Prod.fst = primesBetween 32 96 := by
  decide +kernel


private def window31_1 : List (ℕ × ℕ) := [
  (131, 0x30982618043088230802208444204c1),
  (137, 0x30982618043088230802608444204c1),
  (139, 0x30982618043088230802408444204c1),
  (149, 0x620824114441882609c430982618043088230802408444204c1),
  (151, 0x4114241882609c430982618043088230802408444204c1),
  (157, 0x609c230982618043088230802108444204c1),
  (163, 0x609c230982618043088230802108444204c1),
  (167, 0x4114241884609c230982618043088230802208444204c1),
  (173, 0x609c23098241882618043088230802208444204c1),
  (179, 0x609c2309824114241882618043088230802608444204c1),
  (181, 0x609c2409824114241882618043088230802608444204c1)
]

set_option maxHeartbeats 3000000 in
private theorem window31_1_valid :
    window31_1.all (fun x => verifyPacked (ps31 ++ [x.1]) x.2) = true := by
  decide +kernel

set_option maxHeartbeats 1000000 in
private theorem window31_1_eq : window31_1.map Prod.fst = primesBetween 128 57 := by
  decide +kernel


theorem cover31 {q : ℕ} (hlo : 32 ≤ q) (hhi : q ≤ 184) (hp : q.Prime) :
    ∃ w, verifyPacked (ps31 ++ [q]) w = true := by
  by_cases h0 : q < 128
  · exact checked_window window31_0_eq window31_0_valid (by omega) (by omega) hp
  exact checked_window window31_1_eq window31_1_valid (by omega) (by omega) hp


def ps37 : List ℕ := [3, 5, 7, 11, 13, 17, 19, 37]

private def window37_0 : List (ℕ × ℕ) := [
  (41, 0x6104261802308843080223044420441),
  (43, 0x6104261802308843080243044420441),
  (47, 0xc260984108c221000309826104430882618043080263044420441),
  (53, 0x18860b580118850988409883110660a8c110000310a1310813106220cc20106609884098830a8c11314010c2609045098410a8e008c2210003098241142418826104430882618043080263044420441),
  (59, 0x6104261804308823080223044420441),
  (61, 0x6104261804308823080213044420441),
  (67, 0x6104261804308823080243044420441),
  (71, 0x4114241884309846104261804308823080225044420441),
  (73, 0x4114241882309846104261804308823080243044420441),
  (79, 0x309826104261804308823080213044420441),
  (83, 0x309826104261804308823080243044420441),
  (89, 0x4114241884309826104261804308823080223044420441),
  (97, 0x308826180263044420441),
  (101, 0x822854700883108041882730043098461044308826180223044420441),
  (103, 0x82285470048310804114241882730043098461044308826180263044420441),
  (107, 0x62082a38044114241882730023098461044308826180243044420441),
  (109, 0xc42860d004e610806214273082d60044114262102620c262082c50023098461044308826180243044420441),
  (113, 0x30982610443088261802a3044420441),
  (127, 0x3098261044308826180213044420441),
  (131, 0x3098261044308826180223044420441)
]

set_option maxHeartbeats 3000000 in
private theorem window37_0_valid :
    window37_0.all (fun x => verifyPacked (ps37 ++ [x.1]) x.2) = true := by
  decide +kernel

set_option maxHeartbeats 1000000 in
private theorem window37_0_eq : window37_0.map Prod.fst = primesBetween 38 96 := by
  decide +kernel


private def window37_1 : List (ℕ × ℕ) := [
  (137, 0x6214262104620c2419844114241884730043098261044308826180263044420441),
  (139, 0xc4304c4204c418883304822894700883108041882730043098261044308826180243044420441),
  (149, 0x41142a380430982418827300261044308826180243044420441),
  (151, 0x62082a38043098241142418827300261044308826180243044420441),
  (157, 0x30882610426180213044420441),
  (163, 0x30882610426180213044420441),
  (167, 0x30882610426180223044420441),
  (173, 0x30882610426180223044420441),
  (179, 0x30882610426180263044420441),
  (181, 0x30882610426180263044420441),
  (191, 0x30882610426180263044420441),
  (193, 0x30882610426180213044420441),
  (197, 0x30882610426180243044420441),
  (199, 0x30882610426180213044420441),
  (211, 0x30882610426180213044420441),
  (223, 0x30882610426180263044420441),
  (227, 0x30882610426180223044420441),
  (229, 0x30882610426180213044420441)
]

set_option maxHeartbeats 3000000 in
private theorem window37_1_valid :
    window37_1.all (fun x => verifyPacked (ps37 ++ [x.1]) x.2) = true := by
  decide +kernel

set_option maxHeartbeats 1000000 in
private theorem window37_1_eq : window37_1.map Prod.fst = primesBetween 134 96 := by
  decide +kernel


private def window37_2 : List (ℕ × ℕ) := [
  (233, 0x30882610426180243044420441),
  (239, 0x30882610426180243044420441),
  (241, 0x30882610426180243044420441),
  (251, 0x30882610426180223044420441),
  (257, 0x30882610426180223044420441),
  (263, 0x30882610426180243044420441),
  (269, 0x30882610426180263044420441),
  (271, 0x30882610426180243044420441),
  (277, 0x30882610426180213044420441),
  (281, 0x30882610426180223044420441),
  (283, 0x30882610426180213044420441),
  (293, 0x30882610426180223044420441),
  (307, 0x30882610426180243048420441),
  (311, 0x30882610426180263044420441),
  (313, 0x30882610426180213044420441),
  (317, 0x30882610426180263044420441)
]

set_option maxHeartbeats 3000000 in
private theorem window37_2_valid :
    window37_2.all (fun x => verifyPacked (ps37 ++ [x.1]) x.2) = true := by
  decide +kernel

set_option maxHeartbeats 1000000 in
private theorem window37_2_eq : window37_2.map Prod.fst = primesBetween 230 96 := by
  decide +kernel


private def window37_3 : List (ℕ × ℕ) := [
  (331, 0x30882610426180213044420441),
  (337, 0x30882610426180243044420441),
  (347, 0x30882610426180243044420441),
  (349, 0x30882610426180243044420441),
  (353, 0x30882610426180243044420441),
  (359, 0x30882610426180243044420441),
  (367, 0x30882610426180213044420441),
  (373, 0x30882610426180243044420441),
  (379, 0x308826104261802a3044420441),
  (383, 0x30882610426180223044420441),
  (389, 0x30882610426180263044420441),
  (397, 0x30882610426180213044420441),
  (401, 0x30882610426180263044420441),
  (409, 0x30882610426180213044420441),
  (419, 0x30882610426180243044420441),
  (421, 0x30882610426180213044420441)
]

set_option maxHeartbeats 3000000 in
private theorem window37_3_valid :
    window37_3.all (fun x => verifyPacked (ps37 ++ [x.1]) x.2) = true := by
  decide +kernel

set_option maxHeartbeats 1000000 in
private theorem window37_3_eq : window37_3.map Prod.fst = primesBetween 326 96 := by
  decide +kernel


private def window37_4 : List (ℕ × ℕ) := [
  (431, 0x30882610426180243044420441),
  (433, 0x30882610426180263044420441),
  (439, 0x62102620c4a30444114441884730043098430882610426180243044420441),
  (443, 0x4114241884730043098430882610426180263044420441),
  (449, 0x4114241884730043098430882610426180223044420441),
  (457, 0x4114241884730043098430882610426180213044420441),
  (461, 0x4114241884730043098430882610426180223044420441),
  (463, 0x4114241884730043098430882610426180213044420441),
  (467, 0x4114241884730043098430882610426180263044420441),
  (479, 0x4114241884730043098430882610426180223044420441),
  (487, 0x41882730043098430882610426180213044420441),
  (491, 0x41882730043098430882610426180243044420441),
  (499, 0x41882730043098430882610426180213044420441),
  (503, 0x41882730043098430882610426180243044420441),
  (509, 0x146084822894700883108041882730043098430882610426180223044420441)
]

set_option maxHeartbeats 3000000 in
private theorem window37_4_valid :
    window37_4.all (fun x => verifyPacked (ps37 ++ [x.1]) x.2) = true := by
  decide +kernel

set_option maxHeartbeats 1000000 in
private theorem window37_4_eq : window37_4.map Prod.fst = primesBetween 422 96 := by
  decide +kernel


private def window37_5 : List (ℕ × ℕ) := [
  (521, 0x41142a38044188400000620c2a3044620844114441882730043098430882610426180223044420441),
  (523, 0x8228547008831080000006210240a04620c4a3042620844114441882730043098430882610426180213044420441),
  (541, 0x208a151c0220c4200006210240a04620c262082a30424114441882730043098430882610426180213044420441),
  (547, 0xc28098840988313140128c11104510082285470088310804114241882730043098430882610426180213044420441),
  (557, 0x822848310804114241882730043098430882610426180243044420441),
  (563, 0x822848310804114241882730043098430882610426180223044420441),
  (569, 0xc4284c4204c41894608547008822848310804114241882730043098430882610426180243044420441),
  (571, 0xc4284c4204c41854608547008822848310804114241882730043098430882610426180243044420441),
  (577, 0x82285470048310804114241882730043098430882610426180263044420441),
  (587, 0x10450a8e0090621000620c2a3042620844114241882730043098430882610426180223044420441),
  (593, 0x82285470048310804114262082730043098430882610426180223044420441),
  (599, 0x82285470048310804114262082730043098430882610426180263044420441),
  (601, 0x82285470048310804114262082730043098430882610426180243044420441),
  (607, 0x10450a8e009062100062102620c44114262082a3042730043098430882610426180243044420441),
  (613, 0x41142a380241884730023098430882610426180213044420441)
]

set_option maxHeartbeats 3000000 in
private theorem window37_5_valid :
    window37_5.all (fun x => verifyPacked (ps37 ++ [x.1]) x.2) = true := by
  decide +kernel

set_option maxHeartbeats 1000000 in
private theorem window37_5_eq : window37_5.map Prod.fst = primesBetween 518 96 := by
  decide +kernel


private def window37_6 : List (ℕ × ℕ) := [
  (617, 0xc4285ac004c4208c41880620c2c5004a304441142a380241884730023098430882610426180223044420441),
  (619, 0xc1404c4208c41854608800018280988411883128c10b1401104509062100000000a30c260a0462104620c2a3044620844114441882a3804730023098430882610426180213044420441),
  (631, 0x6208241144a380441882730023098430882610426180213044420441),
  (641, 0x7308262104620c4a30446208241144a380441882730023098430882610426180263044420441),
  (643, 0x620c2a30446208241144a380441882730023098430882610426180263044420441),
  (647, 0x62102620c462082a304241144a380441882730023098430882610426180223044420441),
  (653, 0x41142a380441882730023098430882610426180263044420441),
  (659, 0x41142a380441882730023098430882610426180243044420441),
  (661, 0x41142a380441882730023098430882610426180213044420441),
  (673, 0x41142a380441882730023098430882610426180213044420441),
  (677, 0x41142a380441882730023098430882610426180223044420441),
  (683, 0xc42058a008c418546088c410882288041142a380441882730023098430882610426180243044420441),
  (691, 0x61404c4204c4185460858a004c410882288041142a380441882730023098430882610426180213044420441),
  (701, 0xc410482288041142a380441882730023098430882610426180223044420441),
  (709, 0x1cc2098281188411883100060a0262102a3882620c4c5004a304462082411440000060a0262104620c2a30446208441142a380441882730023098430882610426180213044420441)
]

set_option maxHeartbeats 3000000 in
private theorem window37_6_valid :
    window37_6.all (fun x => verifyPacked (ps37 ++ [x.1]) x.2) = true := by
  decide +kernel

set_option maxHeartbeats 1000000 in
private theorem window37_6_eq : window37_6.map Prod.fst = primesBetween 614 96 := by
  decide +kernel


private def window37_7 : List (ℕ × ℕ) := [
  (719, 0xc4184c4105460858a0048228804114262082a380441882730023098430882610426180223044420441),
  (727, 0x62082a38044114241882730023098430882610426180243044420441),
  (733, 0x62082a38044114241882730023098430882610426180213044420441),
  (739, 0x620c2a304462082a38044114241882730023098430882610426180243044420441),
  (743, 0x62082a3042a38044114241882730023098430882610426180223044420441),
  (751, 0x4114241882a38023098430882610426180213044420441),
  (757, 0x4114241882a38023098430882610426180213044420441),
  (761, 0x4114241882a38023098430882610426180223044420441),
  (769, 0x4114241882a38023098430882610426180243044420441),
  (773, 0x4114241882a38023098430882610426180223044420441),
  (787, 0x30a0262104620c4c5004a3044620844114241882a38023098430882610426180213044420441),
  (797, 0x564009848128c514a000a8c411885098840a8c30c1a00a8c1100062102620c4a3042c5004620844114241882a38023098430882610426180223044420441)
]

set_option maxHeartbeats 3000000 in
private theorem window37_7_valid :
    window37_7.all (fun x => verifyPacked (ps37 ++ [x.1]) x.2) = true := by
  decide +kernel

set_option maxHeartbeats 1000000 in
private theorem window37_7_eq : window37_7.map Prod.fst = primesBetween 710 96 := by
  decide +kernel


private def window37_8 : List (ℕ × ℕ) := [
  (809, 0x4114262082a38023098430882610426180243044420441),
  (811, 0x4114262082a38023098430882610426180243044420441),
  (821, 0x4114262082a38023098430882610426180243044420441),
  (823, 0x4114262082a38023098430882610426180213044420441),
  (827, 0x62102620c4c5004a30444114262082a38023098430882610426180223044420441),
  (829, 0x51c416b002310a1305020020d004c4288062142d600460a027308462104620c40000062142a30c27308460a0462104620c2c5004a30444114262082a38023098430882610426180213044420441),
  (839, 0x188509cc20b580098841188310007308262104620c2c50044114262082a3042a38023098430882610426180223044420441)
]

set_option maxHeartbeats 3000000 in
private theorem window37_8_valid :
    window37_8.all (fun x => verifyPacked (ps37 ++ [x.1]) x.2) = true := by
  decide +kernel

set_option maxHeartbeats 1000000 in
private theorem window37_8_eq : window37_8.map Prod.fst = primesBetween 806 40 := by
  decide +kernel


theorem cover37 {q : ℕ} (hlo : 38 ≤ q) (hhi : q ≤ 845) (hp : q.Prime) :
    ∃ w, verifyPacked (ps37 ++ [q]) w = true := by
  by_cases h0 : q < 134
  · exact checked_window window37_0_eq window37_0_valid (by omega) (by omega) hp
  by_cases h1 : q < 230
  · exact checked_window window37_1_eq window37_1_valid (by omega) (by omega) hp
  by_cases h2 : q < 326
  · exact checked_window window37_2_eq window37_2_valid (by omega) (by omega) hp
  by_cases h3 : q < 422
  · exact checked_window window37_3_eq window37_3_valid (by omega) (by omega) hp
  by_cases h4 : q < 518
  · exact checked_window window37_4_eq window37_4_valid (by omega) (by omega) hp
  by_cases h5 : q < 614
  · exact checked_window window37_5_eq window37_5_valid (by omega) (by omega) hp
  by_cases h6 : q < 710
  · exact checked_window window37_6_eq window37_6_valid (by omega) (by omega) hp
  by_cases h7 : q < 806
  · exact checked_window window37_7_eq window37_7_valid (by omega) (by omega) hp
  exact checked_window window37_8_eq window37_8_valid (by omega) (by omega) hp

end SigmaTailWindows

namespace SigmaNineTailBoxesLocal

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

private theorem lower_update {e l : Exponents} {i : Fin 8} {k : ℕ}
    (hl : Above l e) (hk : k ≤ e i) : Above (Function.update l i k) e := by
  intro j
  by_cases h : j = i
  · subst j
    simpa using hk
  · simpa [Function.update_of_ne h] using hl j

private theorem upper_update {e : Exponents} {u : Ceiling} {i : Fin 8} {k : ℕ}
    (hu : Bounded e u) (hk : e i ≤ k) : Bounded e (Function.update u i (some k)) := by
  intro j b hj
  by_cases h : j = i
  · subst j
    have : k = b := by simpa using hj
    simpa [← this] using hk
  · apply hu j b
    simpa [Function.update_of_ne h] using hj

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
  deriving DecidableEq, Repr

def checkBound (p l : Exponents) (u : Ceiling) (c : ℕ) : BoundCertificate → Bool
  | .overshoot => decide (3 * value p l < divisorSum p l)
  | .cap => decide (upperNum p u * (c+1) ≤ 3 * upperDen p u * c)
  | .split i cut next below above =>
      decide (SigmaLocalModuli.skipped p (p i) cut next) &&
      checkBound p l (Function.update u i (some cut)) c below &&
      checkBound p (Function.update l i next) u c above

theorem bound_sound {p e : Exponents} {q t : ℕ} (hp : ∀ i, 2 ≤ p i)
    (ha : ∀ i, SigmaLocalModuli.Allowed p (p i) (e i))
    (hq : 5 < q) (ht : 1 ≤ t)
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
      · have hlow : next ≤ e i :=
          SigmaLocalModuli.lower_of_skipped hskip (ha i) (by omega)
        exact ihAbove (lower_update hl hlow) hu habove

private theorem local_allowed_of_equation {p e : Exponents} {q t : ℕ}
    (hp : ∀ i, (p i).Prime) (he : ∀ i, 1 ≤ e i)
    (heq : divisorSum p e * geometric q t = 3 * (value p e * q^t) + 5) :
    ∀ i, SigmaLocalModuli.Allowed p (p i) (e i) := by
  intro i j hj hdiv
  have hpN : p j ∣ value p e := by
    have hdvd : p j ∣ p j ^ e j := dvd_pow_self _ (by have := he j; omega)
    exact hdvd.trans (Finset.dvd_prod_of_mem _ (Finset.mem_univ _))
  have hpS : p j ∣ divisorSum p e :=
    hdiv.trans (Finset.dvd_prod_of_mem _ (Finset.mem_univ _))
  have hk : p j ∣ 3 * (value p e * q ^ t) :=
    dvd_mul_of_dvd_right (dvd_mul_of_dvd_left hpN _) _
  have hwhole := dvd_mul_of_dvd_left hpS (geometric q t)
  rw [heq] at hwhole
  have h5 : p j ∣ 5 := (Nat.dvd_add_iff_right hk).mpr hwhole
  rcases (Nat.dvd_prime Nat.prime_five).mp h5 with h | h
  · exact (hp j).ne_one h
  · exact hj h

def p23 : Exponents := ![3, 5, 7, 11, 13, 17, 19, 23]
def p29 : Exponents := ![3, 5, 7, 11, 13, 17, 19, 29]
def p31 : Exponents := ![3, 5, 7, 11, 13, 17, 19, 31]
def p37 : Exponents := ![3, 5, 7, 11, 13, 17, 19, 37]

def l23 : Exponents := ![1, 2, 1, 4, 4, 2, 1, 4]
def l29 : Exponents := ![1, 2, 1, 4, 4, 2, 1, 4]
def l31 : Exponents := ![1, 6, 1, 4, 4, 2, 1, 1]
def l37 : Exponents := ![1, 2, 1, 4, 4, 2, 1, 6]

theorem initial_valid23 : ∀ i, 1 ≤ l23 i ∧
    SigmaLocalModuli.Allowed p23 (p23 i) (l23 i) ∧
    SigmaLocalModuli.skipped p23 (p23 i) 0 (l23 i) := by
  decide +kernel

theorem initial_valid29 : ∀ i, 1 ≤ l29 i ∧
    SigmaLocalModuli.Allowed p29 (p29 i) (l29 i) ∧
    SigmaLocalModuli.skipped p29 (p29 i) 0 (l29 i) := by
  decide +kernel

theorem initial_valid31 : ∀ i, 1 ≤ l31 i ∧
    SigmaLocalModuli.Allowed p31 (p31 i) (l31 i) ∧
    SigmaLocalModuli.skipped p31 (p31 i) 0 (l31 i) := by
  decide +kernel

theorem initial_valid37 : ∀ i, 1 ≤ l37 i ∧
    SigmaLocalModuli.Allowed p37 (p37 i) (l37 i) ∧
    SigmaLocalModuli.skipped p37 (p37 i) 0 (l37 i) := by
  decide +kernel

def cert23 : BoundCertificate :=
  (.split 0 3 6
    (.split 0 1 3
      .cap
      (.split 1 2 6
        .cap
        (.split 2 1 3 .cap .overshoot)))
    (.split 2 1 3 .cap .overshoot))

def cert29 : BoundCertificate :=
  (.split 0 3 6
    .cap
    (.split 1 2 6
      (.split 2 1 3 .cap (.split 6 1 3 .cap .overshoot))
      (.split 2 1 3 .cap .overshoot)))

def cert31 : BoundCertificate :=
  (.split 0 3 6
    .cap
    (.split 2 1 3 .cap .overshoot))

def cert37 : BoundCertificate :=
  (.split 0 3 6
    .cap
    (.split 1 2 6
      .cap
      (.split 2 1 3 .cap (.split 6 1 3 .cap .overshoot))))

theorem check23 : checkBound p23 l23 (fun _ => none) 552 cert23 = true := by
  set_option maxHeartbeats 3000000 in decide +kernel

theorem check29 : checkBound p29 l29 (fun _ => none) 657 cert29 = true := by
  set_option maxHeartbeats 3000000 in decide +kernel

theorem check31 : checkBound p31 l31 (fun _ => none) 184 cert31 = true := by
  set_option maxHeartbeats 3000000 in decide +kernel

theorem check37 : checkBound p37 l37 (fun _ => none) 845 cert37 = true := by
  set_option maxHeartbeats 3000000 in decide +kernel

private theorem support_bound {p l : Exponents} {c : ℕ} {cert : BoundCertificate}
    {e : Exponents} {q t : ℕ}
    (hp : ∀ i, (p i).Prime) (hstart : ∀ i, 1 ≤ l i ∧
      SigmaLocalModuli.Allowed p (p i) (l i) ∧
      SigmaLocalModuli.skipped p (p i) 0 (l i))
    (he : ∀ i, 1 ≤ e i) (hq : 5 < q) (ht : 1 ≤ t)
    (heq : divisorSum p e * geometric q t = 3 * (value p e * q^t) + 5)
    (hc : checkBound p l (fun _ => none) c cert = true) : q ≤ c := by
  have hprime : ∀ i, 2 ≤ p i := fun i => (hp i).two_le
  have ha := local_allowed_of_equation hp he heq
  have hl : Above l e := by
    intro i
    exact SigmaLocalModuli.lower_of_skipped (hstart i).2.2 (ha i) (by have := he i; omega)
  exact bound_sound hprime ha hq ht heq cert hl (by simp [Bounded]) hc

theorem cutoff23 {e : Exponents} {q t : ℕ} (he : ∀ i, 1 ≤ e i)
    (hq : 5 < q) (ht : 1 ≤ t)
    (heq : divisorSum p23 e * geometric q t = 3 * (value p23 e * q^t) + 5) :
    q ≤ 552 := by
  apply support_bound (p := p23) (l := l23) (c := 552) (cert := cert23)
  · intro i
    fin_cases i <;> norm_num [p23]
  · exact initial_valid23
  · exact he
  · exact hq
  · exact ht
  · exact heq
  · exact check23

theorem cutoff29 {e : Exponents} {q t : ℕ} (he : ∀ i, 1 ≤ e i)
    (hq : 5 < q) (ht : 1 ≤ t)
    (heq : divisorSum p29 e * geometric q t = 3 * (value p29 e * q^t) + 5) :
    q ≤ 657 := by
  apply support_bound (p := p29) (l := l29) (c := 657) (cert := cert29)
  · intro i
    fin_cases i <;> norm_num [p29]
  · exact initial_valid29
  · exact he
  · exact hq
  · exact ht
  · exact heq
  · exact check29

theorem cutoff31 {e : Exponents} {q t : ℕ} (he : ∀ i, 1 ≤ e i)
    (hq : 5 < q) (ht : 1 ≤ t)
    (heq : divisorSum p31 e * geometric q t = 3 * (value p31 e * q^t) + 5) :
    q ≤ 184 := by
  apply support_bound (p := p31) (l := l31) (c := 184) (cert := cert31)
  · intro i
    fin_cases i <;> norm_num [p31]
  · exact initial_valid31
  · exact he
  · exact hq
  · exact ht
  · exact heq
  · exact check31

theorem cutoff37 {e : Exponents} {q t : ℕ} (he : ∀ i, 1 ≤ e i)
    (hq : 5 < q) (ht : 1 ≤ t)
    (heq : divisorSum p37 e * geometric q t = 3 * (value p37 e * q^t) + 5) :
    q ≤ 845 := by
  apply support_bound (p := p37) (l := l37) (c := 845) (cert := cert37)
  · intro i
    fin_cases i <;> norm_num [p37]
  · exact initial_valid37
  · exact he
  · exact hq
  · exact ht
  · exact heq
  · exact check37

end SigmaNineTailBoxesLocal

open SigmaAbundancyBounds SigmaTailWindows

namespace SigmaNineTailClosure

def ProfileBound (ps : List ℕ) (c : ℕ) : Prop :=
  ∀ p e : Fin 9 → ℕ, StrictMono p → (∀ i, (p i).Prime) →
    (∀ i, 1 ≤ e i) → List.ofFn (fun i : Fin 8 => p i.castSucc) = ps →
    (∏ i, ∑ j ∈ Finset.range (e i + 1), p i ^ j) = 3 * (∏ i, p i ^ e i) + 5 →
    p 8 ≤ c

theorem solve_of_caps (h23 : ProfileBound ps23 552) (h29 : ProfileBound ps29 657)
    (h31 : ProfileBound ps31 184) (h37 : ProfileBound ps37 845) :
    OMA.R_OeisA76495_conjecture_R1_H1_R1_H4_R1_H2_R1.H2 := by
  intro p e hs hp he hprefix heq
  let ps := List.ofFn (fun i : Fin 8 => p i.castSucc)
  have h8 : Fin.last 8 = (8 : Fin 9) := by decide
  have h7 : (Fin.last 7).castSucc = (7 : Fin 9) := by decide
  have hfull : List.ofFn p = ps ++ [p 8] := by
    rw [List.ofFn_succ', List.concat_eq_append, h8]
  have hlast : ps.getLastD 0 = p 7 := by
    dsimp only [ps]
    rw [List.ofFn_succ', List.concat_eq_append, List.getLastD_concat, h7]
  have hlo : ps.getLastD 0 < p 8 := by
    rw [hlast]
    exact hs (by decide : (7 : Fin 9) < 8)
  have hw : ∃ w, verifyPacked (ps ++ [p 8]) w = true := by
    change ps ∈ ([ps23, ps29, ps31, ps37] : List (List ℕ)) at hprefix
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hprefix
    rcases hprefix with hx | hx | hx | hx
    · rw [hx]
      exact cover23 (by rw [hx] at hlo; exact hlo)
        (h23 p e hs (fun i => (hp i).1) he hx heq) (hp 8).1
    · rw [hx]
      exact cover29 (by rw [hx] at hlo; exact hlo)
        (h29 p e hs (fun i => (hp i).1) he hx heq) (hp 8).1
    · rw [hx]
      exact cover31 (by rw [hx] at hlo; exact hlo)
        (h31 p e hs (fun i => (hp i).1) he hx heq) (hp 8).1
    · rw [hx]
      exact cover37 (by rw [hx] at hlo; exact hlo)
        (h37 p e hs (fun i => (hp i).1) he hx heq) (hp 8).1
  rw [← hfull] at hw
  obtain ⟨w, hw⟩ := hw
  have heqn : divisorSum p e = 3 * value p e + 5 := by
    simpa only [divisorSum, value, geometric_eq_sum] using heq
  have hprofile : profileOf (List.ofFn p) = p := by
    funext i
    simp only [profileOf, List.getElem?_ofFn, i.isLt, dite_true, Option.getD_some]
  exact packed_sound hw e (by rw [hprofile]; exact fun i => (hp i).1) he
    (by simpa only [hprofile] using heqn)

private theorem lift_bound (r : Fin 8 → ℕ) {c : ℕ} (h5 : 5 < r 7)
    (bound : ∀ {f : Fin 8 → ℕ} {q t : ℕ}, (∀ i, 1 ≤ f i) → 5 < q → 1 ≤ t →
      SigmaNineTailBoxesLocal.divisorSum r f * geometric q t =
        3 * (SigmaNineTailBoxesLocal.value r f * q^t) + 5 → q ≤ c) :
    ProfileBound (List.ofFn r) c := by
  intro p e hmono _hp he hprefix heq
  have hr : (fun i : Fin 8 => p i.castSucc) = r := List.ofFn_injective hprefix
  have hq : 5 < p 8 := by
    have h := congrFun hr (7 : Fin 8)
    have h7 : (7 : Fin 8).castSucc = (7 : Fin 9) := by decide
    change p ((7 : Fin 8).castSucc) = r 7 at h
    rw [h7] at h
    exact (h.symm ▸ h5).trans (hmono (by decide : (7 : Fin 9) < 8))
  let fe : Fin 8 → ℕ := fun i => e i.castSucc
  have hlast : Fin.last 8 = (8 : Fin 9) := by decide
  have heq' : SigmaNineTailBoxesLocal.divisorSum r fe * geometric (p 8) (e 8) =
      3 * (SigmaNineTailBoxesLocal.value r fe * p 8 ^ e 8) + 5 := by
    have h := heq
    simp_rw [← geometric_eq_sum] at h
    rw [Fin.prod_univ_castSucc (fun i : Fin 9 => geometric (p i) (e i)),
      Fin.prod_univ_castSucc (fun i : Fin 9 => p i ^ e i), hlast] at h
    rw [← hr]
    exact h
  exact bound (fun i => he i.castSucc) hq (he 8) heq'

theorem solve : OMA.R_OeisA76495_conjecture_R1_H1_R1_H4_R1_H2_R1.H2 := by
  apply solve_of_caps
  · have h := lift_bound SigmaNineTailBoxesLocal.p23 (c := 552) (by decide)
        (@SigmaNineTailBoxesLocal.cutoff23)
    rw [show List.ofFn SigmaNineTailBoxesLocal.p23 = ps23 by decide] at h
    exact h
  · have h := lift_bound SigmaNineTailBoxesLocal.p29 (c := 657) (by decide)
        (@SigmaNineTailBoxesLocal.cutoff29)
    rw [show List.ofFn SigmaNineTailBoxesLocal.p29 = ps29 by decide] at h
    exact h
  · have h := lift_bound SigmaNineTailBoxesLocal.p31 (c := 184) (by decide)
        (@SigmaNineTailBoxesLocal.cutoff31)
    rw [show List.ofFn SigmaNineTailBoxesLocal.p31 = ps31 by decide] at h
    exact h
  · have h := lift_bound SigmaNineTailBoxesLocal.p37 (c := 845) (by decide)
        (@SigmaNineTailBoxesLocal.cutoff37)
    rw [show List.ofFn SigmaNineTailBoxesLocal.p37 = ps37 by decide] at h
    exact h

end SigmaNineTailClosure

theorem OMA.solution : OMA.R_OeisA76495_conjecture_R1_H1_R1_H4_R1_H2_R1.H2 :=
  SigmaNineTailClosure.solve
