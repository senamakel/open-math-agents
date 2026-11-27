import OMAReductions.R_OeisA76495_conjecture_R1_H1_R1

/-! Kernel certificate for the five-prime odd-square branch of OEIS A076495.
The prime support omits 5. Increasing supports and even exponents are verified
by a finite replay of abundance, congruence and exact arithmetic tests. -/

/-! Cross-multiplied bounds for an exact prime and exponent search for
the divisor-sum equation sigma(n) = 2*n+5. -/

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

theorem geometric_upper (p e : ℕ) (hp : 1 ≤ p) :
    geometric p e * (p-1) ≤ p * p^e := by
  have h : geometric p e*(p-1)+1 = p*p^e := by
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
  omega

/-- Below ratio three, an odd number with odd divisor sum and remainder five
satisfies the exact quotient-two equation, provided its divisor sum exceeds five. -/
theorem quotient_two {n s : ℕ} (hn : Odd n) (hs : Odd s)
    (hmod : s % n = 5) (hlarge : 5 < s) (hupper : s < 3*n) :
    s = 2*n+5 := by
  let k := s / n
  have hd := Nat.mod_add_div s n
  rw [hmod] at hd
  change 5+n*k = s at hd
  have hn2 := Nat.odd_iff.mp hn
  have hs2 := Nat.odd_iff.mp hs
  have hm := congrArg (fun a : ℕ => a % 2) hd
  rw [Nat.add_mod, Nat.mul_mod, hn2, hs2] at hm
  have he : k % 2 = 0 := by
    change (1 + (1 * (k % 2)) % 2) % 2 = 1 at hm
    simp only [one_mul, Nat.mod_mod] at hm
    omega
  have hk0 : k ≠ 0 := by
    intro hzero
    simp [hzero] at hd
    omega
  have hk3 : k < 3 := by
    by_contra! hk
    have hmul := Nat.mul_le_mul_left n hk
    nlinarith only [hd, hmul, hupper]
  have hparity : ∀ j : ℕ, j % 2 = 0 → j ≠ 0 → j < 3 → j = 2 := by
    intro j hj h0 hj3
    omega
  have hk2 : k = 2 := hparity k he hk0 hk3
  rw [hk2] at hd
  omega

/-- A prefix which already overshoots the target remains excluded after
increasing its exponents and multiplying by a suffix. -/
theorem prefix_overshoot {n₀ s₀ n s m t : ℕ}
    (hn : 0 < n) (hm : 0 < m) (hN : n₀ ≤ n) (hprefix : s₀*n ≤ s*n₀)
    (hsmall : 2*n₀+5 < s₀) (hsuffix : m ≤ t) :
    2*(n*m)+5 < s*t := by
  have hn5 := Nat.mul_le_mul_left 5 hN
  have hstrict := Nat.mul_lt_mul_of_pos_right hsmall hn
  have hactual : 2*n+5 < s := by
    by_contra! hno
    have hupper := Nat.mul_le_mul_right n₀ hno
    nlinarith only [hprefix,hstrict,hn5,hupper]
  have hst := Nat.mul_le_mul_left s hsuffix
  have hmult := Nat.mul_lt_mul_of_pos_right hactual hm
  have hm5 := Nat.mul_le_mul_left 5 (show 1 ≤ m by omega)
  nlinarith only [hst,hmult,hm5]

/-- An integer prefix excess of one is enough when the suffix exceeds five. -/
theorem fixed_prefix_overshoot {n s m t : ℕ}
    (hprefix : 2*n < s) (hm : 5 < m) (hsuffix : m ≤ t) :
    2*(n*m)+5 < s*t := by
  have hnext : 2*n+1 ≤ s := by omega
  have hmul := Nat.mul_le_mul_right m hnext
  have hs := Nat.mul_le_mul_left s hsuffix
  nlinarith only [hm, hmul, hs]

/-- A geometric ratio at base at least q is at most q / (q-1),
in integer cross-multiplied form. -/
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

theorem geometric_even_odd (p k : ℕ) (hp : Odd p) :
    Odd (geometric p (2*k)) := by
  induction k with
  | zero => exact ⟨0, by simp [geometric]⟩
  | succ k ih =>
    obtain ⟨a, ha⟩ := hp
    obtain ⟨b, hb⟩ := ih
    refine ⟨p*(2*a*b+a+b+1), ?_⟩
    rw [show 2*(k+1) = 2*k+1+1 by omega, geometric, geometric, hb, ha]
    ring

theorem last_prime_dvd_prefix_excess {p n s e : ℕ} (he : 0 < e)
    (h : s*geometric p e = 2*(n*p^e)+5) : s % p = 5 % p := by
  obtain ⟨e, rfl⟩ := Nat.exists_eq_succ_of_ne_zero he.ne'
  have hpow : p ∣ p^(e+1) := by
    rw [pow_succ]
    exact dvd_mul_left _ _
  have hd := congrArg (fun x : ℕ => x % p) h
  rw [geometric] at hd
  have hleft : s*(1+p*geometric p e) = s+(s*geometric p e)*p := by ring
  rw [hleft, Nat.add_mul_mod_self_right] at hd
  obtain ⟨q, hq⟩ := hpow
  rw [hq, show 2*(n*(p*q))+5 = 5+(2*n*q)*p by ring,
    Nat.add_mul_mod_self_right] at hd
  exact hd

end SigmaAbundancyBounds

namespace SigmaFiveMixedCertificate

open SigmaAbundancyBounds

abbrev Factor := ℕ × ℕ
abbrev Slot := ℕ × Option ℕ

def value (xs : List Factor) : ℕ := (xs.map fun x => x.1 ^ x.2).prod

def divisorSum (xs : List Factor) : ℕ := (xs.map fun x => geometric x.1 x.2).prod

def capNum (ps : List Slot) : ℕ :=
  (ps.map fun x => x.2.elim x.1 (geometric x.1)).prod

def capDen (ps : List Slot) : ℕ :=
  (ps.map fun x => x.2.elim (x.1-1) (x.1 ^ ·)).prod

def minimum (E : ℕ) (ps : List Slot) : List Factor :=
  ps.map fun x => (x.1, x.2.getD E)

def Matches : List Slot → List Factor → Prop :=
  List.Forall₂ (fun (p : Slot) (x : Factor) => p.1 = x.1 ∧
    ∀ k, p.2 = some k → x.2 = k)

def Valid (xs : List Factor) : Prop :=
  ∀ x ∈ xs, x.1.Prime ∧ Odd x.1 ∧ x.1 ≠ 5 ∧ 2 ≤ x.2 ∧ Even x.2

theorem valid_append {xs ys : List Factor} (h : Valid (xs ++ ys)) :
    Valid xs ∧ Valid ys :=
  ⟨fun x hx => h x (List.mem_append_left ys hx),
    fun x hx => h x (List.mem_append_right xs hx)⟩

theorem value_pos {xs : List Factor} (hx : Valid xs) : 0 < value xs := by
  induction xs with
  | nil => decide
  | cons x xs ih =>
    change 0 < x.1^x.2 * value xs
    exact Nat.mul_pos (pow_pos (hx x (by simp)).1.pos _)
      (ih (fun y hy => hx y (by simp [hy])))

theorem value_le_divisorSum (xs : List Factor) : value xs ≤ divisorSum xs := by
  induction xs with
  | nil => decide
  | cons x xs ih =>
    change x.1^x.2 * value xs ≤ geometric x.1 x.2 * divisorSum xs
    apply Nat.mul_le_mul _ ih
    rw [geometric_eq_sum]
    exact Finset.single_le_sum (fun _ _ => Nat.zero_le _)
      (Finset.mem_range.mpr (Nat.lt_succ_self _))

theorem prefix_upper {ps : List Slot} {xs : List Factor} (h : Matches ps xs)
    (hv : Valid xs) : divisorSum xs * capDen ps ≤ value xs * capNum ps := by
  induction h with
  | nil => decide
  | @cons p x ps xs hx htail ih =>
    have ht := ih (fun y hy => hv y (by simp [hy]))
    have hp := (hv x (by simp)).1
    have hslot : geometric x.1 x.2 * p.2.elim (p.1-1) (p.1 ^ ·) ≤
        x.1^x.2 * p.2.elim p.1 (geometric p.1) := by
      rcases p with ⟨q,o⟩
      cases hopt : o with
      | none =>
        rw [show q = x.1 from hx.1]
        simp only [Option.elim_none]
        simpa only [mul_comm] using geometric_upper x.1 x.2 hp.one_le
      | some e =>
        have he : x.2 = e := hx.2 _ hopt
        simp only [Option.elim_some, show q = x.1 from hx.1, he, mul_comm, le_refl]
    change (geometric x.1 x.2 * divisorSum xs) *
        (p.2.elim (p.1-1) (p.1 ^ ·) * capDen ps) ≤
      (x.1^x.2 * value xs)*(p.2.elim p.1 (geometric p.1)*capNum ps)
    calc
      _ = (geometric x.1 x.2 * p.2.elim (p.1-1) (p.1 ^ ·)) *
            (divisorSum xs * capDen ps) := by ring
      _ ≤ (x.1^x.2 * p.2.elim p.1 (geometric p.1)) *
            (value xs * capNum ps) := Nat.mul_le_mul hslot ht
      _ = _ := by ring

theorem value_append (xs ys : List Factor) : value (xs ++ ys) = value xs * value ys := by
  simp [value, List.prod_append]

theorem divisorSum_append (xs ys : List Factor) :
    divisorSum (xs ++ ys) = divisorSum xs * divisorSum ys := by
  simp [divisorSum, List.prod_append]

def Above (E : ℕ) : List Slot → List Factor → Prop :=
  List.Forall₂ (fun (p : Slot) (x : Factor) => p.1 = x.1 ∧ p.2.getD E ≤ x.2)

theorem prefix_lower {E : ℕ} {ps : List Slot} {xs : List Factor}
    (h : Above E ps xs) (hv : Valid xs) :
    value (minimum E ps) ≤ value xs ∧
      divisorSum (minimum E ps) * value xs ≤ divisorSum xs * value (minimum E ps) := by
  induction h with
  | nil => exact ⟨le_rfl, le_rfl⟩
  | @cons p x ps xs hx htail ih =>
    have ht := ih (fun y hy => hv y (by simp [hy]))
    have hp := (hv x (by simp)).1
    have hpow := Nat.pow_le_pow_right hp.one_le hx.2
    have hgeo := geometric_scaled_mono x.1 hx.2
    have hbase : p.1 = x.1 := hx.1
    constructor
    · change p.1 ^ (p.2.getD E) * value (minimum E ps) ≤ x.1 ^ x.2 * value xs
      rw [hbase]
      exact Nat.mul_le_mul hpow ht.1
    · change (geometric p.1 (p.2.getD E) * divisorSum (minimum E ps)) *
          (x.1 ^ x.2 * value xs) ≤
        (geometric x.1 x.2 * divisorSum xs) * (p.1 ^ (p.2.getD E) * value (minimum E ps))
      rw [hbase]
      calc
        _ = (geometric x.1 (p.2.getD E) * x.1 ^ x.2) *
              (divisorSum (minimum E ps) * value xs) := by ring
        _ ≤ (geometric x.1 x.2 * x.1 ^ (p.2.getD E)) *
              (divisorSum xs * value (minimum E ps)) := Nat.mul_le_mul hgeo ht.2
        _ = _ := by ring

theorem suffix_bound_list (xs : List Factor) {q : ℕ} (hq : 2 ≤ q)
    (hl : ∀ x ∈ xs, q ≤ x.1) :
    divisorSum xs * (q-1)^xs.length ≤ q^xs.length * value xs := by
  induction xs with
  | nil => simp [divisorSum, value]
  | cons x xs ih =>
    have ht := ih (fun y hy => hl y (by simp [hy]))
    have hh := geometric_lower_base_bound hq (hl x (by simp))
      (e := x.2)
    change (geometric x.1 x.2 * divisorSum xs)*(q-1)^(xs.length+1) ≤
      q^(xs.length+1)*(x.1^x.2 * value xs)
    rw [pow_succ, pow_succ]
    calc
      _ = (geometric x.1 x.2 * (q-1)) * (divisorSum xs * (q-1)^xs.length) := by ring
      _ ≤ (q*x.1^x.2) * (q^xs.length * value xs) := Nat.mul_le_mul hh ht
      _ = _ := by ring

theorem suffix_value_gt_five {x : Factor} {xs : List Factor} (hv : Valid (x::xs)) :
    5 < value (x::xs) := by
  obtain ⟨hp, ho, _, he, _⟩ := hv x (by simp)
  have hp3 : 3 ≤ x.1 := by
    have h2 := hp.two_le
    obtain ⟨k,hk⟩ := ho
    omega
  have ht := value_pos (fun y hy => hv y (by simp [hy]) : Valid xs)
  change 5 < x.1^x.2 * value xs
  calc
    5 < (3 : ℕ)^2 := by decide
    _ ≤ x.1^2 := Nat.pow_le_pow_left hp3 2
    _ ≤ x.1^x.2 := Nat.pow_le_pow_right hp.one_le he
    _ = x.1^x.2 * 1 := (mul_one _).symm
    _ ≤ x.1^x.2 * value xs := Nat.mul_le_mul_left _ (show 1 ≤ value xs from ht)

theorem prefix_excludes_when_above {E : ℕ} {ps : List Slot} {xs : List Factor}
    (ha : Above E ps xs) (hv : Valid xs)
    (hsmall : 2*value (minimum E ps) < divisorSum (minimum E ps)) :
    2*value xs < divisorSum xs := by
  have hpos := value_pos hv
  have hlow := (prefix_lower ha hv).2
  have hmul := Nat.mul_lt_mul_of_pos_right hsmall hpos
  by_contra! hno
  have hmul' := Nat.mul_le_mul_right (value (minimum E ps)) hno
  nlinarith only [hmul, hmul', hlow]

theorem cutoff_excludes_suffix {ps : List Slot} {xs ys : List Factor} {q : ℕ}
    (hm : Matches ps xs) (hvalid : Valid (xs ++ ys)) (hq : 2 ≤ q)
    (hl : ∀ y ∈ ys, q ≤ y.1)
    (hc : capNum ps*q^ys.length ≤ 2*(capDen ps*(q-1)^ys.length)) :
    divisorSum (xs ++ ys) ≠ 2*value (xs ++ ys)+5 := by
  obtain ⟨hx,hy⟩ := valid_append hvalid
  have hpre := prefix_upper hm hx
  have htail := suffix_bound_list ys hq hl
  intro heq
  rw [divisorSum_append, value_append] at heq
  let C := capDen ps*(q-1)^ys.length
  have hpos (p : Slot) (x : Factor)
      (h : p.1 = x.1) (hp : x.1.Prime) : 0 < p.2.elim (p.1-1) (p.1 ^ ·) := by
    rw [h]
    cases p.2 with
    | none => simp only [Option.elim_none]; have hh := hp.two_le; omega
    | some e => exact pow_pos hp.pos _
  have hD {ps : List Slot} {xs : List Factor} (hh : Matches ps xs)
      (hv : Valid xs) : 0 < capDen ps := by
    induction hh with
    | nil => decide
    | @cons p x ps xs hr ht ih =>
      change 0 < p.2.elim (p.1-1) (p.1 ^ ·)*capDen ps
      exact Nat.mul_pos (hpos p x hr.1 (hv x (by simp)).1)
        (ih (fun y hy => hv y (by simp [hy])))
  have hC : 0 < C := Nat.mul_pos (hD hm hx) (pow_pos (by omega) _)
  have hbound : (divisorSum xs*divisorSum ys)*C ≤
      (value xs*value ys)*(capNum ps*q^ys.length) := by
    calc
      _ = (divisorSum xs*capDen ps)*(divisorSum ys*(q-1)^ys.length) := by dsimp [C]; ring
      _ ≤ (value xs*capNum ps)*(q^ys.length*value ys) := Nat.mul_le_mul hpre htail
      _ = _ := by ring
  have hc' := Nat.mul_le_mul_left (value xs*value ys) hc
  rw [heq] at hbound
  change (value xs*value ys)*(capNum ps*q^ys.length) ≤ (value xs*value ys)*(2*C) at hc'
  nlinarith only [hbound, hc', hC]

def smallEven (E : ℕ) : List ℕ :=
  (List.range E).filter fun e => decide (2 ≤ e ∧ Even e)

def exponentVariants (E : ℕ) : List Slot → List (List Slot)
  | [] => []
  | (p, o)::ps =>
    let continued := (exponentVariants E ps).map ((p,o)::·)
    match o with
    | some _ => continued
    | none => (smallEven E).map (fun e => (p,some e)::ps) ++ continued

theorem exponent_coverage {E : ℕ} {ps : List Slot} {xs : List Factor}
    (hm : Matches ps xs) (hv : Valid xs) :
    Above E ps xs ∨ ∃ ps' ∈ exponentVariants E ps, Matches ps' xs := by
  induction hm with
  | nil => exact Or.inl List.Forall₂.nil
  | @cons slot x ps xs hx htail ih =>
    obtain ⟨p, o⟩ := slot
    have htv : Valid xs := fun y hy => hv y (by simp [hy])
    rcases ih htv with ha | ⟨qs, hqs, hmatch⟩
    · cases o with
      | some e =>
        have he : x.2 = e := hx.2 _ rfl
        exact Or.inl (List.Forall₂.cons ⟨hx.1, he.symm.le⟩ ha)
      | none =>
        by_cases hE : E ≤ x.2
        · exact Or.inl (List.Forall₂.cons ⟨hx.1,hE⟩ ha)
        · have hm' : x.2 ∈ smallEven E := by
            simp only [smallEven, List.mem_filter, List.mem_range, decide_eq_true_eq]
            exact ⟨Nat.lt_of_not_ge hE, (hv x (by simp)).2.2.2⟩
          refine Or.inr ⟨(p,some x.2)::ps, ?_, ?_⟩
          · exact List.mem_append_left _
              (List.mem_map.mpr ⟨x.2,hm',rfl⟩)
          · exact List.Forall₂.cons ⟨hx.1, fun k hk => (Option.some.inj hk)⟩ htail
    · refine Or.inr ⟨(p,o)::qs, ?_, List.Forall₂.cons hx hmatch⟩
      cases o with
      | some e => exact List.mem_map.mpr ⟨qs,hqs,rfl⟩
      | none => exact List.mem_append_right _ (List.mem_map.mpr ⟨qs,hqs,rfl⟩)

def Excludes (ps : List Slot) : Prop :=
  ∀ xs ys : List Factor, Matches ps xs → (xs ++ ys).length = 5 →
    Valid (xs ++ ys) → (xs ++ ys).Pairwise (fun x y => x.1 < y.1) →
    divisorSum (xs ++ ys) ≠ 2*value (xs ++ ys)+5

theorem exclude_with_exponent_variants {ps : List Slot} {E : ℕ}
    (hsmall : 2*value (minimum E ps)+(if ps.length = 5 then 5 else 0) <
      divisorSum (minimum E ps))
    (hnext : ∀ ps' ∈ exponentVariants E ps, Excludes ps') : Excludes ps := by
  intro xs ys hm hcard hv hsort heq
  obtain ⟨hx,hy⟩ := valid_append hv
  rcases exponent_coverage hm hx with ha | ⟨ps', hmem, hmatch⟩
  · have hlen := hm.length_eq
    cases ys with
    | nil =>
      have hp5 : ps.length = 5 := by simpa [hlen] using hcard
      simp only [hp5, if_true] at hsmall
      have hlower := prefix_lower ha hx
      have hh := prefix_overshoot (m := 1) (t := 1) (value_pos hx) (by decide)
        hlower.1 hlower.2 hsmall (by decide)
      rw [List.append_nil] at heq
      simp only [mul_one, heq, lt_self_iff_false] at hh
    | cons y ys =>
      have hp5 : ps.length ≠ 5 := by
        simp only [List.length_append, List.length_cons] at hcard
        omega
      simp only [hp5, if_false, add_zero] at hsmall
      have hpre := prefix_excludes_when_above ha hx hsmall
      have htail := suffix_value_gt_five hy
      have hh := fixed_prefix_overshoot hpre htail (value_le_divisorSum (y::ys))
      rw [value_append, divisorSum_append] at heq
      exact (ne_of_lt hh) heq.symm
  · exact hnext ps' hmem xs ys hmatch hcard hv hsort heq

theorem slots_covered {ps : List Slot} {xs : List Factor} (hm : Matches ps xs) :
    ∀ p ∈ ps, ∃ x ∈ xs, p.1 = x.1 := by
  induction hm with
  | nil => simp
  | @cons a b ps xs hab htail ih =>
    intro p hp
    rcases List.mem_cons.mp hp with rfl | hmem
    · exact ⟨b, List.mem_cons_self, hab.1⟩
    · obtain ⟨x,hx,hpx⟩ := ih p hmem
      exact ⟨x,List.mem_cons_of_mem _ hx,hpx⟩

def PrimeTableComplete (table : List ℕ) (cap : ℕ) : Prop :=
  ∀ q, q.Prime → Odd q → q ≠ 5 → q < cap → q ∈ table

def fullyFixed (ps : List Slot) : Bool := ps.all (fun p => p.2.isSome)

theorem matching_fixed {ps : List Slot} {xs : List Factor}
    (hm : Matches ps xs) (hf : fullyFixed ps = true) : minimum 0 ps = xs := by
  induction hm with
  | nil => rfl
  | @cons slot x ps xs hx htail ih =>
    simp only [fullyFixed, List.all_cons, Bool.and_eq_true] at hf
    have hh := hf
    rcases slot with ⟨q,o⟩
    cases h : o with
    | none => simpa [h] using hh.1
    | some k =>
      have he : x.2 = k := hx.2 _ h
      have hpair : (q,k) = x := Prod.ext hx.1 he.symm
      change (q,k)::minimum 0 ps = x::xs
      rw [hpair, ih hh.2]

def congruentOnLastPrime (ps : List Slot) (q : ℕ) : Bool :=
  if ps.length = 4 ∧ fullyFixed ps = true then decide (divisorSum (minimum 0 ps) % q = 5 % q)
  else true

theorem mem_takeWhile_lt {table : List ℕ} {q q0 : ℕ}
    (hs : table.Pairwise (· < ·)) (hm : q ∈ table) (hq : q < q0) :
    q ∈ table.takeWhile (fun p => decide (p < q0)) := by
  induction table with
  | nil => simp at hm
  | cons p ps ih =>
    obtain ⟨hhead, hrest⟩ := List.pairwise_cons.mp hs
    rcases List.mem_cons.mp hm with rfl | ht
    · simp [List.takeWhile_cons, hq]
    · have hp : p < q0 := (hhead _ ht).trans hq
      simp only [List.takeWhile_cons, hp, decide_true, Bool.true_eq, if_true]
      exact List.mem_cons_of_mem _ (ih hrest ht)

def primeCandidates (table : List ℕ) (ps : List Slot) (q0 : ℕ) : List ℕ :=
  (table.takeWhile (fun q => decide (q < q0))).filter
    (fun q => ps.all (fun p => decide (p.1 < q)) && congruentOnLastPrime ps q)

theorem exclude_with_prime_variants {table : List ℕ} {ps : List Slot} {q0 cap : ℕ}
    (hcomp : PrimeTableComplete table cap) (hordered : table.Pairwise (· < ·)) (hcap : q0 ≤ cap) (hq0 : 2 ≤ q0)
    (hshort : ps.length < 5)
    (hcut : capNum ps*q0^(5-ps.length) ≤ 2*(capDen ps*(q0-1)^(5-ps.length)))
    (hnext : ∀ q ∈ primeCandidates table ps q0, Excludes (ps ++ [(q,none)])) :
    Excludes ps := by
  intro xs ys hm hcard hv hsort heq
  have hlen := hm.length_eq
  cases ys with
  | nil => simp at hcard; omega
  | cons y ys =>
    have hp := hv y (by simp)
    by_cases hq : q0 ≤ y.1
    · have htail : ∀ z ∈ y::ys, q0 ≤ z.1 := by
        intro z hz
        rcases List.mem_cons.mp hz with rfl | hh
        · exact hq
        · have hs := (List.pairwise_append.mp hsort).2.1
          exact hq.trans (((List.pairwise_cons.mp hs).1 _ hh).le)
      have hr : (y::ys).length = 5-ps.length := by
        simp only [List.length_append] at hcard
        omega
      exact cutoff_excludes_suffix hm hv hq0 htail (by simpa only [hr] using hcut) heq
    · have hmem : y.1 ∈ primeCandidates table ps q0 := by
        simp only [primeCandidates, List.mem_filter, Bool.and_eq_true, decide_eq_true_eq,
          List.all_eq_true]
        have hqlt := Nat.lt_of_not_ge hq
        refine ⟨mem_takeWhile_lt hordered
          (hcomp _ hp.1 hp.2.1 hp.2.2.1 (lt_of_lt_of_le hqlt hcap)) hqlt, ?_, ?_⟩
        · intro p hpm
          obtain ⟨x,hxm,hpx⟩ := slots_covered hm p hpm
          rw [hpx]
          exact (List.pairwise_append.mp hsort).2.2 _ hxm _ (by simp)
        · unfold congruentOnLastPrime
          split
          · rename_i hfixed
            have hym : ys.length = 0 := by
              simp only [List.length_append, List.length_cons] at hcard
              have h4 := hfixed.1
              omega
            have hy0 := List.length_eq_zero_iff.mp hym
            subst ys
            have heq' : divisorSum xs * geometric y.1 y.2 =
                2*(value xs * y.1^y.2)+5 := by
              rw [divisorSum_append, value_append] at heq
              simpa [divisorSum, value] using heq
            simpa only [decide_eq_true_eq, matching_fixed hm hfixed.2] using
              last_prime_dvd_prefix_excess (by have hh := hp.2.2.2.1; omega) heq'
          · rfl
      have hsingle : Matches [(y.1,none)] [y] :=
        List.Forall₂.cons ⟨rfl, fun _ hk => by cases hk⟩ List.Forall₂.nil
      have hm' : Matches (ps ++ [(y.1,none)]) (xs ++ [y]) :=
        List.rel_append hm hsingle
      have happ : (xs ++ [y]) ++ ys = xs ++ y::ys := by simp
      exact hnext y.1 hmem (xs ++ [y]) ys hm'
        (by simpa only [happ] using hcard) (by simpa only [happ] using hv)
        (by simpa only [happ] using hsort) (by simpa only [happ] using heq)

def excessThreshold (E : ℕ) (ps : List Slot) : Prop :=
  2*value (minimum E ps)+(if ps.length = 5 then 5 else 0) <
    divisorSum (minimum E ps)

instance (E : ℕ) (ps : List Slot) : Decidable (excessThreshold E ps) :=
  inferInstanceAs (Decidable (_ < _))

theorem exponentVariants_two (ps : List Slot) : exponentVariants 2 ps = [] := by
  have hsmall : smallEven 2 = [] := by decide
  induction ps with
  | nil => rfl
  | cons p ps ih =>
    rcases p with ⟨p,o⟩
    cases o <;> simp [exponentVariants, hsmall, ih]

theorem full_has_empty_tail {ps : List Slot} {xs ys : List Factor}
    (h5 : ps.length = 5) (hm : Matches ps xs) (hcard : (xs ++ ys).length = 5) :
    ys = [] := by
  have hl := hm.length_eq
  apply List.length_eq_zero_iff.mp
  simp only [List.length_append] at hcard
  omega

theorem exclude_full_cap {ps : List Slot} (h5 : ps.length = 5)
    (hc : capNum ps ≤ 2*capDen ps) : Excludes ps := by
  intro xs ys hm hcard hv _
  have hnil := full_has_empty_tail h5 hm hcard
  subst ys
  exact cutoff_excludes_suffix hm hv (q := 2) (by decide)
    (by simp) (by simpa using hc)

theorem exclude_full_fixed {ps : List Slot} (h5 : ps.length = 5)
    (hfixed : fullyFixed ps = true)
    (hc : divisorSum (minimum 0 ps) ≠ 2*value (minimum 0 ps)+5) : Excludes ps := by
  intro xs ys hm hcard _ _
  have hnil := full_has_empty_tail h5 hm hcard
  subst ys
  simpa only [matching_fixed hm hfixed, List.append_nil] using hc

def arithmeticTerminal (ps : List Slot) : Bool :=
  decide (excessThreshold 2 ps) ||
  (decide (ps.length = 5) &&
    (decide (capNum ps ≤ 2*capDen ps) ||
      (fullyFixed ps && decide (divisorSum (minimum 0 ps) ≠ 2*value (minimum 0 ps)+5))))

theorem arithmeticTerminal_sound {ps : List Slot}
    (h : arithmeticTerminal ps = true) : Excludes ps := by
  simp only [arithmeticTerminal, Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq] at h
  rcases h with h | ⟨h5, hcap | ⟨hfixed,hne⟩⟩
  · exact exclude_with_exponent_variants h (by simp [exponentVariants_two])
  · exact exclude_full_cap h5 hcap
  · exact exclude_full_fixed h5 hfixed hne

end SigmaFiveMixedCertificate

namespace SigmaMixedReplay

open SigmaFiveMixedCertificate

/-- `true, q₀` extends the support to primes below q₀. `false, E` fixes
at least one remaining exponent below E. -/
abbrev Plan := List Slot → Option (Bool × ℕ)

def cutoffCheck (cap : ℕ) (ps : List Slot) (q0 : ℕ) : Bool :=
  decide (q0 ≤ cap ∧ 2 ≤ q0 ∧ ps.length < 5 ∧
    capNum ps*q0^(5-ps.length) ≤ 2*(capDen ps*(q0-1)^(5-ps.length)))

end SigmaMixedReplay

namespace SigmaMixedDAG

open SigmaFiveMixedCertificate SigmaMixedReplay

def progress : List Slot → ℕ
  | [] => 0
  | (_p,o)::ps => progress ps + (if o.isSome then 2 else 1)

theorem progress_bound (ps : List Slot) : progress ps ≤ 2*ps.length := by
  induction ps with
  | nil => decide
  | cons slot ps ih =>
    rcases slot with ⟨p,o⟩
    cases o <;> simp only [progress, Option.isSome_none, Option.isSome_some,
      Bool.false_eq_true, if_false, if_true, List.length_cons] <;> omega

theorem progress_append_slot (ps : List Slot) (q : ℕ) :
    progress (ps ++ [(q,none)]) = progress ps+1 := by
  induction ps with
  | nil => rfl
  | cons slot ps ih =>
    rcases slot with ⟨p,o⟩
    simp only [List.cons_append, progress, ih]
    omega

theorem exponent_progress {E : ℕ} {ps ps' : List Slot}
    (hm : ps' ∈ exponentVariants E ps) :
    ps'.length = ps.length ∧ progress ps' = progress ps+1 := by
  induction ps generalizing ps' with
  | nil => simp [exponentVariants] at hm
  | cons slot ps ih =>
    rcases slot with ⟨p,o⟩
    cases o with
    | some e =>
      obtain ⟨qs,hq,rfl⟩ := List.mem_map.mp hm
      obtain ⟨hL,hP⟩ := ih hq
      simp [progress,hL,hP,Nat.add_right_comm]
    | none =>
      rcases List.mem_append.mp hm with hm | hm
      · obtain ⟨e,he,rfl⟩ := List.mem_map.mp hm
        simp [progress,Nat.add_assoc]
      · obtain ⟨qs,hq,rfl⟩ := List.mem_map.mp hm
        obtain ⟨hL,hP⟩ := ih hq
        simp [progress,hL,hP]

def known (prune : List Slot → Bool) (plan : Plan) (ps : List Slot) : Bool :=
  arithmeticTerminal ps || prune ps || (plan ps).isSome

def checkStep (table : List ℕ) (cap : ℕ) (prune : List Slot → Bool) (plan : Plan)
    (ps : List Slot) : Bool × ℕ → Bool
  | (false,E) => decide (excessThreshold E ps) &&
      (exponentVariants E ps).all (known prune plan)
  | (true,q0) => cutoffCheck cap ps q0 &&
      (primeCandidates table ps q0).all (fun q => known prune plan (ps ++ [(q,none)]))

theorem known_sound {table : List ℕ} {cap : ℕ} {prune : List Slot → Bool} {plan : Plan}
    (hcomplete : PrimeTableComplete table cap) (hordered : table.Pairwise (· < ·))
    (hprune : ∀ ps, prune ps = true → Excludes ps)
    (hsteps : ∀ ps step, plan ps = some step → checkStep table cap prune plan ps step = true)
    {ps : List Slot} (hsize : ps.length ≤ 5) (hp : known prune plan ps = true) :
    Excludes ps := by
  suffices
      ∀ fuel : ℕ, ∀ ps : List Slot, ps.length ≤ 5 → 10-progress ps < fuel →
        known prune plan ps = true → Excludes ps from
    this 11 ps hsize (by omega) hp
  intro fuel
  induction fuel with
  | zero => intro ps hsize hf; omega
  | succ fuel ih =>
    intro ps hsize hf hk
    have hbound := progress_bound ps
    simp only [known,Bool.or_eq_true] at hk
    rcases hk with (harith | hmod) | hplan
    · exact arithmeticTerminal_sound harith
    · exact hprune ps hmod
    · cases hstep : plan ps with
      | none => simp [hstep] at hplan
      | some step =>
        have hc := hsteps ps step hstep
        rcases step with ⟨dir,bound⟩
        cases dir
        · simp only [checkStep, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true] at hc
          apply exclude_with_exponent_variants hc.1
          intro child hm
          obtain ⟨hlen,hinc⟩ := exponent_progress hm
          have hcb := progress_bound child
          exact ih child (by omega) (by omega) (hc.2 child hm)
        · simp only [checkStep, cutoffCheck, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true] at hc
          refine exclude_with_prime_variants hcomplete hordered hc.1.1 hc.1.2.1 hc.1.2.2.1 hc.1.2.2.2 ?_
          intro q hm
          have hlen : (ps ++ [(q,none)]).length = ps.length+1 := by simp
          have hinc := progress_append_slot ps q
          exact ih _ (by omega) (by omega) (hc.2 q hm)


end SigmaMixedDAG

namespace SigmaMixedData
open SigmaFiveMixedCertificate SigmaMixedReplay SigmaMixedDAG
abbrev Row := ℕ × ℕ
def rows0 : List Row := [
  (0, 17),
  (1914940564306470175862949536, 8),
  (1914940564306470175856658083, 8),
  (1856912124964967976282359456, 8),
  (1856912124964967976276068003, 8),
  (1856912171081828160556244841, 20),
  (1856912171081828160564633445, 16),
  (1856912171081845752735998816, 16),
  (1856912171081814966425101152, 16),
  (1856912171081814966410421095, 16),
  (1856912189528581030352528224, 16),
  (1856912189528559040119972709, 16),
  (1856912124964976772383777632, 16),
  (1856912124964976772369097575, 16),
  (1856912124964985568462119781, 16),
  (1856912124964954782151222117, 16),
  (1856912171081814966410421984, 20),
  (1856912124964976772369098464, 16),
  (1856912124964954782136542949, 16),
  (1856912124964967977081374368, 8),
  (1856912124964954782948132512, 8),
  (1856912124964954782941841059, 8),
  (1856912171082096441521341731, 12),
  (1856912124965258247480018211, 12),
  (1856912124965236257257948451, 12),
  (1856912189529403464379008672, 16),
  (1856912124965829992721155744, 16),
  (1856912124965799206410258080, 16),
  (1856912124965799206395578023, 16)]
def rows1 : List Row := [
  (1856912171081836956649267429, 12),
  (1856912171081836956649268064, 16),
  (1856912124964976772375389029, 16),
  (1856912189528559040119973472, 16),
  (1856912124964985568462120544, 16),
  (1856912124964954782151222880, 16),
  (1856912124964954782136542823, 16),
  (1856912124964954782142834403, 20),
  (1856912124964967976812939168, 8),
  (1856912124964954782673406240, 12),
  (1856912124965236256716884256, 8),
  (1856912171082096441393415648, 12),
  (1856912171082096441387124195, 12),
  (1856912124965258247352092128, 12),
  (1856912124965258247345800675, 12),
  (1856912124965236257119536613, 12),
  (1856912124965236257123730915, 12),
  (1856912171082659390669457059, 16),
  (1856912124965812400545597088, 24),
  (1856912124965812400535111333, 24),
  (1856912124965821196628133539, 16),
  (1856912124965799206406063779, 16)]
def rows2 : List Row := [
  (1914940564306470175862949792, 8),
  (1856912124964967976282359712, 8),
  (1856912124964967976276068640, 8),
  (1856912124964954782142826784, 8),
  (1856912171081828160564633447, 16),
  (1856912189528589826445550432, 16),
  (1856912189528559040134652768, 16),
  (1856912124964985568476799840, 16),
  (1856912124964985568462119783, 16),
  (1856912124964954782151222119, 16),
  (1856912171081814966416713312, 20),
  (1856912124964976772375389792, 16),
  (1856912124964954782142834277, 16),
  (1856912124964985568462120672, 16),
  (1856912124964954782151223008, 16),
  (1856912124964954782136542951, 16),
  (1856912124964967976812938915, 8),
  (1856912124964967977081374624, 12),
  (1856912124964954782948132768, 12),
  (1856912124964954782941841696, 16),
  (1856912124965236256710593312, 12),
  (1856912171082118431753897248, 12),
  (1856912171082096441531827488, 12),
  (1856912171082096441521341733, 12),
  (1856912124965258247490503968, 12),
  (1856912124965236257257948453, 12)]
def rows3 : List Row := [
  (1856912124964954782136535840, 8),
  (1856912171081845752742290272, 16),
  (1856912171081814966416712551, 16),
  (1856912189528581030358819680, 16),
  (1856912189528559040126264165, 16),
  (1856912124964976772375389031, 16),
  (1856912124964985568468411237, 16),
  (1856912171081814966410421987, 20),
  (1856912124964976772375389920, 20),
  (1856912124964976772369098467, 16),
  (1856912124964954782142834405, 20),
  (1856912124964967977087665824, 8),
  (1856912124964967977081374371, 8),
  (1856912171082096441397609952, 12),
  (1856912171082096441387124197, 12),
  (1856912124965258247345800677, 12),
  (1856912124965236257123730917, 12),
  (1856912171082681380902012576, 16),
  (1856912171082659390669457061, 16),
  (1856912189529416658518541984, 24),
  (1856912189529403464379008675, 16),
  (1856912124965812400549791392, 24),
  (1856912124965821196638619296, 16),
  (1856912124965799206406063781, 16),
  (1856912124965799206410258083, 16)]
def rows4 : List Row := [
  (1856912171081836956642977376, 16),
  (1856912189528559040126264928, 16),
  (1856912124964976772369098341, 16),
  (1856912124964985568468412000, 16),
  (1856912124964954782142834279, 16),
  (1856912124964967976812939552, 12),
  (1856912171081814967215720352, 12),
  (1856912124964976773174396832, 12),
  (1856912124964954782952327072, 12),
  (1856912124964954782941841317, 12),
  (1856912124965236256710593568, 12),
  (1856912171082096441393415651, 12),
  (1856912124965258247352092131, 12),
  (201327008, 31)]
def rows5 : List Row := [
  (1856912124964967976282360096, 8),
  (1856912124964954782136536096, 8),
  (1856912171081836956657656672, 16),
  (1856912171081836956642976615, 16),
  (1856912189528581030352528229, 16),
  (1856912189528589826451841888, 16),
  (1856912124964976772383777637, 16),
  (1856912124964985568468411239, 16),
  (1856912171081836956642977504, 20),
  (1856912171081814966410421989, 20),
  (1856912124964976772369098469, 16),
  (1856912124964985568468412128, 20),
  (1856912124964985568462120675, 16),
  (1856912124964954782142834407, 20),
  (1856912124964954782151223011, 16),
  (1856912124964954782673406752, 12),
  (1856912124964967977087666080, 12),
  (1856912124964954782948133152, 16),
  (1856912124965236256716884768, 12),
  (1856912124965236256710593315, 12),
  (1856912124965236256710593696, 12),
  (1856912171082118431753897251, 12),
  (1856912171082096441531827491, 12),
  (1856912124965258247490503971, 12),
  (1856912171082690176995034784, 16),
  (1856912171082659390684137120, 16),
  (1856912171082659390669457063, 16),
  (1856912189529425454611564192, 16),
  (1856912189529403464389494432, 16),
  (1856912189529403464379008677, 16),
  (1856912124965812400535111337, 24),
  (1856912124965821196642813600, 16),
  (1856912124965821196628133543, 16),
  (1856912124965829992731641504, 16),
  (1856912124965829992721155749, 16),
  (1856912124965799206406063783, 16),
  (1856912124965799206410258085, 16)]
def rows6 : List Row := [
  (1856912124964967976276069152, 8),
  (1856912124964954782142827296, 8),
  (1856912124964954782136535843, 8),
  (1856912124964954782136536224, 8),
  (1856912171081845752735999584, 16),
  (1856912171081814966425101920, 16),
  (1856912171081814966410421863, 16),
  (1856912189528581030352528992, 16),
  (1856912189528559040119973477, 16),
  (1856912124964976772383778400, 16),
  (1856912124964976772369098343, 16),
  (1856912124964985568462120549, 16),
  (1856912124964954782151222885, 16),
  (1856912124964976772375389923, 20),
  (1856912171081814966947285280, 12),
  (1856912124964976772905961760, 12),
  (1856912124964954782683892000, 12),
  (1856912124964954782673406245, 12),
  (1856912171082096441393415653, 12),
  (1856912171082096441397609955, 12),
  (1856912124965258247352092133, 12),
  (1856912171082681380902012579, 16),
  (1856912124965812400545597093, 24),
  (1856912124965821196638619299, 16)]
def rows7 : List Row := [
  (1856912171081845752750678880, 16),
  (1856912171081845752735998823, 16),
  (1856912171081814966425101159, 16),
  (1856912189528581030367208288, 16),
  (1856912189528589826445550437, 16),
  (1856912189528559040134652773, 16),
  (1856912124964976772383777639, 16),
  (1856912124964985568476799845, 16),
  (1856912171081836956649268832, 20),
  (1856912124964976772375389797, 16),
  (1856912171081845752735999712, 20),
  (1856912171081814966425102048, 20),
  (1856912171081814966410421991, 20),
  (1856912124964976772383778528, 16),
  (1856912124964976772369098471, 16),
  (1856912124964985568462120677, 16),
  (1856912124964994364561434336, 20),
  (1856912124964954782142834409, 20),
  (1856912124964954782151223013, 16),
  (1856912171081828161355253664, 12),
  (1856912171081814967222011808, 12),
  (1856912124964967977091860384, 12),
  (1856912124964967977081374629, 12),
  (1856912124964976773180688288, 12),
  (1856912124964954782948132773, 12),
  (1856912171081814967215720736, 16),
  (1856912124964976773174397216, 16),
  (1856912124964954782952327456, 16),
  (1856912124964954782941841701, 16),
  (1856912171082096440984472352, 12),
  (1856912124965258246943148832, 12),
  (1856912124965236256721079072, 12),
  (1856912124965236256710593317, 12),
  (1856912124965236256716885024, 12),
  (1856912124965236256710593952, 16),
  (1856912171082118431764383008, 12),
  (1856912171082096441531827493, 12),
  (1856912189529434250704586400, 16),
  (1856912189529403464379008679, 16),
  (1856912226422904805937645216, 24),
  (1856912124965812400558180000, 24),
  (1856912124965829992735835808, 16),
  (1856912124965799206410258087, 16)]
def rows8 : List Row := [
  (1856912124964967976276069408, 8),
  (1856912124964954782142827552, 8),
  (1856912124964954782136536480, 8),
  (1856912171081836956649268071, 16),
  (1856912189528581030358819685, 16),
  (1856912189528589826445551200, 16),
  (1856912189528559040134653536, 16),
  (1856912124964985568476800608, 16),
  (1856912124964985568462120551, 16),
  (1856912124964954782151222887, 16),
  (1856912171081836956642977507, 20),
  (1856912124964976772375389925, 20),
  (1856912124964985568468412131, 20),
  (1856912124964954782673406755, 12),
  (1856912124965236256716884771, 12),
  (1856912124965236256716885152, 12),
  (1856912124965236256710593699, 12),
  (1856912171082096441397609957, 12),
  (1856912171082659390684137123, 16),
  (1856912189529416658529027744, 24),
  (1856912189529416658518541989, 24),
  (1856912189529425454611564195, 16),
  (1856912189529403464389494435, 16),
  (1856912124965812400549791397, 24),
  (1856912124965821196642813603, 16)]
def rows9 : List Row := [
  (1856912124964967976282360608, 8),
  (1856912124964967976276069155, 8),
  (1856912124964967976276069536, 8),
  (1856912124964954782142827680, 8),
  (1856912124964954782136536227, 8),
  (1856912124964954782136536608, 8),
  (1856912189528589826460230496, 16),
  (1856912124964985568476799847, 16),
  (1856912171081845752742291040, 20),
  (1856912171081814966416713319, 20),
  (1856912189528581030358820448, 16),
  (1856912189528559040126264933, 16),
  (1856912124964976772375389799, 16),
  (1856912124964985568468412005, 16),
  (1856912171081854548829021920, 20),
  (1856912171081814966410421993, 20),
  (1856912124964985568476800736, 16),
  (1856912124964985568462120679, 16),
  (1856912124964954782151223015, 16),
  (1856912171081828161086818592, 12),
  (1856912124964967976823425312, 12),
  (1856912124964967976812939557, 12),
  (1856912171081836957448275872, 12),
  (1856912171081814967226206112, 12),
  (1856912124964976773184882592, 12),
  (1856912124964976773174396837, 12),
  (1856912189528559040925272352, 16),
  (1856912124964985569267419424, 16),
  (1856912124964954782956521760, 16),
  (1856912124964954782941841703, 16),
  (1856912171082096440984472608, 12),
  (1856912124965258246943149088, 12),
  (1856912124965236256721079328, 12),
  (1856912124965236256710593573, 12)]
def rows10 : List Row := [
  (885444700701215162976, 8),
  (1856912171081845752742290279, 16),
  (1856912189528589826451841893, 16),
  (1856912171081836956642977509, 20),
  (1856912171081845752735999715, 20),
  (1856912171081814966425102051, 20),
  (1856912124964976772375389927, 20),
  (1856912124964976772383778531, 16),
  (1856912124964985568468412133, 20),
  (1856912124964994364561434339, 20),
  (1856912171081814966947285792, 16),
  (1856912124964976772905962272, 12),
  (1856912124964954782683892512, 12),
  (1856912124964954782673406757, 12),
  (1856912171081828161361545120, 12),
  (1856912124964967977087666085, 12),
  (1856912171081814967222012192, 16),
  (1856912124964976773180688672, 16),
  (1856912124964954782948133157, 16),
  (885444700701349380640, 8),
  (1856912171082096440990763808, 12),
  (1856912171082096440984472355, 12),
  (1856912124965258246949440288, 12),
  (1856912124965258246943148835, 12),
  (1856912124965236256716884773, 12),
  (1856912124965236256721079075, 12),
  (1856912171082096440984472736, 12),
  (1856912124965258246943149216, 12),
  (1856912124965236256721079456, 12),
  (1856912124965236256710593701, 12),
  (1856912124965236256716885408, 16),
  (1856912171082118431764383011, 12),
  (1856912171082681380916692640, 16),
  (1856912171082681380902012583, 16),
  (1856912171082690176995034789, 16),
  (1856912171082659390684137125, 16),
  (1856912189529425454622049952, 16),
  (1856912189529403464389494437, 16),
  (1856912124965812400545597097, 24),
  (1856912124965821196638619303, 16),
  (1856912124965829992731641509, 16)]
def rows11 : List Row := [
  (885444700701215163104, 8),
  (1856912124964967976282360864, 8),
  (1856912124964967976276069792, 8),
  (1856912124964954782142827936, 8),
  (1856912171081836956657657440, 16),
  (1856912171081836956642977383, 16),
  (1856912171081854548835313248, 20),
  (1856912189528581030352528997, 16),
  (1856912189528589826451842656, 16),
  (1856912124964976772383778405, 16),
  (1856912124964985568468412007, 16),
  (1856912171081836957179840800, 12),
  (1856912171081814966957771040, 12),
  (1856912171081814966947285285, 12),
  (1856912124964976772916447520, 12),
  (1856912124964976772905961765, 12),
  (1856912124965236256716885155, 12),
  (885445263651302801952, 41)]
def rows12 : List Row := [
  (1856912124964967976282360992, 8),
  (1856912124964967976276069539, 8),
  (1856912124964967976276069920, 8),
  (1856912124964954782142828064, 8),
  (1856912124964954782136536611, 8),
  (1856912171081836956657656679, 16),
  (1856912189528581030367208293, 16),
  (1856912171081836956657657568, 20),
  (1856912171081836956642977511, 20),
  (1856912171081845752735999717, 20),
  (1856912171081854548829021923, 20),
  (1856912171081814966425102053, 20),
  (1856912124964976772375389929, 20),
  (1856912124964976772383778533, 16),
  (1856912124964985568468412135, 20),
  (1856912124964985568476800739, 16),
  (1856912124964994364561434341, 20),
  (1856912171081828161365739424, 12),
  (1856912171081836957454567328, 12),
  (1856912124964976773180688293, 12),
  (1856912171081836957448276256, 16),
  (1856912171081814967226206496, 16),
  (1856912189528559040931563808, 16),
  (1856912124964976773184882976, 16),
  (1856912124964976773174397221, 16),
  (1856912124964985569273710880, 16),
  (1856912171082096440994958112, 12),
  (1856912171082096440984472357, 12),
  (1856912124965258246953634592, 12),
  (1856912124965236256721079077, 12),
  (1856912171082096440990764064, 12),
  (1856912124965258246949440544, 12),
  (1856912124965236256716885029, 12),
  (1856912171082096440984472992, 16),
  (1856912124965258246943149472, 16),
  (1856912124965236256721079712, 16),
  (1856912124965236256710593957, 16),
  (1856912171082690177009714848, 16),
  (1856912171082659390684137127, 16),
  (1856912189529416658518541993, 24),
  (1856912189529425454611564199, 16),
  (1856912189529434250715072160, 16),
  (1856912189529434250704586405, 16),
  (1856912189529403464389494439, 16),
  (1856912226422904805937645221, 24),
  (1856912124965812400549791401, 24),
  (1856912124965812400558180005, 24),
  (1856912124965821196642813607, 16),
  (1856912124965829992735835813, 16)]
def rows13 : List Row := [
  (913114816811779490400, 95),
  (885444700701221454432, 8),
  (1856912171081845752750679648, 16),
  (1856912171081845752735999591, 16),
  (1856912171081814966425101927, 16),
  (1856912189528581030367209056, 16),
  (1856912189528589826445551205, 16),
  (1856912189528559040134653541, 16),
  (1856912124964976772383778407, 16),
  (1856912124964985568476800613, 16),
  (885444700701215163360, 371),
  (1856912171081814966947285795, 16),
  (1856912124964976772905962275, 12),
  (1856912124964954782683892515, 12),
  (913114816811913708064, 69),
  (885444700701349380643, 8),
  (1856912171082096440990763811, 12),
  (1856912124965258246949440291, 12),
  (1856912171082096440990764192, 12),
  (1856912171082096440984472739, 12),
  (1856912124965258246949440672, 12),
  (1856912124965258246943149219, 12),
  (1856912124965236256716885157, 12),
  (1856912124965236256721079459, 12),
  (885444700701349381024, 111),
  (1856912171082681380916692643, 16),
  (1856912189529416658529027749, 24),
  (1856912189529425454622049955, 16),
  (885444700701752034016, 61)]
def rows14 : List Row := [
  (913114816811779490528, 67),
  (885444700701221454560, 8),
  (885444700701215163107, 8),
  (1856912124964967976282361248, 8),
  (1856912171081845752750678887, 16),
  (1856912189528589826460230501, 16),
  (1856912171081836956649268839, 20),
  (1856912189528581030358820453, 16),
  (1856912171081836956642977513, 20),
  (1856912171081845752750679776, 20),
  (1856912171081845752735999719, 20),
  (1856912171081854548829021925, 20),
  (1856912171081814966425102055, 20),
  (1856912124964976772383778535, 16),
  (1856912124964985568468412137, 20),
  (1856912124964985568476800741, 16),
  (1856912124964994364561434343, 20),
  (1856912171081828161097304352, 12),
  (1856912171081828161086818597, 12),
  (1856912171081836957458761632, 12),
  (1856912171081845753541298464, 16),
  (1856912171081814967230400800, 16),
  (1856912171081814967215720743, 16),
  (1856912189528581031157827872, 16),
  (1856912189528559040935758112, 16),
  (1856912189528559040925272357, 16),
  (1856912124964976773189077280, 16),
  (1856912124964976773174397223, 16),
  (1856912124964985569277905184, 16),
  (1856912124964985569267419429, 16),
  (1856912124964954782952327463, 16),
  (1856912124964954782956521765, 16),
  (1856912171082118431217028128, 12),
  (1856912171082096440994958368, 12),
  (1856912171082096440984472613, 12),
  (1856912124965258246953634848, 12),
  (1856912124965236256721079333, 12),
  (1856912189528840514694024608, 16),
  (1856912124965267043036171680, 16),
  (1856912124965236256725274016, 16),
  (1856912124965236256710593959, 16),
  (1856912189529416658541610656, 24),
  (1856912226422904805952325280, 24)]
def rows15 : List Row := [
  (1856912124964967976282361376, 8),
  (1856912124964967976276069923, 8),
  (1856912124964954782136537376, 8),
  (1856912189528589826460231264, 16),
  (1856912124964985568476800615, 16),
  (1856912171081836956657657571, 20),
  (1856912171081836957179841312, 16),
  (1856912171081814966947285797, 16),
  (1856912124964976772916448032, 12),
  (1856912124964976772905962277, 12),
  (1856912171081836957454567712, 16),
  (1856912124964976773180688677, 16),
  (1856912171082096440990763813, 12),
  (1856912171082096440994958115, 12),
  (1856912124965258246953634595, 12),
  (1856912171082096440994958496, 12),
  (1856912171082096440984472741, 12),
  (1856912124965258246953634976, 12),
  (1856912124965236256721079461, 12),
  (1856912171082096440990764448, 20),
  (1856912124965258246949440928, 16),
  (1856912124965236256716885413, 16),
  (885444700701349381280, 79)]
def rows16 : List Row := [
  (913114816811785781856, 91),
  (1856912171081845752742291047, 20),
  (1856912189528589826451842661, 16),
  (1856912171081845752735999721, 20),
  (1856912171081854548843701984, 20),
  (1856912171081854548829021927, 20),
  (1856912171081814966425102057, 20),
  (1856912124964985568476800743, 16),
  (1856912124964994364561434345, 20),
  (1856912171081836957190326560, 12),
  (1856912171081836957179840805, 12),
  (1856912189528589827250850080, 16),
  (1856912189528559040939952416, 16),
  (1856912124964985569282099488, 16),
  (1856912124964985569267419431, 16),
  (885444700701215163744, 139),
  (913114816811913708067, 67),
  (1856912171082096440990764195, 12),
  (1856912124965258246949440675, 12),
  (1856912226422904805937645225, 24),
  (1856912124965812400558180009, 24)]
def rows17 : List Row := [
  (913114816811785781984, 65),
  (885444700701221454563, 8),
  (913114816811779490531, 67),
  (1856912171081836956657657573, 20),
  (1856912171081845752750679779, 20),
  (1856912171081845753272863520, 16),
  (1856912171081814966961965856, 16),
  (1856912171081814966947285799, 16),
  (1856912171081836957458762016, 16),
  (1856912171081845753547589920, 16),
  (1856912189528581031164119328, 16),
  (1856912189528559040931563813, 16),
  (1856912124964985569273710885, 16),
  (885444700701215163872, 123),
  (1856912171082096440994958117, 12),
  (1856912171082118431223319584, 12),
  (1856912171082096440990764069, 12),
  (1856912171082118431217028512, 16),
  (1856912171082096440994958752, 16),
  (1856912171082096440984472997, 16),
  (1856912189528840514700316064, 16),
  (1856912124965258246953635232, 16),
  (1856912124965267043042463136, 16),
  (1856912124965236256716885415, 16),
  (1856912124965236256721079717, 16),
  (1856912171082681380916692647, 16),
  (1856912171082690177009714853, 16),
  (1856912189529416658529027753, 24),
  (1856912189529425454622049959, 16),
  (1856912189529434250715072165, 16)]
def rows18 : List Row := [
  (1856912124964967976276070688, 12),
  (1856912124964954782142828832, 12),
  (1856912124964954782136537379, 8),
  (1856912124964954782136537760, 12),
  (1856912171081836956657657447, 16),
  (1856912171081854548835313255, 20),
  (1856912189528581030367209061, 16),
  (1856912171081854548829021929, 20),
  (1856912171081836957179841315, 16),
  (1856912124964976772916448035, 12),
  (1856912171082096440990764197, 12),
  (1856912171082096440994958499, 12),
  (1856912124965258246953634979, 12)]
def rows19 : List Row := [
  (1856912171081836956657657575, 20),
  (1856912171081845752750679781, 20),
  (1856912171081854548843701987, 20),
  (1856912171081836957462956320, 16),
  (1856912171081836957448276263, 16),
  (1856912171081845753551784224, 16),
  (1856912171081814967226206503, 16),
  (1856912189528581031168313632, 16),
  (1856912189528581031157827877, 16),
  (1856912189528589827257141536, 16),
  (1856912124964976773184882983, 16),
  (1856912124964976773189077285, 16),
  (1856912171082118431227513888, 12),
  (1856912171082096440994958373, 12),
  (1856912171082127227310050720, 16),
  (1856912171082096440999153056, 16),
  (1856912171082096440984472999, 16),
  (1856912189528862504926580128, 16),
  (1856912189528840514704510368, 16),
  (1856912189528840514694024613, 16),
  (1856912124965258246957829536, 16),
  (1856912124965258246943149479, 16),
  (1856912124965267043046657440, 16),
  (1856912124965267043036171685, 16),
  (1856912124965236256721079719, 16),
  (1856912124965236256725274021, 16),
  (1856912189529416658541610661, 24),
  (1856912226422904805952325285, 24)]
def rows20 : List Row := [
  (913114816811785781987, 65),
  (1856912124964954782136538016, 12),
  (1856912171081845752750679655, 16),
  (1856912189528589826460231269, 16),
  (1856912171081836957179841317, 16),
  (1856912171081845753272863523, 16),
  (1856912171082096440994958501, 12),
  (1856912171082118431223319968, 20),
  (1856912171082096440990764453, 20)]
def rows21 : List Row := [
  (1856912124964967976282362144, 12),
  (1856912124964967976276070691, 12),
  (1856912124964967976276071072, 12),
  (1856912124964954782142829216, 12),
  (1856912124964954782136537763, 12),
  (1856912171081836956657657577, 20),
  (1856912171081845752750679783, 20),
  (1856912171081854548843701989, 20),
  (1856912171081845753555978528, 16),
  (1856912171081845753541298471, 16),
  (1856912189528581031172507936, 16),
  (1856912189528589827261335840, 16),
  (1856912189528589827250850085, 16),
  (1856912189528559040939952421, 16),
  (1856912124964985569277905191, 16),
  (1856912124964985569282099493, 16),
  (1953626190534406590418653856, 8),
  (1856912189528871301019602336, 16),
  (1856912189528840514708704672, 16),
  (1856912189528840514694024615, 16),
  (1856912124965267043050851744, 16),
  (1856912124965236256725274023, 16)]
def rows22 : List Row := [
  (1856912171081836957194521376, 16),
  (1856912171081836957179841319, 16),
  (1856912171081845753272863525, 16),
  (1856912171081814966961965861, 16),
  (1856912189528581031164119333, 16),
  (1856912171082118431227514272, 16),
  (1856912171082127227316342176, 20),
  (1856912171082096440990764455, 20),
  (1856912171082096440994958757, 16),
  (1856912189528862504932871584, 16),
  (1856912189528840514700316069, 16),
  (1856912124965258246949440935, 16),
  (1856912124965267043042463141, 16)]
def rows23 : List Row := [
  (1856912171081828160549949728, 12),
  (1856912124964967976286556448, 12),
  (1856912124964967976276070693, 12),
  (1953626190534125116119322912, 12),
  (1856912171081814966416707872, 12),
  (1856912124964976772375384352, 12),
  (1856912124964954782142828837, 12),
  (1856912171081814966410416800, 12),
  (1856912124964976772369093280, 12),
  (1856912124964954782147023520, 12),
  (1856912124964954782136537765, 12),
  (1856912124964967976276071328, 12),
  (1856912124964954782142829472, 12),
  (1856912171081845752750679785, 20),
  (1856912171081854548843701991, 20),
  (1856912189528589827265530144, 16),
  (1953626190534406590418654112, 8),
  (1856912189529416658541610665, 24),
  (1856912226422904805952325289, 24)]
def rows24 : List Row := [
  (1856912124964967976282362528, 12),
  (1856912124964967976276071075, 12),
  (1856912124964954782136538528, 12),
  (1856912171081845753287543584, 16),
  (1856912171081845753272863527, 16),
  (1856912171081836957458762023, 16),
  (1856912189528589827257141541, 16),
  (1953626190534406590418653859, 8),
  (1856912171082118431231708576, 16),
  (1856912171082127227320536480, 16),
  (1856912171082096440994958759, 16),
  (1856912171082096440999153061, 16),
  (1856912189528862504937065888, 16),
  (1856912189528871301025893792, 16),
  (1856912189528840514700316071, 16),
  (1856912189528840514704510373, 16),
  (1856912124965258246953635239, 16),
  (1856912124965267043046657445, 16)]
def rows25 : List Row := [
  (1856912171081814966410417056, 12),
  (1856912124964976772369093536, 12),
  (1856912124964954782147023776, 12),
  (1856912124964954782136538021, 12),
  (1856912171081854548843701993, 20)]
def rows26 : List Row := [
  (1856912171081828160556241184, 12),
  (1856912171081828160549949731, 12),
  (1856912124964967976282362149, 12),
  (1856912124964967976286556451, 12),
  (1856912171081828160549950112, 12),
  (1856912171081814966416708256, 12),
  (1856912171081814966410416803, 12),
  (1856912124964967976286556832, 12),
  (1856912124964967976276071077, 12),
  (1856912124964976772375384736, 12),
  (1856912124964976772369093283, 12),
  (1856912124964954782142829221, 12),
  (1856912124964954782147023523, 12),
  (1856912124964967976282362784, 12),
  (1856912124964954782136538784, 12),
  (1856912171081845753551784231, 16),
  (1856912189528581031172507941, 16),
  (1953626190534406590429139616, 8),
  (1856912171082127227324730784, 16),
  (1856912171082096440999153063, 16),
  (1856912189528862504941260192, 16),
  (1856912189528862504926580135, 16),
  (1856912189528871301030088096, 16),
  (1856912189528871301019602341, 16),
  (1856912189528840514704510375, 16),
  (1856912189528840514708704677, 16),
  (1856912124965258246957829543, 16),
  (1856912124965267043050851749, 16)]
def rows27 : List Row := [
  (1856912124964967976276071840, 12),
  (1856912124964954782142829984, 12),
  (1856912124964954782136538531, 12),
  (1856912171081836957194521381, 16),
  (1953626190534406590418654624, 8)]
def rows28 : List Row := [
  (1856912171081828160560435488, 12),
  (1856912171081828160549949733, 12),
  (1953626190534147106351878432, 12),
  (1953626190534125116119322917, 12),
  (1856912171081836956649263392, 12),
  (1856912171081814966416707877, 12),
  (1856912124964976772375384357, 12),
  (1856912171081836956642972320, 12),
  (1856912171081814966420902560, 12),
  (1856912171081814966410416805, 12),
  (1856912124964976772379579040, 12),
  (1856912124964976772369093285, 12),
  (1856912171081828160549950368, 12),
  (1856912171081814966416708512, 12),
  (1856912124964967976286557088, 12),
  (1856912124964967976276071333, 12),
  (1856912124964976772375384992, 12),
  (1856912124964954782142829477, 12),
  (1856912189528589827265530149, 16),
  (1953626190534428580651209632, 8),
  (1953626190534406590429139872, 8),
  (1856912189528871301034282400, 16),
  (1856912189528840514708704679, 16)]
def rows29 : List Row := [
  (1856912171081828160556241568, 12),
  (1856912171081828160549950115, 12),
  (1856912124964967976282362533, 12),
  (1856912124964967976286556835, 12),
  (1856912171081814966410417568, 12),
  (1856912124964976772369094048, 12),
  (1856912124964954782147024288, 12),
  (1856912124964954782136538533, 12),
  (1856912124964967976276072096, 12),
  (1856912124964954782142830240, 12),
  (1856912124964954782136539168, 12),
  (1856912171081845753287543589, 16),
  (1953626190534406590418654880, 8),
  (1953626190534406590429139619, 8),
  (1856912189528862504932871591, 16),
  (1856912189528871301025893797, 16)]
def rows30 : List Row := [
  (1856912171081836956642972576, 12),
  (1856912171081814966420902816, 12),
  (1856912124964976772379579296, 12),
  (1856912124964976772369093541, 12),
  (1856912124964967976282363296, 12),
  (1856912124964967976276071843, 12),
  (1856912124964954782136539296, 12),
  (1953626190534406590418654627, 8)]
def rows31 : List Row := [
  (1856912171081828160556241189, 12),
  (1856912171081828160560435491, 12),
  (1856912171081828160560435872, 12),
  (1856912171081828160549950117, 12),
  (1856912171081836956649263776, 12),
  (1856912171081836956642972323, 12),
  (1856912171081814966416708261, 12),
  (1856912171081814966420902563, 12),
  (1856912124964976772375384741, 12),
  (1856912124964976772379579043, 12),
  (1856912171081828160556241824, 12),
  (1856912124964967976282362789, 12),
  (1856912171081814966410417824, 12),
  (1856912124964976772369094304, 12),
  (1856912124964954782147024544, 12),
  (1856912124964954782136538789, 12),
  (1856912189528862504937065895, 16),
  (1856912189528871301030088101, 16)]
def rows32 : List Row := [
  (1856912171081828160549950880, 12),
  (1856912171081814966416709024, 12),
  (1856912171081814966410417571, 12),
  (1856912124964967976286557600, 12),
  (1856912124964967976276071845, 12),
  (1856912124964976772375385504, 12),
  (1856912124964976772369094051, 12),
  (1856912124964954782142829989, 12),
  (1856912124964954782147024291, 12),
  (1856912124964967976282363552, 12),
  (1856912124964967976276072480, 12),
  (1856912124964954782142830624, 12),
  (1953626190534406590418655264, 8),
  (1953626190534428580651210144, 8),
  (1953626190534406590429140384, 8)]
def rows33 : List Row := [
  (1953626190534147106351878437, 12),
  (1856912171081836956649263397, 12),
  (1856912171081836956653458080, 12),
  (1856912171081836956642972325, 12),
  (1856912171081828160560436128, 12),
  (1856912171081836956649264032, 12),
  (1856912124964976772375384997, 12),
  (1856912124964967976276072608, 12),
  (1856912124964954782142830752, 12),
  (1856912124964954782136539299, 12),
  (1953626190534406590418655392, 8),
  (1953626190534428580661695392, 8),
  (1856912189528862504941260199, 16),
  (1856912189528871301034282405, 16)]
def rows34 : List Row := [
  (1856912171081828160556241573, 12),
  (1856912171081828160560435875, 12),
  (1856912171081836956642973088, 12),
  (1856912171081814966420903328, 12),
  (1856912171081814966410417573, 12),
  (1856912124964976772379579808, 12),
  (1856912124964976772369094053, 12),
  (1856912171081828160549951136, 12),
  (1856912171081814966416709280, 12),
  (1856912124964967976286557856, 12),
  (1856912124964967976276072101, 12),
  (1856912124964976772375385760, 12),
  (1856912124964954782142830245, 12),
  (1856912171081814966410418208, 12),
  (1856912124964976772369094688, 12),
  (1856912124964954782147024928, 12),
  (1856912124964954782136539173, 12),
  (1953626190534428580651210400, 8),
  (1953626190534406590429140640, 8)]
def rows35 : List Row := [
  (1856912171081836956653458336, 12),
  (1856912171081828160556242336, 12),
  (1856912171081828160549950883, 12),
  (1856912124964967976282363301, 12),
  (1856912124964967976286557603, 12),
  (1856912124964967976282363936, 12),
  (1856912171081814966410418336, 12),
  (1856912124964976772369094816, 12),
  (1856912124964954782147025056, 12),
  (1856912124964954782136539301, 12),
  (1953626190534428580651210147, 8),
  (1953626190534406590429140387, 8)]
def rows36 : List Row := [
  (1856912171081836956649263781, 12),
  (1856912171081836956653458083, 12),
  (1856912171081836956642973344, 12),
  (1856912171081814966420903584, 12),
  (1856912124964976772379580064, 12),
  (1856912124964976772369094309, 12),
  (1856912124964967976282364064, 12),
  (1856912124964967976276072611, 12),
  (1953626190534406590418655395, 8)]
def rows37 : List Row := [
  (422212934828384, 107),
  (1856912171081828160560436640, 12),
  (1856912171081828160549950885, 12),
  (1856912171081836956649264544, 12),
  (1856912171081836956642973091, 12),
  (1856912171081814966416709029, 12),
  (1856912171081814966420903331, 12),
  (1856912124964976772375385509, 12),
  (1856912124964976772379579811, 12),
  (1856912171081828160556242592, 12),
  (1856912124964967976282363557, 12),
  (1856912171081828160549951520, 12),
  (1856912171081814966416709664, 12),
  (1856912124964967976286558240, 12),
  (1856912124964967976276072485, 12),
  (1856912124964976772375386144, 12),
  (1856912124964954782142830629, 12),
  (1953626190534428580651210784, 8),
  (1953626190534428580661695904, 8),
  (1953626190534406590429141024, 8)]
def rows38 : List Row := [
  (1856912171081828160549951648, 12),
  (1856912171081814966416709792, 12),
  (1856912171081814966410418339, 12),
  (1856912124964967976286558368, 12),
  (1856912124964967976276072613, 12),
  (1856912124964976772375386272, 12),
  (1856912124964976772369094819, 12),
  (1856912124964954782142830757, 12),
  (1856912124964954782147025059, 12),
  (1856912124964954782136540320, 12),
  (1953626190534428580651210912, 8),
  (1953626190534406590429141152, 8)]
def rows39 : List Row := [
  (1856912171081836956653458848, 12),
  (1856912171081836956642973093, 12),
  (1856912171081828160560436896, 12),
  (1856912171081836956649264800, 12),
  (1856912124964976772375385765, 12),
  (1856912171081836956642973728, 12),
  (1856912171081814966420903968, 12),
  (1856912124964976772379580448, 12),
  (1856912124964976772369094693, 12),
  (1856912124964954782136540448, 12),
  (1953626190534428580661696160, 8),
  (422212934828640, 53)]
def rows40 : List Row := [
  (1856912171081828160556242341, 12),
  (1856912171081828160560436643, 12),
  (1856912171081828160556242976, 12),
  (1856912124964967976282363941, 12),
  (1856912171081836956642973856, 12),
  (1856912171081814966420904096, 12),
  (1856912171081814966410418341, 12),
  (1856912124964976772379580576, 12),
  (1856912124964976772369094821, 12),
  (1953626190534428580661695907, 8)]
def rows41 : List Row := [
  (1856912171081836956653459104, 12),
  (1856912171081828160556243104, 12),
  (1856912171081828160549951651, 12),
  (1856912124964967976282364069, 12),
  (1856912124964967976286558371, 12),
  (1856912124964967976276073632, 12),
  (1856912124964954782142831776, 12),
  (1856912124964954782136540704, 12),
  (1953626190534406590418656416, 8),
  (1953626190534428580651210915, 8),
  (1953626190534406590429141155, 8)]
def rows42 : List Row := [
  (1856912171081836956649264549, 12),
  (1856912171081836956653458851, 12),
  (1856912171081828160560437280, 12),
  (1856912171081836956649265184, 12),
  (1856912124964976772375386149, 12),
  (1856912124964967976276073760, 16),
  (1856912124964954782142831904, 12),
  (1856912124964954782136540451, 12),
  (1953626190534406590418656544, 8),
  (1953626190534428580661696544, 8)]
def rows43 : List Row := [
  (1856912171081828160560437408, 12),
  (1856912171081828160549951653, 12),
  (1856912171081836956649265312, 12),
  (1856912171081836956642973859, 12),
  (1856912171081814966416709797, 12),
  (1856912171081814966420904099, 12),
  (1856912124964976772375386277, 12),
  (1856912124964976772379580579, 12),
  (1856912171081814966410419360, 12),
  (1856912124964976772369095840, 12),
  (1856912124964954782147026080, 12),
  (1856912124964954782136540325, 12),
  (1953626190534428580661696672, 8)]
def rows44 : List Row := [
  (1856912171081836956653459488, 12),
  (1856912124964967976282365088, 16),
  (1856912171081814966410419488, 12),
  (1856912124964976772369095968, 12),
  (1856912124964954782147026208, 12),
  (1856912124964954782136540453, 12),
  (1856912124964967976276074016, 16),
  (1856912124964954782142832160, 12),
  (1953626190534406590418656800, 8)]
def rows45 : List Row := [
  (1856912171081836956653459616, 12),
  (1856912171081836956642973861, 12),
  (1856912124964967976282365216, 16),
  (1856912124964967976276073763, 16),
  (1856912124964954782136541216, 12),
  (1953626190534406590418656547, 8)]
def rows46 : List Row := [
  (1856912171081828160556243109, 12),
  (1856912171081828160560437411, 12),
  (1856912171081828160549952672, 16),
  (1856912171081814966416710816, 12),
  (1856912124964967976286559392, 12),
  (1856912124964967976276073637, 12),
  (1856912124964976772375387296, 12),
  (1856912124964954782142831781, 12),
  (1856912171081814966410419744, 12),
  (1856912124964976772369096224, 12),
  (1856912124964954782147026464, 12),
  (1856912124964954782136540709, 12),
  (1953626190534428580651211936, 8),
  (1953626190534428580661696675, 8),
  (1953626190534406590429142176, 8)]
def rows47 : List Row := [
  (1856912171081828160549952800, 16),
  (1856912171081814966416710944, 12),
  (1856912171081814966410419491, 12),
  (1856912124964967976286559520, 16),
  (1856912124964967976276073765, 16),
  (1856912124964976772375387424, 12),
  (1856912124964976772369095971, 12),
  (1856912124964954782142831909, 12),
  (1856912124964954782147026211, 12),
  (1856912124964967976282365472, 16),
  (1953626190534428580651212064, 8),
  (1953626190534406590429142304, 8)]
def rows48 : List Row := [
  (1856912171081836956649265317, 12),
  (1856912171081836956653459619, 12),
  (1856912171081836956642974880, 12),
  (1856912171081814966420905120, 12),
  (1856912124964976772379581600, 12),
  (1856912124964976772369095845, 12),
  (1856912124964967976276074528, 20),
  (1856912124964954782142832672, 12),
  (1856912124964954782136541219, 12),
  (1856912124964954782136541600, 12),
  (1953626190534406590418657312, 8)]
def rows49 : List Row := [
  (1856912171081828160556244128, 16),
  (1856912124964967976282365093, 16),
  (1856912171081836956642975008, 12),
  (1856912171081814966420905248, 12),
  (1856912171081814966410419493, 12),
  (1856912124964967976290753824, 16),
  (1856912124964967976276073767, 16),
  (1856912124964976772379581728, 12),
  (1856912124964976772369095973, 12),
  (1856912171081828160549953056, 16),
  (1856912171081814966416711200, 12),
  (1856912124964967976286559776, 16),
  (1856912124964967976276074021, 16),
  (1856912124964976772375387680, 12),
  (1856912124964954782142832165, 12),
  (1953626236651266774692535840, 8),
  (1953626190534428580651212320, 8),
  (1953626190534406590429142560, 8),
  (1856912124965799206395577056, 8)]
def rows50 : List Row := [
  (1856912171081828160556244256, 16),
  (1856912171081828160549952803, 16),
  (1856912124964967976282365221, 16),
  (1856912124964967976286559523, 16),
  (1856912171081814966410420256, 12),
  (1856912124964976772369096736, 12),
  (1856912124964954782147026976, 12),
  (1856912124964954782136541221, 12),
  (1856912124964954782136541856, 12),
  (1953626190534428580651212067, 8),
  (1953626190534406590429142307, 8)]
def rows51 : List Row := [
  (1856912171081828160560438432, 16),
  (1856912171081836956649266336, 12),
  (1856912189528572234265795744, 16),
  (1856912124964976772375387301, 12),
  (1856912171081836956642975264, 12),
  (1856912171081814966420905504, 12),
  (1856912189528572234259504672, 16),
  (1856912124964967976290754080, 16),
  (1856912124964967976276074023, 16),
  (1856912124964976772379581984, 12),
  (1856912124964976772369096229, 12),
  (1856912124964967976276074531, 20),
  (1856912124964954782142833056, 12),
  (1856912124964954782136541603, 12),
  (1856912124964954782136541984, 16),
  (1953626190534406590418657315, 8),
  (1953626190534406590418657696, 8),
  (1953626190534428580661697696, 8),
  (1856912124965236256710591456, 8),
  (1856912124965799206395577312, 8)]
def rows52 : List Row := [
  (1856912124964954782136533984, 8),
  (1856912171081828160560438560, 16),
  (1856912171081828160549952805, 16),
  (1856912171081836956649266464, 12),
  (1856912171081836956642975011, 12),
  (1856912171081814966416710949, 12),
  (1856912171081814966420905251, 12),
  (1856912124964976772375387429, 12),
  (1856912124964976772379581731, 12),
  (1856912171081828160556244512, 16),
  (1856912124964967976282365477, 16),
  (1953626190534428580661697824, 8),
  (1856912124965812400535110368, 8),
  (1856912124965799206395577059, 8),
  (1856912124965799206664012768, 8),
  (1856912124966080681640723360, 16)]
def rows53 : List Row := [
  (1914940564306456982119777184, 8),
  (1856912171081828160564632736, 16),
  (1856912171081828160549952679, 16),
  (1856912171081836956653460640, 12),
  (1856912171081814966416711712, 12),
  (1856912171081814966410420259, 12),
  (1856912124964967976286560288, 20),
  (1856912124964967976276074533, 20),
  (1856912124964976772375388192, 12),
  (1856912124964976772369096739, 12),
  (1856912124964954782142832677, 12),
  (1856912124964954782147026979, 12),
  (1856912171081814966410420640, 12),
  (1856912124964976772369097120, 12),
  (1856912124964954782147027360, 12),
  (1856912124964954782136541605, 12),
  (1856912124964954782142833312, 16),
  (1953626190534406590418657952, 8),
  (1953626236651266774692536352, 8),
  (1953626190534428580651212832, 8),
  (1953626190534406590429143072, 8)]
def rows54 : List Row := [
  (1856912171081828160564632864, 16),
  (1856912171081828160549952807, 16),
  (1856912171081836956653460768, 12),
  (1856912171081836956642975013, 12),
  (1856912124964967976286559527, 16),
  (1856912124964967976290753829, 16),
  (1856912171081828160560438816, 16),
  (1856912171081836956649266720, 12),
  (1856912189528572234265796128, 16),
  (1856912124964976772375387685, 12),
  (1856912124964954782142833440, 16),
  (1856912124964954782136541987, 16),
  (1856912124964954782136542368, 16),
  (1856912124964954782270751904, 8),
  (1953626190534406590418657699, 8),
  (1953626190534406590418658080, 12),
  (1953626190534428580661698080, 8),
  (1856912124965236256716882912, 8),
  (1856912124965236256710591840, 8),
  (1856912124965236257113244832, 8),
  (1856912124965812400535110624, 8),
  (1856912124965799206395577696, 8)]
def rows55 : List Row := [
  (1914940564306456981851342112, 8),
  (1856912124964967976276067296, 8),
  (1856912124964954782142825440, 8),
  (1856912124964954782136534368, 8),
  (1856912171081828160556244261, 16),
  (1856912171081828160560438563, 16),
  (1856912171081836956642975776, 12),
  (1856912171081814966420906016, 12),
  (1856912171081814966410420261, 12),
  (1856912124964967976290754592, 20),
  (1856912124964967976276074535, 20),
  (1856912124964976772379582496, 12),
  (1856912124964976772369096741, 12),
  (1856912171081814966410420896, 16),
  (1856912124964976772369097376, 12),
  (1856912124964954782147027616, 12),
  (1856912124964954782136541861, 12),
  (1856912124964954782270752032, 8),
  (1953626190534428580661697827, 8),
  (1856912124965236256710591968, 8),
  (1856912124965236257113244960, 8),
  (1856912124965812400535110371, 8),
  (1856912124965799206395577824, 12),
  (1856912124965812400803546080, 12),
  (1856912124965799206670304224, 8),
  (1856912124966080681640723363, 20)]
def rows56 : List Row := [
  (1914940564306470176259310496, 8),
  (1914940564306456982126068640, 8),
  (1914940564306456982119777187, 8),
  (1856912124964954782136534496, 8),
  (1856912189528572234265795749, 16),
  (1856912171081828160564633120, 16),
  (1856912171081828160549953063, 16),
  (1856912171081836956653461024, 12),
  (1856912189528572234269990432, 16),
  (1856912189528572234259504677, 16),
  (1856912124964967976286559783, 16),
  (1856912124964967976290754085, 16),
  (1856912124964967976286560291, 20),
  (1856912171081814966416712096, 12),
  (1856912171081814966410420643, 12),
  (1856912124964976772375388576, 12),
  (1856912124964976772369097123, 12),
  (1856912124964954782142833061, 12),
  (1856912124964954782147027363, 12),
  (1856912171081814966410421024, 16),
  (1856912124964976772369097504, 16),
  (1856912124964954782147027744, 16),
  (1856912124964954782136541989, 16),
  (1953626236651266774692536355, 8),
  (1953626236651266774692536736, 8),
  (1953626190534428580651212835, 8),
  (1953626190534428580651213216, 8),
  (1953626190534406590429143075, 8),
  (1953626190534406590429143456, 8),
  (1856912124965236257247462752, 12)]
def rows57 : List Row := [
  (1856912171081836956649266469, 12),
  (1856912171081836956653460771, 12),
  (1856912124964967976294948896, 20),
  (1856912124964967976276074537, 20),
  (1856912124964954782142833824, 16),
  (1856912124964954782136542371, 16),
  (1856912124964967976410285216, 8),
  (1856912124964954782673405280, 8),
  (1953626190534406590418658083, 12),
  (1856912124965236256716883296, 8),
  (1856912124965236257119536288, 8),
  (1856912124965236257247462880, 12),
  (1856912124965812400535111008, 8),
  (1856912171082940865914602400, 20),
  (1856912124966102671873278880, 16),
  (1856912124966080681651209120, 16)]
def rows58 : List Row := [
  (1914940564306470175990875424, 8),
  (1914940564306456981851342115, 8),
  (1856912124964967976282358752, 8),
  (1856912124964967976276067680, 8),
  (1856912124964954782142825824, 8),
  (1856912171081828160560438439, 16),
  (1856912189528572234274184736, 16),
  (1856912171081836956649267232, 12),
  (1856912171081836956642975779, 12),
  (1856912171081814966416711717, 12),
  (1856912171081814966420906019, 12),
  (1856912124964976772375388197, 12),
  (1856912124964976772379582499, 12),
  (1856912171081836956642976160, 12),
  (1856912171081814966420906400, 12),
  (1856912171081814966410420645, 12),
  (1856912124964976772379582880, 12),
  (1856912124964976772369097125, 12),
  (1856912171081814966416712352, 16),
  (1856912124964976772375388832, 16),
  (1856912124964954782142833317, 16),
  (1856912124964985568462119712, 16),
  (1856912124964954782151222048, 16),
  (1856912124964954782136541991, 16),
  (1856912124964967976410285344, 8),
  (1856912124964954782270752035, 8),
  (1856912124964954782270752416, 8),
  (1856912124964954782673405408, 8),
  (1856912124964954782941840736, 8),
  (1953626236651266774692536992, 8),
  (1953626236651266774703022112, 8),
  (1953626190534428580651213472, 8),
  (1953626190534428580661698592, 8),
  (1953626190534406590429143712, 8),
  (1856912124965236256716883424, 8),
  (1856912124965236256710591971, 8),
  (1856912124965236256710592352, 8),
  (1856912124965236257119536416, 8),
  (1856912124965236257113244963, 8),
  (1856912124965236257113245344, 12),
  (1856912124965812400535111136, 12),
  (1856912124965799206395577827, 12),
  (1856912124965812400809837536, 12)]
def rows59 : List Row := [
  (1914940564306456981717124960, 8),
  (1914940564306470176265601952, 8),
  (1914940564306470176259310499, 8),
  (1914940564306456982126068643, 8),
  (1856912124964967976276067808, 8),
  (1856912124964954782142825952, 8),
  (1856912124964954782136534499, 8),
  (1856912124964954782136534880, 8),
  (1856912171081828160560438567, 16),
  (1856912171081828160564632869, 16),
  (1856912189528572234265796133, 16),
  (1856912171081814966416712480, 16),
  (1856912171081814966410421027, 16),
  (1856912124964976772375388960, 16),
  (1856912124964976772369097507, 16),
  (1856912124964954782142833445, 16),
  (1856912124964954782147027747, 16),
  (1856912171081814966410421408, 16),
  (1856912124964976772369097888, 16),
  (1856912124964954782147028128, 16),
  (1856912124964954782136542373, 16),
  (1856912124964954782136543008, 16),
  (1856912124964954782941840864, 8),
  (1953626190534428580651213600, 12),
  (1953626190534406590429143840, 12),
  (1953626190534406590418658085, 12),
  (1953626236651266774692536739, 8),
  (1953626190534428580651213219, 8),
  (1953626190534406590429143459, 8),
  (1856912189529684939624154016, 16),
  (1856912124966111467966301088, 16),
  (1856912124966080681655403424, 16),
  (1856912124966080681640723367, 16)]
def rows60 : List Row := [
  (1856912171081836956653461536, 12),
  (1856912171081836956642975781, 12),
  (1856912124964967976286560295, 20),
  (1856912124964967976290754597, 20),
  (1856912124964967976294948899, 20),
  (1856912171081836956642976416, 16),
  (1856912171081814966420906656, 16),
  (1856912124964976772379583136, 12),
  (1856912124964976772369097381, 12),
  (1856912189528559040126263968, 16),
  (1856912124964985568468411040, 16),
  (1856912124964954782136543136, 20),
  (1856912124964954782270752672, 8),
  (1856912124964967976812938592, 8),
  (1856912124965236256710592608, 8),
  (1856912124965236257247462883, 12),
  (1856912171082659390669456864, 12),
  (1856912124965799206406063584, 12),
  (1856912124965799206395577829, 12),
  (1953626190534982734780040160, 12),
  (1856912171082672585077425120, 12),
  (1856912124965812400814031840, 12),
  (1856912124965812400803546085, 12),
  (1856912124966102671873278883, 20),
  (1856912124966080681651209123, 20)]
def rows61 : List Row := [
  (1914940564306470175990875427, 8),
  (1856912124964967976282359136, 8),
  (1856912124964954782136535136, 8),
  (1856912171081828160560438823, 16),
  (1856912171081836956649267616, 12),
  (1856912171081836956642976163, 12),
  (1856912171081814966416712101, 12),
  (1856912171081814966420906403, 12),
  (1856912124964976772375388581, 12),
  (1856912124964976772379582883, 12),
  (1856912171081836956642976544, 16),
  (1856912171081814966420906784, 16),
  (1856912171081814966410421029, 16),
  (1856912124964976772379583264, 16),
  (1856912124964976772369097509, 16),
  (1856912124964985568468411168, 16),
  (1856912124964985568462119715, 16),
  (1856912124964985568462120096, 16),
  (1856912124964954782151222432, 16),
  (1856912124964954782136542375, 16),
  (1856912124964967976410285347, 8),
  (1856912124964967976410285728, 8),
  (1856912124964954782270752419, 8),
  (1856912124964967976812938720, 8),
  (1856912124964954782673405411, 8),
  (1856912124964954782673405792, 8),
  (1856912124964967977081374048, 8),
  (1856912124964954782948132192, 8),
  (1856912124964954783076058784, 8),
  (1953626236651288764925092256, 8),
  (1953626236651266774703022115, 8),
  (1953626236651266774703022496, 8),
  (1953626190534428580661698595, 8),
  (1953626190534428580661698976, 8),
  (1856912124965236256716883427, 8),
  (1856912124965236256716883808, 8),
  (1856912124965236256710592355, 8),
  (1856912124965236256710592736, 8),
  (1856912124965236257119536419, 8),
  (1856912124965236257119536800, 12),
  (1856912124965236257113245347, 12),
  (1856912171082096441521341792, 12),
  (1856912124965236257257948512, 12),
  (1856912124965236257247462757, 12),
  (1856912124965812400535111139, 12)]
def rows62 : List Row := [
  (1914940564306470175856658272, 8),
  (1914940564306456981723416416, 8),
  (1914940564306456981717124963, 8),
  (1914940564306470176265601955, 8),
  (1856912124964967976282359264, 8),
  (1856912124964967976276067811, 8),
  (1856912124964954782142825955, 8),
  (1856912124964967976276068192, 8),
  (1856912124964954782142826336, 8),
  (1856912124964954782136534883, 8),
  (1856912124964954782136535264, 8),
  (1856912171081845752735998624, 16),
  (1856912171081814966425100960, 16),
  (1856912171081814966410420903, 16),
  (1856912171081814966416712864, 16),
  (1856912171081814966410421411, 16),
  (1856912124964976772375389344, 16),
  (1856912124964976772369097891, 16),
  (1856912124964954782142833829, 16),
  (1856912124964954782147028131, 16),
  (1856912124964954782142834464, 20),
  (1856912124964967977081374176, 8),
  (1856912124964954782948132320, 8),
  (1856912124964954782941840867, 8),
  (1856912124964954782941841248, 12),
  (1856912124964954783344494240, 12),
  (1953626190534428580651213603, 12),
  (1953626190534406590429143843, 12),
  (1856912171082096441521341920, 12),
  (1856912124965236257257948640, 12),
  (1856912124965236257247462885, 12),
  (1856912171082940865925088160, 20),
  (1856912189529684939624154019, 20),
  (1856912124966102671883764640, 16),
  (1856912124966111467966301091, 20),
  (1856912124966080681655403427, 20)]
def rows63 : List Row := [
  (1856912189528572234274184741, 16),
  (1856912171081836956649267237, 12),
  (1856912171081836956653461539, 12),
  (1856912171081836956653461920, 12),
  (1856912171081836956642976165, 12),
  (1856912171081836956649267872, 16),
  (1856912124964976772375388837, 16),
  (1856912171081845752735998752, 16),
  (1856912171081814966425101088, 16),
  (1856912171081814966410421031, 16),
  (1856912124964976772383777568, 16),
  (1856912124964976772369097511, 16),
  (1856912124964985568472605472, 16),
  (1856912124964985568462119717, 16),
  (1856912124964954782147027751, 16),
  (1856912124964954782151222053, 16),
  (1856912124964954782136543139, 20),
  (1856912124964967976410285984, 8),
  (1856912124964954782270753056, 8),
  (1856912124964954782673406048, 8),
  (1856912124964954783076059040, 12),
  (1953626236651288764925092512, 8),
  (1953626236651266774703022752, 8),
  (1953626190534428580661699232, 8),
  (1856912124965236256716884064, 8),
  (1856912124965236256710592992, 12),
  (1856912171082096441387124384, 12),
  (1856912124965258247345800864, 12),
  (1856912124965236257123731104, 12),
  (1856912124965236257113245349, 12),
  (1856912171082672584808990176, 12),
  (1856912171082659390669456867, 12),
  (1856912124965812400545596896, 12),
  (1856912124965812400535111141, 12),
  (1856912124965799206406063587, 12),
  (1856912171082672585083716576, 12),
  (1856912124965812400809837541, 12)]
def rows64 : List Row := [
  (1856912124964967976276068448, 8),
  (1856912124964954782142826592, 8),
  (1856912124964954782136535520, 8),
  (1856912124964967976290754601, 20),
  (1856912124964967976294948903, 20),
  (1856912171081836956649268000, 16),
  (1856912171081836956642976547, 16),
  (1856912171081814966416712485, 16),
  (1856912171081814966420906787, 16),
  (1856912124964976772375388965, 16),
  (1856912124964976772379583267, 16),
  (1856912171081836956642976928, 16),
  (1856912171081814966420907168, 16),
  (1856912171081814966410421413, 16),
  (1856912124964976772379583648, 16),
  (1856912124964976772369097893, 16),
  (1856912124964985568468411552, 16),
  (1856912124964985568462120099, 16),
  (1856912171081814966410422048, 20),
  (1856912124964976772369098528, 16),
  (1856912124964954782147028768, 16),
  (1856912124964954782136543013, 16),
  (1856912124964967976410285731, 8),
  (1856912124964967976812938723, 8),
  (1856912124964967976812939104, 8),
  (1856912124964954782673405795, 8),
  (1856912124964954782673406176, 12),
  (1856912124964967977087665504, 8),
  (1856912124964954782941841504, 12),
  (1856912124964967977215592096, 12),
  (1856912124964954783076058787, 8),
  (1953626190534428580661699360, 12),
  (1953626190534406590429143845, 12),
  (1953626236651288764925092259, 8),
  (1953626236651266774703022499, 8),
  (1953626190534428580661698979, 8),
  (1856912124965236256716883811, 8),
  (1856912124965236256716884192, 8),
  (1856912124965236256710592739, 8),
  (1856912124965236256710593120, 12),
  (1856912124965236257119536803, 12),
  (1856912171082971652240180128, 20),
  (1856912171082940865929282464, 20),
  (1856912171082940865914602407, 20),
  (1856912189529706929856709536, 16),
  (1856912189529684939634639776, 16),
  (1856912124966102671887958944, 16),
  (1856912124966102671873278887, 16),
  (1856912124966111467976786848, 16),
  (1856912124966080681651209127, 16),
  (1856912124966080681659597731, 20)]
def rows65 : List Row := [
  (1914940564306470175862949728, 8),
  (1914940564306470175856658275, 8),
  (1914940564306456981723416419, 8),
  (1856912124964967976282359267, 8),
  (1856912124964967976282359648, 8),
  (1856912124964967976276068195, 8),
  (1856912124964954782142826339, 8),
  (1856912124964967976276068576, 8),
  (1856912124964954782142826720, 8),
  (1856912124964954782136535267, 8),
  (1856912124964954782136535648, 8),
  (1856912171081836956653462176, 16),
  (1856912171081845752742290080, 16),
  (1856912189528581030358819488, 16),
  (1856912189528559040126263973, 16),
  (1856912124964985568468411045, 16),
  (1856912124964985568476799776, 16),
  (1856912124964985568462119719, 16),
  (1856912124964976772369098656, 20),
  (1856912124964954782147028896, 20),
  (1856912124964954782136543141, 20),
  (1856912124964967977087665632, 8),
  (1856912124964967977081374179, 8),
  (1856912124964954782948132323, 8),
  (1856912124964967977081374560, 12),
  (1856912124964954782948132704, 12),
  (1856912124964954782941841251, 12),
  (1856912124964954782941841632, 12),
  (1856912124964967977484027552, 12),
  (1856912124964954783350785696, 12),
  (1856912124964954783344494243, 12),
  (1856912171082096441521341923, 12),
  (1856912124965236257257948643, 12),
  (1856912171082659390669456869, 12),
  (1856912124965799206406063589, 12),
  (1953626190534982734790525920, 12),
  (1953626190534982734780040165, 12),
  (1856912171082672585087910880, 12),
  (1856912124965812400814031845, 12),
  (1856912124966102671883764643, 20)]
def rows66 : List Row := [
  (201326816, 47),
  (1856912171081836956649267621, 12),
  (1856912171081836956653461923, 12),
  (1856912171081836956653462304, 16),
  (1856912171081836956642976549, 16),
  (1856912171081845752742290208, 16),
  (1856912171081845752735998755, 16),
  (1856912124964985568468411173, 16),
  (1856912124964985568472605475, 16),
  (1856912171081845752735999136, 16),
  (1856912171081814966425101472, 16),
  (1856912171081814966410421415, 16),
  (1856912124964976772383777952, 16),
  (1856912124964976772369097895, 16),
  (1856912124964985568472605856, 16),
  (1856912124964985568462120101, 16),
  (1856912124964954782147028135, 16),
  (1856912124964954782151222437, 16),
  (1856912189528559040119973664, 16),
  (1856912124964985568462120736, 16),
  (1856912124964954782151223072, 16),
  (1856912124964954782136543015, 16),
  (1856912124964967976410286368, 8),
  (1856912124964967976812939360, 12),
  (1856912124964954782673406432, 12),
  (1856912124964967977215592352, 12),
  (1856912124965236256716884448, 12),
  (1856912171082096441393415840, 12),
  (1856912171082096441387124387, 12),
  (1856912124965258247352092320, 12),
  (1856912124965258247345800867, 12),
  (1856912124965236257119536805, 12),
  (1856912124965236257123731107, 12),
  (1856912171082096441531827552, 12),
  (1856912171082096441521341797, 12),
  (1856912124965236257257948517, 12),
  (1856912171082672584808990179, 12),
  (1856912124965812400545596899, 12),
  (1856912171082940865933476768, 20),
  (1856912189529684939638834080, 16),
  (1856912189529684939624154023, 16),
  (1856912124966111467980981152, 16),
  (1856912124966111467966301095, 16),
  (1856912124966080681655403431, 16)]
def rows67 : List Row := [
  (1856912124964967976282359904, 8),
  (1856912124964967976276068832, 8),
  (1856912124964954782142826976, 8),
  (1856912171081836956657656480, 16),
  (1856912171081836956642976423, 16),
  (1856912171081845752746484384, 16),
  (1856912171081814966420906663, 16),
  (1856912189528589826451841696, 16),
  (1856912171081836956649268384, 16),
  (1856912171081836956642976931, 16),
  (1856912171081814966416712869, 16),
  (1856912171081814966420907171, 16),
  (1856912124964976772375389349, 16),
  (1856912124964976772379583651, 16),
  (1856912124964976772375389984, 20),
  (1856912124964954782142834469, 20),
  (1856912124964985568462120864, 20),
  (1856912124964954782151223200, 20),
  (1856912124964954782136543143, 20),
  (1856912124964954782270753568, 8),
  (1856912124964967976812939107, 8),
  (1856912124964967976812939488, 12),
  (1856912124964954782673406179, 12),
  (1856912124964954782673406560, 12),
  (1856912171081814967215720288, 12),
  (1856912124964976773174396768, 12),
  (1856912124964954782941841253, 12),
  (1856912124964967977081374816, 12),
  (1856912124964954782948132960, 12),
  (1856912124964967977215592099, 12),
  (1856912171081814967618373280, 12),
  (1856912124964976773577049760, 12),
  (1856912124964954783354980000, 12),
  (1953626190534428580661699363, 12),
  (1856912124965236256716884195, 8),
  (1856912124965236256716884576, 12),
  (1856912124965236256710593123, 12),
  (1856912171082096441531827680, 12),
  (1856912171082096441521341925, 12),
  (1856912124965236257257948645, 12),
  (1856912189529706929856709539, 20),
  (1856912189529684939634639779, 20),
  (1856912124966102671887958947, 20),
  (1856912124966111467976786851, 20),
  (201326944, 35)]
def rows68 : List Row := [
  (1914940564306470175862949731, 8),
  (1856912124964967976282359651, 8),
  (1856912124964967976282360032, 8),
  (1856912124964967976276068579, 8),
  (1856912124964954782142826723, 8),
  (1856912124964967976276068960, 8),
  (1856912124964954782142827104, 8),
  (1856912124964954782136535651, 8),
  (1856912171081836956657656608, 16),
  (1856912171081836956642976551, 16),
  (1856912171081845752746484512, 16),
  (1856912171081845752735998757, 16),
  (1856912171081814966420906791, 16),
  (1856912171081814966425101093, 16),
  (1856912124964976772379583271, 16),
  (1856912124964976772383777573, 16),
  (1856912124964985568476800160, 16),
  (1856912124964985568462120103, 16),
  (1856912124964976772369098659, 20),
  (1856912124964954782147028899, 20),
  (1856912124964967977087665635, 8),
  (1856912124964967977087666016, 12),
  (1856912124964967977081374563, 12),
  (1856912124964954782948132707, 12),
  (1856912124964954782948133088, 12),
  (1856912124964954782941841635, 12),
  (1856912171081814967349938080, 12),
  (1856912124964976773308614560, 12),
  (1856912124964954783086544800, 12),
  (1856912124964967977490319008, 12),
  (1856912124964967977484027555, 12),
  (1856912124964954783350785699, 12),
  (1856912171082096440984472032, 12),
  (1856912124965236256721078752, 12),
  (1856912124965236256710592997, 12),
  (1856912171082096441397610144, 12),
  (1856912171082096441387124389, 12),
  (1856912124965258247356286624, 12),
  (1856912124965258247345800869, 12),
  (1856912124965236257123731109, 12),
  (1856912171082672584808990181, 12),
  (1856912124965812400545596901, 12)]
def rows69 : List Row := [
  (1856912171081845752750678688, 16),
  (1856912171081845752735998631, 16),
  (1856912171081836956649268005, 16),
  (1856912171081836956653462307, 16),
  (1856912171081836956653462688, 16),
  (1856912171081836956642976933, 16),
  (1856912171081845752742290592, 16),
  (1856912171081845752735999139, 16),
  (1856912124964985568468411557, 16),
  (1856912124964985568472605859, 16),
  (1856912171081836956642977568, 24),
  (1856912171081814966420907808, 20),
  (1856912189528559040126265120, 20),
  (1856912124964976772379584288, 16),
  (1856912124964976772369098533, 16),
  (1856912124964985568468412192, 20),
  (1856912124964994364555143072, 20),
  (1856912124964954782155417504, 20),
  (1856912124964954782136543145, 20),
  (1856912124964954782270753824, 8),
  (1856912171081814966947285216, 12),
  (1856912124964976772905961696, 12),
  (1856912124964954782673406181, 12),
  (1856912124964967976812939744, 12),
  (1856912171081814967215720544, 12),
  (1856912124964976773174397024, 12),
  (1856912124964954782941841509, 12),
  (1856912171081828161489471136, 12),
  (1856912124964967977226077856, 12),
  (1856912171082096440984472160, 12),
  (1856912124965236256721078880, 12),
  (1856912124965236256710593125, 12),
  (1856912124965236256710593760, 12),
  (1856912171082096441393415843, 12),
  (1856912171082971652250665888, 20),
  (1856912171082940865925088167, 20),
  (1856912189529706929867195296, 16),
  (1856912189529684939638834083, 20),
  (1856912124966102671883764647, 16),
  (1856912124966102671892153251, 20),
  (1856912124966111467980981155, 20)]
def rows70 : List Row := [
  (1856912124964967976282360288, 8),
  (1856912124964954782136536288, 8),
  (1856912189528581030358819493, 16),
  (1856912171081845752750678816, 16),
  (1856912171081845752735998759, 16),
  (1856912124964985568472605479, 16),
  (1856912124964985568476799781, 16),
  (1856912124964976772379584416, 20),
  (1856912124964976772369098661, 20),
  (1856912124964985568462120867, 20),
  (1856912124964967976410286880, 8),
  (1856912124964954782270753571, 8),
  (1856912124964954782270753952, 8),
  (1856912124964967976812939491, 12),
  (1856912124964967976812939872, 12),
  (1856912124964954782673406563, 12),
  (1856912171081828161355253600, 12),
  (1856912171081814967222011744, 12),
  (1856912171081814967215720291, 12),
  (1856912124964967977081374565, 12),
  (1856912124964976773180688224, 12),
  (1856912124964976773174396771, 12),
  (1856912124964954782948132709, 12),
  (1856912124964967977087666272, 12),
  (1856912171081814967215720672, 12),
  (1856912124964976773174397152, 12),
  (1856912124964954782941841637, 12),
  (1856912171081828161757906592, 12),
  (1856912171081814967624664736, 12),
  (1856912171081814967618373283, 12),
  (1856912124964967977494513312, 12),
  (1856912124964976773583341216, 12),
  (1856912124964976773577049763, 12),
  (1856912124964954783354980003, 12),
  (1856912124965236256716884579, 12),
  (1856912124965236256710593888, 16),
  (1856912171082096441531827683, 12),
  (1953626190534982734790525925, 12)]
def rows71 : List Row := [
  (1856912124964967976282360035, 8),
  (1856912124964967976282360416, 8),
  (1856912124964967976276068963, 8),
  (1856912124964954782142827107, 8),
  (1856912124964954782136536416, 8),
  (1856912171081845752742290213, 16),
  (1856912171081845752746484515, 16),
  (1856912171081836956657656992, 16),
  (1856912171081836956642976935, 16),
  (1856912171081845752746484896, 16),
  (1856912171081845752735999141, 16),
  (1856912171081814966420907175, 16),
  (1856912171081814966425101477, 16),
  (1856912124964976772379583655, 16),
  (1856912124964976772383777957, 16),
  (1856912171081845752735999776, 20),
  (1856912171081814966425102112, 20),
  (1856912171081814966410422055, 20),
  (1856912189528581030352529184, 16),
  (1856912189528559040130459424, 16),
  (1856912189528559040119973669, 16),
  (1856912124964976772383778592, 16),
  (1856912124964976772369098535, 16),
  (1856912124964985568472606496, 16),
  (1856912124964985568462120741, 16),
  (1856912124964994364561434400, 20),
  (1856912124964954782147028775, 16),
  (1856912124964954782151223077, 16),
  (1856912171081828161086818400, 12),
  (1856912124964967976812939365, 12),
  (1856912171081814966947285472, 12),
  (1856912124964976772905961952, 12),
  (1856912124964954782673406437, 12),
  (1856912124964967977087666019, 12),
  (1856912124964954782948133091, 12),
  (1856912171081828161489471392, 12),
  (1856912124964967977226078112, 12),
  (1856912124964967977490319011, 12),
  (1856912171082096440990763488, 12),
  (1856912124965236256716884453, 12),
  (1856912171082096441393415845, 12),
  (1856912171082096441397610147, 12),
  (1856912124965258247352092325, 12),
  (1856912124965258247356286627, 12),
  (1856912171082096441531827557, 12),
  (1856912171082971652254860192, 20),
  (1856912171082971652240180135, 20),
  (1856912171082940865929282471, 20),
  (1856912189529706929871389600, 16),
  (1856912189529706929856709543, 16),
  (1856912189529684939634639783, 16),
  (1856912189529684939643028387, 20),
  (1856912124966102671887958951, 16),
  (1856912124966111467976786855, 16),
  (1856912124966111467985175459, 20)]
def rows72 : List Row := [
  (885444700701215162784, 8),
  (1856912171081836956653462183, 16),
  (1856912189528589826451841701, 16),
  (1856912171081836956649268389, 16),
  (1856912171081836956653462691, 16),
  (1856912124964976772375389989, 20),
  (1856912124964976772383778720, 20),
  (1856912124964976772369098663, 20),
  (1856912124964985568472606624, 20),
  (1856912124964985568462120869, 20),
  (1856912124964994364555143075, 20),
  (1856912124964954782147028903, 20),
  (1856912124964954782151223205, 20),
  (1856912124964954782155417507, 20),
  (1856912124964967976410287136, 12),
  (1856912124964954782270754208, 12),
  (1856912171081828161086818528, 12),
  (1856912171081814966947285219, 12),
  (1856912124964967976812939493, 12),
  (1856912124964976772905961699, 12),
  (1856912171081814966947285600, 12),
  (1856912124964976772905962080, 12),
  (1856912124964954782673406565, 12),
  (1856912171081836957448275808, 12),
  (1856912171081814967215720293, 12),
  (1856912124964976773174396773, 12),
  (1856912171081828161355253856, 12),
  (1856912171081814967222012000, 12),
  (1856912124964967977081374821, 12),
  (1856912124964976773180688480, 12),
  (1856912124964954782948132965, 12),
  (1856912171081828161489471139, 12),
  (1856912124964967977226077859, 12),
  (1856912171081836957850928800, 12),
  (1856912171081814967628859040, 12),
  (1856912124964976773587535520, 12),
  (1856912171082096440990763616, 12),
  (1856912171082096440984472163, 12),
  (1856912124965236256716884581, 12),
  (1856912124965236256721078883, 12),
  (1856912124965236256716885216, 12),
  (1856912171082096441531827685, 12),
  (1856912189529706929867195299, 20)]
def rows73 : List Row := [
  (885444700701215162912, 8),
  (1856912124964967976276069600, 8),
  (1856912124964954782142827744, 8),
  (1856912171081836956653462311, 16),
  (1856912171081836956657656613, 16),
  (1856912171081845752750679200, 16),
  (1856912171081845752735999143, 16),
  (1856912124964985568472605863, 16),
  (1856912124964985568476800165, 16),
  (1856912171081854548829021984, 20),
  (1856912171081814966429296416, 20),
  (1856912189528589826445551392, 16),
  (1856912189528559040134653728, 16),
  (1856912124964985568476800800, 16),
  (1856912124964985568462120743, 16),
  (1856912124964976772379584419, 20),
  (1856912124964967976410286883, 8),
  (1856912124964967976410287264, 12),
  (1856912124964954782270753955, 8),
  (1856912124964954782270754336, 12),
  (1856912124964967976812939875, 12),
  (1856912171081828161361545056, 12),
  (1856912171081828161355253603, 12),
  (1856912171081814967222011747, 12),
  (1856912124964967977087666021, 12),
  (1856912124964976773180688227, 12),
  (1856912171081814967222012128, 12),
  (1856912171081814967215720675, 12),
  (1856912124964976773180688608, 12),
  (1856912124964976773174397155, 12),
  (1856912124964954782948133093, 12),
  (1856912171081836957582493600, 12),
  (1856912171081814967360423840, 12),
  (1856912124964976773319100320, 12),
  (1856912171081828161764198048, 12),
  (1856912171081828161757906595, 12),
  (1856912171081814967624664739, 12),
  (1856912124964967977494513315, 12),
  (1856912124964976773583341219, 12),
  (1856912171082096440994957792, 12),
  (1856912171082096440984472037, 12),
  (1856912124965236256721078757, 12),
  (1856912124965236256716885344, 16),
  (1856912124965236256710593891, 16),
  (1856912171082096441397610149, 12),
  (1856912171082971652259054496, 20),
  (1856912171082940865933476775, 20),
  (1856912189529684939638834087, 16),
  (1856912124966111467980981159, 16)]
def rows74 : List Row := [
  (1856912124964967976282360419, 8),
  (1856912124964967976276069728, 8),
  (1856912124964954782142827872, 8),
  (1856912124964954782136536419, 8),
  (1856912171081845752746484391, 16),
  (1856912171081845752742290597, 16),
  (1856912171081845752746484899, 16),
  (1856912171081836956653463328, 24),
  (1856912189528581030358820640, 20),
  (1856912189528559040126265125, 20),
  (1856912124964985568468412197, 20),
  (1856912124964976772387973024, 20),
  (1856912124964976772369098665, 20),
  (1856912124964985568476800928, 20),
  (1856912124964985568462120871, 20),
  (1856912124964994364565628832, 20),
  (1856912124964994364555143077, 20),
  (1856912171081836957179840736, 12),
  (1856912171081814966947285221, 12),
  (1856912124964976772905961701, 12),
  (1856912171081828161086818784, 12),
  (1856912124964967976812939749, 12),
  (1856912171081836957448276064, 12),
  (1856912124964976773174397029, 12),
  (885444700701349380704, 12),
  (1856912171082096440994957920, 12),
  (1856912171082096440984472165, 12),
  (1856912124965236256721078885, 12),
  (1856912171082096440984472800, 12),
  (1856912124965236256721079520, 12),
  (1856912124965236256710593765, 12),
  (1856912189529706929871389603, 20)]
def rows75 : List Row := [
  (913114816811779490208, 8),
  (885444700701221454240, 8),
  (1856912171081845752746484519, 16),
  (1856912171081845752750678821, 16),
  (1856912124964985568472606627, 20),
  (1856912124964967976410287520, 12),
  (1856912171081828161086818531, 12),
  (1856912171081828161086818912, 12),
  (1856912171081814966947285603, 12),
  (1856912124964967976812939877, 12),
  (1856912124964976772905962083, 12),
  (1856912171081828161355253605, 12),
  (1856912171081836957454567264, 12),
  (1856912171081836957448275811, 12),
  (1856912171081814967222011749, 12),
  (1856912124964976773180688229, 12),
  (1856912171081828161361545312, 12),
  (1856912124964967977087666277, 12),
  (1856912171081836957448276192, 12),
  (1856912171081814967215720677, 12),
  (1856912124964976773174397157, 12),
  (1856912171081828161768392352, 12),
  (1856912171081836957857220256, 12),
  (1856912171081836957850928803, 12),
  (1856912171081814967628859043, 12),
  (1856912124964976773587535523, 12),
  (885444700701349380832, 225),
  (1856912171082096440990763619, 12),
  (1856912171082096440984472928, 16),
  (1856912124965236256721079648, 16),
  (1856912124965236256710593893, 16),
  (885444700701617816160, 109)]
def rows76 : List Row := [
  (913114816811779490336, 133),
  (885444700701221454368, 8),
  (885444700701215162915, 8),
  (885444700701215163296, 641),
  (1856912124964967976282361056, 8),
  (1856912124964954782136537056, 8),
  (1856912171081836956653462695, 16),
  (1856912171081836956657656997, 16),
  (1856912171081836956657657632, 24),
  (1856912171081836956642977575, 24),
  (1856912171081845752746485536, 20),
  (1856912171081814966420907815, 20),
  (1856912189528581030363014944, 16),
  (1856912189528581030352529189, 16),
  (1856912189528589826451842848, 20),
  (1856912124964976772379584295, 16),
  (1856912124964976772383778597, 16),
  (1856912124964994364561434405, 20),
  (1856912124964985568480995232, 20),
  (1856912124964985568462120873, 20),
  (1856912124964994364569823136, 20),
  (1856912124964994364555143079, 20),
  (1856912124964954782151223209, 20),
  (1856912124964954782155417511, 20),
  (1856912124964967976410287267, 12),
  (1856912124964967976410287648, 12),
  (1856912124964954782270754339, 12),
  (1856912171081828161086818405, 12),
  (1856912171081836957179840992, 12),
  (1856912171081814966947285477, 12),
  (1856912124964976772905961957, 12),
  (1856912171081828161361545059, 12),
  (1856912171081814967222012131, 12),
  (1856912124964976773180688611, 12),
  (1856912171081828161499957152, 12),
  (1856912171081828161764198051, 12),
  (1856912171082096440990763493, 12),
  (1856912124965236256716885347, 16),
  (885444700701617816288, 73),
  (1856912171082971652250665895, 20),
  (1856912189529706929867195303, 16),
  (1856912189529706929875583907, 20)]
def rows77 : List Row := [
  (1856912124964967976282361184, 8),
  (1856912124964967976276069731, 8),
  (1856912124964954782142827875, 8),
  (1856912124964954782136537184, 8),
  (1856912124964976772379584423, 20),
  (1856912124964976772383778725, 20),
  (1856912124964976772387973027, 20),
  (1856912124964994364565628835, 20),
  (1953626190534138310386781216, 12),
  (1856912171081828160684166176, 12),
  (1856912124964967976420772896, 12),
  (1856912171081814966544633248, 12),
  (1856912124964976772503309728, 12),
  (1856912124964954782281239968, 12),
  (1856912171081828161086818533, 12),
  (1856912171081836957179840739, 12),
  (1856912171081836957179841120, 12),
  (1856912171081814966947285605, 12),
  (1856912124964976772905962085, 12),
  (1856912171081836957448275813, 12),
  (1856912171081836957454567520, 12),
  (1856912124964976773180688485, 12),
  (1856912171081836957861414560, 12),
  (913114816811913708128, 57),
  (1856912171082096440990763621, 12),
  (1856912171082096440994957923, 12),
  (1856912171082096440990764256, 12),
  (1856912124965236256716885221, 12),
  (1856912189528840514694024544, 16),
  (1856912124965267043036171616, 16),
  (1856912124965236256725273952, 16),
  (1856912124965236256710593895, 16),
  (885444700701349381088, 99)]
def rows78 : List Row := [
  (913114816811785781664, 8),
  (1856912171081845752746484903, 16),
  (1856912171081845752750679205, 16),
  (1856912171081836956661851936, 24),
  (1856912171081845752750679840, 20),
  (1856912171081845752735999783, 20),
  (1856912171081854548839507744, 20),
  (1856912189528581030367209248, 16),
  (1856912189528589826456037152, 16),
  (1856912189528589826445551397, 16),
  (1856912189528598622544865056, 20),
  (1856912189528559040134653733, 16),
  (1856912124964985568472606503, 16),
  (1856912124964985568476800805, 16),
  (1856912124964994364574017440, 20),
  (1856912124964994364555143081, 20),
  (1856912171081828160684166304, 12),
  (1856912124964967976420773024, 12),
  (1856912171081814966544633376, 12),
  (1856912124964976772503309856, 12),
  (1856912124964954782281240096, 12),
  (885444700701215163552, 187),
  (1856912171081828161086818915, 12),
  (1856912171081828161361545061, 12),
  (1856912171081836957454567267, 12),
  (1856912171081836957454567648, 12),
  (1856912171081836957448276195, 12),
  (1856912171081814967222012133, 12),
  (1856912124964976773180688613, 12),
  (1856912171081836957592979360, 12),
  (1856912171081828161768392355, 12),
  (1856912171081836957857220259, 12),
  (1856912171082096440994957797, 12),
  (1856912171082096440990764384, 16),
  (1856912171082096440984472931, 16),
  (1856912124965236256716885349, 16),
  (1856912124965236256721079651, 16),
  (1856912171082971652254860199, 20),
  (1856912189529706929871389607, 16)]
def rows79 : List Row := [
  (913114816811785781792, 127),
  (885444700701221454371, 8),
  (913114816811779490339, 131),
  (1856912124964967976276070368, 12),
  (1856912124964954782142828512, 8),
  (1856912124964954782136537440, 12),
  (1856912189528581030358820645, 20),
  (1856912124964985568472606631, 20),
  (1856912124964985568476800933, 20),
  (1856912124964985568480995235, 20),
  (1856912124964967976410287651, 12),
  (1856912124964954782270755104, 12),
  (1856912171081836957179840741, 12),
  (1856912171081828161086818789, 12),
  (885444700701215163680, 151),
  (931561560885623259744, 567),
  (885444722691581936224, 12),
  (885444700701359866464, 12),
  (885444700701349380709, 12),
  (1856912171082096440994957925, 12),
  (1856912171082096440994958560, 12),
  (1856912171082096440984472805, 12),
  (1856912124965236256721079525, 12)]
def rows80 : List Row := [
  (1856912124964967976282361187, 8),
  (1856912124964967976276070496, 12),
  (1856912124964954782142828640, 8),
  (1856912124964954782136537187, 8),
  (1856912171081836956666046240, 24),
  (1856912171081845752754874144, 20),
  (1856912171081854548843702048, 20),
  (1856912171081854548829021991, 20),
  (1856912171081814966429296423, 20),
  (1856912189528589826460231456, 16),
  (1856912171081828160684166560, 12),
  (1856912124964967976420773280, 12),
  (1856912171081828161086818917, 12),
  (1856912171081836957179841123, 12),
  (1856912171081836957454567269, 12),
  (1856912171081836957448276197, 12),
  (1856912171081836957861414563, 12),
  (1856912171082096440994958688, 16),
  (1856912171082096440984472933, 16),
  (1856912189528840514700316000, 16),
  (1856912189528840514694024547, 16),
  (1856912124965267043042463072, 16),
  (1856912124965267043036171619, 16),
  (1856912124965236256716885351, 16),
  (1856912124965236256721079653, 16),
  (1856912124965236256725273955, 16),
  (1856912171082971652259054503, 20)]
def rows81 : List Row := [
  (1856912171081836956653463335, 24),
  (1856912189528589826451842853, 20),
  (1856912124964976772383778729, 20),
  (1856912124964976772387973031, 20),
  (1856912124964994364565628839, 20),
  (1856912124964994364569823141, 20),
  (1856912124964994364574017443, 20),
  (1856912171081828160684166307, 12),
  (1856912124964967976420773027, 12),
  (1856912171081828160684166688, 12),
  (1856912171081814966544633379, 12),
  (1856912124964967976420773408, 12),
  (1856912124964976772503309859, 12),
  (1856912124964954782281240099, 12),
  (1856912171081836957179840997, 12),
  (1856912171081836957454567651, 12),
  (1856912171082096440990764387, 16)]
def rows82 : List Row := [
  (913114816811785781795, 125),
  (1856912124964967976282361824, 12),
  (1856912124964967976276070752, 12),
  (1856912124964954782142828896, 12),
  (1856912124964954782136537824, 12),
  (1856912171081854548847896352, 20),
  (1953626190534138310397266976, 12),
  (1856912171081828160694651936, 12),
  (1856912171081836956777188768, 12),
  (1856912171081814966555119008, 12),
  (1856912124964976772513795488, 12),
  (1856912124964967976410288416, 12),
  (1856912124964954782270755107, 12),
  (1856912124964954782270755488, 12),
  (1856912171081836957179841125, 12),
  (913114838802146263648, 57),
  (913114816811924193888, 57),
  (913114816811913708133, 57),
  (1856912171082096440990764261, 12),
  (1856912171082127227310050656, 16),
  (1856912171082096440999152992, 16),
  (1856912171082096440984472935, 16),
  (1856912189528840514704510304, 16),
  (1856912189528840514694024549, 16),
  (1856912124965267043046657376, 16),
  (1856912124965267043036171621, 16),
  (1856912124965236256721079655, 16),
  (1856912124965236256725273957, 16)]
def rows83 : List Row := [
  (1856912124964967976282361952, 12),
  (1856912124964967976276070499, 12),
  (1856912124964954782142828643, 8),
  (1856912171081845752746485543, 20),
  (1856912189528581030367209253, 16),
  (1856912189528598622544865061, 20),
  (1856912124964985568476800937, 20),
  (1856912124964985568480995239, 20),
  (1856912171081836956777188896, 12),
  (1856912124964976772513795616, 12),
  (1856912171081836957454567653, 12),
  (1856912171082096440990764389, 16),
  (1856912171082096440994958691, 16),
  (1856912189528840514700316003, 16),
  (1856912124965267043042463075, 16)]
def rows84 : List Row := [
  (1856912171081828160549949408, 12),
  (1856912124964967976276070373, 12),
  (1856912171081814966410416480, 12),
  (1856912124964976772369092960, 12),
  (1856912124964954782136537445, 12),
  (1856912171081828160684166691, 12),
  (1856912124964967976420773411, 12),
  (1856912171081814966544634144, 12),
  (1856912124964976772503310624, 12),
  (1856912124964954782281240864, 12),
  (1856912124964954782270755744, 12),
  (931561582875855815264, 557),
  (885444722691592421984, 12),
  (885444722691581936229, 12),
  (931561560885633745504, 567),
  (885444700701359866469, 12),
  (931561560885623259749, 567),
  (1856912171082096440994958565, 12),
  (1856912189528840514708704608, 16),
  (1856912189528840514694024551, 16),
  (1856912124965267043050851680, 16),
  (1856912124965267043036171623, 16),
  (1856912124965236256725273959, 16)]
def rows85 : List Row := [
  (1856912171081828160549949536, 12),
  (1856912124964967976276070501, 12),
  (1856912124964967976282362208, 12),
  (1856912124964967976276071136, 12),
  (1856912124964954782142829280, 12),
  (1856912124964954782136538208, 12),
  (1856912171081836956661851943, 24),
  (1856912171081854548839507751, 20),
  (1856912189528589826460231461, 16),
  (1856912124964994364569823145, 20),
  (1856912124964994364574017447, 20),
  (1856912171081828160694652320, 12),
  (1856912124964967976410288419, 12),
  (1856912124964967976410288800, 12),
  (1856912124964954782270755491, 12),
  (1953626190534406590418653920, 8),
  (1856912171082127227316342112, 16),
  (1856912171082127227310050659, 16),
  (1856912171082096440990764391, 16),
  (1856912171082096440994958693, 16),
  (1856912171082096440999152995, 16),
  (1856912189528840514700316005, 16),
  (1856912189528840514704510307, 16),
  (1856912124965267043042463077, 16),
  (1856912124965267043046657379, 16)]
def rows86 : List Row := [
  (1856912124964967976282361955, 12),
  (1856912124964954782136538336, 12),
  (1856912171081836956777188899, 12),
  (1856912124964976772513795619, 12)]
def rows87 : List Row := [
  (1856912171081828160556240864, 12),
  (1856912124964967976282361829, 12),
  (1856912171081828160549949792, 12),
  (1856912171081814966416707936, 12),
  (1856912124964967976276070757, 12),
  (1856912124964976772375384416, 12),
  (1856912124964954782142828901, 12),
  (1856912171081814966410416864, 12),
  (1856912124964976772369093344, 12),
  (1856912124964954782136537829, 12),
  (1856912171081845752754874151, 20),
  (1856912171081836956787674528, 12),
  (1856912171081828160684167456, 12),
  (1856912171081814966544634147, 12),
  (1856912124964967976420774176, 12),
  (1856912124964976772503310627, 12),
  (1856912124964954782281240867, 12),
  (1856912171081814966544634528, 12),
  (1856912124964976772503311008, 12),
  (1856912124964954782281241248, 12),
  (1856912124964967976410289056, 16),
  (913114838802156749408, 57),
  (913114838802146263653, 57),
  (913114816811924193893, 57),
  (1856912171082127227320536416, 16),
  (1856912171082127227310050661, 16),
  (1856912171082096440994958695, 16),
  (1856912171082096440999152997, 16),
  (1856912189528840514700316007, 16),
  (1856912189528840514704510309, 16),
  (1856912189528840514708704611, 16),
  (1856912124965267043042463079, 16),
  (1856912124965267043046657381, 16),
  (1856912124965267043050851683, 16)]
def rows88 : List Row := [
  (1856912171081828160556240992, 12),
  (1856912171081828160549949539, 12),
  (1856912124964967976282361957, 12),
  (1856912124964967976282362592, 12),
  (1856912124964967976276071520, 12),
  (1856912124964954782142829664, 12),
  (1856912124964967976410288803, 12),
  (1856912124964954782270756256, 16),
  (1953626190534406590418654304, 8),
  (1856912171082127227316342115, 16)]
def rows89 : List Row := [
  (1856912171081836956642972000, 12),
  (1856912124964976772369092965, 12),
  (1856912124964967976276071648, 12),
  (1856912124964954782142829792, 12),
  (1856912124964954782136538339, 12),
  (1856912124964954782136538720, 12),
  (1856912171081854548847896359, 20),
  (1856912171081836956777189664, 12),
  (1856912124964976772513796384, 12),
  (1856912171081814966544634784, 12),
  (1856912124964976772503311264, 12),
  (1856912124964954782281241504, 12),
  (1953626190534406590418654432, 8),
  (931561582875866301024, 557),
  (885444722691592421989, 12),
  (931561582875855815269, 557),
  (931561560885633745509, 567),
  (1856912171082127227324730720, 16),
  (1856912171082127227310050663, 16),
  (1856912171082096440999152999, 16),
  (1856912189528840514704510311, 16),
  (1856912189528840514708704613, 16),
  (1856912124965267043046657383, 16),
  (1856912124965267043050851685, 16)]
def rows90 : List Row := [
  (1856912171081828160549949541, 12),
  (1856912171081828160556241248, 12),
  (1856912124964967976282362213, 12),
  (1856912171081828160549950176, 12),
  (1856912171081814966416708320, 12),
  (1856912124964967976276071141, 12),
  (1856912124964976772375384800, 12),
  (1856912124964954782142829285, 12),
  (1856912171081814966410417248, 12),
  (1856912124964976772369093728, 12),
  (1856912124964954782136538213, 12),
  (1856912171081828160684167459, 12),
  (1856912124964967976420774179, 12),
  (1856912171081828160684167840, 12),
  (1856912171081814966544634531, 12),
  (1856912124964967976420774560, 12),
  (1856912124964976772503311011, 12),
  (1856912124964954782281241251, 12),
  (1856912124964954782270756512, 16),
  (1953626190534406590429139680, 8),
  (1856912171082127227316342117, 16),
  (1856912171082127227320536419, 16)]
def rows91 : List Row := [
  (1856912171081828160556240995, 12),
  (1856912124964967976282362976, 12),
  (1856912171081814966410417376, 12),
  (1856912124964976772369093856, 12),
  (1856912124964954782136538341, 12),
  (1856912124964954782270756259, 16),
  (1856912189528840514708704615, 16),
  (1856912124965267043050851687, 16)]
def rows92 : List Row := [
  (1856912171081836956649263456, 12),
  (1856912124964976772375384421, 12),
  (1856912171081836956642972384, 12),
  (1856912124964976772369093349, 12),
  (1856912124964967976282363104, 12),
  (1856912124964967976276071651, 12),
  (1856912124964954782142829795, 12),
  (1856912124964967976276072032, 12),
  (1856912124964954782142830176, 12),
  (1856912124964954782136538723, 12),
  (1856912124964954782136539104, 12),
  (1856912171081836956777189667, 12),
  (1856912124964976772513796387, 12),
  (1856912171081836956777190048, 12),
  (1856912124964976772513796768, 12),
  (1856912171081828160684168096, 16),
  (1856912124964967976420774816, 16),
  (1953626190534406590418654435, 8),
  (1953626190534406590418654816, 8),
  (913114838802156749413, 57),
  (1856912171082127227316342119, 16),
  (1856912171082127227320536421, 16),
  (1856912171082127227324730723, 16)]
def rows93 : List Row := [
  (1856912171081828160556240997, 12),
  (1856912171081828160556241632, 12),
  (1856912124964967976282362597, 12),
  (1856912171081828160549950560, 12),
  (1856912171081814966416708704, 12),
  (1856912124964967976276071525, 12),
  (1856912124964976772375385184, 12),
  (1856912124964954782142829669, 12),
  (1856912171081828160684167843, 12),
  (1856912124964967976420774563, 12),
  (1856912171081814966544635296, 16),
  (1856912124964976772503311776, 16),
  (1856912124964954782281242016, 16),
  (1953626190534406590429140064, 8)]
def rows94 : List Row := [
  (1856912171081828160549950688, 12),
  (1856912171081814966416708832, 12),
  (1856912171081814966410417379, 12),
  (1856912124964967976276071653, 12),
  (1856912124964976772375385312, 12),
  (1856912124964976772369093859, 12),
  (1856912124964954782142829797, 12),
  (1856912171081814966410417760, 12),
  (1856912124964976772369094240, 12),
  (1856912124964954782136538725, 12),
  (1856912124964954782136539360, 12),
  (1856912171081836956777190304, 12),
  (1856912171081814966555120544, 12),
  (1856912189528572234393719712, 16),
  (1856912124964967976424969120, 16),
  (1856912124964967976410289063, 16),
  (1856912124964976772513797024, 12),
  (931561582875866301029, 557),
  (1953626190534406590429140192, 8),
  (1856912171082127227320536423, 16),
  (1856912171082127227324730725, 16)]
def rows95 : List Row := [
  (1856912171081836956649263840, 12),
  (1856912124964976772375384805, 12),
  (1856912171081836956642972768, 12),
  (1856912124964976772369093733, 12),
  (1856912124964967976282363107, 12),
  (1856912124964967976282363488, 12),
  (1856912124964967976276072035, 12),
  (1856912124964954782142830179, 12),
  (1856912124964967976276072416, 12),
  (1856912124964954782142830560, 12),
  (1856912124964954782136539107, 12),
  (1856912171081836956777190051, 12),
  (1856912124964976772513796771, 12),
  (1856912189528559040254186912, 16),
  (1856912124964985568596333984, 16),
  (1856912124964954782285436320, 16),
  (1856912124964954782270756263, 16),
  (1856912171081814966544635552, 20),
  (1856912124964976772503312032, 16),
  (1856912124964954782281242272, 16),
  (1953626190534406590418654819, 8),
  (1953626190534406590418655200, 8)]
def rows96 : List Row := [
  (96, 31),
  (1856912171081828160556242016, 12),
  (1856912124964967976282362981, 12),
  (1856912171081836956642972896, 12),
  (1856912171081814966410417381, 12),
  (1856912124964976772369093861, 12),
  (1856912171081814966544635299, 16),
  (1856912124964976772503311779, 16),
  (1856912124964954782281242019, 16),
  (1856912171082127227324730727, 16)]
def rows97 : List Row := [
  (1856912171081828160556242144, 12),
  (1856912171081828160549950691, 12),
  (1856912171081814966416708835, 12),
  (1856912124964967976282363109, 12),
  (1856912124964976772375385315, 12),
  (1856912171081828160549951072, 12),
  (1856912171081814966416709216, 12),
  (1856912171081814966410417763, 12),
  (1856912124964967976276072037, 12),
  (1856912124964976772375385696, 12),
  (1856912124964976772369094243, 12),
  (1856912124964954782142830181, 12),
  (1856912171081814966410418144, 12),
  (1856912124964976772369094624, 12),
  (1856912124964954782136539109, 12),
  (1856912124964967976276072672, 12),
  (1856912124964954782142830816, 12),
  (1856912124964954782136539744, 12),
  (1856912171081828160694653856, 16),
  (1856912189528559040254187168, 16),
  (1856912124964985568596334240, 16),
  (1856912124964954782285436576, 16),
  (1856912124964954782270756519, 16),
  (1953626190534406590418655456, 8),
  (1953626190534406590429140195, 8),
  (1953626190534406590429140576, 8),
  (224, 17)]
def rows98 : List Row := [
  (1856912171081836956649264224, 12),
  (1856912124964976772375385189, 12),
  (1856912124964967976282363491, 12),
  (1856912124964967976282363872, 12),
  (1856912124964967976276072419, 12),
  (1856912124964954782142830563, 12),
  (1856912171081836956777190816, 16),
  (1856912189528559040254186915, 16),
  (1856912124964976772513797536, 16),
  (1856912124964985568596333987, 16),
  (1856912124964954782285436323, 16),
  (1953626190534406590418655203, 8)]
def rows99 : List Row := [
  (1856912171081828160549950693, 12),
  (1856912171081836956649264352, 12),
  (1856912171081836956642972899, 12),
  (1856912171081814966416708837, 12),
  (1856912124964976772375385317, 12),
  (1856912171081836956642973280, 12),
  (1856912171081814966410417765, 12),
  (1856912124964976772369094245, 12),
  (1856912171081814966410418400, 12),
  (1856912124964976772369094880, 12),
  (1856912124964954782136539365, 12),
  (1856912171081828160698848160, 16),
  (1856912171081828160684168103, 16),
  (1856912171081836956787676064, 12),
  (1856912189528572234404205472, 16),
  (1856912124964967976420774823, 16)]
def rows100 : List Row := [
  (1856912171081828160556242147, 12),
  (1856912171081828160556242528, 12),
  (1856912171081828160549951075, 12),
  (1856912171081814966416709219, 12),
  (1856912124964967976282363493, 12),
  (1856912124964976772375385699, 12),
  (1856912171081828160549951456, 12),
  (1856912171081814966416709600, 12),
  (1856912171081814966410418147, 12),
  (1856912124964967976276072421, 12),
  (1856912124964976772375386080, 12),
  (1856912124964976772369094627, 12),
  (1856912124964954782142830565, 12),
  (1856912124964967976282364128, 12),
  (1856912124964967976276073056, 12),
  (1856912124964954782142831200, 12),
  (1856912124964954782136540128, 12),
  (1856912171081845752870213024, 16),
  (1856912171081814966559315360, 16),
  (1856912171081814966544635303, 16),
  (1856912189528581030486742432, 16),
  (1856912189528559040264672672, 16),
  (1856912124964976772517991840, 16),
  (1856912124964976772503311783, 16),
  (1856912124964985568606819744, 16),
  (1856912124964954782281242023, 16),
  (1856912171081836956777191072, 20),
  (1856912171081814966555121312, 20),
  (1856912124964976772513797792, 16),
  (1953626190534406590418655840, 8),
  (1953626190534406590429140579, 8),
  (1953626190534406590429140960, 8)]
def rows101 : List Row := [
  (1856912171081836956642972901, 12),
  (1856912124964967976282363875, 12),
  (1856912124964954782136540256, 12),
  (1856912189528572234408399776, 16),
  (1856912189528572234393719719, 16),
  (1856912124964967976424969127, 16),
  (1856912171081836956777190819, 16),
  (1856912124964976772513797539, 16),
  (422212934828448, 77)]
def rows102 : List Row := [
  (1856912171081828160556242149, 12),
  (1856912171081836956649264355, 12),
  (1856912171081828160549951077, 12),
  (1856912171081836956649264736, 12),
  (1856912171081836956642973283, 12),
  (1856912171081814966416709221, 12),
  (1856912124964976772375385701, 12),
  (1856912171081836956642973664, 12),
  (1856912171081814966410418149, 12),
  (1856912124964976772369094629, 12),
  (1856912171081828160549951712, 12),
  (1856912171081814966416709856, 12),
  (1856912124964967976276072677, 12),
  (1856912124964976772375386336, 12),
  (1856912124964954782142830821, 12),
  (1856912171081814966410418784, 12),
  (1856912124964976772369095264, 12),
  (1856912124964954782136539749, 12),
  (1856912189528589826579764640, 16),
  (1856912189528559040254186919, 16),
  (1856912124964985568611014048, 16),
  (1856912124964985568596333991, 16),
  (1856912124964954782285436327, 16),
  (1856912171081845752870213280, 20),
  (1856912171081814966559315616, 20),
  (1856912171081814966544635559, 20),
  (1856912189528581030486742688, 16),
  (1856912189528559040264672928, 16),
  (1856912124964976772517992096, 16),
  (1856912124964976772503312039, 16),
  (1856912124964985568606820000, 16),
  (1856912124964954782281242279, 16),
  (1953626190534406590429141216, 8),
  (422212934828576, 57),
  (422213203263904, 39)]
def rows103 : List Row := [
  (1856912171081828160556242531, 12),
  (1856912171081828160556242912, 12),
  (1856912171081828160549951459, 12),
  (1856912171081814966416709603, 12),
  (1856912124964967976282363877, 12),
  (1856912124964976772375386083, 12),
  (1856912124964967976282364512, 12),
  (1856912124964967976276073440, 12),
  (1856912124964954782142831584, 12),
  (1856912171081845752870213027, 16),
  (1856912171081814966559315363, 16),
  (1856912189528581030486742435, 16),
  (1856912189528559040264672675, 16),
  (1856912124964976772517991843, 16),
  (1856912124964985568606819747, 16),
  (1953626190534406590418656224, 8),
  (1953626190534406590429140963, 8)]
def rows104 : List Row := [
  (1856912171081836956649264357, 12),
  (1856912171081836956642973285, 12),
  (1856912171081836956642973920, 12),
  (1856912124964976772369094885, 12),
  (1856912124964967976276073568, 12),
  (1856912124964954782142831712, 12),
  (1856912124964954782136540259, 12),
  (1856912124964954782136540640, 12),
  (1856912171081854548963235488, 20),
  (1856912189528589826579764896, 16),
  (1856912189528559040268867232, 16),
  (1856912189528559040254187175, 16),
  (1856912124964985568611014304, 16),
  (1856912124964985568596334247, 16),
  (1856912124964954782285436583, 16),
  (1953626190534406590418656352, 8)]
def rows105 : List Row := [
  (1856912171081828160556242533, 12),
  (1856912171081836956649264739, 12),
  (1856912171081828160549951461, 12),
  (1856912171081836956649265120, 12),
  (1856912171081836956642973667, 12),
  (1856912171081814966416709605, 12),
  (1856912124964976772375386085, 12),
  (1856912171081828160556243168, 12),
  (1856912124964967976282364133, 12),
  (1856912171081828160549952096, 12),
  (1856912171081814966416710240, 12),
  (1856912124964967976276073061, 12),
  (1856912124964976772375386720, 12),
  (1856912124964954782142831205, 12),
  (1856912171081814966410419168, 12),
  (1856912124964976772369095648, 12),
  (1856912124964954782136540133, 12),
  (1856912171081836956791870880, 16),
  (1856912171081836956777190823, 16),
  (1856912189528581030497228192, 16),
  (1856912189528589826579764643, 16),
  (1856912124964976772513797543, 16),
  (1856912124964985568611014051, 16),
  (1856912171081836956787676832, 20),
  (1953626190534406590429141600, 8)]
def rows106 : List Row := [
  (1856912171081828160556242915, 12),
  (1856912124964967976282364896, 12),
  (1856912171081814966410419296, 12),
  (1856912124964976772369095776, 12),
  (1856912124964954782136540261, 12),
  (1856912171081828160698848167, 16),
  (1856912189528572234404205479, 16)]
def rows107 : List Row := [
  (1856912171081836956649264741, 12),
  (1856912171081836956642973669, 12),
  (1856912171081836956649265376, 12),
  (1856912124964976772375386341, 12),
  (1856912171081836956642974304, 12),
  (1856912124964976772369095269, 12),
  (1856912124964967976282365024, 12),
  (1856912124964967976276073571, 12),
  (1856912124964954782142831715, 12),
  (1856912124964967976276073952, 16),
  (1856912124964954782142832096, 12),
  (1856912124964954782136540643, 12),
  (1856912124964954782136541024, 12),
  (1856912171081845752884893088, 16),
  (1856912171081845752870213031, 16),
  (1856912171081814966559315367, 16),
  (1856912189528581030486742439, 16),
  (1856912189528589826590250400, 16),
  (1856912189528559040264672679, 16),
  (1856912124964976772517991847, 16),
  (1856912124964985568606819751, 16),
  (1856912171081836956791871136, 20),
  (1856912171081836956777191079, 20),
  (1856912171081845752880699040, 20),
  (1856912189528581030497228448, 16),
  (1856912124964976772513797799, 16),
  (1953626190534406590418656355, 8),
  (1953626190534406590418656736, 8)]
def rows108 : List Row := [
  (1856912171081828160556242917, 12),
  (1856912171081836956649265123, 12),
  (1856912171081828160556243552, 12),
  (1856912124964967976282364517, 12),
  (1856912171081828160549952480, 12),
  (1856912171081814966416710624, 12),
  (1856912124964967976276073445, 12),
  (1856912124964976772375387104, 12),
  (1856912124964954782142831589, 12),
  (1856912171081836956791870883, 16),
  (1856912189528581030497228195, 16),
  (1953626190534406590429141984, 8)]
def rows109 : List Row := [
  (1856912171081828160549952608, 12),
  (1856912171081814966416710752, 12),
  (1856912171081814966410419299, 12),
  (1856912124964967976276073573, 12),
  (1856912124964976772375387232, 12),
  (1856912124964976772369095779, 12),
  (1856912124964954782142831717, 12),
  (1856912171081814966410419680, 12),
  (1856912124964976772369096160, 12),
  (1856912124964954782136540645, 12),
  (1856912189528589826579764647, 16),
  (1856912124964985568611014055, 16),
  (1856912171081845752884893344, 20),
  (1856912171081845752870213287, 20),
  (1856912171081854548973721248, 20),
  (1856912171081814966559315623, 20),
  (1856912189528581030501422752, 16),
  (1856912189528581030486742695, 16),
  (1856912189528589826590250656, 16),
  (1856912189528559040264672935, 16),
  (1856912124964976772517992103, 16),
  (1856912124964985568606820007, 16),
  (1953626190534406590429142112, 8)]
def rows110 : List Row := [
  (1856912171081836956649265125, 12),
  (1856912171081836956649265760, 12),
  (1856912124964976772375386725, 12),
  (1856912171081836956642974688, 12),
  (1856912124964976772369095653, 12),
  (1856912124964967976282365027, 12),
  (1856912124964967976282365408, 16),
  (1856912124964967976276073955, 16),
  (1856912124964954782142832099, 12),
  (1856912124964967976276074336, 16),
  (1856912124964954782142832480, 12),
  (1856912124964954782136541027, 12),
  (1856912124964954782136541408, 12),
  (1856912171081845752884893091, 16),
  (1856912189528589826590250403, 16),
  (1953626190534406590418656739, 8),
  (1953626190534406590418657120, 8)]
def rows111 : List Row := [
  (1856912171081828160556243936, 12),
  (1856912124964967976282364901, 12),
  (1856912171081836956642974816, 12),
  (1856912171081814966410419301, 12),
  (1856912124964976772369095781, 12),
  (1856912171081854548977915552, 20),
  (1856912171081854548963235495, 20),
  (1856912189528589826594444960, 16),
  (1856912189528589826579764903, 16),
  (1856912124964985568611014311, 16),
  (1856913305556856973719241312, 12)]
def rows112 : List Row := [
  (1856912171081828160556244064, 16),
  (1856912171081828160549952611, 12),
  (1856912171081814966416710755, 12),
  (1856912124964967976282365029, 12),
  (1856912124964976772375387235, 12),
  (1856912171081828160549952992, 16),
  (1856912171081814966416711136, 12),
  (1856912171081814966410419683, 12),
  (1856912124964967976276073957, 16),
  (1856912124964976772375387616, 12),
  (1856912124964976772369096163, 12),
  (1856912124964954782142832101, 12),
  (1856912171081814966410420064, 12),
  (1856912124964976772369096544, 12),
  (1856912124964954782136541029, 12),
  (1856912124964954782136541664, 12),
  (1856912171081836956791870887, 16),
  (1856912189528581030497228199, 16),
  (1953626236651266774692535776, 8),
  (1953626190534406590429142115, 8),
  (1953626190534406590429142496, 8)]
def rows113 : List Row := [
  (1856912171081836956649266144, 12),
  (1856912124964976772375387109, 12),
  (1856912124964967976282365411, 16),
  (1856912124964967976282365792, 16),
  (1856912124964967976276074339, 16),
  (1856912124964954782142832483, 12),
  (1856912124964954782142832864, 12),
  (1856912124964954782136541411, 12),
  (1953626190534406590418657123, 8),
  (1953626190534406590418657504, 8)]
def rows114 : List Row := [
  (1856912171081828160549952613, 12),
  (1856912171081836956649266272, 12),
  (1856912171081836956642974819, 12),
  (1856912171081814966416710757, 12),
  (1856912124964976772375387237, 12),
  (1856912171081836956642975200, 12),
  (1856912171081814966410419685, 12),
  (1856912124964967976290754016, 16),
  (1856912124964967976276073959, 16),
  (1856912124964976772369096165, 12),
  (1856912171081845752884893095, 16),
  (1856912189528589826590250407, 16),
  (1856912171081836956791871143, 20),
  (1856912189528581030497228455, 16),
  (1856912124965236256710591392, 8),
  (1856912124965799206395577248, 8),
  (1856913333226973084283568736, 12),
  (1856913305556856973725532768, 12)]
def rows115 : List Row := [
  (1856912171081828160556244067, 16),
  (1856912171081828160556244448, 16),
  (1856912171081828160549952995, 16),
  (1856912171081814966416711139, 12),
  (1856912124964967976282365413, 16),
  (1856912124964976772375387619, 12),
  (1856912171081828160549953376, 16),
  (1856912171081814966416711520, 12),
  (1856912171081814966410420067, 12),
  (1856912124964967976276074341, 16),
  (1856912124964976772375388000, 12),
  (1856912124964976772369096547, 12),
  (1856912124964954782142832485, 12),
  (1856912171081814966410420448, 12),
  (1856912124964976772369096928, 12),
  (1856912124964954782136541413, 12),
  (1856912124964954782142833120, 12),
  (1856912124964954782136542048, 16),
  (1953626190534406590418657760, 8),
  (1953626236651266774692535779, 8),
  (1953626236651266774692536160, 8),
  (1953626190534406590429142499, 8),
  (1953626190534406590429142880, 8),
  (1856912124965799206664012704, 8)]
def rows116 : List Row := [
  (1856912171081836956642974821, 12),
  (1856912124964967976282365795, 16),
  (1856912124964954782142832867, 12),
  (1856912171081845752884893351, 20),
  (1856912189528589826590250663, 16),
  (1914940564306738456693834720, 8),
  (1953626190534406590418657507, 8),
  (1856912124965236256710591648, 8),
  (1856912124965236257113244640, 8),
  (1856912124965799206395577504, 8),
  (1856913351673717157993120352, 12),
  (1856913305556878963951796832, 12),
  (1856913305556856973729727072, 12),
  (1856913305556856973719241317, 12)]
def rows117 : List Row := [
  (1856912124964954782136534176, 8),
  (1856912171081828160556244069, 16),
  (1856912171081836956649266275, 12),
  (1856912171081828160549952997, 16),
  (1856912171081836956649266656, 12),
  (1856912171081836956642975203, 12),
  (1856912171081814966416711141, 12),
  (1856912124964967976282365415, 16),
  (1856912124964967976290754019, 16),
  (1856912124964976772375387621, 12),
  (1856912171081836956642975584, 12),
  (1856912171081814966410420069, 12),
  (1856912124964967976290754400, 16),
  (1856912124964967976276074343, 16),
  (1856912124964976772369096549, 12),
  (1856912171081814966410420704, 12),
  (1856912124964976772369097184, 12),
  (1856912124964954782136541669, 12),
  (1856912124965236256716882848, 8),
  (1856912124965236256710591395, 8),
  (1856912124965236256710591776, 8),
  (1856912124965812400535110560, 8),
  (1856912124965799206395577251, 8),
  (1856912124965799206395577632, 8),
  (1856913333226973084289860192, 12)]
def rows118 : List Row := [
  (1856912124964954782136534304, 8),
  (1856912171081828160556244451, 16),
  (1856912171081828160556244832, 20),
  (1856912171081828160549953379, 16),
  (1856912171081814966416711523, 12),
  (1856912124964967976282365797, 16),
  (1856912124964976772375388003, 12),
  (1856912171081814966416711904, 12),
  (1856912171081814966410420451, 12),
  (1856912124964976772375388384, 12),
  (1856912124964976772369096931, 12),
  (1856912124964954782142832869, 12),
  (1856912124964954782142833504, 16),
  (1856912171081854548977915559, 20),
  (1953626236651266774692536163, 8),
  (1953626236651266774692536544, 8),
  (1953626190534406590429142883, 8),
  (1953626190534406590429143264, 8),
  (1856912124965236257247462560, 8),
  (1856912124965812400803546016, 8),
  (1856912124965799206670304160, 8),
  (1856912124965799206664012707, 8)]
def rows119 : List Row := [
  (1856912171081828160556244071, 16),
  (1856912171081836956649266277, 12),
  (1856912171081828160564633056, 16),
  (1856912171081828160549952999, 16),
  (1856912171081836956642975205, 12),
  (1856912124964967976290754021, 16),
  (1914940564306738456700126176, 8),
  (1856912124965236256716883104, 8),
  (1856912124965236257119536096, 8),
  (1856912124965236257113245024, 8),
  (1856912124965236257247462688, 12),
  (1856912124965812400535110816, 8),
  (1856913333226995074516124256, 12),
  (1856913333226973084294054496, 12),
  (1856913333226973084283568741, 12),
  (1856913351673717157999411808, 12),
  (1856913305556878963958088288, 12),
  (1856913305556856973725532773, 12)]
def rows120 : List Row := [
  (1856912124964967976276067488, 8),
  (1856912124964954782142825632, 8),
  (1856912171081828160556244453, 16),
  (1856912171081836956649266659, 12),
  (1856912171081828160549953381, 16),
  (1856912171081836956649267040, 12),
  (1856912171081836956642975587, 12),
  (1856912171081814966416711525, 12),
  (1856912124964967976282365799, 16),
  (1856912124964967976290754403, 16),
  (1856912124964976772375388005, 12),
  (1856912171081836956642975968, 12),
  (1856912171081814966410420453, 12),
  (1856912124964976772369096933, 12),
  (1856912171081814966416712160, 12),
  (1856912124964976772375388640, 12),
  (1856912124964954782142833125, 12),
  (1856912171081814966410421088, 16),
  (1856912124964976772369097568, 16),
  (1856912124964954782136542053, 16),
  (1856912124964954782673405216, 8),
  (1953626236651266774692536800, 8),
  (1953626236651266774703021920, 8),
  (1953626190534406590429143520, 8),
  (1856912124965236256716882851, 8),
  (1856912124965236256716883232, 8),
  (1856912124965236256710591779, 8),
  (1856912124965236256710592160, 8),
  (1856912124965236257113245152, 12),
  (1856912124965812400535110944, 8),
  (1856912124965799206395577635, 8),
  (1856912124965799206395578016, 16)]
def rows121 : List Row := [
  (1914940564306456981717124768, 8),
  (1856912124964967976276067616, 8),
  (1856912124964954782142825760, 8),
  (1856912124964954782136534307, 8),
  (1856912124964954782136534688, 8),
  (1856912124964967976290754023, 16),
  (1856912171081828160556244835, 20),
  (1856912171081814966416711907, 12),
  (1856912124964976772375388387, 12),
  (1856912124964954782136542816, 16),
  (1953626236651266774692536547, 8),
  (1953626190534406590429143267, 8),
  (1856912124965812400809837472, 8),
  (1856912124965799206670304163, 8),
  (1856913351673739148225675872, 12),
  (1856913351673717158003606112, 12),
  (1856913351673717157993120357, 12),
  (1856913305556856973729727077, 12)]
def rows122 : List Row := [
  (1856912171081828160556244455, 16),
  (1856912171081828160564633059, 16),
  (1856912171081836956649266661, 12),
  (1856912171081828160564633440, 16),
  (1856912171081828160549953383, 16),
  (1856912171081836956642975589, 12),
  (1856912124964967976290754405, 16),
  (1856912171081836956642976224, 12),
  (1856912124964976772369097189, 12),
  (1856912189528559040119972704, 16),
  (1856912124964985568462119776, 16),
  (1856912124964954782151222112, 16),
  (1856912124964954782136542055, 16),
  (1856912124964954782136542944, 16),
  (1856912124965236256710592416, 8),
  (1856912124965236257119536480, 8),
  (1856912124965236257247462691, 12),
  (1856913333226995074522415712, 12),
  (1856913333226973084289860197, 12)]
def rows123 : List Row := [
  (1914940564306456981717125024, 8),
  (1856912124964967976282358944, 8),
  (1856912124964954782136534944, 8),
  (1856912171081828160556244837, 20),
  (1856912171081836956649267043, 12),
  (1856912171081836956649267424, 12),
  (1856912171081836956642975971, 12),
  (1856912171081814966416711909, 12),
  (1856912124964976772375388389, 12),
  (1856912171081814966416712544, 16),
  (1856912124964976772375389024, 16),
  (1856912124964954782142833509, 16),
  (1856912124964967976812938528, 8),
  (1856912124964954782673405219, 8),
  (1856912124964954782673405600, 8),
  (1953626236651266774703021923, 8),
  (1953626236651266774703022304, 8),
  (1856912124965236256716883235, 8),
  (1856912124965236256716883616, 8),
  (1856912124965236256710592163, 8),
  (1856912124965236257119536608, 12),
  (1856912124965236257113245155, 12),
  (1856912124965812400535111328, 24),
  (1856912124965799206395578019, 16)]
def rows124 : List Row := [
  (1914940564306470175856658080, 8),
  (1914940564306456981723416224, 8),
  (1914940564306456981717124771, 8),
  (1856912124964967976282359072, 8),
  (1856912124964967976276067619, 8),
  (1856912124964967976276068000, 8),
  (1856912124964954782142826144, 8),
  (1856912124964954782136534691, 8),
  (1856912171081828160564633061, 16),
  (1856912124964967976290754407, 16),
  (1856912124964954782142834272, 16),
  (1856912124964954782941841056, 8),
  (1856912171082096441521341728, 12),
  (1856912124965258247480018208, 12),
  (1856912124965236257257948448, 12),
  (1856912124965236257247462693, 12),
  (1856913333226973084294054501, 12),
  (1856913351673739148231967328, 12),
  (1856913351673717157999411813, 12)]
def rows125 : List Row := [
  (1856912171081828160556244839, 20),
  (1856912171081828160564633443, 16),
  (1856912171081836956649267045, 12),
  (1856912171081836956642975973, 12),
  (1856912171081836956649267680, 12),
  (1856912124964976772375388645, 12),
  (1856912171081836956642976608, 16),
  (1856912189528559040126264160, 16),
  (1856912124964976772369097573, 16),
  (1856912124964985568468411232, 16),
  (1856912124964954782142833511, 16),
  (1856912124964954782142834400, 20),
  (1856912124964954782136542947, 16),
  (1856912124964954782673405856, 8),
  (1953626236651266774703022560, 8),
  (1856912124965236256716883872, 8),
  (1856912124965236256710592800, 8),
  (1856912171082096441387124192, 12),
  (1856912124965258247345800672, 12),
  (1856912124965236257123730912, 12),
  (1856912124965236257113245157, 12),
  (1856912171082659390669457056, 16),
  (1856912124965821196628133536, 16),
  (1856912124965799206406063776, 16),
  (1856912124965799206395578021, 16)]
def rows126 : List Row := [
  (1914940564306470175856658336, 8),
  (1914940564306456981723416480, 8),
  (1856912124964967976276068256, 8),
  (1856912124964954782142826400, 8),
  (1856912124964954782136535328, 8),
  (1856912171081828160564633063, 16),
  (1856912171081836956649267427, 12),
  (1856912171081814966410421856, 16),
  (1856912124964976772369098336, 16),
  (1856912124964954782136542821, 16),
  (1856912124964967976812938531, 8),
  (1856912124964967976812938912, 8),
  (1856912124964954782673405603, 8),
  (1856912124964954782941841312, 12),
  (1953626236651266774703022307, 8),
  (1856912124965236256716883619, 8),
  (1856912124965236257119536611, 12),
  (1856913351673717158003606117, 12)]
def bucket : ℕ → List Row
  | 0 => rows0
  | 1 => rows1
  | 2 => rows2
  | 3 => rows3
  | 4 => rows4
  | 5 => rows5
  | 6 => rows6
  | 7 => rows7
  | 8 => rows8
  | 9 => rows9
  | 10 => rows10
  | 11 => rows11
  | 12 => rows12
  | 13 => rows13
  | 14 => rows14
  | 15 => rows15
  | 16 => rows16
  | 17 => rows17
  | 18 => rows18
  | 19 => rows19
  | 20 => rows20
  | 21 => rows21
  | 22 => rows22
  | 23 => rows23
  | 24 => rows24
  | 25 => rows25
  | 26 => rows26
  | 27 => rows27
  | 28 => rows28
  | 29 => rows29
  | 30 => rows30
  | 31 => rows31
  | 32 => rows32
  | 33 => rows33
  | 34 => rows34
  | 35 => rows35
  | 36 => rows36
  | 37 => rows37
  | 38 => rows38
  | 39 => rows39
  | 40 => rows40
  | 41 => rows41
  | 42 => rows42
  | 43 => rows43
  | 44 => rows44
  | 45 => rows45
  | 46 => rows46
  | 47 => rows47
  | 48 => rows48
  | 49 => rows49
  | 50 => rows50
  | 51 => rows51
  | 52 => rows52
  | 53 => rows53
  | 54 => rows54
  | 55 => rows55
  | 56 => rows56
  | 57 => rows57
  | 58 => rows58
  | 59 => rows59
  | 60 => rows60
  | 61 => rows61
  | 62 => rows62
  | 63 => rows63
  | 64 => rows64
  | 65 => rows65
  | 66 => rows66
  | 67 => rows67
  | 68 => rows68
  | 69 => rows69
  | 70 => rows70
  | 71 => rows71
  | 72 => rows72
  | 73 => rows73
  | 74 => rows74
  | 75 => rows75
  | 76 => rows76
  | 77 => rows77
  | 78 => rows78
  | 79 => rows79
  | 80 => rows80
  | 81 => rows81
  | 82 => rows82
  | 83 => rows83
  | 84 => rows84
  | 85 => rows85
  | 86 => rows86
  | 87 => rows87
  | 88 => rows88
  | 89 => rows89
  | 90 => rows90
  | 91 => rows91
  | 92 => rows92
  | 93 => rows93
  | 94 => rows94
  | 95 => rows95
  | 96 => rows96
  | 97 => rows97
  | 98 => rows98
  | 99 => rows99
  | 100 => rows100
  | 101 => rows101
  | 102 => rows102
  | 103 => rows103
  | 104 => rows104
  | 105 => rows105
  | 106 => rows106
  | 107 => rows107
  | 108 => rows108
  | 109 => rows109
  | 110 => rows110
  | 111 => rows111
  | 112 => rows112
  | 113 => rows113
  | 114 => rows114
  | 115 => rows115
  | 116 => rows116
  | 117 => rows117
  | 118 => rows118
  | 119 => rows119
  | 120 => rows120
  | 121 => rows121
  | 122 => rows122
  | 123 => rows123
  | 124 => rows124
  | 125 => rows125
  | 126 => rows126
  | _ => []

def key (ps : List Slot) : ℕ :=
  ps.foldl (fun acc (p, e) => acc*(65536*32)+p*32+(e.map (·+1)).getD 0) 0

def decodeKey : ℕ → ℕ → List Slot
  | 0, _ => []
  | fuel+1, k =>
    if k = 0 then []
    else
      let digit := k % (65536*32)
      let e := digit % 32
      decodeKey fuel (k / (65536*32)) ++
        [(digit / 32, if e = 0 then none else some (e-1))]

def decodeStep (step : ℕ) : Bool × ℕ := (step % 2 == 1, step / 2)

def plan : Plan := fun ps =>
  let k := key ps
  if decodeKey 5 k = ps then
    ((bucket (k % 127)).lookup k).map decodeStep
  else none

def cap : ℕ := 320

def primeTable : List ℕ :=
  (List.range cap).filter (fun q => decide (q.Prime ∧ Odd q ∧ q ≠ 5))

theorem primeTable_complete : PrimeTableComplete primeTable cap := by
  intro q hprime hodd hne hcap
  simp [primeTable, hprime, hodd, hne, hcap]

theorem primeTable_sorted : primeTable.Pairwise (· < ·) :=
  List.Pairwise.filter _ List.pairwise_lt_range

def checkRow (prune : List Slot → Bool) (row : Row) : Bool :=
  checkStep primeTable cap prune plan (decodeKey 5 row.1) (decodeStep row.2)

theorem lookup_member {k v : ℕ} {rows : List Row}
    (h : rows.lookup k = some v) : (k,v) ∈ rows := by
  induction rows with
  | nil => simp at h
  | cons row rows ih =>
    rcases row with ⟨r,s⟩
    by_cases heq : k = r
    · subst r
      simp [List.lookup] at h
      simp [h]
    · have hbeq : (k == r) = false := by simpa using heq
      have htail : rows.lookup k = some v := by simpa [List.lookup,hbeq] using h
      exact List.mem_cons_of_mem _ (ih htail)

theorem plan_checked {prune : List Slot → Bool}
    (hverified : ∀ i < 127, (bucket i).all (checkRow prune) = true)
    (ps : List Slot) (step : Bool × ℕ) (h : plan ps = some step) :
    checkStep primeTable cap prune plan ps step = true := by
  dsimp [plan] at h
  split at h
  · rename_i hkey
    cases hl : (bucket (key ps % 127)).lookup (key ps) with
    | none => simp [hl] at h
    | some raw =>
      have hs : decodeStep raw = step := by simpa [hl] using h
      have hv := List.all_eq_true.mp (hverified _ (Nat.mod_lt _ (by decide)))
        (key ps,raw) (lookup_member hl)
      simpa [checkRow,hkey,hs] using hv
  · cases h

end SigmaMixedData

open SigmaAbundancyBounds
open SigmaFiveMixedCertificate

namespace SigmaMixedModular

private theorem geometric_cast_step (m p e : ℕ) :
    (geometric p (e + 1) : ZMod m) = 1 + (p : ZMod m) * geometric p e := by
  simp [geometric]

theorem geometric_mod3_base_zero (p e : ℕ) (hp : (p : ZMod 3) = 0) :
    (geometric p e : ZMod 3) = 1 := by
  induction e with
  | zero => simp [geometric]
  | succ e ih =>
      rw [geometric_cast_step, hp, ih]
      simp

theorem geometric_mod3_base_one (p e : ℕ) (hp : (p : ZMod 3) = 1) :
    (geometric p e : ZMod 3) = (e + 1 : ℕ) := by
  induction e with
  | zero => simp [geometric]
  | succ e ih =>
      rw [geometric_cast_step, hp, ih]
      push_cast
      ring

theorem geometric_mod3_base_two_even (p e : ℕ) (hp : (p : ZMod 3) = 2)
    (he : Even e) : (geometric p e : ZMod 3) = 1 := by
  obtain ⟨k, rfl⟩ := he
  induction k with
  | zero => simp [geometric]
  | succ k ih =>
      rw [show k + 1 + (k + 1) = (k + k) + 2 by omega,
        geometric_cast_step]
      rw [show k + k + 1 = (k + k) + 1 by omega, geometric_cast_step]
      rw [hp, ih]
      decide

theorem geometric_mod4_base_one (p e : ℕ) (hp : (p : ZMod 4) = 1) :
    (geometric p e : ZMod 4) = (e + 1 : ℕ) := by
  induction e with
  | zero => simp [geometric]
  | succ e ih =>
      rw [geometric_cast_step, hp, ih]
      push_cast
      ring

theorem geometric_mod4_base_three_even (p e : ℕ) (hp : (p : ZMod 4) = 3)
    (he : Even e) : (geometric p e : ZMod 4) = 1 := by
  obtain ⟨k, rfl⟩ := he
  induction k with
  | zero => simp [geometric]
  | succ k ih =>
      rw [show k + 1 + (k + 1) = (k + k) + 2 by omega,
        geometric_cast_step]
      rw [show k + k + 1 = (k + k) + 1 by omega, geometric_cast_step]
      rw [hp, ih]
      decide

theorem odd_square_mod4 (n : ℕ) (hn : Odd n) :
    (n ^ 2 : ZMod 4) = 1 := by
  obtain ⟨k, rfl⟩ := hn
  have hcast : ((2 * k + 1 : ℕ) : ZMod 4) = 2 * (k : ZMod 4) + 1 := by
    push_cast
    ring
  rw [hcast, pow_two]
  have hfour : (4 : ZMod 4) = 0 := ZMod.natCast_self 4
  calc
    (2 * (k : ZMod 4) + 1) * (2 * (k : ZMod 4) + 1) =
        1 + 4 * (k : ZMod 4) + 4 * (k : ZMod 4) ^ 2 := by ring
    _ = 1 := by rw [hfour]; ring

private def openFour (s : Slot) : Bool := s.2.isNone && s.1 % 4 == 1

private def fixedFourThree (s : Slot) : Bool :=
  s.2.elim false (fun e => s.1 % 4 == 1 && e % 4 == 2)

private def openThree (s : Slot) : Bool := s.2.isNone && s.1 % 3 == 1

private def fixedThreeZero (s : Slot) : Bool :=
  s.2.elim false (fun e => s.1 % 3 == 1 && e % 6 == 2)

private def fixedThreeTwo (s : Slot) : Bool :=
  s.2.elim false (fun e => s.1 % 3 == 1 && e % 6 == 4)

def modularTerminal (ps : List Slot) : Bool :=
  ((ps.any (fun s => s.1 == 3)) && ps.any fixedThreeZero) ||
    (ps.length == 5 &&
      ((!ps.any openFour && !(ps.countP fixedFourThree % 2 == 1)) ||
        (ps.any (fun s => s.1 == 3) &&
          (ps.any fixedThreeZero ||
            (!ps.any openThree && !(ps.countP fixedThreeTwo % 2 == 1)))))
    )

private theorem primeOdd_mod4 (p : ℕ) (ho : Odd p) :
    (p : ZMod 4) = 1 ∨ (p : ZMod 4) = 3 := by
  obtain ⟨k, rfl⟩ := ho
  have hmod : (2 * k + 1) % 4 = 1 ∨ (2 * k + 1) % 4 = 3 := by omega
  rcases hmod with h | h
  · left
    exact (ZMod.natCast_eq_natCast_iff _ _ 4).2 (by
      change (2 * k + 1) % 4 = 1 % 4
      simpa using h)
  · right
    exact (ZMod.natCast_eq_natCast_iff _ _ 4).2 (by
      change (2 * k + 1) % 4 = 3 % 4
      simpa using h)

private theorem cast_succ_mod4 (e r : ℕ) (h : (e + 1) % 4 = r) :
    ((e + 1 : ℕ) : ZMod 4) = r := by
  exact (ZMod.natCast_eq_natCast_iff _ _ 4).2 (by
    change (e + 1) % 4 = r % 4
    have hr : r < 4 := by omega
    rw [Nat.mod_eq_of_lt hr]
    exact h)

private theorem geometric_base_one_mod4 (p e : ℕ) (hp : (p : ZMod 4) = 1)
    (he : Even e) :
    (geometric p e : ZMod 4) = if e % 4 = 2 then 3 else 1 := by
  rw [geometric_mod4_base_one p e hp]
  by_cases h : e % 4 = 2
  · rw [if_pos h]
    apply cast_succ_mod4
    have hadd : (e + 1) % 4 = ((e % 4) + (1 % 4)) % 4 := Nat.add_mod e 1 4
    rw [h] at hadd
    norm_num at hadd
    exact hadd
  · rw [if_neg h]
    have hemod : e % 4 = 0 := by
      have hmod2 : (e % 4) % 2 = 0 := by
        calc
          (e % 4) % 2 = e % 2 := Nat.mod_mod_of_dvd e (by decide : 2 ∣ 4)
          _ = 0 := Nat.even_iff.mp he
      have hr : e % 4 < 4 := Nat.mod_lt e (by decide)
      omega
    apply cast_succ_mod4
    have hadd : (e + 1) % 4 = ((e % 4) + (1 % 4)) % 4 := Nat.add_mod e 1 4
    rw [hemod] at hadd
    norm_num at hadd
    exact hadd

private theorem geometric_base_three_mod4 (p e : ℕ) (hp : (p : ZMod 4) = 3)
    (he : Even e) : (geometric p e : ZMod 4) = 1 := by
  exact geometric_mod4_base_three_even p e hp he

private theorem cast_mod_six (e : ℕ) :
    (e : ZMod 3) = ((e % 6 : ℕ) : ZMod 3) := by
  have hcast := congrArg (fun n : ℕ => (n : ZMod 3)) (Nat.mod_add_div e 6)
  push_cast at hcast
  rw [show (6 : ZMod 3) = 0 by decide] at hcast
  simpa using hcast.symm

private theorem geometric_base_one_mod3_classes (p e : ℕ)
    (hp : (p : ZMod 3) = 1) (he : Even e) :
    (geometric p e : ZMod 3) =
      if e % 6 = 2 then 0 else if e % 6 = 4 then 2 else 1 := by
  rw [geometric_mod3_base_one p e hp]
  have hsucc : ((e + 1 : ℕ) : ZMod 3) = ((e % 6 : ℕ) : ZMod 3) + 1 := by
    calc
      ((e + 1 : ℕ) : ZMod 3) = (e : ZMod 3) + 1 := by simp
      _ = ((e % 6 : ℕ) : ZMod 3) + 1 := by rw [cast_mod_six]
  have hevenMod : (e % 6) % 2 = 0 := by
    calc
      (e % 6) % 2 = e % 2 := Nat.mod_mod_of_dvd e (by decide : 2 ∣ 6)
      _ = 0 := Nat.even_iff.mp he
  have hlt : e % 6 < 6 := Nat.mod_lt e (by decide)
  have hcases : e % 6 = 0 ∨ e % 6 = 2 ∨ e % 6 = 4 := by omega
  by_cases h2 : e % 6 = 2
  · rw [if_pos h2]
    rw [hsucc]
    rw [h2]
    decide
  · by_cases h4 : e % 6 = 4
    · rw [if_neg h2, if_pos h4]
      rw [hsucc]
      rw [h4]
      decide
    · rw [if_neg h2, if_neg h4]
      rcases hcases with h0 | h2' | h4'
      · rw [hsucc]
        rw [h0]
        decide
      · exact False.elim (h2 h2')
      · exact False.elim (h4 h4')

private theorem prime_mod3_cases (p : ℕ) :
    (p : ZMod 3) = 0 ∨ (p : ZMod 3) = 1 ∨ (p : ZMod 3) = 2 := by
  have hcast : (p : ZMod 3) = ((p % 3 : ℕ) : ZMod 3) := by
    have hcast := congrArg (fun n : ℕ => (n : ZMod 3)) (Nat.mod_add_div p 3)
    push_cast at hcast
    rw [show (3 : ZMod 3) = 0 by decide] at hcast
    simpa using hcast.symm
  have hlt : p % 3 < 3 := Nat.mod_lt p (by decide)
  have hrem : p % 3 = 0 ∨ p % 3 = 1 ∨ p % 3 = 2 := by omega
  rcases hrem with h | h | h
  · left
    rw [hcast, h]
    decide
  · right; left
    rw [hcast, h]
    decide
  · right; right
    rw [hcast, h]
    decide

private theorem cast_mod3_eq (p r : ℕ) (hr : r < 3)
    (h : (p : ZMod 3) = r) : p % 3 = r := by
  have hmod := (ZMod.natCast_eq_natCast_iff p r 3).mp h
  simpa [Nat.ModEq, Nat.mod_eq_of_lt hr] using hmod

private theorem cast_mod3_from_mod (p r : ℕ) (hr : r < 3)
    (h : p % 3 = r) : (p : ZMod 3) = r := by
  have hcast : (p : ZMod 3) = ((p % 3 : ℕ) : ZMod 3) := by
    have hh := congrArg (fun n : ℕ => (n : ZMod 3)) (Nat.mod_add_div p 3)
    push_cast at hh
    rw [show (3 : ZMod 3) = 0 by decide, zero_mul, add_zero] at hh
    simpa using hh.symm
  rw [hcast, h]

private theorem divisorSum_mod3_formula {ps : List Slot} {xs : List Factor}
    (hm : Matches ps xs) (hv : Valid xs)
    (hopen : ∀ s ∈ ps, openThree s = false)
    (hzero : ∀ s ∈ ps, fixedThreeZero s = false) :
    (divisorSum xs : ZMod 3) = (2 : ZMod 3) ^ ps.countP fixedThreeTwo := by
  induction hm with
  | nil => simp [divisorSum]
  | @cons s x ps xs hst htail ih =>
    have hx := hv x (by simp)
    have htailValid : Valid xs := fun y hy => hv y (by simp [hy])
    have htailOpen : ∀ t ∈ ps, openThree t = false := by
      intro t ht
      exact hopen t (by simp [ht])
    have htailZero : ∀ t ∈ ps, fixedThreeZero t = false := by
      intro t ht
      exact hzero t (by simp [ht])
    have hpCases := prime_mod3_cases x.1
    have hloc : (geometric x.1 x.2 : ZMod 3) = if fixedThreeTwo s then 2 else 1 := by
      rcases s with ⟨p,o⟩
      have hpx : p = x.1 := by simpa using hst.1
      cases hopt : o with
      | none =>
        have hopenHead := hopen (p,o) (by simp)
        have hpnot : p % 3 ≠ 1 := by simpa [openThree,hopt] using hopenHead
        have hp0or2 : (x.1 : ZMod 3) = 0 ∨ (x.1 : ZMod 3) = 2 := by
          rcases hpCases with h0 | h1 | h2
          · exact Or.inl h0
          · have hm1 := cast_mod3_eq x.1 1 (by decide) h1
            exact False.elim (hpnot (by simpa [hpx] using hm1))
          · exact Or.inr h2
        have heven := hx.2.2.2.2
        have hfix : fixedThreeTwo (p,none) = false := by simp [fixedThreeTwo]
        rcases hp0or2 with hp0 | hp2
        · rw [if_neg (by simp [hfix])]
          exact geometric_mod3_base_zero x.1 x.2 hp0
        · rw [if_neg (by simp [hfix])]
          exact geometric_mod3_base_two_even x.1 x.2 hp2 heven
      | some e =>
        have he : x.2 = e := hst.2 _ hopt
        rcases hpCases with hp0 | hp1 | hp2
        · have hfix : fixedThreeTwo (p,some e) = false := by
            simp [fixedThreeTwo, hpx]
            intro hm1
            have hc := cast_mod3_eq p 0 (by decide) (by simpa [hpx] using hp0)
            omega
          rw [he, if_neg (by simp [hfix])]
          exact geometric_mod3_base_zero x.1 e (by simpa [hpx] using hp0)
        · have hpmod1 : x.1 % 3 = 1 := cast_mod3_eq x.1 1 (by decide) hp1
          have hgeo := geometric_base_one_mod3_classes x.1 e hp1
            (by simpa [he] using hx.2.2.2.2)
          have hnozero := hzero (p,o) (by simp)
          have hnot2 : e % 6 ≠ 2 := by
            intro he2
            simp [fixedThreeZero, hopt, hpx, hpmod1, he2] at hnozero
          by_cases hfour : e % 6 = 4
          · have hfix : fixedThreeTwo (p,some e) = true := by
              simp [fixedThreeTwo, hpx, hpmod1, hfour]
            rw [he, if_pos (by simp [hfix])]
            simpa [hfour] using hgeo
          · have hfix : fixedThreeTwo (p,some e) = false := by
              simp [fixedThreeTwo, hpx, hpmod1, hfour]
            have hezero : e % 6 = 0 := by
              have hlt := Nat.mod_lt e (by decide : 0 < 6)
              have hpar : (e % 6) % 2 = 0 := by
                calc
                  (e % 6) % 2 = e % 2 := Nat.mod_mod_of_dvd e (by decide : 2 ∣ 6)
                  _ = 0 := Nat.even_iff.mp (by simpa [he] using hx.2.2.2.2)
              omega
            rw [he, if_neg (by simp [hfix])]
            simpa [hezero] using hgeo
        · have hfix : fixedThreeTwo (p,some e) = false := by
            simp [fixedThreeTwo, hpx]
            intro hm1
            have hc := cast_mod3_eq p 2 (by decide) (by simpa [hpx] using hp2)
            omega
          rw [he, if_neg (by simp [hfix])]
          exact geometric_mod3_base_two_even x.1 e (by simpa [hpx] using hp2)
            (by simpa [he] using hx.2.2.2.2)
    change ((geometric x.1 x.2 * divisorSum xs : ℕ) : ZMod 3) = _
    push_cast
    rw [hloc, ih htailValid htailOpen htailZero]
    rw [List.countP_cons]
    by_cases hb : fixedThreeTwo s = true <;> simp [hb, pow_succ, mul_comm]

private theorem matches_slot_prime_has_factor {ps : List Slot} {xs : List Factor}
    (hm : Matches ps xs) (h : ∃ s ∈ ps, s.1 = 3) : ∃ x ∈ xs, x.1 = 3 := by
  induction hm with
  | nil =>
      rcases h with ⟨s, hs, _⟩
      simp at hs
  | @cons s x ps xs hst htail ih =>
      rcases h with ⟨t, ht, hprime⟩
      simp only [List.mem_cons] at ht
      rcases ht with rfl | ht
      · exact ⟨x, by simp, hst.1.symm.trans hprime⟩
      · obtain ⟨y, hy, hpy⟩ := ih ⟨t, ht, hprime⟩
        exact ⟨y, by simp [hy], hpy⟩

private theorem value_cast_as_prod (xs : List Factor) :
    (value xs : ZMod 3) = (xs.map fun y => (y.1 ^ y.2 : ZMod 3)).prod := by
  induction xs with
  | nil => simp [value]
  | cons y ys ih =>
      change ((y.1 ^ y.2 * value ys : ℕ) : ZMod 3) = _
      rw [Nat.cast_mul, ih]
      simp

private theorem value_mod3_zero_of_three_slot {ps : List Slot} {xs : List Factor}
    (hm : Matches ps xs) (hv : Valid xs) (hthree : ∃ s ∈ ps, s.1 = 3) :
    (value xs : ZMod 3) = 0 := by
  obtain ⟨x, hxmem, hxthree⟩ := matches_slot_prime_has_factor hm hthree
  have hfactor : (x.1 ^ x.2 : ZMod 3) = 0 := by
    have hepos : 0 < x.2 := by have h := (hv x hxmem).2.2.2.1; omega
    rw [hxthree]
    have hthree : (3 : ZMod 3) = 0 := by decide
    simp [hthree, Nat.ne_of_gt hepos]
  rw [value_cast_as_prod]
  apply List.prod_eq_zero
  rw [List.mem_map]
  exact ⟨x, hxmem, hfactor⟩

private theorem divisorSum_mod3_zero_of_fixed_slot {ps : List Slot} {xs : List Factor}
    (hm : Matches ps xs) (hv : Valid xs) (hzero : ∃ s ∈ ps, fixedThreeZero s = true) :
    (divisorSum xs : ZMod 3) = 0 := by
  induction hm with
  | nil =>
      rcases hzero with ⟨s, hs, _⟩
      simp at hs
  | @cons s x ps xs hst htail ih =>
      have hx := hv x (by simp)
      have htailValid : Valid xs := fun y hy => hv y (by simp [hy])
      rcases s with ⟨p,o⟩
      rcases hzero with ⟨t, ht, hz⟩
      simp only [List.mem_cons] at ht
      rcases ht with rfl | ht
      ·
        cases hopt : o with
        | none => simp [fixedThreeZero, hopt] at hz
        | some e =>
          have he : x.2 = e := hst.2 _ hopt
          have hz' := hz
          simp only [fixedThreeZero, hopt, Option.elim_some, Bool.and_eq_true] at hz'
          rcases hz' with ⟨hpmod, hemod⟩
          have hpmod : p % 3 = 1 := of_decide_eq_true hpmod
          have hemod : e % 6 = 2 := of_decide_eq_true hemod
          have hpx : p = x.1 := by simpa using hst.1
          have hpcast : (p : ZMod 3) = 1 := cast_mod3_from_mod p 1 (by decide) hpmod
          have hgeo := geometric_base_one_mod3_classes p e hpcast
            (by simpa [he] using hx.2.2.2.2)
          have hgeo0 : (geometric x.1 x.2 : ZMod 3) = 0 := by
            simpa [hpx, he, hemod] using hgeo
          change ((geometric x.1 x.2 * divisorSum xs : ℕ) : ZMod 3) = 0
          push_cast
          rw [hgeo0]
          simp
      · have htailZero := ih htailValid ⟨t, ht, hz⟩
        change ((geometric x.1 x.2 * divisorSum xs : ℕ) : ZMod 3) = 0
        push_cast
        rw [htailZero]
        simp

private theorem exclude_mod3_zero_prefix {ps : List Slot}
    (hthree : ∃ s ∈ ps, s.1 = 3)
    (hzero : ∃ s ∈ ps, fixedThreeZero s = true) : Excludes ps := by
  intro xs ys hm hcard hv hsort heqNe
  obtain ⟨hvx,hvy⟩ := valid_append hv
  have hsumZero := divisorSum_mod3_zero_of_fixed_slot hm hvx hzero
  have hvalZero := value_mod3_zero_of_three_slot hm hvx hthree
  have hsumTotal : (divisorSum (xs ++ ys) : ZMod 3) = 0 := by
    rw [divisorSum_append]
    push_cast
    rw [hsumZero]
    simp
  have hvalTotal : (value (xs ++ ys) : ZMod 3) = 0 := by
    rw [value_append]
    push_cast
    rw [hvalZero]
    simp
  have hRhs : ((2 * value (xs ++ ys) + 5 : ℕ) : ZMod 3) = 2 := by
    push_cast
    rw [hvalTotal]
    decide
  have hEq := congrArg (fun n : ℕ => (n : ZMod 3)) heqNe
  have h02 : (0 : ZMod 3) = 2 := by
    calc
      0 = (divisorSum (xs ++ ys) : ZMod 3) := hsumTotal.symm
      _ = ((2 * value (xs ++ ys) + 5 : ℕ) : ZMod 3) := hEq
      _ = 2 := hRhs
  exact (by decide : (0 : ZMod 3) ≠ 2) h02

private theorem exclude_mod3_wrong_product {ps : List Slot}
    (h5 : ps.length = 5) (hthree : ∃ s ∈ ps, s.1 = 3)
    (hopen : ∀ s ∈ ps, openThree s = false)
    (hzero : ∀ s ∈ ps, fixedThreeZero s = false)
    (heven : Even (ps.countP fixedThreeTwo)) : Excludes ps := by
  intro xs ys hm hcard hv hsort
  have hnil := full_has_empty_tail h5 hm hcard
  subst ys
  simp only [List.append_nil] at hv hcard hsort
  intro heq
  simp only [List.append_nil] at heq
  have hsum := divisorSum_mod3_formula hm hv hopen hzero
  have hval := value_mod3_zero_of_three_slot hm hv hthree
  have hsumOne : (divisorSum xs : ZMod 3) = 1 := by
    obtain ⟨k,hk⟩ := heven
    have htwo : (2 : ZMod 3)^2 = 1 := by decide
    have hpow : ∀ k : ℕ, (2 : ZMod 3)^(k+k) = 1 := by
      intro k
      induction k with
      | zero => simp
      | succ k ih =>
        calc
          (2 : ZMod 3)^((k+1)+(k+1)) = (2 : ZMod 3)^((k+k)+2) := by congr 1 <;> omega
          _ = (2 : ZMod 3)^(k+k) * (2 : ZMod 3)^2 := by rw [pow_add]
          _ = 1 := by rw [ih, htwo]; simp
    rw [hsum, hk, hpow k]
  have hRhs : ((2 * value xs + 5 : ℕ) : ZMod 3) = 2 := by
    push_cast
    rw [hval]
    decide
  have hEq := congrArg (fun n : ℕ => (n : ZMod 3)) heq
  have h12 : (1 : ZMod 3) = 2 := by
    calc
      1 = (divisorSum xs : ZMod 3) := hsumOne.symm
      _ = ((2 * value xs + 5 : ℕ) : ZMod 3) := hEq
      _ = 2 := hRhs
  exact (by decide : (1 : ZMod 3) ≠ 2) h12

private theorem value_mod4_one {xs : List Factor}
    (hv : Valid xs) : (value xs : ZMod 4) = 1 := by
  induction xs with
  | nil => simp [value]
  | cons x xs ih =>
    have hx := hv x (by simp)
    have htail : Valid xs := fun y hy => hv y (by simp [hy])
    obtain ⟨k, hk⟩ := hx.2.2.2.2
    have hpow := odd_square_mod4 (x.1 ^ k) (hx.2.1.pow)
    change ((x.1 ^ x.2 * value xs : ℕ) : ZMod 4) = 1
    rw [hk]
    rw [pow_add]
    rw [pow_two] at hpow
    calc
      (↑(x.1 ^ k * x.1 ^ k * value xs) : ZMod 4) =
          (↑(x.1 ^ k) * ↑(x.1 ^ k)) * ↑(value xs) := by push_cast; ring
      _ = 1 := by rw [hpow, ih htail]; simp

private theorem divisorSum_mod4_formula {ps : List Slot} {xs : List Factor}
    (hm : Matches ps xs) (hv : Valid xs)
    (hopen : ∀ s ∈ ps, openFour s = false) :
    (divisorSum xs : ZMod 4) = (3 : ZMod 4) ^ ps.countP fixedFourThree := by
  induction hm with
  | nil => simp [divisorSum]
  | @cons s x ps xs hst htail ih =>
    have hx := hv x (by simp)
    have htailValid : Valid xs := fun y hy => hv y (by simp [hy])
    have htailOpen : ∀ t ∈ ps, openFour t = false := by
      intro t ht
      exact hopen t (by simp [ht])
    have hpmod := primeOdd_mod4 x.1 hx.2.1
    have hloc : (geometric x.1 x.2 : ZMod 4) =
        if fixedFourThree s then 3 else 1 := by
      rcases s with ⟨p, o⟩
      cases hopt : o with
      | none =>
        have hno := hopen (p, o) (by simp)
        have hpnot : p % 4 ≠ 1 := by simpa [openFour, hopt] using hno
        have hpx : p = x.1 := by simpa using hst.1
        have hxnot : x.1 % 4 ≠ 1 := by rw [← hpx]; exact hpnot
        have hp3 : (x.1 : ZMod 4) = 3 := by
          rcases hpmod with h | h
          · have hxmod := (ZMod.natCast_eq_natCast_iff x.1 1 4).mp h
            change x.1 % 4 = 1 % 4 at hxmod
            exact False.elim (hxnot (by simpa using hxmod))
          · exact h
        have heven := hx.2.2.2.2
        have hnotfixed : fixedFourThree (p,none) = false := by simp [fixedFourThree]
        rw [if_neg (by simp [hnotfixed])]
        exact geometric_base_three_mod4 x.1 x.2 hp3 heven
      | some e =>
        have he : x.2 = e := hst.2 _ hopt
        have hpx : p = x.1 := by simpa using hst.1
        have hpEq : (x.1 : ZMod 4) = 1 ∨ (x.1 : ZMod 4) = 3 := hpmod
        rcases hpEq with hp1 | hp3
        · have hgeo := geometric_base_one_mod4 x.1 e hp1 (by simpa [he] using hx.2.2.2.2)
          have hpmod1 : x.1 % 4 = 1 := by
            have := (ZMod.natCast_eq_natCast_iff x.1 1 4).mp hp1
            change x.1 % 4 = 1 % 4 at this
            simpa using this
          by_cases htwo : e % 4 = 2
          · have hfix : fixedFourThree (p,some e) = true := by simp [fixedFourThree, hpx, hpmod1, htwo]
            rw [he]
            rw [if_pos (by simp [hfix])]
            simpa [he, htwo] using hgeo
          · have hgeo1 : (geometric x.1 e : ZMod 4) = 1 := by
              simpa [htwo] using hgeo
            have hfix : fixedFourThree (p,some e) = false := by simp [fixedFourThree, hpx, hpmod1, htwo]
            rw [he]
            rw [if_neg (by simp [hfix])]
            exact hgeo1
        · have hp3x : (p : ZMod 4) = 3 := by simpa [hpx] using hp3
          have hp3Factor : (x.1 : ZMod 4) = 3 := by simpa [hpx] using hp3x
          have hgeo := geometric_base_three_mod4 x.1 e hp3Factor (by simpa [he] using hx.2.2.2.2)
          have hpmod3 : p % 4 = 3 := by
            have hmod := (ZMod.natCast_eq_natCast_iff p 3 4).mp hp3x
            simpa [Nat.ModEq] using hmod
          have hfix : fixedFourThree (p,some e) = false := by simp [fixedFourThree, hpmod3]
          rw [he]
          rw [if_neg (by simp [hfix])]
          simpa [hpx] using hgeo
    change ((geometric x.1 x.2 * divisorSum xs : ℕ) : ZMod 4) = _
    push_cast
    rw [hloc, ih htailValid htailOpen]
    rw [List.countP_cons]
    by_cases hb : fixedFourThree s = true <;> simp [hb, pow_succ, mul_comm]

theorem modularTerminal_sound {ps : List Slot}
    (h : modularTerminal ps = true) : Excludes ps := by
  simp [modularTerminal] at h
  rcases h with hprefix | ⟨h5, hfull⟩
  · rcases hprefix with ⟨hthreeBool, hzeroBool⟩
    have hthree : ∃ s ∈ ps, s.1 = 3 := by
      rcases hthreeBool with ⟨o, ho⟩
      exact ⟨(3,o), ho, rfl⟩
    have hzero : ∃ s ∈ ps, fixedThreeZero s = true := by
      rcases hzeroBool with ⟨p,o,hmem,hb⟩
      exact ⟨(p,o),hmem,hb⟩
    exact exclude_mod3_zero_prefix hthree hzero
  · rcases hfull with h4 | h3
    · rcases h4 with ⟨hopenFalse, hparityFalse⟩
      have hopen : ∀ s ∈ ps, openFour s = false := by
        intro ⟨p,o⟩ hs
        exact hopenFalse p o hs
      have heven : Even (ps.countP fixedFourThree) := Nat.even_iff.mpr hparityFalse
      intro xs ys hm hcard hv hsort
      have hnil := full_has_empty_tail h5 hm hcard
      subst ys
      simp only [List.append_nil] at hcard hv hsort
      intro heq
      simp only [List.append_nil] at heq
      have hsum := divisorSum_mod4_formula hm hv hopen
      have hval := value_mod4_one hv
      have hsumOne : (divisorSum xs : ZMod 4) = 1 := by
        obtain ⟨k, hk⟩ := heven
        have hthree : (3 : ZMod 4)^2 = 1 := by decide
        have hpow : ∀ k : ℕ, (3 : ZMod 4)^(k+k) = 1 := by
          intro k
          induction k with
          | zero => simp
          | succ k ih =>
            calc
              (3 : ZMod 4)^((k+1)+(k+1)) = (3 : ZMod 4)^((k+k)+2) := by congr 1 <;> omega
              _ = (3 : ZMod 4)^(k+k) * (3 : ZMod 4)^2 := by rw [pow_add]
              _ = 1 := by rw [ih, hthree]; simp
        rw [hsum, hk, hpow k]
      have hRhs : ((2 * value xs + 5 : ℕ) : ZMod 4) = 3 := by
        push_cast
        rw [hval]
        decide
      have hEqCast := congrArg (fun n : ℕ => (n : ZMod 4)) heq
      have hEqOneThree : (1 : ZMod 4) = 3 := by
        calc
          1 = (divisorSum xs : ZMod 4) := hsumOne.symm
          _ = ((2 * value xs + 5 : ℕ) : ZMod 4) := hEqCast
          _ = 3 := hRhs
      exact (by decide : (1 : ZMod 4) ≠ 3) hEqOneThree
    · rcases h3 with ⟨hthreeBool, hmod3⟩
      have hthree : ∃ s ∈ ps, s.1 = 3 := by
        rcases hthreeBool with ⟨o, ho⟩
        exact ⟨(3,o), ho, rfl⟩
      rcases hmod3 with hzeroBool | ⟨hopenFalse, hparityFalse⟩
      · have hzero : ∃ s ∈ ps, fixedThreeZero s = true := by
          rcases hzeroBool with ⟨p,o,hmem,hb⟩
          exact ⟨(p,o),hmem,hb⟩
        exact exclude_mod3_zero_prefix hthree hzero
      · have hopen : ∀ s ∈ ps, openThree s = false := by
          intro ⟨p,o⟩ hs
          exact hopenFalse p o hs
        have heven : Even (ps.countP fixedThreeTwo) := Nat.even_iff.mpr hparityFalse
        cases hz : ps.any fixedThreeZero with
        | true =>
          have hzero : ∃ s ∈ ps, fixedThreeZero s = true := List.any_eq_true.mp hz
          exact exclude_mod3_zero_prefix hthree hzero
        | false =>
          have hzero : ∀ s ∈ ps, fixedThreeZero s = false := by
            intro s hs
            have hnot := (List.any_eq_false.mp hz) s hs
            simpa using hnot
          exact exclude_mod3_wrong_product h5 hthree hopen hzero heven

end SigmaMixedModular

open Finset ArithmeticFunction BigOperators

namespace SigmaFiveExactBridge

open SigmaFiveMixedCertificate SigmaAbundancyBounds

abbrev Factor := SigmaFiveMixedCertificate.Factor

def factorsOf (n : ℕ) (f : Fin 5 → ℕ) : List Factor :=
  List.ofFn fun i => (f i, n.factorization (f i))

theorem odd_square_five_factor_list {n : ℕ} (hn : Odd n)
    (hsq : IsSquare n) (hcard : n.primeFactors.card = 5) (h5 : ¬ 5 ∣ n) :
    ∃ xs : List Factor,
      xs.length = 5 ∧
      xs.Pairwise (fun x y => x.1 < y.1) ∧
      SigmaFiveMixedCertificate.Valid xs ∧
      SigmaFiveMixedCertificate.value xs = n ∧
      SigmaFiveMixedCertificate.divisorSum xs = sigma 1 n := by
  classical
  have hn0 : n ≠ 0 := by
    intro hz
    subst n
    obtain ⟨k, hk⟩ := hn
    omega
  obtain ⟨m, hm⟩ := hsq
  have hfac : n.factorization = (2 : ℕ) • m.factorization := by
    rw [hm, show m * m = m ^ 2 by rw [pow_two], Nat.factorization_pow]
  let f := n.primeFactors.orderEmbOfFin hcard
  let xs : List Factor := factorsOf n f
  have hfmem (i : Fin 5) : f i ∈ n.primeFactors :=
    Finset.orderEmbOfFin_mem _ _ _
  have hprime (i : Fin 5) : (f i).Prime :=
    Nat.prime_of_mem_primeFactors (hfmem i)
  have hoddPrime (i : Fin 5) : Odd (f i) := by
    have hdiv := (Nat.mem_primeFactors.mp (hfmem i)).2.1
    have hne : f i ≠ 2 := by
      intro htwo
      have htwodvd : 2 ∣ n := htwo ▸ hdiv
      exact hn.not_two_dvd_nat htwodvd
    have hmod := (hprime i).mod_two_eq_one_iff_ne_two.mpr hne
    exact ⟨(f i) / 2, by omega⟩
  have hexpEven (i : Fin 5) : Even (n.factorization (f i)) := by
    refine ⟨m.factorization (f i), ?_⟩
    simp [hfac, two_smul]
  have hexpPos (i : Fin 5) : 0 < n.factorization (f i) :=
    (hprime i).factorization_pos_of_dvd hn0
      (Nat.dvd_of_mem_primeFactors (hfmem i))
  have hprimeNeFive (i : Fin 5) : f i ≠ 5 := by
    intro heq
    apply h5
    rw [← heq]
    exact Nat.dvd_of_mem_primeFactors (hfmem i)
  have hlength : xs.length = 5 := by simp [xs, factorsOf]
  have hpair : xs.Pairwise (fun x y => x.1 < y.1) := by
    change List.Pairwise (fun x y => x.1 < y.1)
      (List.ofFn fun i : Fin 5 => (f i, n.factorization (f i)))
    rw [List.pairwise_ofFn]
    intro i j hij
    exact f.strictMono hij
  have hvalid : SigmaFiveMixedCertificate.Valid xs := by
    intro x hx
    simp only [xs, factorsOf, List.mem_ofFn] at hx
    obtain ⟨i, rfl⟩ := hx
    refine ⟨hprime i, hoddPrime i, hprimeNeFive i, ?_, ?_⟩
    · have he := hexpEven i
      have hp := hexpPos i
      rcases he with ⟨k, hk⟩
      omega
    · exact hexpEven i
  have hvalue : SigmaFiveMixedCertificate.value xs = n := by
    change ((List.ofFn fun i : Fin 5 => (f i, n.factorization (f i))).map
      (fun x => x.1 ^ x.2)).prod = n
    rw [List.map_ofFn, List.prod_ofFn]
    have hprod := Nat.prod_primeFactors_pow_factorization hn0
    rw [← Finset.map_orderEmbOfFin_univ n.primeFactors hcard,
      Finset.prod_map] at hprod
    simpa using hprod.symm
  have hdivisorSum : SigmaFiveMixedCertificate.divisorSum xs = sigma 1 n := by
    have hfactor : sigma 1 n =
        ∏ p ∈ n.primeFactors, sigma 1 (p ^ n.factorization p) := by
      rw [isMultiplicative_sigma.multiplicative_factorization _ hn0]
      simp [Finsupp.prod, Nat.support_factorization]
    rw [← Finset.map_orderEmbOfFin_univ n.primeFactors hcard, Finset.prod_map] at hfactor
    change ((List.ofFn fun i : Fin 5 =>
      (f i, n.factorization (f i))).map
        (fun x => SigmaAbundancyBounds.geometric x.1 x.2)).prod = sigma 1 n
    rw [List.map_ofFn, List.prod_ofFn]
    calc
      _ = ∏ i : Fin 5, sigma 1 ((f i) ^ n.factorization (f i)) := by
        apply Finset.prod_congr rfl
        intro i hi
        rw [sigma_one_apply_prime_pow (hprime i)]
        change SigmaAbundancyBounds.geometric (f i) (n.factorization (f i)) = _
        exact SigmaAbundancyBounds.geometric_eq_sum (f i) _
      _ = sigma 1 n := hfactor.symm
  exact ⟨xs, hlength, hpair, hvalid, hvalue, hdivisorSum⟩

private def leastOddPrime (i : ℕ) : ℕ :=
  match i with
  | 0 => 3
  | 1 => 5
  | 2 => 7
  | 3 => 11
  | _ => 13

private theorem rank_filter_bound {s : Finset ℕ} {k : ℕ} (hs : s.card = k)
    (i : Fin k) (t : ℕ) (hfi : s.orderEmbOfFin hs i < t) :
    i.val + 1 ≤ (s.filter (fun x => x < t)).card := by
  let f := s.orderEmbOfFin hs
  let pre := Finset.Iic i
  have hsub : Finset.image f pre ⊆ s.filter (fun x => x < t) := by
    apply Finset.image_subset_iff.mpr
    intro j hj
    have hjle : j ≤ i := Finset.mem_Iic.mp hj
    have hmem : f j ∈ s := Finset.orderEmbOfFin_mem _ _ _
    have hlt : f j < t := lt_of_le_of_lt (f.monotone hjle) hfi
    exact Finset.mem_filter.mpr ⟨hmem, hlt⟩
  have hc := Finset.card_le_card hsub
  rw [Finset.card_image_of_injective pre f.injective, Fin.card_Iic] at hc
  exact hc

private theorem rank_lower_bound {s : Finset ℕ} {k : ℕ} (hs : s.card = k)
    (hk : k ≤ 5) (hprime : ∀ p ∈ s, p.Prime) (hlower : ∀ p ∈ s, 3 ≤ p) :
    ∀ i : Fin k, leastOddPrime i.val ≤ s.orderEmbOfFin hs i := by
  intro i
  have hi7 : i.val < 5 := lt_of_lt_of_le i.isLt hk
  interval_cases hval : i.val
  all_goals
    by_contra! hlt
    have hsub : s.filter (fun p => p < leastOddPrime i.val) ⊆
        (Finset.range (leastOddPrime i.val)).filter (fun p => p.Prime ∧ 3 ≤ p) := by
      intro p hp
      rcases Finset.mem_filter.mp hp with ⟨hps, hpt⟩
      exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hpt,
        ⟨hprime p hps, hlower p hps⟩⟩
    have hcount : (s.filter (fun p => p < leastOddPrime i.val)).card ≤ i.val := by
      calc
        _ ≤ ((Finset.range (leastOddPrime i.val)).filter
            (fun p => p.Prime ∧ 3 ≤ p)).card := Finset.card_le_card hsub
        _ = i.val := by rw [hval]; simp [leastOddPrime]; decide
    have hprefix := rank_filter_bound hs i (leastOddPrime i.val) (by
      simpa [leastOddPrime, hval] using hlt)
    omega

theorem odd_square_five_sigma_lt_three {n : ℕ} (hn : Odd n)
    (hcard : n.primeFactors.card = 5) : sigma 1 n < 3*n := by
  classical
  have hn0 : n ≠ 0 := by
    intro hz
    subst n
    obtain ⟨k, hk⟩ := hn
    omega
  let f := n.primeFactors.orderEmbOfFin hcard
  let e : Fin 5 → ℕ := fun i => n.factorization (f i)
  have hmem (i : Fin 5) : f i ∈ n.primeFactors := Finset.orderEmbOfFin_mem _ _ _
  have hp (i : Fin 5) : (f i).Prime := Nat.prime_of_mem_primeFactors (hmem i)
  have hq (i : Fin 5) (_hi : i ∈ Finset.univ) : 2 ≤ leastOddPrime i.val := by
    fin_cases i <;> norm_num [leastOddPrime]
  have hpall (p : ℕ) (hp : p ∈ n.primeFactors) : p.Prime :=
    Nat.prime_of_mem_primeFactors hp
  have hlowerall (p : ℕ) (hp : p ∈ n.primeFactors) : 3 ≤ p := by
    have hd := (Nat.mem_primeFactors.mp hp).2.1
    have hne : p ≠ 2 := by
      intro he
      exact hn.not_two_dvd_nat (he ▸ hd)
    have hp2 := (hpall p hp).two_le
    omega
  have hrank := rank_lower_bound hcard (by omega) hpall hlowerall
  have hlower (i : Fin 5) (hi : i ∈ Finset.univ) : leastOddPrime i.val ≤ f i := by
    exact hrank i
  have hprod : (∏ i : Fin 5, f i ^ e i) = n := by
    have hh := Nat.prod_primeFactors_pow_factorization hn0
    rw [← Finset.map_orderEmbOfFin_univ n.primeFactors hcard,
      Finset.prod_map] at hh
    simpa [e, f] using hh.symm
  have hsig : sigma 1 n = ∏ i : Fin 5,
      SigmaAbundancyBounds.geometric (f i) (e i) := by
    have hfactor : sigma 1 n =
        ∏ p ∈ n.primeFactors, sigma 1 (p ^ n.factorization p) := by
      rw [isMultiplicative_sigma.multiplicative_factorization _ hn0]
      simp [Finsupp.prod, Nat.support_factorization]
    rw [← Finset.map_orderEmbOfFin_univ n.primeFactors hcard,
      Finset.prod_map] at hfactor
    calc
      sigma 1 n = ∏ i : Fin 5, sigma 1 ((f i) ^ e i) := by simpa [f, e] using hfactor
      _ = _ := by
        apply Finset.prod_congr rfl
        intro i hi
        rw [sigma_one_apply_prime_pow (hp i)]
        exact (SigmaAbundancyBounds.geometric_eq_sum _ _).symm
  let D := ∏ i : Fin 5, (leastOddPrime i - 1)
  let Q := ∏ i : Fin 5, leastOddPrime i
  have hprofile := SigmaAbundancyBounds.product_profile_bound
    Finset.univ f (fun i => leastOddPrime i.val) e hq hlower
  have hD : 0 < D := by norm_num [D, leastOddPrime, Fin.prod_univ_succ]
  have hQ : Q < 3*D := by norm_num [Q, D, leastOddPrime, Fin.prod_univ_succ]
  have hscaled := Nat.mul_lt_mul_of_pos_right hQ (Nat.pos_of_ne_zero hn0)
  have hmain : (∏ i : Fin 5, SigmaAbundancyBounds.geometric (f i) (e i))*D <
      3*D*n := by
    calc
      _ ≤ Q*n := by simpa [D, hsig, hprod] using hprofile
      _ < 3*D*n := by nlinarith [hscaled]
  by_contra! hnot
  have hcontra := Nat.mul_le_mul_right D hnot
  nlinarith [hmain]

private theorem odd_divisorSum_of_valid (xs : List Factor)
    (hv : SigmaFiveMixedCertificate.Valid xs) : Odd (SigmaFiveMixedCertificate.divisorSum xs) := by
  induction xs with
  | nil => exact ⟨0, by simp [SigmaFiveMixedCertificate.divisorSum]⟩
  | cons x xs ih =>
    have hx := hv x (by simp)
    have ht : SigmaFiveMixedCertificate.Valid xs := fun y hy => hv y (by simp [hy])
    have hgeom : Odd (SigmaAbundancyBounds.geometric x.1 x.2) := by
      obtain ⟨k, hk⟩ := hx.2.2.2.2
      have heq : x.2 = 2 * (x.2 / 2) := by omega
      rw [heq]
      exact SigmaAbundancyBounds.geometric_even_odd x.1 (x.2 / 2) hx.2.1
    change Odd (SigmaAbundancyBounds.geometric x.1 x.2 *
      SigmaFiveMixedCertificate.divisorSum xs)
    exact hgeom.mul (ih ht)

theorem odd_square_five_sigma_odd {n : ℕ} (hn : Odd n) (hsq : IsSquare n)
    (hcard : n.primeFactors.card = 5) (h5 : ¬ 5 ∣ n) : Odd (sigma 1 n) := by
  obtain ⟨xs, _, _, hv, _, hsum⟩ := odd_square_five_factor_list hn hsq hcard h5
  rw [← hsum]
  exact odd_divisorSum_of_valid xs hv

theorem odd_square_five_sigma_gt_five {n : ℕ} (hn : Odd n) (hsq : IsSquare n)
    (hcard : n.primeFactors.card = 5) (h5 : ¬ 5 ∣ n) : 5 < sigma 1 n := by
  obtain ⟨xs, _, _, hv, hvalue, hsum⟩ := odd_square_five_factor_list hn hsq hcard h5
  have hlen : xs.length = 5 := by simpa using ‹xs.length = 5›
  have hgt : 5 < SigmaFiveMixedCertificate.value xs := by
    cases hxs : xs with
    | nil => simp [hxs] at hlen
    | cons x tail =>
      have hv' : SigmaFiveMixedCertificate.Valid (x::tail) := by
        simpa [hxs] using hv
      simpa [hxs] using SigmaFiveMixedCertificate.suffix_value_gt_five hv'
  have hle := SigmaFiveMixedCertificate.value_le_divisorSum xs
  calc
    5 < SigmaFiveMixedCertificate.value xs := hgt
    _ ≤ SigmaFiveMixedCertificate.divisorSum xs := hle
    _ = sigma 1 n := hsum

theorem odd_square_five_quotient_two {n : ℕ} (hn : Odd n) (hsq : IsSquare n)
    (hcard : n.primeFactors.card = 5) (h5 : ¬ 5 ∣ n)
    (hmod : sigma 1 n % n = 5) : sigma 1 n = 2*n+5 := by
  exact SigmaAbundancyBounds.quotient_two hn
    (odd_square_five_sigma_odd hn hsq hcard h5) hmod
    (odd_square_five_sigma_gt_five hn hsq hcard h5)
    (odd_square_five_sigma_lt_three hn hcard)

end SigmaFiveExactBridge

namespace SigmaExactContainer
open SigmaFiveMixedCertificate SigmaMixedDAG SigmaMixedData SigmaMixedModular SigmaFiveExactBridge
open ArithmeticFunction
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem checked0 : (bucket 0).all (checkRow modularTerminal) = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem checked1 : (bucket 1).all (checkRow modularTerminal) = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem checked2 : (bucket 2).all (checkRow modularTerminal) = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem checked3 : (bucket 3).all (checkRow modularTerminal) = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem checked4 : (bucket 4).all (checkRow modularTerminal) = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem checked5 : (bucket 5).all (checkRow modularTerminal) = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem checked6 : (bucket 6).all (checkRow modularTerminal) = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem checked7 : (bucket 7).all (checkRow modularTerminal) = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem checked8 : (bucket 8).all (checkRow modularTerminal) = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem checked9 : (bucket 9).all (checkRow modularTerminal) = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem checked10 : (bucket 10).all (checkRow modularTerminal) = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem checked11 : (bucket 11).all (checkRow modularTerminal) = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem checked12 : (bucket 12).all (checkRow modularTerminal) = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem checked13 : (bucket 13).all (checkRow modularTerminal) = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem checked14 : (bucket 14).all (checkRow modularTerminal) = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem checked15 : (bucket 15).all (checkRow modularTerminal) = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem checked16 : (bucket 16).all (checkRow modularTerminal) = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem checked17 : (bucket 17).all (checkRow modularTerminal) = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem checked18 : (bucket 18).all (checkRow modularTerminal) = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem checked19 : (bucket 19).all (checkRow modularTerminal) = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem checked20 : (bucket 20).all (checkRow modularTerminal) = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem checked21 : (bucket 21).all (checkRow modularTerminal) = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem checked22 : (bucket 22).all (checkRow modularTerminal) = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem checked23 : (bucket 23).all (checkRow modularTerminal) = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem checked24 : (bucket 24).all (checkRow modularTerminal) = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem checked25 : (bucket 25).all (checkRow modularTerminal) = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem checked26 : (bucket 26).all (checkRow modularTerminal) = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem checked27 : (bucket 27).all (checkRow modularTerminal) = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem checked28 : (bucket 28).all (checkRow modularTerminal) = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem checked29 : (bucket 29).all (checkRow modularTerminal) = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem checked30 : (bucket 30).all (checkRow modularTerminal) = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem checked31 : (bucket 31).all (checkRow modularTerminal) = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem checked32 : (bucket 32).all (checkRow modularTerminal) = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem checked33 : (bucket 33).all (checkRow modularTerminal) = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem checked34 : (bucket 34).all (checkRow modularTerminal) = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem checked35 : (bucket 35).all (checkRow modularTerminal) = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem checked36 : (bucket 36).all (checkRow modularTerminal) = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem checked37 : (bucket 37).all (checkRow modularTerminal) = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem checked38 : (bucket 38).all (checkRow modularTerminal) = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem checked39 : (bucket 39).all (checkRow modularTerminal) = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem checked40 : (bucket 40).all (checkRow modularTerminal) = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem checked41 : (bucket 41).all (checkRow modularTerminal) = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem checked42 : (bucket 42).all (checkRow modularTerminal) = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem checked43 : (bucket 43).all (checkRow modularTerminal) = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem checked44 : (bucket 44).all (checkRow modularTerminal) = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem checked45 : (bucket 45).all (checkRow modularTerminal) = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem checked46 : (bucket 46).all (checkRow modularTerminal) = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem checked47 : (bucket 47).all (checkRow modularTerminal) = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem checked48 : (bucket 48).all (checkRow modularTerminal) = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem checked49 : (bucket 49).all (checkRow modularTerminal) = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem checked50 : (bucket 50).all (checkRow modularTerminal) = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem checked51 : (bucket 51).all (checkRow modularTerminal) = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem checked52 : (bucket 52).all (checkRow modularTerminal) = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem checked53 : (bucket 53).all (checkRow modularTerminal) = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem checked54 : (bucket 54).all (checkRow modularTerminal) = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem checked55 : (bucket 55).all (checkRow modularTerminal) = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem checked56 : (bucket 56).all (checkRow modularTerminal) = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem checked57 : (bucket 57).all (checkRow modularTerminal) = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem checked58 : (bucket 58).all (checkRow modularTerminal) = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem checked59 : (bucket 59).all (checkRow modularTerminal) = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem checked60 : (bucket 60).all (checkRow modularTerminal) = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem checked61 : (bucket 61).all (checkRow modularTerminal) = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem checked62 : (bucket 62).all (checkRow modularTerminal) = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem checked63 : (bucket 63).all (checkRow modularTerminal) = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem checked64 : (bucket 64).all (checkRow modularTerminal) = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem checked65 : (bucket 65).all (checkRow modularTerminal) = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem checked66 : (bucket 66).all (checkRow modularTerminal) = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem checked67 : (bucket 67).all (checkRow modularTerminal) = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem checked68 : (bucket 68).all (checkRow modularTerminal) = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem checked69 : (bucket 69).all (checkRow modularTerminal) = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem checked70 : (bucket 70).all (checkRow modularTerminal) = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem checked71 : (bucket 71).all (checkRow modularTerminal) = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem checked72 : (bucket 72).all (checkRow modularTerminal) = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem checked73 : (bucket 73).all (checkRow modularTerminal) = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem checked74 : (bucket 74).all (checkRow modularTerminal) = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem checked75 : (bucket 75).all (checkRow modularTerminal) = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem checked76 : (bucket 76).all (checkRow modularTerminal) = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem checked77 : (bucket 77).all (checkRow modularTerminal) = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem checked78 : (bucket 78).all (checkRow modularTerminal) = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem checked79 : (bucket 79).all (checkRow modularTerminal) = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem checked80 : (bucket 80).all (checkRow modularTerminal) = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem checked81 : (bucket 81).all (checkRow modularTerminal) = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem checked82 : (bucket 82).all (checkRow modularTerminal) = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem checked83 : (bucket 83).all (checkRow modularTerminal) = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem checked84 : (bucket 84).all (checkRow modularTerminal) = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem checked85 : (bucket 85).all (checkRow modularTerminal) = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem checked86 : (bucket 86).all (checkRow modularTerminal) = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem checked87 : (bucket 87).all (checkRow modularTerminal) = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem checked88 : (bucket 88).all (checkRow modularTerminal) = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem checked89 : (bucket 89).all (checkRow modularTerminal) = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem checked90 : (bucket 90).all (checkRow modularTerminal) = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem checked91 : (bucket 91).all (checkRow modularTerminal) = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem checked92 : (bucket 92).all (checkRow modularTerminal) = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem checked93 : (bucket 93).all (checkRow modularTerminal) = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem checked94 : (bucket 94).all (checkRow modularTerminal) = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem checked95 : (bucket 95).all (checkRow modularTerminal) = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem checked96 : (bucket 96).all (checkRow modularTerminal) = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem checked97 : (bucket 97).all (checkRow modularTerminal) = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem checked98 : (bucket 98).all (checkRow modularTerminal) = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem checked99 : (bucket 99).all (checkRow modularTerminal) = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem checked100 : (bucket 100).all (checkRow modularTerminal) = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem checked101 : (bucket 101).all (checkRow modularTerminal) = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem checked102 : (bucket 102).all (checkRow modularTerminal) = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem checked103 : (bucket 103).all (checkRow modularTerminal) = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem checked104 : (bucket 104).all (checkRow modularTerminal) = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem checked105 : (bucket 105).all (checkRow modularTerminal) = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem checked106 : (bucket 106).all (checkRow modularTerminal) = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem checked107 : (bucket 107).all (checkRow modularTerminal) = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem checked108 : (bucket 108).all (checkRow modularTerminal) = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem checked109 : (bucket 109).all (checkRow modularTerminal) = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem checked110 : (bucket 110).all (checkRow modularTerminal) = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem checked111 : (bucket 111).all (checkRow modularTerminal) = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem checked112 : (bucket 112).all (checkRow modularTerminal) = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem checked113 : (bucket 113).all (checkRow modularTerminal) = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem checked114 : (bucket 114).all (checkRow modularTerminal) = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem checked115 : (bucket 115).all (checkRow modularTerminal) = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem checked116 : (bucket 116).all (checkRow modularTerminal) = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem checked117 : (bucket 117).all (checkRow modularTerminal) = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem checked118 : (bucket 118).all (checkRow modularTerminal) = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem checked119 : (bucket 119).all (checkRow modularTerminal) = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem checked120 : (bucket 120).all (checkRow modularTerminal) = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem checked121 : (bucket 121).all (checkRow modularTerminal) = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem checked122 : (bucket 122).all (checkRow modularTerminal) = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem checked123 : (bucket 123).all (checkRow modularTerminal) = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem checked124 : (bucket 124).all (checkRow modularTerminal) = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem checked125 : (bucket 125).all (checkRow modularTerminal) = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem checked126 : (bucket 126).all (checkRow modularTerminal) = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem everyBucket : ∀ k < 127, (bucket k).all (checkRow modularTerminal) = true := by
  intro k hk
  interval_cases k
  · exact checked0
  · exact checked1
  · exact checked2
  · exact checked3
  · exact checked4
  · exact checked5
  · exact checked6
  · exact checked7
  · exact checked8
  · exact checked9
  · exact checked10
  · exact checked11
  · exact checked12
  · exact checked13
  · exact checked14
  · exact checked15
  · exact checked16
  · exact checked17
  · exact checked18
  · exact checked19
  · exact checked20
  · exact checked21
  · exact checked22
  · exact checked23
  · exact checked24
  · exact checked25
  · exact checked26
  · exact checked27
  · exact checked28
  · exact checked29
  · exact checked30
  · exact checked31
  · exact checked32
  · exact checked33
  · exact checked34
  · exact checked35
  · exact checked36
  · exact checked37
  · exact checked38
  · exact checked39
  · exact checked40
  · exact checked41
  · exact checked42
  · exact checked43
  · exact checked44
  · exact checked45
  · exact checked46
  · exact checked47
  · exact checked48
  · exact checked49
  · exact checked50
  · exact checked51
  · exact checked52
  · exact checked53
  · exact checked54
  · exact checked55
  · exact checked56
  · exact checked57
  · exact checked58
  · exact checked59
  · exact checked60
  · exact checked61
  · exact checked62
  · exact checked63
  · exact checked64
  · exact checked65
  · exact checked66
  · exact checked67
  · exact checked68
  · exact checked69
  · exact checked70
  · exact checked71
  · exact checked72
  · exact checked73
  · exact checked74
  · exact checked75
  · exact checked76
  · exact checked77
  · exact checked78
  · exact checked79
  · exact checked80
  · exact checked81
  · exact checked82
  · exact checked83
  · exact checked84
  · exact checked85
  · exact checked86
  · exact checked87
  · exact checked88
  · exact checked89
  · exact checked90
  · exact checked91
  · exact checked92
  · exact checked93
  · exact checked94
  · exact checked95
  · exact checked96
  · exact checked97
  · exact checked98
  · exact checked99
  · exact checked100
  · exact checked101
  · exact checked102
  · exact checked103
  · exact checked104
  · exact checked105
  · exact checked106
  · exact checked107
  · exact checked108
  · exact checked109
  · exact checked110
  · exact checked111
  · exact checked112
  · exact checked113
  · exact checked114
  · exact checked115
  · exact checked116
  · exact checked117
  · exact checked118
  · exact checked119
  · exact checked120
  · exact checked121
  · exact checked122
  · exact checked123
  · exact checked124
  · exact checked125
  · exact checked126

theorem lists_no_five : Excludes [] := by
  apply known_sound primeTable_complete primeTable_sorted
    (fun ps hp => modularTerminal_sound (ps := ps) hp)
    (plan_checked everyBucket)
  · decide
  · decide +kernel

theorem odd_square_five_without_five {n : ℕ} (hn : Odd n) (hs : IsSquare n)
    (hc : n.primeFactors.card = 5) (h5 : ¬ (5 ∣ n)) : sigma 1 n % n ≠ 5 := by
  intro hmod
  obtain ⟨xs, hlength, hsorted, hvalid, hvalue, hsum⟩ :=
    odd_square_five_factor_list hn hs hc h5
  have hex := lists_no_five [] xs List.Forall₂.nil hlength hvalid hsorted
  exact hex (by
    change divisorSum xs = 2*value xs+5
    rw [hsum,hvalue]
    exact odd_square_five_quotient_two hn hs hc h5 hmod)


end SigmaExactContainer

theorem OMA.solution : OMA.R_OeisA76495_conjecture_R1_H1_R1.H1 := by
  intro n hn hs hc h5
  exact SigmaExactContainer.odd_square_five_without_five hn hs hc h5
