import OMAStatements.S_oeis_a097154

namespace OMA.S_oeis_a097154


private theorem ofDigits_one_eq_sum (ds : List ℕ) : Nat.ofDigits 1 ds = ds.sum := by
  induction ds with
  | nil => simp [Nat.ofDigits]
  | cons d ds ih => simp [Nat.ofDigits_cons, ih]

private theorem ofDigits_mod9_eq_sum_mod9 (ds : List ℕ) :
    Nat.ofDigits 10 ds % 9 = ds.sum % 9 := by
  rw [Nat.ofDigits_mod]
  norm_num [ofDigits_one_eq_sum]

private theorem foldr_max_le_nine (ds : List ℕ) (h : ∀ d ∈ ds, d < 10) :
    ds.foldr max 0 ≤ 9 := by
  induction ds with
  | nil => simp
  | cons d ds ih =>
    have hd := h d (by simp)
    have hds : ∀ e ∈ ds, e < 10 := by
      intro e he
      exact h e (by simp [he])
    simp only [List.foldr_cons]
    have := ih hds
    omega

private theorem mem_le_foldr_max (ds : List ℕ) (d : ℕ) (hd : d ∈ ds) :
    d ≤ ds.foldr max 0 := by
  induction ds with
  | nil => simp at hd
  | cons a ds ih =>
    simp only [List.foldr_cons, List.mem_cons] at *
    rcases hd with rfl | hd
    · exact Nat.le_max_left _ _
    · exact le_trans (ih hd) (Nat.le_max_right _ _)

private theorem ofDigits_all_zero (ds : List ℕ) (h : ∀ d ∈ ds, d = 0) :
    Nat.ofDigits 10 ds = 0 := by
  induction ds with
  | nil => simp [Nat.ofDigits]
  | cons d ds ih =>
    have hd := h d (by simp)
    have hds : ∀ e ∈ ds, e = 0 := by
      intro e he
      exact h e (by simp [he])
    simp [Nat.ofDigits_cons, hd, ih hds]

private theorem ofDigits_reverse_zero_imp_zero (ds : List ℕ)
    (h : Nat.ofDigits 10 ds.reverse = 0) : Nat.ofDigits 10 ds = 0 := by
  induction ds with
  | nil => simp [Nat.ofDigits]
  | cons d ds ih =>
    rw [Nat.ofDigits_reverse_cons] at h
    have hp : (10:ℕ) ^ ds.length ≠ 0 := by positivity
    have hparts := Nat.add_eq_zero_iff.mp h
    have hmul := Nat.mul_eq_zero.mp hparts.2
    have hd : d = 0 := hmul.resolve_left hp
    simp [Nat.ofDigits_cons, hd, ih hparts.1]

private theorem ofDigits_lt_pow_length (ds : List ℕ)
    (hdig : ∀ d ∈ ds, d < 10) : Nat.ofDigits 10 ds < 10 ^ ds.length := by
  induction ds with
  | nil => simp [Nat.ofDigits]
  | cons d ds ih =>
    have hd := hdig d (by simp)
    have hds : ∀ e ∈ ds, e < 10 := by
      intro e he
      exact hdig e (by simp [he])
    have ht := ih hds
    rw [Nat.ofDigits_cons, List.length_cons, pow_succ]
    have hle : Nat.ofDigits 10 ds + 1 ≤ 10 ^ ds.length := Nat.succ_le_of_lt ht
    nlinarith

private theorem reverse_endpoint_val (mid : List ℕ) (a b : ℕ) :
    Nat.ofDigits 10 (b :: (mid ++ [a])).reverse =
      a + 10 * Nat.ofDigits 10 mid.reverse + 10 ^ (mid.length + 1) * b := by
  have hrev : (b :: (mid ++ [a])).reverse = [a] ++ mid.reverse ++ [b] := by
    simp [List.reverse_cons, List.reverse_append]
  rw [hrev]
  change Nat.ofDigits 10 (a :: (mid.reverse ++ [b])) = _
  rw [Nat.ofDigits_cons, Nat.ofDigits_append, Nat.ofDigits_singleton,
    List.length_reverse, pow_succ]
  ring

private theorem endpoint_val (mid : List ℕ) (a b : ℕ) :
    Nat.ofDigits 10 (b :: (mid ++ [a])) =
      b + 10 * Nat.ofDigits 10 mid + 10 ^ (mid.length + 1) * a := by
  rw [Nat.ofDigits_cons, Nat.ofDigits_append, Nat.ofDigits_singleton, pow_succ]
  ring

private theorem endpoint_mod10 (mid : List ℕ) (a b : ℕ) :
    Nat.ofDigits 10 (b :: (mid ++ [a])).reverse % 10 = a % 10 ∧
    Nat.ofDigits 10 (b :: (mid ++ [a])) % 10 = b % 10 := by
  rw [reverse_endpoint_val, endpoint_val]
  constructor <;> simp [Nat.add_mod, Nat.mul_mod, Nat.pow_succ]

private theorem endpoints_cases (mid : List ℕ) (a b : ℕ)
    (ha : a < 10) (hb : b < 10)
    (h : Nat.ofDigits 10 (b :: (mid ++ [a])).reverse =
         Nat.ofDigits 10 (b :: (mid ++ [a])) + 9) :
    (a = 9 ∧ b = 0) ∨ b = a + 1 := by
  have hm := endpoint_mod10 mid a b
  have hmod := congrArg (fun n : ℕ => n % 10) h
  rw [hm.1, Nat.add_mod, hm.2] at hmod
  interval_cases a <;> interval_cases b <;> omega

private theorem endpoints_inner (mid : List ℕ) (a b : ℕ)
    (h : Nat.ofDigits 10 (b :: (mid ++ [a])).reverse =
         Nat.ofDigits 10 (b :: (mid ++ [a])) + 9) :
    (a = 9 ∧ b = 0 →
      Nat.ofDigits 10 mid.reverse = Nat.ofDigits 10 mid + 9 * 10 ^ mid.length) ∧
    (b = a + 1 →
      Nat.ofDigits 10 mid = Nat.ofDigits 10 mid.reverse + 10 ^ mid.length - 1) := by
  have hr := reverse_endpoint_val mid a b
  have hn := endpoint_val mid a b
  have hp : (10:ℕ) ^ (mid.length + 1) = 10 * 10 ^ mid.length := by
    rw [pow_succ]
    ring
  constructor
  · intro he
    rcases he with ⟨rfl, rfl⟩
    rw [hr, hn, hp] at h
    nlinarith
  · intro hb
    rw [hr, hn, hb, hp] at h
    have hcore : Nat.ofDigits 10 mid + 1 = Nat.ofDigits 10 mid.reverse + 10 ^ mid.length := by
      nlinarith
    omega

private theorem fixedPoints : {x : ℕ | f x = x} = {0, 89} := by
  ext x
  constructor
  · intro hx
    have hsub : reverse x - maxDigit x = x := hx
    by_cases hx0 : x = 0
    · simp [hx0]
    · right
      have hsum : reverse x = x + maxDigit x := by omega
      let ds := Nat.digits 10 x
      have hxrep : Nat.ofDigits 10 ds = x := by simp [ds, Nat.ofDigits_digits]
      have hrevrep : Nat.ofDigits 10 ds.reverse = reverse x := by simp [reverse, ds]
      have hdig : ∀ d ∈ ds, d < 10 := by
        intro d hd
        exact Nat.digits_lt_base (by norm_num) hd
      have hmaxle : maxDigit x ≤ 9 :=
        foldr_max_le_nine ds (by simpa [ds] using hdig)
      have hmodx : x % 9 = ds.sum % 9 := by
        rw [← hxrep, ofDigits_mod9_eq_sum_mod9]
      have hmodr : reverse x % 9 = ds.sum % 9 := by
        rw [← hrevrep, ofDigits_mod9_eq_sum_mod9]
        simp
      have hmaxmod : maxDigit x % 9 = 0 := by
        have hcong : reverse x % 9 = x % 9 := by omega
        rw [hsum, Nat.add_mod] at hcong
        have hxmod : x % 9 < 9 := Nat.mod_lt _ (by norm_num)
        interval_cases hm : maxDigit x <;> norm_num [Nat.add_mod] at hcong ⊢ <;> omega
      have hmax : maxDigit x = 9 := by
        have hm : maxDigit x = 0 ∨ maxDigit x = 9 := by omega
        rcases hm with hm | hm
        · have hdigits0 : ∀ d ∈ ds, d = 0 := by
            intro d hd
            have hle := mem_le_foldr_max ds d hd
            have hfold : ds.foldr max 0 = 0 := by simpa [maxDigit, ds] using hm
            rw [hfold] at hle
            omega
          have hz := ofDigits_all_zero ds hdigits0
          omega
        · exact hm
      have hfixdigits : Nat.ofDigits 10 ds.reverse = Nat.ofDigits 10 ds + 9 := by
        calc
          Nat.ofDigits 10 ds.reverse = reverse x := hrevrep
          _ = x + maxDigit x := hsum
          _ = Nat.ofDigits 10 ds + 9 := by rw [hmax, hxrep]
      have hne : ds ≠ [] := by
        intro h
        have hxzero : x = 0 := by
          rw [← hxrep, h]
          simp [Nat.ofDigits]
        exact hx0 hxzero
      obtain ⟨b, tail, hds⟩ := List.exists_cons_of_ne_nil hne
      have htail : tail ≠ [] := by
        intro he
        subst tail
        rw [hds] at hfixdigits
        norm_num [Nat.ofDigits] at hfixdigits
      cases hr : tail.reverse with
      | nil =>
        have : tail = [] := (List.reverse_eq_nil_iff).mp hr
        contradiction
      | cons a rest =>
        have htail_eq : tail = rest.reverse ++ [a] :=
          (List.reverse_eq_cons_iff).mp hr
        let mid := rest.reverse
        have hfix' : Nat.ofDigits 10 (b :: (mid ++ [a])).reverse =
            Nat.ofDigits 10 (b :: (mid ++ [a])) + 9 := by
          simpa [ds, hds, htail_eq, mid] using hfixdigits
        have ha : a < 10 := by
          have haMem : a ∈ Nat.digits 10 x := by
            change a ∈ ds
            rw [hds, htail_eq]
            simp
          exact Nat.digits_lt_base (by norm_num) haMem
        have hb : b < 10 := by
          have hbMem : b ∈ Nat.digits 10 x := by
            change b ∈ ds
            rw [hds]
            simp
          exact Nat.digits_lt_base (by norm_num) hbMem
        have heq := endpoints_cases mid a b ha hb hfix'
        have hdigmid : ∀ d ∈ mid, d < 10 := by
          intro d hd
          have hdm : d ∈ Nat.digits 10 x := by
            change d ∈ ds
            rw [hds, htail_eq]
            simp [mid, hd]
          exact Nat.digits_lt_base (by norm_num) hdm
        have hbound := ofDigits_lt_pow_length mid hdigmid
        have hdigrev : ∀ d ∈ mid.reverse, d < 10 := by
          intro d hd
          exact hdigmid d (by simpa using hd)
        have hrevbound := ofDigits_lt_pow_length mid.reverse hdigrev
        have hrevbound' : Nat.ofDigits 10 mid.reverse < 10 ^ mid.length := by
          simpa using hrevbound
        rcases heq with ⟨ha9, hb0⟩ | hbnext
        · have hinner := (endpoints_inner mid a b hfix').1 ⟨ha9, hb0⟩
          have hpos : 0 < 10 ^ mid.length := pow_pos (by norm_num : 0 < (10:ℕ)) _
          omega
        · have hinner := (endpoints_inner mid a b hfix').2 hbnext
          have hrevzero : Nat.ofDigits 10 mid.reverse = 0 := by omega
          have hmidzero := ofDigits_reverse_zero_imp_zero mid hrevzero
          have hlen : mid.length = 0 := by
            by_contra hn
            have hp : 10 ≤ 10 ^ mid.length := by
              have hle : 1 ≤ mid.length := Nat.one_le_iff_ne_zero.mpr hn
              have hpow : mid.length = (mid.length - 1) + 1 := by omega
              rw [hpow, pow_succ]
              have hpos : 0 < 10 ^ (mid.length - 1) := pow_pos (by norm_num) _
              nlinarith
            omega
          have hmid : mid = [] := List.eq_nil_of_length_eq_zero hlen
          have hmaxdigits : max b a = 9 := by
            have hm' : ds.foldr max 0 = 9 := by simpa [maxDigit, ds] using hmax
            simpa [hds, htail_eq, mid, hmid, List.foldr_append] using hm'
          have ha8 : a = 8 := by omega
          have hb9 : b = 9 := by omega
          have hx89 : x = 89 := by
            rw [← hxrep]
            simpa [hds, htail_eq, mid, hmid, ha8, hb9, Nat.ofDigits_cons]
          exact hx89
  · intro hx
    rcases hx with rfl | rfl
    · simp [f, reverse, maxDigit, Nat.digits_zero]
    · have hd : Nat.digits 10 89 = [9, 8] := by norm_num [Nat.digits, Nat.digitsAux]
      simp [f, reverse, maxDigit, hd, Nat.ofDigits_cons]

end OMA.S_oeis_a097154

theorem OMA.solution : type_of% @OMA.S_oeis_a097154.main :=
  OMA.S_oeis_a097154.fixedPoints
