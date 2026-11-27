import OMAStatements.S_oeis_a243928

namespace OMA.S_oeis_a243928

def Reach (d x : ℚ) : Prop := ∃ k, x ∈ seen d k

private theorem one_reach (d : ℚ) : Reach d 1 := ⟨0, rfl⟩

private theorem plus_reach {d x : ℚ} : Reach d x → Reach d (x+1) := by
  rintro ⟨n, hn⟩
  exact ⟨n+1, Or.inl (Or.inr ⟨x, hn, rfl⟩)⟩

private theorem turn_reach {d x : ℚ} (hx : x ≠ 0) : Reach d x → Reach d (-d/x) := by
  rintro ⟨n, hn⟩
  exact ⟨n+1, Or.inr ⟨x, ⟨hn, hx⟩, rfl⟩⟩

private theorem translate {d : ℚ} (back : ∀ x, Reach d x → Reach d (x-1))
    (x : ℚ) (a : ℤ) (hx : Reach d x) : Reach d (x + a) := by
  induction a using Int.induction_on with
  | zero => simpa using hx
  | succ n ih =>
      have h := plus_reach ih
      convert h using 1 <;> push_cast <;> ring
  | pred n ih =>
      have h := back _ ih
      convert h using 1 <;> push_cast <;> ring

theorem all_reach (d : ℤ) (hd : d ≠ 0)
    (back : ∀ x : ℚ, Reach d x → Reach d (x-1)) (x : ℚ) :
    Reach d x := by
  induction x using (measure Rat.den).wf.induction with
  | h x ih =>
      let b : ℤ := x.den
      let a : ℤ := x.num
      let r := a % b
      let q := a / b
      have hb : 0 < b := by
        dsimp [b]
        exact_mod_cast x.pos
      have hr : 0 ≤ r := Int.emod_nonneg _ hb.ne'
      have hs : r < b := Int.emod_lt_of_pos _ hb
      have hmain : x = (r : ℚ)/(b : ℚ) + q := by
        have hq := Int.emod_add_mul_ediv a b
        have hf := congrArg (fun x : ℤ => (x : ℚ)) hq
        change (r+b*q : ℤ) = a at hq
        change ((r+b*q : ℤ) : ℚ) = (a : ℚ) at hf
        push_cast at hf
        have hbq : (b : ℚ) ≠ 0 := by exact_mod_cast hb.ne'
        rw [← x.num_div_den]
        change (a : ℚ)/(b : ℚ) = _
        field_simp
        linarith
      have hz : Reach d ((r : ℚ)/(b : ℚ)) := by
        by_cases hr0 : r = 0
        · simp [hr0]
          simpa using back 1 (one_reach (d : ℚ))
        let y : ℚ := (-(d*b : ℤ) : ℚ)/(r : ℚ)
        have hyr : y.den ∣ r.toNat := by
          have h := Rat.den_dvd (-(d*b)) r
          rw [Rat.divInt_eq_div] at h
          have h' : (y.den : ℤ) ∣ (r.toNat : ℤ) := by
            rw [Int.toNat_of_nonneg hr]
            exact h
          exact_mod_cast h'
        have hylt : y.den < x.den := by
          have hden := Nat.le_of_dvd (by omega : 0 < r.toNat) hyr
          have hrt : (r.toNat : ℤ) < b := by simpa [Int.toNat_of_nonneg hr] using hs
          omega
        have hy := ih y hylt
        have hrQ : (r : ℚ) ≠ 0 := by exact_mod_cast hr0
        have hbQ : (b : ℚ) ≠ 0 := by exact_mod_cast hb.ne'
        have hdQ : (d : ℚ) ≠ 0 := by exact_mod_cast hd
        have hy0 : y ≠ 0 := by
          dsimp [y]
          push_cast
          exact div_ne_zero (neg_ne_zero.mpr (mul_ne_zero hdQ hbQ)) hrQ
        have hturn := turn_reach hy0 hy
        have he : -(d : ℚ)/y = (r : ℚ)/(b : ℚ) := by
          dsimp [y]
          push_cast
          field_simp
        rwa [he] at hturn
      rw [hmain]
      exact translate back _ q hz

theorem once_of_reach {d x : ℚ} (h : Reach d x) : ∃! n, x ∈ row d n := by
  classical
  let p (n : ℕ) := x ∈ seen d n
  have h' : ∃ n, p n := h
  refine ⟨Nat.find h', ⟨Nat.find_spec h', ?_⟩, ?_⟩
  · exact fun n hn => Nat.find_min' h' hn
  · rintro n ⟨hn,hmin⟩
    exact le_antisymm (hmin (Nat.find_spec h')) (Nat.find_min' h' hn)

private theorem shift_reach {d x : ℚ} (n : ℕ) : Reach d x → Reach d (x+n) := by
  induction n with
  | zero => intro h; simpa using h
  | succ n ih =>
      intro hx
      have h := plus_reach (ih hx)
      convert h using 1 <;> push_cast <;> ring

private theorem seed3 (q : ℕ) : Reach 3 (1+q) := by
  have h : Reach 3 1 := ⟨0, by simp [seen]⟩
  simpa using shift_reach q h

private theorem exceptional3 (x : ℚ) (hx : x = 0 ∨ x = 1 ∨ x = 3/2 ∨ x = 2 ∨ x = 3) :
    Reach 3 (x-1) := by
  rcases hx with rfl | rfl | rfl | rfl | rfl
  · have h : Reach 3 (-3) := by simpa using turn_reach (d := (3:ℚ)) (by norm_num) (seed3 0)
    have h := shift_reach 2 h
    convert h using 1 <;> norm_num
  · have h : Reach 3 (-3) := by simpa using turn_reach (d := (3:ℚ)) (by norm_num) (seed3 0)
    have h := shift_reach 3 h
    simpa using h
  · have h : Reach 3 2 := by convert seed3 1 using 1 <;> norm_num
    have h : Reach 3 (-3/2) := turn_reach (by norm_num) h
    have h := plus_reach h
    have h := plus_reach h
    norm_num at h ⊢
    simpa using h
  · convert seed3 0 using 1 <;> norm_num
  · convert seed3 1 using 1 <;> norm_num

theorem back3 : ∀ x : ℚ, Reach 3 x → Reach 3 (x-1) := by
  intro x hx
  by_cases h0 : x = 0
  · exact exceptional3 x (Or.inl h0)
  by_cases h1 : x = 1
  · exact exceptional3 x (Or.inr (Or.inl h1))
  by_cases h32 : x = 3/2
  · exact exceptional3 x (Or.inr (Or.inr (Or.inl h32)))
  by_cases h2 : x = 2
  · exact exceptional3 x (Or.inr (Or.inr (Or.inr (Or.inl h2))))
  by_cases h3 : x = 3
  · exact exceptional3 x (Or.inr (Or.inr (Or.inr (Or.inr h3))))
  have hx0 : x ≠ 0 := h0
  have hx1 : x-1 ≠ 0 := by intro h; apply h1; linarith
  have hx32 : 2*x-3 ≠ 0 := by intro h; apply h32; linarith
  have hx2 : x-2 ≠ 0 := by intro h; apply h2; linarith
  have hx3 : x-3 ≠ 0 := by intro h; apply h3; linarith
  have h0 : Reach 3 (-3/x) := turn_reach hx0 hx
  have e1 : -3/x + 3 = 3*(x-1)/x := by field_simp; ring
  have h1 : Reach 3 (3*(x-1)/x) := by
    have h := shift_reach 3 h0
    rw [← e1]
    exact h
  have h2 : Reach 3 (-x/(x-1)) := by
    have h := turn_reach (div_ne_zero (mul_ne_zero (by norm_num) hx1) hx0) h1
    have e : -3/(3*(x-1)/x) = -x/(x-1) := by field_simp <;> ring
    rw [← e]
    exact h
  have e2 : -x/(x-1) + 3 = (2*x-3)/(x-1) := by field_simp; ring
  have h3 : Reach 3 ((2*x-3)/(x-1)) := by
    have h := shift_reach 3 h2
    rw [← e2]
    exact h
  have h4 : Reach 3 (-3*(x-1)/(2*x-3)) := by
    have h := turn_reach (div_ne_zero hx32 hx1) h3
    have e : -3/((2*x-3)/(x-1)) = -3*(x-1)/(2*x-3) := by field_simp <;> ring
    rw [← e]
    exact h
  have e3 : -3*(x-1)/(2*x-3) + 3 = 3*(x-2)/(2*x-3) := by
    apply (eq_div_iff hx32).2
    rw [add_mul, div_mul_cancel₀ _ hx32]
    ring
  have h5 : Reach 3 (3*(x-2)/(2*x-3)) := by
    have h := shift_reach 3 h4
    rw [← e3]
    exact h
  have h6 : Reach 3 (-(2*x-3)/(x-2)) := by
    have h := turn_reach (div_ne_zero (mul_ne_zero (by norm_num) hx2) hx32) h5
    have e : -3/(3*(x-2)/(2*x-3)) = -(2*x-3)/(x-2) := by field_simp <;> ring
    rw [← e]
    exact h
  have e4 : -(2*x-3)/(x-2) + 3 = (x-3)/(x-2) := by field_simp; ring
  have h7 : Reach 3 ((x-3)/(x-2)) := by
    have h := shift_reach 3 h6
    rw [← e4]
    exact h
  have h8 : Reach 3 (-3*(x-2)/(x-3)) := by
    have h := turn_reach (div_ne_zero hx3 hx2) h7
    have e : -3/((x-3)/(x-2)) = -3*(x-2)/(x-3) := by field_simp <;> ring
    rw [← e]
    exact h
  have e5 : -3*(x-2)/(x-3) + 3 = -3/(x-3) := by field_simp; ring
  have h9 : Reach 3 (-3/(x-3)) := by
    have h := shift_reach 3 h8
    rw [← e5]
    exact h
  have h10 : Reach 3 (x-3) := by
    have h := turn_reach (div_ne_zero (by norm_num) hx3) h9
    have e : -3/(-3/(x-3)) = x-3 := by field_simp <;> ring
    rw [← e]
    exact h
  have h11 := shift_reach 2 h10
  have e6 : x-3+2 = x-1 := by ring
  rw [← e6]
  exact h11



private theorem prove_three : ∀ x : ℚ, ∃! n, x ∈ row 3 n :=
  fun x => once_of_reach (all_reach 3 (by decide) back3 x)

end OMA.S_oeis_a243928

theorem OMA.solution : type_of% @OMA.S_oeis_a243928.main :=
  OMA.S_oeis_a243928.prove_three
