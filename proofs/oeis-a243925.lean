import OMAStatements.S_oeis_a243925

namespace OMA.S_oeis_a243925

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


theorem back2 (x : ℚ) (hx : Reach 2 x) : Reach 2 (x-1) := by
  have hneg : Reach 2 (-2) := by
    simpa using turn_reach (x := 1) (by decide) (one_reach 2)
  have hminus : Reach 2 (-1) := by convert plus_reach hneg using 1; norm_num
  have hzero : Reach 2 0 := by simpa using plus_reach hminus
  by_cases h0 : x = 0
  · simpa [h0] using hminus
  by_cases h1 : x = 1
  · simpa [h1] using hzero
  by_cases h2 : x = 2
  · simpa [h2, show (2:ℚ)-1=1 by norm_num] using one_reach 2
  have hx1 : x-1 ≠ 0 := sub_ne_zero.mpr h1
  have hx2 : x-2 ≠ 0 := sub_ne_zero.mpr h2
  have s1 := turn_reach h0 hx
  have t1 : Reach 2 (2*(x-1)/x) := by
    have h := plus_reach (plus_reach s1)
    convert h using 1
    field_simp
    ring
  have s2 : Reach 2 (-x/(x-1)) := by
    have h := turn_reach (div_ne_zero (mul_ne_zero (by decide) hx1) h0) t1
    convert h using 1
    field_simp
  have t2 : Reach 2 ((x-2)/(x-1)) := by
    have h := plus_reach (plus_reach s2)
    convert h using 1
    field_simp
    ring
  have s3 : Reach 2 (-2*(x-1)/(x-2)) := by
    have h := turn_reach (div_ne_zero hx2 hx1) t2
    convert h using 1
    field_simp
  have t3 : Reach 2 (-2/(x-2)) := by
    have h := plus_reach (plus_reach s3)
    convert h using 1
    field_simp
    ring
  have s4 : Reach 2 (x-2) := by
    have h := turn_reach (div_ne_zero (by decide) hx2) t3
    convert h using 1
    field_simp
  convert plus_reach s4 using 1
  ring

private theorem prove_two : ∀ x : ℚ, ∃! n, x ∈ row 2 n :=
  fun x => once_of_reach (all_reach 2 (by decide) back2 x)

end OMA.S_oeis_a243925

theorem OMA.solution : type_of% @OMA.S_oeis_a243925.main :=
  OMA.S_oeis_a243925.prove_two
