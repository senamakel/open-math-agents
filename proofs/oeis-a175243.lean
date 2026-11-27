import OMAStatements.S_oeis_a175243

open scoped BigOperators

open scoped BigOperators

namespace OMA.S_oeis_a175243

theorem expand_symmetric_powers (r : ℝ) (hr : r ≠ 0) (k n : ℕ) :
    (r^n+(r⁻¹)^n-2)^k =
      ∑ j ∈ Finset.range (2*k+1), (-(1:ℝ))^(2*k-j) *
        ((2*k).choose j : ℝ) * (r^j/r^k)^n := by
  have h0 : r^n ≠ 0 := pow_ne_zero _ hr
  have hbase : r^n+(r⁻¹)^n-2 = (r^n-1)^2/r^n := by
    rw [inv_pow]
    field_simp
    ring
  rw [hbase, div_pow, ← pow_mul, sub_eq_add_neg, add_pow, Finset.sum_div]
  apply Finset.sum_congr rfl
  intro j _
  rw [div_pow, ← pow_mul r j n, ← pow_mul r k n]
  rw [Nat.mul_comm j n, Nat.mul_comm k n, ← pow_mul r n j]
  ring

end OMA.S_oeis_a175243
namespace OMA.S_oeis_a175243

theorem column_recurrence_of_modes (m : ℕ) (r : ℝ) (hr : r ≠ 0)
    (hCheb : ∀ n : ℕ, 2 * (Polynomial.Chebyshev.T ℝ n).eval (1+(m : ℝ)/2) =
      r^n+(r⁻¹)^n)
    (P : Polynomial ℤ)
    (hModes : ∀ j ∈ Finset.range (2*(m-1)+1), ∀ n : ℕ,
      ∑ i ∈ Finset.range (P.natDegree+1),
        (P.coeff i : ℝ) * ((n+i : ℕ) : ℝ) * (r^j/r^(m-1))^(n+i) = 0) :
    ∀ n : ℕ, ∑ i ∈ Finset.range (P.natDegree+1), (P.coeff i : ℝ) * column m (n+i) = 0 := by
  let c : ℕ → ℝ := fun j => (-(1:ℝ))^(2*(m-1)-j) *
    ((2*(m-1)).choose j : ℝ) / (m : ℝ)
  let mode : ℕ → ℝ := fun j => r^j/r^(m-1)
  have hf (n : ℕ) : column m n =
      ∑ j ∈ Finset.range (2*(m-1)+1), c j * ((n:ℝ) * (mode j)^n) := by
    simp only [column, hCheb, expand_symmetric_powers r hr, Finset.mul_sum, Finset.sum_div]
    apply Finset.sum_congr rfl
    intro j _
    dsimp [c, mode]
    ring
  intro n
  simp only [hf, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_eq_zero
  intro j hj
  calc
    _ = c j * ∑ i ∈ Finset.range (P.natDegree+1),
        (P.coeff i : ℝ) * ((n+i : ℕ) : ℝ) * (mode j)^(n+i) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      ring
    _ = 0 := by rw [hModes j hj, mul_zero]

end OMA.S_oeis_a175243

namespace OMA.S_oeis_a175243

theorem ratio_power_cases (r : ℝ) (hr : r ≠ 0) (j k : ℕ) (hj : j ≤ 2*k) :
    (∃ i ≤ k, r^j/r^k = r^i) ∨ (∃ i ≤ k, r^j/r^k = (r⁻¹)^i) := by
  rcases le_total k j with h | h
  · left
    refine ⟨j-k, by omega, ?_⟩
    have hpow : r^j = r^k * r^(j-k) := by
      rw [← pow_add]
      congr 1
      omega
    rw [hpow, mul_comm]
    exact mul_div_cancel_right₀ _ (pow_ne_zero _ hr)
  · right
    refine ⟨k-j, Nat.sub_le _ _, ?_⟩
    have hpow : r^k = r^j * r^(k-j) := by
      rw [← pow_add, Nat.add_sub_of_le h]
    rw [inv_pow, hpow]
    field_simp

end OMA.S_oeis_a175243
namespace OMA.S_oeis_a175243

theorem column_recurrence_of_double_roots (m : ℕ) (r : ℝ) (hr : r ≠ 0)
    (hCheb : ∀ n : ℕ, 2 * (Polynomial.Chebyshev.T ℝ n).eval (1+(m : ℝ)/2) =
      r^n+(r⁻¹)^n)
    (P : Polynomial ℤ)
    (hRoots : ∀ k ≤ m-1,
      ∀ z : ℝ, z = r^k ∨ z = (r⁻¹)^k →
        (P.map (Int.castRingHom ℝ)).eval z = 0 ∧
          (P.map (Int.castRingHom ℝ)).derivative.eval z = 0)
    (hShift : ∀ (Q : Polynomial ℝ) (z : ℝ), Q.eval z = 0 →
      Q.derivative.eval z = 0 → ∀ n : ℕ,
        ∑ i ∈ Finset.range (Q.natDegree+1),
          Q.coeff i * ((n+i : ℕ) : ℝ) * z^(n+i) = 0) :
    ∀ n : ℕ, ∑ i ∈ Finset.range (P.natDegree+1), (P.coeff i : ℝ) * column m (n+i) = 0 := by
  apply column_recurrence_of_modes m r hr hCheb P
  intro j hj n
  have hj' : j ≤ 2*(m-1) := Nat.le_of_lt_succ (Finset.mem_range.mp hj)
  let z := r^j / r^(m-1)
  have hz : ∃ k ≤ m-1, z = r^k ∨ z = (r⁻¹)^k := by
    rcases ratio_power_cases r hr j (m-1) hj' with ⟨k,hk,h⟩ | ⟨k,hk,h⟩
    · exact ⟨k,hk,Or.inl h⟩
    · exact ⟨k,hk,Or.inr h⟩
  obtain ⟨k,hk,hz⟩ := hz
  obtain ⟨he,hd⟩ := hRoots k hk z hz
  have hc : Function.Injective (Int.castRingHom ℝ) := Int.cast_injective
  simpa only [Polynomial.natDegree_map_eq_of_injective hc, Polynomial.coeff_map,
    Int.coe_castRingHom] using hShift (P.map (Int.castRingHom ℝ)) z he hd n

end OMA.S_oeis_a175243

open Polynomial
open scoped BigOperators

namespace A175243

lemma weightedCoeffSum_eq (P : ℝ[X]) (r : ℝ) (n : ℕ) :
    (∑ i ∈ Finset.range (P.natDegree + 1), P.coeff i * ((n + i : ℕ) : ℝ) * r ^ (n + i)) =
      r ^ n * ((n : ℝ) * P.eval r + r * P.derivative.eval r) := by
  calc
    _ = ∑ i ∈ Finset.range (P.natDegree + 1),
        r ^ n * ((n : ℝ) * (P.coeff i * r ^ i) + P.coeff i * (i : ℝ) * r ^ i) := by
      apply Finset.sum_congr rfl
      intro i hi
      rw [Nat.cast_add, pow_add]
      ring
    _ = r ^ n * ((n : ℝ) * P.eval r + r * P.derivative.eval r) := by
      rw [← Finset.mul_sum]
      rw [Finset.sum_add_distrib]
      have hval : (∑ i ∈ Finset.range (P.natDegree + 1),
          (n : ℝ) * (P.coeff i * r ^ i)) = (n : ℝ) * P.eval r := by
        rw [Polynomial.eval_eq_sum_range, Finset.mul_sum]
      have hder : (∑ i ∈ Finset.range (P.natDegree + 1),
          P.coeff i * (i : ℝ) * r ^ i) = r * P.derivative.eval r := by
        rw [Polynomial.derivative_eval]
        rw [P.sum_over_range (by intro i; simp)]
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro i hi
        cases i with
        | zero => simp
        | succ i => simp only [Nat.succ_sub_one, Nat.cast_succ, pow_succ]; ring
      rw [hder]
      rw [hval]

theorem double_root_annihilates (P : ℝ[X]) (r : ℝ)
    (hP : P.eval r = 0) (hD : P.derivative.eval r = 0) (n : ℕ) :
    (∑ i ∈ Finset.range (P.natDegree + 1),
      P.coeff i * ((n + i : ℕ) : ℝ) * r ^ (n + i)) = 0 := by
  rw [weightedCoeffSum_eq]
  simp [hP, hD]

end A175243
namespace OMA.S_oeis_a175243

open Polynomial

theorem chebC_eval_pow (r : ℝ) (hr : r ≠ 0) (n : ℕ) :
    (Polynomial.Chebyshev.C ℝ n).eval (r + r⁻¹) = r^n + (r⁻¹)^n := by
  induction n using Nat.twoStepInduction with
  | zero => simp [Polynomial.Chebyshev.C_zero]; norm_num
  | one => simp [Polynomial.Chebyshev.C_one]
  | more n ih0 ih1 =>
    have hrec := Polynomial.Chebyshev.C_add_two ℝ (n : ℤ)
    have hev : (Polynomial.Chebyshev.C ℝ (n + 2 : ℕ)).eval (r + r⁻¹) =
        (r + r⁻¹) * ((Polynomial.Chebyshev.C ℝ (n + 1 : ℕ)).eval (r + r⁻¹)) -
          (Polynomial.Chebyshev.C ℝ n).eval (r + r⁻¹) := by
      convert congrArg (fun p : ℝ[X] => p.eval (r + r⁻¹)) hrec using 1 <;> norm_cast
      simp [Polynomial.eval_sub, Polynomial.eval_mul, Polynomial.eval_X]
    rw [hev, ih0, ih1]
    have hp : r * r⁻¹ = 1 := mul_inv_cancel₀ hr
    have hpow1 : r ^ (n + 1) = r ^ n * r := by rw [pow_succ]
    have hpow2 : (r⁻¹) ^ (n + 1) = (r⁻¹) ^ n * r⁻¹ := by rw [pow_succ]
    have hpow3 : r ^ (n + 2) = r ^ (n + 1) * r := by
      rw [show n + 2 = (n + 1) + 1 by omega, pow_succ]
    have hpow4 : (r⁻¹) ^ (n + 2) = (r⁻¹) ^ (n + 1) * r⁻¹ := by
      rw [show n + 2 = (n + 1) + 1 by omega, pow_succ]
    rw [hpow3, hpow4, hpow1, hpow2]
    calc
      (r + r⁻¹) * (r ^ n * r + (r⁻¹) ^ n * r⁻¹) - (r ^ n + (r⁻¹) ^ n) =
          r ^ n * r ^ 2 + (r⁻¹) ^ n * (r⁻¹) ^ 2 := by
        rw [pow_two, pow_two]
        calc
          _ = (r ^ n * r ^ 2 + (r⁻¹) ^ n * (r⁻¹) ^ 2) +
              (r * r⁻¹ - 1) * (r ^ n + (r⁻¹) ^ n) := by ring
          _ = _ := by rw [hp]; simp [pow_two]
      _ = r ^ (n + 1) * r + (r⁻¹) ^ (n + 1) * r⁻¹ := by
        rw [pow_two, pow_two, hpow1, hpow2]
        ring


end OMA.S_oeis_a175243

open scoped BigOperators

namespace OMA.S_oeis_a175243

open Polynomial

noncomputable def Cval (m j : ℕ) : ℤ :=
  (Polynomial.Chebyshev.C ℤ j).eval ((m : ℤ) + 2)

noncomputable def annihilator (m : ℕ) : Polynomial ℤ :=
  (X - 1)^2 * ∏ j ∈ Finset.range (m - 1),
    (X^2 - C (Cval m (j + 1)) * X + 1)^2

theorem quadratic_isMonicOfDegree (c : ℤ) :
    IsMonicOfDegree (X^2 - C c * X + 1 : Polynomial ℤ) 2 := by
  simpa using (isMonicOfDegree_sub_add_two c (1 : ℤ))

theorem factor_monic (m j : ℕ) :
    ((X^2 - C (Cval m (j + 1)) * X + 1 : Polynomial ℤ)^2).Monic := by
  exact (quadratic_isMonicOfDegree _).pow 2 |>.monic

theorem factor_natDegree (m j : ℕ) :
    ((X^2 - C (Cval m (j + 1)) * X + 1 : Polynomial ℤ)^2).natDegree = 4 := by
  exact (quadratic_isMonicOfDegree _).pow 2 |>.natDegree_eq

theorem annihilator_monic (m : ℕ) : (annihilator m).Monic := by
  unfold annihilator
  apply Monic.mul
  · exact (monic_X_sub_C (1 : ℤ)).pow 2
  · apply monic_prod_of_monic
    intro j hj
    exact factor_monic m j

theorem annihilator_natDegree (m : ℕ) (hm : 0 < m) :
    (annihilator m).natDegree = 4*m-2 := by
  unfold annihilator
  have hp : ((X - 1 : Polynomial ℤ)^2).Monic :=
    (monic_X_sub_C (1 : ℤ)).pow 2
  have hq : (∏ j ∈ Finset.range (m - 1),
      (X^2 - C (Cval m (j + 1)) * X + 1 : Polynomial ℤ)^2).Monic := by
    apply monic_prod_of_monic
    intro j hj
    exact factor_monic m j
  rw [natDegree_mul hp.ne_zero hq.ne_zero]
  simp only [natDegree_pow]
  rw [show (X - 1 : Polynomial ℤ) = X - C (1 : ℤ) by simp,
    natDegree_X_sub_C]
  rw [natDegree_prod_of_monic]
  · simp_rw [factor_natDegree]
    simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    have hm1 : m - 1 + 1 = m := by omega
    push_cast
    omega
  · intro j hj
    exact factor_monic m j

end OMA.S_oeis_a175243
namespace OMA.S_oeis_a175243

open Polynomial

theorem exists_positive_prism_root (m : ℕ) (hm : 0 < m) :
    ∃ r : ℝ, 1 < r ∧ r+r⁻¹ = (m:ℝ)+2 := by
  let x : ℝ := 1 + (m:ℝ)/2
  have hm' : 0 < (m : ℝ) := by exact_mod_cast hm
  have hx : 1 < x := by dsimp [x]; linarith
  let s := Real.sqrt (x^2-1)
  have hs : s^2 = x^2-1 := Real.sq_sqrt (by nlinarith)
  have hs0 : 0 ≤ s := Real.sqrt_nonneg _
  let r := x+s
  have hr : 1 < r := by dsimp [r]; linarith
  have hmul : r * (x-s) = 1 := by dsimp [r]; nlinarith
  have hinv : r⁻¹ = x-s := by
    have hh : x-s = 1/r := (eq_div_iff (by linarith : r ≠ 0)).2
      (by simpa only [mul_comm] using hmul)
    simpa only [one_div] using hh.symm
  refine ⟨r,hr,?_⟩
  rw [hinv]
  dsimp [r,x]
  ring

theorem T_value_of_C_value (m : ℕ) (r : ℝ) (hr : r+r⁻¹ = (m:ℝ)+2)
    (hC : ∀ n : ℕ, (Polynomial.Chebyshev.C ℝ n).eval (r+r⁻¹) = r^n+(r⁻¹)^n) :
    ∀ n : ℕ, 2 * (Polynomial.Chebyshev.T ℝ n).eval (1+(m:ℝ)/2) = r^n+(r⁻¹)^n := by
  intro n
  have h := congrArg (fun p : Polynomial ℝ => p.eval (1+(m:ℝ)/2))
    (Polynomial.Chebyshev.C_comp_two_mul_X ℝ (n:ℤ))
  simp only [Polynomial.eval_comp, Polynomial.eval_mul, Polynomial.eval_ofNat,
    Polynomial.eval_X] at h
  rw [show 2 * (1 + (m:ℝ)/2) = r+r⁻¹ by rw [hr]; ring] at h
  exact h.symm.trans (hC n)

theorem Cval_of_root (m : ℕ) (r : ℝ) (hr : r+r⁻¹ = (m:ℝ)+2)
    (hC : ∀ n : ℕ, (Polynomial.Chebyshev.C ℝ n).eval (r+r⁻¹) = r^n+(r⁻¹)^n)
    (j : ℕ) :
    (Cval m j : ℝ) = r^j+(r⁻¹)^j := by
  unfold Cval
  change (Int.castRingHom ℝ) ((Polynomial.Chebyshev.C ℤ j).eval ((m:ℤ)+2)) = _
  rw [← Polynomial.eval₂_at_apply,
    Polynomial.eval₂_eq_eval_map, Polynomial.Chebyshev.map_C]
  simp only [map_add, Int.coe_castRingHom, Int.cast_natCast, Int.cast_ofNat]
  rw [← hr]
  exact hC j

end OMA.S_oeis_a175243

namespace OMA.S_oeis_a175243

open Polynomial

theorem eval_derivative_eq_zero_of_squared_factor (Q F : Polynomial ℝ) (z : ℝ)
    (hF : F.eval z = 0) (hdiv : F^2 ∣ Q) :
    Q.eval z = 0 ∧ Q.derivative.eval z = 0 := by
  obtain ⟨G, hG⟩ := hdiv
  rw [hG, pow_two]
  simp [derivative_mul, hF]

end OMA.S_oeis_a175243

namespace OMA.S_oeis_a175243

open Polynomial

theorem quadratic_eval_of_reciprocal_pair (r : ℝ) (hr : r ≠ 0) (k : ℕ) (c : ℝ)
    (hc : c = r^k + (r⁻¹)^k) (z : ℝ) (hz : z = r^k ∨ z = (r⁻¹)^k) :
    (X^2 - C c * X + 1 : Polynomial ℝ).eval z = 0 := by
  have hmul : r^k * (r⁻¹)^k = 1 := by rw [← mul_pow, mul_inv_cancel₀ hr, one_pow]
  simp only [eval_add, eval_sub, eval_pow, eval_mul, eval_C, eval_X, eval_one, hc]
  rcases hz with rfl | rfl <;> linear_combination -hmul

end OMA.S_oeis_a175243
namespace OMA.S_oeis_a175243

open Polynomial

theorem annihilator_has_double_roots (m : ℕ) (r : ℝ) (hr : r ≠ 0)
    (hC : ∀ k, (Cval m k : ℝ) = r^k+(r⁻¹)^k)
    (k : ℕ) (hk : k ≤ m-1) (z : ℝ) (hz : z = r^k ∨ z = (r⁻¹)^k) :
    ((annihilator m).map (Int.castRingHom ℝ)).eval z = 0 ∧
      ((annihilator m).map (Int.castRingHom ℝ)).derivative.eval z = 0 := by
  cases k with
  | zero =>
    have hz1 : z = 1 := by simpa using hz
    have hD : ((X - 1 : Polynomial ℤ)^2) ∣ annihilator m := by
      unfold annihilator
      exact dvd_mul_right _ _
    have hmapped := Polynomial.map_dvd (Int.castRingHom ℝ) hD
    exact eval_derivative_eq_zero_of_squared_factor _ (X-1) z
      (by simp [hz1]) (by simpa using hmapped)
  | succ k =>
    let Q : Polynomial ℤ := X^2 - C (Cval m (k+1)) * X + 1
    have hD : Q^2 ∣ annihilator m := by
      unfold annihilator
      apply dvd_mul_of_dvd_right
      exact Finset.dvd_prod_of_mem _ (Finset.mem_range.mpr hk)
    have hmapped := Polynomial.map_dvd (Int.castRingHom ℝ) hD
    have he : (Q.map (Int.castRingHom ℝ)).eval z = 0 := by
      simpa only [Q, Polynomial.map_add, Polynomial.map_sub, Polynomial.map_mul,
        Polynomial.map_pow, Polynomial.map_one, Polynomial.map_X, Polynomial.map_C,
        Int.coe_castRingHom] using
          quadratic_eval_of_reciprocal_pair r hr (k+1) (Cval m (k+1)) (hC _) z hz
    exact eval_derivative_eq_zero_of_squared_factor _ _ z he
      (by simpa only [Polynomial.map_pow] using hmapped)

end OMA.S_oeis_a175243
open OMA.S_oeis_a175243 in
theorem OMA.solution : type_of% @OMA.S_oeis_a175243.main := by
  intro m hm
  obtain ⟨r, hr, hrel⟩ := exists_positive_prism_root m hm
  have hr0 : r ≠ 0 := by linarith
  have hC := chebC_eval_pow r hr0
  refine ⟨annihilator m, annihilator_monic m, annihilator_natDegree m hm, ?_⟩
  intro n _
  exact column_recurrence_of_double_roots m r hr0 (T_value_of_C_value m r hrel hC)
    (annihilator m) (annihilator_has_double_roots m r hr0 (Cval_of_root m r hrel hC))
    A175243.double_root_annihilates n
