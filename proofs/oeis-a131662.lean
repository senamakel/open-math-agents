import OMAStatements.S_oeis_a131662

namespace OMA.S_oeis_a131662

open PowerSeries

def residue : ℕ → ℕ
  | 0 => 2519
  | 1 => 11879
  | 2 => 13320
  | 3 => 14399
  | 4 => 15840
  | 5 => 25200
  | 6 => 27719
  | _ => 27720

def model : ℕ → ℕ
  | 0 => 0
  | n+1 => 27720*(n/8) + residue (n%8)

theorem model_shift (n : ℕ) (hn : 0 < n) : model (n+8) = model n + 27720 := by
  obtain ⟨m,rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn.ne'
  rw [show m.succ+8=(m+8)+1 by omega]
  simp only [model]
  rw [show (m+8)/8=m/8+1 by omega, show (m+8)%8=m%8 by omega]
  omega

theorem model_recurrence (n : ℕ) (hn : 9 < n) :
    model n + model (n-9) = model (n-1) + model (n-8) := by
  have h₀ := model_shift (n-8) (by omega)
  have h₁ := model_shift (n-9) (by omega)
  rw [show n-8+8=n by omega] at h₀
  rw [show n-9+8=n-1 by omega] at h₁
  omega

private theorem numerator_expanded : numerator =
    C 2519 * X^1 + C 9360 * X^2 + C 1441 * X^3 + C 1079 * X^4 +
    C 1441 * X^5 + C 9360 * X^6 + C 2519 * X^7 + X^8 := by
  unfold numerator
  simp only [map_ofNat]
  ring

theorem model_series : denominator * mk (fun n => (model n : ℤ)) = numerator := by
  let F : PowerSeries ℤ := mk (fun n => (model n : ℤ))
  change denominator * F = numerator
  rw [show denominator * F = F - X^1*F - X^8*F + X^9*F by unfold denominator; ring,
    numerator_expanded]
  ext n
  simp only [map_add, map_sub, coeff_X_pow_mul', coeff_C_mul_X_pow, coeff_X_pow, F, coeff_mk]
  by_cases hn : 9 < n
  · have h := model_recurrence n hn
    simp only [if_pos (show 1 ≤ n by omega), if_pos (show 8 ≤ n by omega), if_pos (show 9 ≤ n by omega)]
    simp only [if_neg (show n ≠ 1 by omega), if_neg (show n ≠ 2 by omega),
      if_neg (show n ≠ 3 by omega), if_neg (show n ≠ 4 by omega),
      if_neg (show n ≠ 5 by omega), if_neg (show n ≠ 6 by omega),
      if_neg (show n ≠ 7 by omega), if_neg (show n ≠ 8 by omega), add_zero]
    omega
  · interval_cases n <;> norm_num [model, residue]


end OMA.S_oeis_a131662
namespace OMA.S_oeis_a131662

def positiveResidue (n : ℕ) : ℕ := (n-1)%27720+1

def residueSet (r : ℕ) : Prop :=
  r=2519 ∨ r=11879 ∨ r=13320 ∨ r=14399 ∨ r=15840 ∨ r=25200 ∨ r=27719 ∨ r=27720

private abbrev passes (n : ℕ) : Prop :=
  ∀ d : Fin 13, 1 ≤ d.val → d.val ∣ n ∨ d.val ∣ n+1

private theorem qualifies_iff_passes (n : ℕ) : qualifies n ↔ 0<n ∧ passes n := by
  constructor
  · intro h
    exact ⟨h.1, fun d hd => h.2 d.val hd (by have := d.isLt; omega)⟩
  · intro h
    exact ⟨h.1, fun d hd hu => h.2 ⟨d,by omega⟩ hd⟩

private theorem passes_modEq {a b : ℕ} (h : a ≡ b [MOD 27720]) :
    passes a ↔ passes b := by
  have h1 := h.add (Nat.ModEq.refl (n := 27720) 1)
  have hd (d : Fin 13) (hh : 1≤d.val) : d.val ∣ 27720 := by
    have hb := d.isLt
    interval_cases he : d.val <;> norm_num [he] at *
  constructor
  · intro ha d hh
    exact (ha d hh).imp ((h.dvd_iff (hd d hh)).mp) ((h1.dvd_iff (hd d hh)).mp)
  · intro hb d hh
    exact (hb d hh).imp ((h.dvd_iff (hd d hh)).mpr) ((h1.dvd_iff (hd d hh)).mpr)

private theorem core_table : ∀ u : Fin 360,
    ((8 ∣ u.val ∨ 8 ∣ u.val+1) ∧ (9 ∣ u.val ∨ 9 ∣ u.val+1) ∧
      (10 ∣ u.val ∨ 10 ∣ u.val+1) ∧ (12 ∣ u.val ∨ 12 ∣ u.val+1)) →
    u.val=0 ∨ u.val=359 := by decide +kernel

private theorem core_of_passes (r : ℕ) (h : passes r) : r%360=0 ∨ r%360=359 := by
  let u : Fin 360 := ⟨r%360, Nat.mod_lt _ (by decide)⟩
  have e : u.val ≡ r [MOD 360] := Nat.mod_modEq _ _
  have e1 := e.add (Nat.ModEq.refl (n := 360) 1)
  have hlocal (d : Fin 13) (hp : 1 ≤ d.val) (hd : d.val ∣ 360) :
      d.val ∣ u.val ∨ d.val ∣ u.val+1 :=
    (h d hp).imp ((e.dvd_iff hd).mpr) ((e1.dvd_iff hd).mpr)
  exact core_table u ⟨hlocal 8 (by decide) (by decide), hlocal 9 (by decide) (by decide),
    hlocal 10 (by decide) (by decide), hlocal 12 (by decide) (by decide)⟩

private def passesB (n : ℕ) : Bool :=
  (List.range 12).all (fun d => decide (d+1 ∣ n ∨ d+1 ∣ n+1))

private theorem passesB_iff (n : ℕ) : passesB n = true ↔ passes n := by
  simp only [passesB, List.all_eq_true, List.mem_range, decide_eq_true_eq]
  constructor
  · intro h d hd
    have hl : d.val-1<12 := by have := d.isLt; omega
    have hh := h (d.val-1) hl
    rwa [show d.val-1+1=d.val by omega] at hh
  · intro h d hd
    exact h ⟨d+1,by omega⟩ (by simp)

private def testedResidues : List ℕ :=
  ((List.range 78).flatMap (fun q => [360*q,360*q+359])).filter
    (fun r => passesB r && decide (0<r ∧ r≤27720))

private theorem testedResidues_eq :
    testedResidues = [2519,11879,13320,14399,15840,25200,27719,27720] := by
  decide +kernel

private theorem bounded_table {r q : ℕ} (hq : q<78) (hr : r=360*q ∨ r=360*q+359)
    (hp : passes r) (hr0 : 0<r) (hrM : r≤27720) : residueSet r := by
  have ht : r ∈ testedResidues := by
    apply List.mem_filter.mpr
    constructor
    · exact List.mem_flatMap.mpr ⟨q, List.mem_range.mpr hq, by simpa using hr⟩
    · simp [(passesB_iff _).mpr hp, hr0, hrM]
  rw [testedResidues_eq] at ht
  simpa [residueSet] using ht


theorem qualifies_iff_residueSet (n : ℕ) :
    qualifies n ↔ 0<n ∧ residueSet (positiveResidue n) := by
  rw [qualifies_iff_passes]
  apply and_congr_right
  intro hn
  let r := positiveResidue n
  have hr0 : 0<r := by dsimp [r,positiveResidue]; omega
  have hrM : r≤27720 := by
    dsimp [r,positiveResidue]
    have := Nat.mod_lt (n-1) (by decide : 0<27720)
    omega
  have hmod : n ≡ r [MOD 27720] := by
    change n%27720=r%27720
    dsimp [r,positiveResidue]
    omega
  rw [passes_modEq hmod]
  constructor
  · intro h
    have hq : r/360<78 := by omega
    apply bounded_table hq _ h hr0 hrM
    obtain he | he := core_of_passes r h
    · left
      omega
    · right
      omega
  · intro h
    change residueSet r at h
    rcases h with hr|hr|hr|hr|hr|hr|hr|hr <;> rw [hr] <;> decide +kernel

end OMA.S_oeis_a131662

theorem nth_eq_of_strictMono_range {P : ℕ → Prop} [DecidablePred P]
    (f : ℕ → ℕ) (hf : StrictMono f)
    (hclass : ∀ x, P x ↔ ∃ i, f i = x) (n : ℕ) :
    Nat.nth P n = f n := by
  have hinf : (Set.ofPred P).Infinite :=
    (Set.infinite_range_of_injective hf.injective).mono (by
      rintro x ⟨i, rfl⟩
      exact (hclass (f i)).2 ⟨i, rfl⟩)
  have hsurj : ∀ x, P x → x ∈ Set.range f := by
    intro x hx
    rcases (hclass x).mp hx with ⟨i, rfl⟩
    exact ⟨i, rfl⟩
  have hcard : ∀ hf' : (Set.ofPred P).Finite, n < hf'.toFinset.card := by
    intro hf'
    exact (hf'.not_infinite hinf).elim
  have h := Nat.nth_comp_of_strictMono (p := P) (n := n) hf hsurj hcard
  have hall : (fun i => P (f i)) = fun _ => True := by
    funext i
    exact propext ⟨fun _ => trivial, fun _ => (hclass (f i)).2 ⟨i, rfl⟩⟩
  simpa [hall] using h.symm

theorem nth_eq_of_classification {P : ℕ → Prop} [DecidablePred P]
    (f : ℕ → ℕ) (hf : StrictMono f)
    (hclass : ∀ x, P x ↔ ∃ i, f i = x) (n : ℕ) :
    Nat.nth P n = f n := nth_eq_of_strictMono_range f hf hclass n
namespace OMA.S_oeis_a131662

private theorem residue_bounds (j : ℕ) (hj : j<8) : 0<residue j ∧ residue j≤27720 := by
  interval_cases j <;> norm_num [residue]

private theorem residue_iff (r : ℕ) :
    residueSet r ↔ ∃ j : ℕ, j<8 ∧ residue j=r := by
  constructor
  · intro h
    rcases h with h|h|h|h|h|h|h|h <;> subst r
    all_goals first
      | exact ⟨0, by decide, rfl⟩
      | exact ⟨1, by decide, rfl⟩
      | exact ⟨2, by decide, rfl⟩
      | exact ⟨3, by decide, rfl⟩
      | exact ⟨4, by decide, rfl⟩
      | exact ⟨5, by decide, rfl⟩
      | exact ⟨6, by decide, rfl⟩
      | exact ⟨7, by decide, rfl⟩
  · rintro ⟨j,hj,rfl⟩
    interval_cases j <;> norm_num [residue,residueSet]

private theorem model_mono : StrictMono (fun j : ℕ => model (j+1)) := by
  apply strictMono_nat_of_lt_succ
  intro j
  simp only [model]
  have hmod : j%8<8 := Nat.mod_lt _ (by decide)
  by_cases h : j%8=7
  · rw [show (j+1)/8=j/8+1 by omega, show (j+1)%8=0 by omega, h]
    norm_num [residue]
    omega
  · rw [show (j+1)/8=j/8 by omega, show (j+1)%8=j%8+1 by omega]
    apply Nat.add_lt_add_left
    interval_cases hm : j%8 <;> norm_num [residue, hm] at *

private theorem model_range (n : ℕ) :
    qualifies n ↔ ∃ j : ℕ, model (j+1)=n := by
  rw [qualifies_iff_residueSet]
  constructor
  · rintro ⟨hn,hres⟩
    obtain ⟨j,hj,hjval⟩ := (residue_iff _).mp hres
    let q := (n-1)/27720
    refine ⟨8*q+j, ?_⟩
    simp only [model]
    rw [show (8*q+j)/8=q by omega, show (8*q+j)%8=j by omega, hjval]
    dsimp [q,positiveResidue]
    omega
  · rintro ⟨j,rfl⟩
    have hj : j%8<8 := Nat.mod_lt _ (by decide)
    have hb := residue_bounds _ hj
    have hm : positiveResidue (model (j+1)) = residue (j%8) := by
      simp only [positiveResidue,model]
      omega
    exact ⟨by simp only [model]; omega, hm.symm ▸ (residue_iff _).mpr ⟨j%8,hj,rfl⟩⟩

theorem model_eq_term : model = term := by
  classical
  funext n
  cases n with
  | zero => rfl
  | succ n =>
    change model (n+1) = Nat.nth qualifies n
    exact (nth_eq_of_strictMono_range (fun j => model (j+1)) model_mono model_range n).symm

end OMA.S_oeis_a131662

theorem OMA.solution : type_of% @OMA.S_oeis_a131662.main := by
  open OMA.S_oeis_a131662 in
  refine ⟨?_, ?_⟩
  · simpa only [model_eq_term, series] using model_series
  · simpa only [model_eq_term] using model_recurrence
