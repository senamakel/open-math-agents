import OMAReductions.R_PoincareConjecture_poincare_conjecture_R1_H1_R1_H3_R1
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.SpecialFunctions.Complex.Circle
import Mathlib.Topology.Homotopy.Lifting

/-! Compute the winding group using the real exponential covering of the
circle and Mathlib's monodromy equivalence. The deck group is the subgroup
of integer multiples of 2π. -/

open CategoryTheory
open scoped EuclideanGeometry

noncomputable section

private def complexCircleToSphere :
    Circle ≃ₜ Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1 := by
  let e := Complex.orthonormalBasisOneI.repr
  have forward (x : Circle) : e (x : ℂ) ∈ Metric.sphere 0 1 := by
    simpa [Metric.mem_sphere, dist_zero_right] using Circle.norm_coe x
  have backward (x : Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1) :
      e.symm x ∈ Submonoid.unitSphere ℂ := by
    have hx : ‖(x : EuclideanSpace ℝ (Fin 2))‖ = 1 := by
      simpa [Metric.mem_sphere, dist_zero_right] using x.property
    simpa [Submonoid.unitSphere, Metric.mem_sphere, dist_zero_right] using hx
  exact
    { toFun := fun x => ⟨e x, forward x⟩
      invFun := fun x => ⟨e.symm x, backward x⟩
      left_inv := fun x => Subtype.ext (e.symm_apply_apply x)
      right_inv := fun x => Subtype.ext (e.apply_symm_apply x)
      continuous_toFun := e.continuous.comp continuous_subtype_val |>.subtype_mk forward
      continuous_invFun := e.symm.continuous.comp continuous_subtype_val |>.subtype_mk backward }

private theorem integerDeckGroup :
    Nonempty (ℤ ≃+ AddSubgroup.zmultiples (2 * Real.pi)) := by
  let f : ℤ →+ ℝ := zmultiplesHom ℝ (2 * Real.pi)
  let g : ℤ →+ AddSubgroup.zmultiples (2 * Real.pi) :=
    f.codRestrict _ (fun z => AddSubgroup.mem_zmultiples_iff.mpr ⟨z, rfl⟩)
  refine ⟨AddEquiv.ofBijective g ⟨?_, ?_⟩⟩
  · intro a b h
    apply smul_left_injective ℤ (show (2 * Real.pi : ℝ) ≠ 0 by positivity)
    exact congrArg Subtype.val h
  · intro x
    obtain ⟨z, hz⟩ := AddSubgroup.mem_zmultiples_iff.mp x.property
    exact ⟨z, Subtype.ext hz⟩

theorem OMA.solution : OMA.R_PoincareConjecture_poincare_conjecture_R1_H1_R1_H3_R1.H2 := by
  intro x
  let p : ℝ → Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1 :=
    complexCircleToSphere ∘ Circle.exp
  have hp : IsAddQuotientCoveringMap p (AddSubgroup.zmultiples (2 * Real.pi)) :=
    Circle.isAddQuotientCoveringMap_exp.homeomorph_comp complexCircleToSphere
  obtain ⟨y, hy⟩ := hp.surjective x
  obtain ⟨eZ⟩ := integerDeckGroup
  let e := hp.fundamentalGroupEquiv ⟨y, hy⟩
  let e₁ : FundamentalGroup _ x ≃* Multiplicative ℤ :=
    (e.trans MulOpposite.opMulEquiv.symm).trans eZ.symm.toMultiplicative
  let e₂ := e₁.abelianizationCongr.trans Abelianization.equivOfComm.symm
  exact ⟨e₂.toAdditive.toAddCommGrpIso⟩
