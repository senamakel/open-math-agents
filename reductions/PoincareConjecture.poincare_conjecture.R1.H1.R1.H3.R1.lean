import OMAReductions.R_PoincareConjecture_poincare_conjecture_R1_H1_R1
import Mathlib.Topology.Homotopy.HomotopyGroup
import Mathlib.GroupTheory.Abelianization.Defs

/-!
Reduce the circle's degree-one integral homology computation to the degree-one
Hurewicz theorem and the winding-number computation of the circle's fundamental
group.  The latter identifies its abelianization with the additive integers.
This is the standard route in Hatcher, Algebraic Topology, Sections 1.1 and 2.2;
the published Lean development uses the equivalent two-chart Mayer-Vietoris route.
-/

namespace OMA.R_PoincareConjecture_poincare_conjecture_R1_H1_R1_H3_R1

open AlgebraicTopology CategoryTheory Limits
open scoped ContinuousMap EuclideanGeometry

def H1 : Prop :=
  ∀ (x : Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1),
    Nonempty <|
      (((singularHomologyFunctor AddCommGrpCat 1).obj (AddCommGrpCat.of ℤ)).obj
        (TopCat.of (Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1))) ≅
      AddCommGrpCat.of (Additive (Abelianization (FundamentalGroup
        (Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1) x)))

def H2 : Prop :=
  ∀ (x : Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1),
    Nonempty <|
      AddCommGrpCat.of (Additive (Abelianization (FundamentalGroup
        (Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1) x))) ≅ AddCommGrpCat.of ℤ

theorem main : H1 → H2 →
    OMA.R_PoincareConjecture_poincare_conjecture_R1_H1_R1.H3 := by
  intro hurewicz hab
  letI : PathConnectedSpace (Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1) :=
    isPathConnected_iff_pathConnectedSpace.mp (isPathConnected_sphere (by
      rw [← Module.finrank_eq_rank, finrank_euclideanSpace_fin]
      norm_num) _ zero_le_one)
  let x : Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1 := Classical.choice inferInstance
  obtain ⟨e₁⟩ := hurewicz x
  obtain ⟨e₂⟩ := hab x
  exact ⟨e₁ ≪≫ e₂⟩

end OMA.R_PoincareConjecture_poincare_conjecture_R1_H1_R1_H3_R1
