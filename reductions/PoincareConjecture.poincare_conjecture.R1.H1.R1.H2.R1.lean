import OMAReductions.R_PoincareConjecture_poincare_conjecture_R1_H1_R1
import Mathlib.Data.Set.Lattice

/-!
Reduce the S²-to-S¹ homology recurrence to its geometric cover and a reusable
Mayer-Vietoris lemma for a cover by two contractible opens.  The geometric leaf
is the antipodal puncture cover: each punctured 2-sphere is contractible and the
overlap is homotopy equivalent to S¹.  This is the argument in frenzymath/
PoincareConjecture at 62db01af9388dc1d9b56b66d6674f4c09b2318a2,
`SphereOpenCover.lean` and `IntegralSphereHomology.lean` (Apache-2.0).
-/

namespace OMA.R_PoincareConjecture_poincare_conjecture_R1_H1_R1_H2_R1

open AlgebraicTopology CategoryTheory Limits
open scoped ContinuousMap EuclideanGeometry

private theorem homotopy_homology_iso (n : ℕ) {X Y : Type} [TopologicalSpace X]
    [TopologicalSpace Y] (e : X ≃ₕ Y) :
    Nonempty ((((singularHomologyFunctor AddCommGrpCat n).obj (AddCommGrpCat.of ℤ)).obj
      (TopCat.of X)) ≅ (((singularHomologyFunctor AddCommGrpCat n).obj
      (AddCommGrpCat.of ℤ)).obj (TopCat.of Y))) := by
  let F := (singularHomologyFunctor AddCommGrpCat n).obj (AddCommGrpCat.of ℤ)
  let f : TopCat.of X ⟶ TopCat.of Y := TopCat.ofHom e.toFun
  let g : TopCat.of Y ⟶ TopCat.of X := TopCat.ofHom e.invFun
  refine ⟨⟨F.map f, F.map g, ?_, ?_⟩⟩
  · rw [← F.map_comp, ← F.map_id]
    obtain ⟨h⟩ := e.left_inv
    have hh : TopCat.Homotopy (f ≫ g) (𝟙 (TopCat.of X)) := h
    exact hh.congr_homologyMap_singularChainComplexFunctor (AddCommGrpCat.of ℤ) n
  · rw [← F.map_comp, ← F.map_id]
    obtain ⟨h⟩ := e.right_inv
    have hh : TopCat.Homotopy (g ≫ f) (𝟙 (TopCat.of Y)) := h
    exact hh.congr_homologyMap_singularChainComplexFunctor (AddCommGrpCat.of ℤ) n

def H1 : Prop :=
  ∃ A B : Set (Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1),
    IsOpen A ∧ IsOpen B ∧ A ∪ B = Set.univ ∧ ContractibleSpace A ∧
      ContractibleSpace B ∧
      Nonempty (↥(A ∩ B) ≃ₕ Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1)

def H2 : Prop :=
  ∀ (n : ℕ) (hn : 2 ≤ n) {X : Type} [TopologicalSpace X]
    (A B : Set X) (hAopen : IsOpen A) (hBopen : IsOpen B)
    (hcover : A ∪ B = Set.univ) [ContractibleSpace A] [ContractibleSpace B],
    Nonempty ((((singularHomologyFunctor AddCommGrpCat n).obj (AddCommGrpCat.of ℤ)).obj
      (TopCat.of X)) ≅ (((singularHomologyFunctor AddCommGrpCat (n - 1)).obj
      (AddCommGrpCat.of ℤ)).obj (TopCat.of ↥(A ∩ B))))

theorem main : H1 → H2 →
    OMA.R_PoincareConjecture_poincare_conjecture_R1_H1_R1.H2 := by
  rintro ⟨A, B, hAopen, hBopen, hcover, hAcontract, hBcontract, hAB⟩ hMV
  letI : ContractibleSpace A := hAcontract
  letI : ContractibleSpace B := hBcontract
  obtain ⟨hX⟩ := hMV 2 (by omega) A B hAopen hBopen hcover
  obtain ⟨eAB⟩ := hAB
  obtain ⟨hY⟩ := homotopy_homology_iso 1 eAB
  exact ⟨hX ≪≫ hY⟩

end OMA.R_PoincareConjecture_poincare_conjecture_R1_H1_R1_H2_R1
