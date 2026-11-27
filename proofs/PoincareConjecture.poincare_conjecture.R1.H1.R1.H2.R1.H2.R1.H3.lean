import OMAReductions.R_PoincareConjecture_poincare_conjecture_R1_H1_R1_H2_R1_H2_R1
import Mathlib.Topology.Homotopy.Contractible

/-! The positive-degree singular homology of a contractible space is zero.
The connecting isomorphism then follows from the pair long exact sequence. -/

open AlgebraicTopology CategoryTheory Limits
open scoped ContinuousMap

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


theorem OMA.solution : OMA.R_PoincareConjecture_poincare_conjecture_R1_H1_R1_H2_R1_H2_R1.H3 := by
  intro X _ A _ n hn
  have vanishes (m : ℕ) (hm : m ≠ 0) :
      IsZero (((singularHomologyFunctor AddCommGrpCat m).obj (AddCommGrpCat.of ℤ)).obj
        (TopCat.of X)) := by
    obtain ⟨e⟩ := ContractibleSpace.hequiv_unit X
    obtain ⟨i⟩ := homotopy_homology_iso m e
    exact (isZero_singularHomologyFunctor_of_totallyDisconnectedSpace
      AddCommGrpCat m (AddCommGrpCat.of ℤ) (TopCat.of Unit) hm).of_iso i
  exact ShortComplex.ShortExact.isIso_δ _ _ _ _
    (vanishes n (by omega)) (vanishes (n - 1) (by omega))
