import OMAReductions.R_PoincareConjecture_poincare_conjecture_R1_H2_R1
import Mathlib.Algebra.Category.Grp.Zero
import Mathlib.Algebra.Homology.HomologySequence

/-! Separate finite singular-chain support from the chain-map lemma that turns
a chain carried by the complement into a complement homology class. -/
namespace OMA.R_PoincareConjecture_poincare_conjecture_R1_H2_R1_H2_R1

open AlgebraicTopology CategoryTheory Limits

/-- A finite carrier contains the singular simplices in every degree-3 cycle. -/
def H1 : Prop :=
  ∀ (M : Type) [TopologicalSpace M],
    ∀ z : (((singularChainComplexFunctor AddCommGrpCat).obj (AddCommGrpCat.of ℤ)).obj
        (TopCat.of M)).cycles 3,
      ∃ K : Set M, IsCompact K ∧ ∀ x ∉ K,
        ∃ c : (((singularChainComplexFunctor AddCommGrpCat).obj (AddCommGrpCat.of ℤ)).obj
            (TopCat.of ↥({x}ᶜ : Set M))).X 3,
          ((((singularChainComplexFunctor AddCommGrpCat).obj (AddCommGrpCat.of ℤ)).map
              (TopCat.ofHom ⟨Subtype.val, continuous_subtype_val⟩)).f 3) c =
            (((singularChainComplexFunctor AddCommGrpCat).obj (AddCommGrpCat.of ℤ)).obj
              (TopCat.of M)).iCycles 3 z

/-- A carried ambient cycle lifts to a cycle in the complement with the same class. -/
def H2 : Prop :=
  ∀ (M : Type) [TopologicalSpace M] (x : M)
    (z : (((singularChainComplexFunctor AddCommGrpCat).obj (AddCommGrpCat.of ℤ)).obj
      (TopCat.of M)).cycles 3)
    (c : (((singularChainComplexFunctor AddCommGrpCat).obj (AddCommGrpCat.of ℤ)).obj
      (TopCat.of ↥({x}ᶜ : Set M))).X 3),
    ((((singularChainComplexFunctor AddCommGrpCat).obj (AddCommGrpCat.of ℤ)).map
        (TopCat.ofHom ⟨Subtype.val, continuous_subtype_val⟩)).f 3) c =
      (((singularChainComplexFunctor AddCommGrpCat).obj (AddCommGrpCat.of ℤ)).obj
        (TopCat.of M)).iCycles 3 z →
    ∃ b : (((singularChainComplexFunctor AddCommGrpCat).obj (AddCommGrpCat.of ℤ)).obj
        (TopCat.of ↥({x}ᶜ : Set M))).cycles 3,
      HomologicalComplex.homologyMap
          (((singularChainComplexFunctor AddCommGrpCat).obj (AddCommGrpCat.of ℤ)).map
            (TopCat.ofHom ⟨Subtype.val, continuous_subtype_val⟩)) 3
          ((((singularChainComplexFunctor AddCommGrpCat).obj (AddCommGrpCat.of ℤ)).obj
            (TopCat.of ↥({x}ᶜ : Set M))).homologyπ 3 b) =
        (((singularChainComplexFunctor AddCommGrpCat).obj (AddCommGrpCat.of ℤ)).obj
          (TopCat.of M)).homologyπ 3 z

theorem main : H1 → H2 →
    OMA.R_PoincareConjecture_poincare_conjecture_R1_H2_R1.H2 := by
  intro support lift M hM
  let F := (singularChainComplexFunctor AddCommGrpCat).obj (AddCommGrpCat.of ℤ)
  let C := F.obj (TopCat.of M)
  let complement (x : M) := F.obj (TopCat.of ↥({x}ᶜ : Set M))
  let ι (x : M) : complement x ⟶ C :=
    F.map (TopCat.ofHom ⟨Subtype.val, continuous_subtype_val⟩)
  let localize (x : M) := HomologicalComplex.homologyMap (cokernel.π (ι x)) 3
  change ∀ a : C.homology 3, ∃ K : Set M, IsCompact K ∧
    ∀ x ∉ K, localize x a = 0
  intro a
  obtain ⟨z, hz⟩ := (AddCommGrpCat.epi_iff_surjective (C.homologyπ 3)).mp
    (HomologicalComplex.instEpiHomologyπ C 3) a
  obtain ⟨K, hK, hcarry⟩ := support M z
  refine ⟨K, hK, ?_⟩
  intro x hx
  obtain ⟨c, hc⟩ := hcarry x hx
  obtain ⟨b, hb⟩ := lift M x z c hc
  rw [← hz, ← hb]
  change ((HomologicalComplex.homologyMap (ι x) 3) ≫
    HomologicalComplex.homologyMap (cokernel.π (ι x)) 3)
      ((complement x).homologyπ 3 b) = 0
  rw [← HomologicalComplex.homologyMap_comp, cokernel.condition,
    HomologicalComplex.homologyMap_zero]
  simp

end OMA.R_PoincareConjecture_poincare_conjecture_R1_H2_R1_H2_R1
