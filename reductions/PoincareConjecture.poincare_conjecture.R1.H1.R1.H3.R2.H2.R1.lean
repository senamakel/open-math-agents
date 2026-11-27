import OMAReductions.R_PoincareConjecture_poincare_conjecture_R1_H1_R1_H3_R2
import Mathlib.AlgebraicTopology.SingularHomology.HomotopyInvariance
import Mathlib.Algebra.Category.Grp.Abelian
import Mathlib.Algebra.Homology.HomologySequence
import Mathlib.Algebra.Homology.HomologicalComplexAbelian
import Mathlib.Topology.Category.TopCat.EpiMono
import Mathlib.Topology.Homotopy.Contractible

/-! The degree-one contractible-cover calculation follows the separation
of positive-degree collapse, open-cover excision, and the pair sequence in
FrenzyMath's IntegralSphereBase.lean. The connecting map identifies the first
relative homology with the kernel of the zeroth-degree inclusion, rather
than with all zeroth homology of the intersection. -/

namespace OMA.R_PoincareConjecture_poincare_conjecture_R1_H1_R1_H3_R2_H2_R1

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


private theorem subspaceChains_mono {X : Type} [TopologicalSpace X] (A : Set X) :
    Mono (((AlgebraicTopology.singularChainComplexFunctor AddCommGrpCat).obj
      (AddCommGrpCat.of ℤ)).map (TopCat.ofHom ⟨Subtype.val, continuous_subtype_val⟩ :
        TopCat.of A ⟶ TopCat.of X)) := by
  let C := (AlgebraicTopology.singularChainComplexFunctor AddCommGrpCat).obj (AddCommGrpCat.of ℤ)
  let i : TopCat.of A ⟶ TopCat.of X :=
    TopCat.ofHom ⟨Subtype.val, continuous_subtype_val⟩
  let : Mono i := (TopCat.mono_iff_injective i).mpr Subtype.val_injective
  change Mono (C.map i)
  infer_instance

private theorem pairSequenceShortExact {X : Type} [TopologicalSpace X] (A : Set X) :
    (ShortComplex.cokernelSequence
      (((singularChainComplexFunctor AddCommGrpCat).obj (AddCommGrpCat.of ℤ)).map
        (TopCat.ofHom ⟨Subtype.val, continuous_subtype_val⟩ :
          TopCat.of A ⟶ TopCat.of X))).ShortExact where
  exact := ShortComplex.cokernelSequence_exact _
  mono_f := subspaceChains_mono A

private theorem degreeOneRelativeKernel {X : Type} [TopologicalSpace X] [ContractibleSpace X]
    (A : Set X) :
    let C := (singularChainComplexFunctor AddCommGrpCat).obj (AddCommGrpCat.of ℤ)
    let i := TopCat.ofHom (⟨Subtype.val, continuous_subtype_val⟩ : C(A, X))
    Nonempty ((cokernel (C.map i)).homology 1 ≅ kernel
      (((singularHomologyFunctor AddCommGrpCat 0).obj (AddCommGrpCat.of ℤ)).map i)) := by
  dsimp only
  let C := (singularChainComplexFunctor AddCommGrpCat).obj (AddCommGrpCat.of ℤ)
  let i : TopCat.of A ⟶ TopCat.of X := TopCat.ofHom ⟨Subtype.val, continuous_subtype_val⟩
  let S := ShortComplex.cokernelSequence (C.map i)
  have hS : S.ShortExact := pairSequenceShortExact A
  have rel : (ComplexShape.down ℕ).Rel 1 0 := rfl
  obtain ⟨e⟩ := ContractibleSpace.hequiv_unit X
  obtain ⟨eh⟩ := homotopy_homology_iso 1 e
  have hz : IsZero (S.X₂.homology 1) :=
    (isZero_singularHomologyFunctor_of_totallyDisconnectedSpace
      AddCommGrpCat 1 (AddCommGrpCat.of ℤ) (TopCat.of Unit) (by decide)).of_iso eh
  letI : Mono (hS.δ 1 0 rel) := hS.mono_δ 1 0 rel hz
  let hlim := (hS.homology_exact₁ 1 0 rel).fIsKernel
  exact ⟨hlim.conePointUniqueUpToIso
    (limit.isLimit _)⟩

private theorem coverSquare {X : Type} [TopologicalSpace X] (A B : Set X) :
    let C := (singularChainComplexFunctor AddCommGrpCat).obj (AddCommGrpCat.of ℤ)
    let AB : Set B := (Subtype.val : B → X) ⁻¹' A
    let iAB := C.map (TopCat.ofHom ⟨Subtype.val, continuous_subtype_val⟩ :
      TopCat.of AB ⟶ TopCat.of B)
    let iA := C.map (TopCat.ofHom ⟨Subtype.val, continuous_subtype_val⟩ :
      TopCat.of A ⟶ TopCat.of X)
    let fA : C(AB, A) := ⟨fun x => ⟨x.val, x.property⟩,
      (continuous_subtype_val.comp continuous_subtype_val).subtype_mk _⟩
    let f := C.map (TopCat.ofHom fA)
    let g := C.map (TopCat.ofHom ⟨Subtype.val, continuous_subtype_val⟩ :
      TopCat.of B ⟶ TopCat.of X)
    (iAB ≫ g) = (f ≫ iA) := by
  dsimp only
  rw [← Functor.map_comp, ← Functor.map_comp]
  rfl

def H1 : Prop :=
  ∀ {X : Type} [TopologicalSpace X] (A : Set X) [ContractibleSpace A]
    (n : ℕ), 0 < n →
    let C := (AlgebraicTopology.singularChainComplexFunctor AddCommGrpCat).obj
      (AddCommGrpCat.of ℤ)
    let i := C.map (TopCat.ofHom ⟨Subtype.val, continuous_subtype_val⟩ : TopCat.of A ⟶ TopCat.of X)
    IsIso (HomologicalComplex.homologyMap (cokernel.π i) n)

def H2 : Prop :=
  ∀ {X : Type} [TopologicalSpace X] (A B : Set X)
    (n : ℕ), IsOpen A → IsOpen B → A ∪ B = Set.univ →
    let C := (AlgebraicTopology.singularChainComplexFunctor AddCommGrpCat).obj
      (AddCommGrpCat.of ℤ)
    let AB : Set B := (Subtype.val : B → X) ⁻¹' A
    let iAB := C.map (TopCat.ofHom ⟨Subtype.val, continuous_subtype_val⟩ : TopCat.of AB ⟶ TopCat.of B)
    let iA := C.map (TopCat.ofHom ⟨Subtype.val, continuous_subtype_val⟩ : TopCat.of A ⟶ TopCat.of X)
    let fA : C(AB, A) := ⟨fun x => ⟨x.val, x.property⟩,
      (continuous_subtype_val.comp continuous_subtype_val).subtype_mk _⟩
    let f := C.map (TopCat.ofHom fA)
    let g := C.map (TopCat.ofHom ⟨Subtype.val, continuous_subtype_val⟩ : TopCat.of B ⟶ TopCat.of X)
    IsIso (HomologicalComplex.homologyMap (cokernel.map iAB iA f g (coverSquare A B)) n)

theorem main : H1 → H2 → OMA.R_PoincareConjecture_poincare_conjecture_R1_H1_R1_H3_R2.H2 := by
  intro hCollapse hExcision A B hAopen hBopen hcover hA hB
  letI : ContractibleSpace A := hA
  letI : ContractibleSpace B := hB
  let X := Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1
  let AB : Set B := (Subtype.val : B → X) ⁻¹' A
  let C := (singularChainComplexFunctor AddCommGrpCat).obj (AddCommGrpCat.of ℤ)
  let iA := C.map (TopCat.ofHom ⟨Subtype.val, continuous_subtype_val⟩ : TopCat.of A ⟶ TopCat.of X)
  let collapse := HomologicalComplex.homologyMap (cokernel.π iA) 1
  let iAB := C.map (TopCat.ofHom ⟨Subtype.val, continuous_subtype_val⟩ : TopCat.of AB ⟶ TopCat.of B)
  let fA : C(AB, A) := ⟨fun x => ⟨x.val, x.property⟩,
    (continuous_subtype_val.comp continuous_subtype_val).subtype_mk _⟩
  let f := C.map (TopCat.ofHom fA)
  let g := C.map (TopCat.ofHom ⟨Subtype.val, continuous_subtype_val⟩ : TopCat.of B ⟶ TopCat.of X)
  let excision := HomologicalComplex.homologyMap
    (cokernel.map iAB iA f g (coverSquare A B)) 1
  have hc : IsIso collapse := hCollapse A 1 (by decide)
  have he : IsIso excision := hExcision A B 1 hAopen hBopen hcover
  obtain ⟨boundary⟩ := degreeOneRelativeKernel AB
  let eCollapse : _ ≅ _ := ⟨collapse, Classical.choose hc.out,
    (Classical.choose_spec hc.out).left, (Classical.choose_spec hc.out).right⟩
  let eExcision : _ ≅ _ := ⟨excision, Classical.choose he.out,
    (Classical.choose_spec he.out).left, (Classical.choose_spec he.out).right⟩
  exact ⟨eCollapse ≪≫ eExcision.symm ≪≫ boundary⟩

end OMA.R_PoincareConjecture_poincare_conjecture_R1_H1_R1_H3_R2_H2_R1
