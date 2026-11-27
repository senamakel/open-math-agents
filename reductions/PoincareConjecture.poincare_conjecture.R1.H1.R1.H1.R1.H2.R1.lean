import OMAReductions.R_PoincareConjecture_poincare_conjecture_R1_H1_R1_H1_R1
import Mathlib.Algebra.Category.Grp.Abelian
import Mathlib.Algebra.Homology.HomologySequence
import Mathlib.AlgebraicTopology.SingularHomology.Basic
import Mathlib.Topology.Category.TopCat.EpiMono

/-!
Unpack the two-contractible-open-cover homology shift into the three chain facts
used in the published proof: collapse a contractible subspace in positive degree,
excision for an open cover, and the connecting isomorphism for a contractible
ambient subspace.  This follows `IntegralCoverHomology.lean` and
`IntegralRelativeChains.lean` in frenzymath/PoincareConjecture at
62db01af9388dc1d9b56b66d6674f4c09b2318a2 (Apache-2.0).  Relative chains here are
the cokernel of the singular-chain inclusion, matching that source's construction.
-/

namespace OMA.R_PoincareConjecture_poincare_conjecture_R1_H1_R1_H1_R1_H2_R1

open AlgebraicTopology CategoryTheory Limits
open scoped ContinuousMap

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

def H3 : Prop :=
  ∀ {X : Type} [TopologicalSpace X] (A : Set X) [ContractibleSpace X]
    (n : ℕ) (hn : 2 ≤ n),
    let C := (AlgebraicTopology.singularChainComplexFunctor AddCommGrpCat).obj
      (AddCommGrpCat.of ℤ)
    let i := C.map (TopCat.ofHom ⟨Subtype.val, continuous_subtype_val⟩ : TopCat.of A ⟶ TopCat.of X)
    let S := ShortComplex.cokernelSequence i
    let hS : S.ShortExact := pairSequenceShortExact A
    IsIso (hS.δ n (n - 1) (show (n - 1) + 1 = n by omega))

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

theorem main : H1 → H2 → H3 →
    OMA.R_PoincareConjecture_poincare_conjecture_R1_H1_R1_H1_R1.H2 := by
  intro hCollapse hExcision hConnecting n hn X _ A B hAopen hBopen hcover
    hAcontract hBcontract
  letI : ContractibleSpace A := hAcontract
  letI : ContractibleSpace B := hBcontract
  let AB : Set B := (Subtype.val : B → X) ⁻¹' A
  let C := (AlgebraicTopology.singularChainComplexFunctor AddCommGrpCat).obj
    (AddCommGrpCat.of ℤ)
  let iA := C.map (TopCat.ofHom ⟨Subtype.val, continuous_subtype_val⟩ : TopCat.of A ⟶ TopCat.of X)
  let collapse := HomologicalComplex.homologyMap (cokernel.π iA) n
  let iAB := C.map (TopCat.ofHom ⟨Subtype.val, continuous_subtype_val⟩ : TopCat.of AB ⟶ TopCat.of B)
  let fA : C(AB, A) := ⟨fun x => ⟨x.val, x.property⟩,
    (continuous_subtype_val.comp continuous_subtype_val).subtype_mk _⟩
  let f := C.map (TopCat.ofHom fA)
  let g := C.map (TopCat.ofHom ⟨Subtype.val, continuous_subtype_val⟩ : TopCat.of B ⟶ TopCat.of X)
  let excision := HomologicalComplex.homologyMap
    (cokernel.map iAB iA f g (coverSquare A B)) n
  let S := ShortComplex.cokernelSequence iAB
  let hS : S.ShortExact := pairSequenceShortExact AB
  let boundary := hS.δ n (n - 1) (show (n - 1) + 1 = n by omega)
  have hCollapse' : IsIso collapse := hCollapse A n (by omega)
  have hExcision' : IsIso excision := hExcision A B n hAopen hBopen hcover
  have hConnecting' : IsIso boundary := hConnecting AB n (by omega)
  let e : ↥(A ∩ B) ≃ₜ ↥AB :=
    { toFun := fun x => ⟨⟨x.val, x.property.2⟩, x.property.1⟩
      invFun := fun x => ⟨x.val.val, x.property, x.val.property⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl
      continuous_toFun := by fun_prop
      continuous_invFun := by fun_prop }
  obtain ⟨h4⟩ := homotopy_homology_iso (n - 1) e.toHomotopyEquiv
  change Nonempty (_ ≅ _)
  let eCollapse : _ ≅ _ := ⟨collapse, Classical.choose hCollapse'.out,
    (Classical.choose_spec hCollapse'.out).left, (Classical.choose_spec hCollapse'.out).right⟩
  let eExcision : _ ≅ _ := ⟨excision, Classical.choose hExcision'.out,
    (Classical.choose_spec hExcision'.out).left, (Classical.choose_spec hExcision'.out).right⟩
  let eBoundary : _ ≅ _ := ⟨boundary, Classical.choose hConnecting'.out,
    (Classical.choose_spec hConnecting'.out).left, (Classical.choose_spec hConnecting'.out).right⟩
  exact ⟨eCollapse ≪≫ eExcision.symm ≪≫ eBoundary ≪≫ h4.symm⟩

end OMA.R_PoincareConjecture_poincare_conjecture_R1_H1_R1_H1_R1_H2_R1
