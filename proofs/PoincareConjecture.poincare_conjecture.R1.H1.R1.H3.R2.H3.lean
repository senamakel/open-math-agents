import OMAReductions.R_PoincareConjecture_poincare_conjecture_R1_H1_R1_H3_R2
import Mathlib.AlgebraicTopology.SingularHomology.HomotopyInvariance
import Mathlib.Topology.Homotopy.Contractible
import Mathlib.AlgebraicTopology.SingularHomology.HomologyZero
import Mathlib.Algebra.Category.Grp.Abelian

/-!
The kernel transport follows the route in PoincareLib's
`AlgebraicTopology/SingularHomology/Homology/IntegralHomologyZero.lean`
(https://github.com/frenzymath/PoincareConjecture). This proof uses Mathlib's
simplicial-set augmentation and the canonical degree-zero generators.
-/

open CategoryTheory Limits AlgebraicTopology Simplicial HomologicalComplex

private theorem augmentationNaturality {X Y : SSet} (f : X ⟶ Y) (R : AddCommGrpCat) :
    CategoryStruct.comp (SSet.homologyMap f R 0) (Y.homology₀ε R) = X.homology₀ε R := by
  rw [← cancel_epi (X.homology₀Iso R).inv]
  apply Sigma.hom_ext
  intro a
  obtain ⟨x, rfl⟩ := SSet.π₀.mk_surjective a
  rw [← SSet.liftCycles_ιChainComplex_homologyπ_homology₀Iso_hom X R x]
  simp only [Category.assoc, Iso.hom_inv_id_assoc]
  change CategoryStruct.comp _ (CategoryStruct.comp ((X.chainComplex R).homologyπ 0)
    (CategoryStruct.comp (HomologicalComplex.homologyMap (SSet.chainComplexMap f R) 0)
      (Y.homology₀ε R))) = _
  rw [homologyπ_naturality_assoc]
  rw [← Category.assoc, liftCycles_comp_cyclesMap]
  simp

open scoped ContinuousMap

private theorem kernelTransport {X Y Z : Type}
    [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z]
    [PathConnectedSpace Y] (i : C(X, Y)) (e : X ≃ₕ Z) :
    Nonempty (kernel (((singularHomologyFunctor AddCommGrpCat 0).obj
      (AddCommGrpCat.of ℤ)).map (TopCat.ofHom i)) ≅
      kernel ((TopCat.of Z).singularHomology₀ε (AddCommGrpCat.of ℤ))) := by
  let R := AddCommGrpCat.of ℤ
  let F := (singularHomologyFunctor AddCommGrpCat 0).obj R
  let f : TopCat.of X ⟶ TopCat.of Z := TopCat.ofHom e.toFun
  let g : TopCat.of Z ⟶ TopCat.of X := TopCat.ofHom e.invFun
  let E : F.obj (TopCat.of X) ≅ F.obj (TopCat.of Z) :=
    { hom := F.map f
      inv := F.map g
      hom_inv_id := by
        rw [← F.map_comp, ← F.map_id]
        obtain ⟨h⟩ := e.left_inv
        have hh : TopCat.Homotopy (f ≫ g) (𝟙 (TopCat.of X)) := h
        exact hh.congr_homologyMap_singularChainComplexFunctor R 0
      inv_hom_id := by
        rw [← F.map_comp, ← F.map_id]
        obtain ⟨h⟩ := e.right_inv
        have hh : TopCat.Homotopy (g ≫ f) (𝟙 (TopCat.of Z)) := h
        exact hh.congr_homologyMap_singularChainComplexFunctor R 0 }
  let aX := (TopCat.of X).singularHomology₀ε R
  let aY := (TopCat.of Y).singularHomology₀ε R
  let aZ := (TopCat.of Z).singularHomology₀ε R
  have hi : CategoryStruct.comp (F.map (TopCat.ofHom i)) aY = aX :=
    augmentationNaturality (TopCat.toSSet.map (TopCat.ofHom i)) R
  have hf : CategoryStruct.comp E.hom aZ = aX :=
    augmentationNaturality (TopCat.toSSet.map f) R
  have : IsIso aY := by dsimp [aY]; infer_instance
  exact ⟨(kernelCompMono (F.map (TopCat.ofHom i)) aY).symm ≪≫
    kernelIsoOfEq hi ≪≫ kernel.mapIso aX aZ E (Iso.refl R) (by simpa using hf.symm)⟩

private def nestedIntersection {X : Type} [TopologicalSpace X] (A B : Set X) :
    ((Subtype.val : B → X) ⁻¹' A : Set B) ≃ₜ ↥(A ∩ B) where
  toFun x := ⟨x.1.1, x.2, x.1.2⟩
  invFun x := ⟨⟨x.1, x.2.2⟩, x.2.1⟩
  left_inv _ := rfl
  right_inv _ := rfl
  continuous_toFun := (continuous_subtype_val.comp continuous_subtype_val).subtype_mk _
  continuous_invFun := (continuous_subtype_val.subtype_mk _).subtype_mk _

/-- Degree-zero augmentation is natural, so the relative kernel transports
along the homotopy equivalence with the zero-sphere. -/
theorem OMA.solution : OMA.R_PoincareConjecture_poincare_conjecture_R1_H1_R1_H3_R2.H3 := by
  intro A B hB h
  let : ContractibleSpace B := hB
  obtain ⟨e⟩ := h
  exact kernelTransport ⟨Subtype.val, continuous_subtype_val⟩
    ((nestedIntersection A B).toHomotopyEquiv.trans e)
