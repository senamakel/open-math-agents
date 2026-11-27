import OMAReductions.R_PoincareConjecture_poincare_conjecture_R1_H1_R1_H1_R1_H2_R1
import Mathlib.Algebra.Category.Grp.Abelian
import Mathlib.Algebra.Homology.HomologicalComplexAbelian
import Mathlib.Algebra.Homology.HomologySequenceLemmas
import Mathlib.AlgebraicTopology.SingularHomology.Basic

namespace OMA.R_PoincareConjecture_poincare_conjecture_R1_H1_R1_H1_R1_H2_R1_H2_R1

open AlgebraicTopology CategoryTheory Limits
open scoped ContinuousMap

private theorem coverPushoutSquare {X : Type} [TopologicalSpace X] (A B : Set X) :
    let C := (AlgebraicTopology.singularChainComplexFunctor AddCommGrpCat).obj
      (AddCommGrpCat.of ℤ)
    let AB : Set B := (Subtype.val : B → X) ⁻¹' A
    let i := C.map (TopCat.ofHom ⟨Subtype.val, continuous_subtype_val⟩ :
      TopCat.of AB ⟶ TopCat.of B)
    let j := C.map (TopCat.ofHom ⟨fun x : AB => (⟨x.val, x.property⟩ : A),
      (continuous_subtype_val.comp continuous_subtype_val).subtype_mk _⟩ :
        TopCat.of AB ⟶ TopCat.of A)
    let f := C.map (TopCat.ofHom ⟨Subtype.val, continuous_subtype_val⟩ :
      TopCat.of B ⟶ TopCat.of X)
    let g := C.map (TopCat.ofHom ⟨Subtype.val, continuous_subtype_val⟩ :
      TopCat.of A ⟶ TopCat.of X)
    CategoryStruct.comp i f = CategoryStruct.comp j g := by
  dsimp only
  rw [← Functor.map_comp, ← Functor.map_comp]
  congr 1

/-!
The small chains subordinate to a two-open cover are the pushout of the two
subspace chain complexes along their intersection. The geometric obligation
is that this pushout maps quasi-isomorphically to all singular chains, by
barycentric subdivision. This chain model follows `IntegralCoverHomology.lean`
and `IntegralRelativeChains.lean` in FrenzyMath/PoincareConjecture at
62db01af9388dc1d9b56b66d6674f4c09b2318a2 (Apache-2.0). The remaining relative
comparison is formal.
-/

set_option maxHeartbeats 2000000 in
def H1 : Prop :=
  ∀ {X : Type} [TopologicalSpace X] (A B : Set X), IsOpen A → IsOpen B →
    A ∪ B = Set.univ →
    let C := (AlgebraicTopology.singularChainComplexFunctor AddCommGrpCat).obj
      (AddCommGrpCat.of ℤ)
    let AB : Set B := (Subtype.val : B → X) ⁻¹' A
    let i := C.map (TopCat.ofHom ⟨Subtype.val, continuous_subtype_val⟩ :
      TopCat.of AB ⟶ TopCat.of B)
    let j := C.map (TopCat.ofHom ⟨fun x : AB => (⟨x.val, x.property⟩ : A),
      (continuous_subtype_val.comp continuous_subtype_val).subtype_mk _⟩ :
        TopCat.of AB ⟶ TopCat.of A)
    let f := C.map (TopCat.ofHom ⟨Subtype.val, continuous_subtype_val⟩ :
      TopCat.of B ⟶ TopCat.of X)
    let g := C.map (TopCat.ofHom ⟨Subtype.val, continuous_subtype_val⟩ :
      TopCat.of A ⟶ TopCat.of X)
    ∀ n, IsIso (HomologicalComplex.homologyMap (pushout.desc f g
      (coverPushoutSquare A B)) n)

def H2 : Prop :=
  ∀ {K L A : ChainComplex AddCommGrpCat ℕ} (i : A ⟶ K) (j : A ⟶ L)
    (f : K ⟶ L) (w : CategoryStruct.comp i f = j) [Mono i] [Mono j]
    (hiso : ∀ n, IsIso (HomologicalComplex.homologyMap f n)),
    ∀ n, IsIso (HomologicalComplex.homologyMap
      (cokernel.map i j (𝟙 A) f (by simpa [w])) n)

set_option maxHeartbeats 2000000 in
theorem main : H1 → H2 →
    OMA.R_PoincareConjecture_poincare_conjecture_R1_H1_R1_H1_R1_H2_R1.H2 := by
  intro hSmall hRelative X _ A B n hA hB hcover
  let C := (AlgebraicTopology.singularChainComplexFunctor AddCommGrpCat).obj
    (AddCommGrpCat.of ℤ)
  let AB : Set B := (Subtype.val : B → X) ⁻¹' A
  let iAB := C.map (TopCat.ofHom ⟨Subtype.val, continuous_subtype_val⟩ :
    TopCat.of AB ⟶ TopCat.of B)
  let iAA := C.map (TopCat.ofHom ⟨fun x : AB => (⟨x.val, x.property⟩ : A),
    (continuous_subtype_val.comp continuous_subtype_val).subtype_mk _⟩ :
      TopCat.of AB ⟶ TopCat.of A)
  let iA := C.map (TopCat.ofHom ⟨Subtype.val, continuous_subtype_val⟩ :
    TopCat.of A ⟶ TopCat.of X)
  let iB := C.map (TopCat.ofHom ⟨Subtype.val, continuous_subtype_val⟩ :
    TopCat.of B ⟶ TopCat.of X)
  let P := pushout iAB iAA
  let q := pushout.desc iB iA (coverPushoutSquare A B)
  have hq : ∀ k, IsIso (HomologicalComplex.homologyMap q k) :=
    hSmall A B hA hB hcover
  let r := pushout.inr iAB iAA
  have hiAB : Mono iAB := by
    let k : Mono (TopCat.ofHom ⟨Subtype.val, continuous_subtype_val⟩ :
        TopCat.of AB ⟶ TopCat.of B) :=
      (TopCat.mono_iff_injective _).mpr Subtype.val_injective
    dsimp only [iAB]
    infer_instance
  letI : Mono iAB := hiAB
  have hr : Mono r := by infer_instance
  have hiA : Mono iA := by
    let k : Mono (TopCat.ofHom ⟨Subtype.val, continuous_subtype_val⟩ :
        TopCat.of A ⟶ TopCat.of X) :=
      (TopCat.mono_iff_injective _).mpr Subtype.val_injective
    dsimp only [iA]
    infer_instance
  letI : Mono iA := hiA
  have w : CategoryStruct.comp iAB iB = CategoryStruct.comp iAA iA :=
    coverPushoutSquare A B
  have w' : CategoryStruct.comp r q = iA := pushout.inr_desc _ _ _
  have hrel : IsIso (HomologicalComplex.homologyMap
      (cokernel.map r iA (𝟙 _) q w') n) :=
    hRelative r iA q w' hq n
  let u := cokernel.map iAB r iAA (pushout.inl iAB iAA) pushout.condition
  have hu : IsIso u := CategoryTheory.Limits.isIso_cokernel_map_of_isPushout
    (CategoryTheory.IsPushout.of_isColimit (pushoutIsPushout iAB iAA))
  have hdesc : CategoryStruct.comp (pushout.inl iAB iAA) q = iB := by
    dsimp only [q]
    exact pushout.inl_desc iB iA (coverPushoutSquare A B)
  let v := cokernel.map iAB iA iAA iB w
  have hv : v = CategoryStruct.comp u (cokernel.map r iA (𝟙 _) q w') := by
    apply (cancel_epi (cokernel.π iAB)).mp
    simp [u, v] <;> rw [← Category.assoc, hdesc]
  letI : IsIso u := hu
  have hu' : IsIso (HomologicalComplex.homologyMap u n) := by infer_instance
  change IsIso (HomologicalComplex.homologyMap v n)
  rw [hv, HomologicalComplex.homologyMap_comp]
  infer_instance

end OMA.R_PoincareConjecture_poincare_conjecture_R1_H1_R1_H1_R1_H2_R1_H2_R1
