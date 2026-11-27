import OMAReductions.R_PoincareConjecture_poincare_conjecture_R1
import Mathlib.Algebra.Category.Grp.Zero
import Mathlib.Algebra.Homology.HomologySequence

/-!
This is the local orientation proof of vanishing of top homology, as in
Hatcher, Algebraic Topology, Theorem 3.26 and its local homology lemma.
The local class at a point is the image in the homology of the quotient
of singular chains by chains supported in the complement of that point.
-/

namespace OMA.R_PoincareConjecture_poincare_conjecture_R1_H2_R1

open AlgebraicTopology CategoryTheory Limits

/-- Top classes are detected by their images in local homology. -/
def H1 : Prop :=
  ∀ (M : Type) [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [ConnectedSpace M],
    let F := (singularChainComplexFunctor AddCommGrpCat).obj (AddCommGrpCat.of ℤ)
    let C := F.obj (TopCat.of M)
    let ι (x : M) : F.obj (TopCat.of ↥({x}ᶜ : Set M)) ⟶ C :=
      F.map (TopCat.ofHom ⟨Subtype.val, continuous_subtype_val⟩)
    let localize (x : M) := HomologicalComplex.homologyMap (cokernel.π (ι x)) 3
    ∀ a : C.homology 3, (∀ x, localize x a = 0) → a = 0

/-- Each class has zero local image outside a compact set. -/
def H2 : Prop :=
  ∀ (M : Type) [TopologicalSpace M],
    let F := (singularChainComplexFunctor AddCommGrpCat).obj (AddCommGrpCat.of ℤ)
    let C := F.obj (TopCat.of M)
    let ι (x : M) : F.obj (TopCat.of ↥({x}ᶜ : Set M)) ⟶ C :=
      F.map (TopCat.ofHom ⟨Subtype.val, continuous_subtype_val⟩)
    let localize (x : M) := HomologicalComplex.homologyMap (cokernel.π (ι x)) 3
    ∀ a : C.homology 3, ∃ K : Set M, IsCompact K ∧ ∀ x ∉ K, localize x a = 0

/-- The vanishing of a local top class propagates on a connected manifold. -/
def H3 : Prop :=
  ∀ (M : Type) [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [ConnectedSpace M],
    let F := (singularChainComplexFunctor AddCommGrpCat).obj (AddCommGrpCat.of ℤ)
    let C := F.obj (TopCat.of M)
    let ι (x : M) : F.obj (TopCat.of ↥({x}ᶜ : Set M)) ⟶ C :=
      F.map (TopCat.ofHom ⟨Subtype.val, continuous_subtype_val⟩)
    let localize (x : M) := HomologicalComplex.homologyMap (cokernel.π (ι x)) 3
    ∀ a : C.homology 3, (∃ x, localize x a = 0) → ∀ x, localize x a = 0

theorem main : H1 → H2 → H3 → OMA.R_PoincareConjecture_poincare_conjecture_R1.H2 := by
  intro detect support propagate M _ _ _ _ hM
  apply AddCommGrpCat.isZero_iff_subsingleton.mpr
  have vanish (a : (((singularHomologyFunctor AddCommGrpCat 3).obj (AddCommGrpCat.of ℤ)).obj
      (TopCat.of M))) : a = 0 := by
    obtain ⟨K, hK, hout⟩ := support M a
    have hproper : K ≠ Set.univ := by
      intro h
      exact hM ⟨h ▸ hK⟩
    have outside : ∃ x, x ∉ K := by
      by_contra! h
      exact hproper (Set.eq_univ_of_forall h)
    obtain ⟨x, hx⟩ := outside
    exact detect M a (propagate M a ⟨x, hout x hx⟩)
  exact ⟨fun a b => (vanish a).trans (vanish b).symm⟩

end OMA.R_PoincareConjecture_poincare_conjecture_R1_H2_R1
