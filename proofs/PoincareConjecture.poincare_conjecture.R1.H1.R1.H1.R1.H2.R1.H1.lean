import OMAReductions.R_PoincareConjecture_poincare_conjecture_R1_H1_R1_H1_R1_H2_R1
import Mathlib.Topology.Homotopy.Contractible

/-! The positive-degree singular homology of a contractible space is zero.
The pair long exact sequence gives the collapse isomorphism, using the
constant retraction to split the map on the subspace homology. -/

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

theorem OMA.solution :
    OMA.R_PoincareConjecture_poincare_conjecture_R1_H1_R1_H1_R1_H2_R1.H1 := by
  intro X _ A _ n hn
  let C := (singularChainComplexFunctor AddCommGrpCat).obj (AddCommGrpCat.of ℤ)
  let j : TopCat.of A ⟶ TopCat.of X :=
    TopCat.ofHom ⟨Subtype.val, continuous_subtype_val⟩
  let S := ShortComplex.cokernelSequence (C.map j)
  have hS : S.ShortExact := pairSequenceShortExact A
  have hrel : (ComplexShape.down ℕ).Rel n (n - 1) := by
    change (n - 1) + 1 = n
    omega
  obtain ⟨a, ha⟩ := id_nullhomotopic A
  obtain ⟨e⟩ := ContractibleSpace.hequiv_unit A
  obtain ⟨eH⟩ := homotopy_homology_iso n e
  have hzero : IsZero (S.X₁.homology n) :=
    (isZero_singularHomologyFunctor_of_totallyDisconnectedSpace
      AddCommGrpCat n (AddCommGrpCat.of ℤ) (TopCat.of Unit) (by omega)).of_iso eH
  let F := (singularHomologyFunctor AddCommGrpCat (n - 1)).obj (AddCommGrpCat.of ℤ)
  let r : TopCat.of X ⟶ TopCat.of A := TopCat.ofHom (ContinuousMap.const X a)
  let hr : TopCat.Homotopy (j ≫ r) (𝟙 (TopCat.of A)) := Classical.choice ha.symm
  have hsplit : (F.map j ≫ F.map r) = 𝟙 _ := by
    rw [← F.map_comp, ← F.map_id]
    exact hr.congr_homologyMap_singularChainComplexFunctor (AddCommGrpCat.of ℤ) (n - 1)
  have hmono : Mono (HomologicalComplex.homologyMap S.f (n - 1)) := by
    change Mono (F.map j)
    constructor
    intro T g h eq
    have eq' := congrArg (fun k : T ⟶ F.obj (TopCat.of X) => k ≫ F.map r) eq
    simpa only [Category.assoc, hsplit, Category.comp_id] using eq'
  have hδ : hS.δ n (n - 1) hrel = 0 := by
    letI := hmono
    rw [← cancel_mono (HomologicalComplex.homologyMap S.f (n - 1)), zero_comp]
    exact hS.δ_comp n (n - 1) hrel
  have hgmono : Mono (HomologicalComplex.homologyMap S.g n) :=
    (hS.homology_exact₂ n).mono_g (hzero.eq_of_src _ _)
  have hgepi : Epi (HomologicalComplex.homologyMap S.g n) :=
    (hS.homology_exact₃ n (n - 1) hrel).epi_f hδ
  letI := hgmono
  letI := hgepi
  exact isIso_of_mono_of_epi (HomologicalComplex.homologyMap S.g n)
