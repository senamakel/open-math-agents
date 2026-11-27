import OMAReductions.R_PoincareConjecture_poincare_conjecture_R1_H3_R2
import Mathlib

open Set TopologicalSpace Topology
open scoped Manifold ContDiff

private abbrev componentFiber {M : Type*} [TopologicalSpace M] (c : ConnectedComponents M) :
    Set M := ConnectedComponents.mk ⁻¹' {c}

private theorem componentFiberOpen {M : Type*} [TopologicalSpace M] [LocallyConnectedSpace M]
    (c : ConnectedComponents M) : IsOpen (componentFiber c) := by
  obtain ⟨x, rfl⟩ := ConnectedComponents.surjective_coe c
  simpa only [componentFiber, connectedComponents_preimage_singleton] using
    (isOpen_connectedComponent (x := x))

private theorem componentFiberAtlas {M : Type*} [TopologicalSpace M]
    (h : ∀ x : M, ∃ atlas : ChartedSpace (EuclideanSpace ℝ (Fin 3)) (connectedComponent x),
      letI := atlas
      IsManifold (𝓡 3) ∞ (connectedComponent x))
    (c : ConnectedComponents M) :
    ∃ atlas : ChartedSpace (EuclideanSpace ℝ (Fin 3)) (componentFiber c),
      letI := atlas
      IsManifold (𝓡 3) ∞ (componentFiber c) := by
  obtain ⟨x, rfl⟩ := ConnectedComponents.surjective_coe c
  let P (S : Set M) : Prop :=
    ∃ a : ChartedSpace (EuclideanSpace ℝ (Fin 3)) S, letI := a; IsManifold (𝓡 3) ∞ S
  change P (componentFiber (ConnectedComponents.mk x))
  have he : componentFiber (ConnectedComponents.mk x) = connectedComponent x :=
    connectedComponents_preimage_singleton
  exact he.symm ▸ (show P (connectedComponent x) from h x)

private theorem componentFiberDisjoint {M : Type*} [TopologicalSpace M]
    {c d : ConnectedComponents M} (h : c ≠ d) :
    Disjoint (componentFiber c) (componentFiber d) := by
  rw [Set.disjoint_left]
  intro x hc hd
  exact h ((Set.mem_singleton_iff.mp hc).symm.trans (Set.mem_singleton_iff.mp hd))

private theorem disjointLiftedChartTransition {X Y Z H : Type*}
    [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z] [TopologicalSpace H] [Nonempty H]
    {f : X → Z} {g : Y → Z} (hf : IsOpenEmbedding f) (hg : IsOpenEmbedding g)
    (hd : Disjoint (range f) (range g)) (e : OpenPartialHomeomorph X H)
    (d : OpenPartialHomeomorph Y H) :
    ((e.lift_openEmbedding hf).symm.trans (d.lift_openEmbedding hg)).source = ∅ := by
  apply Set.eq_empty_iff_forall_notMem.mpr
  intro x hx
  rw [OpenPartialHomeomorph.trans_source, OpenPartialHomeomorph.lift_openEmbedding_symm,
    OpenPartialHomeomorph.lift_openEmbedding_source] at hx
  obtain ⟨_, y, _, hy⟩ := hx
  exact Set.disjoint_left.mp hd ⟨e.symm x, rfl⟩ ⟨y, hy⟩


private theorem glueComponentAtlases {M : Type*} [TopologicalSpace M] [LocallyConnectedSpace M]
    (h : ∀ x : M, ∃ a : ChartedSpace (EuclideanSpace ℝ (Fin 3)) (connectedComponent x),
        letI := a; IsManifold (𝓡 3) ∞ (connectedComponent x)) :
    ∃ a : ChartedSpace (EuclideanSpace ℝ (Fin 3)) M,
      letI := a; IsManifold (𝓡 3) ∞ M := by
  classical
  let E := EuclideanSpace ℝ (Fin 3)
  choose A hA using componentFiberAtlas h
  let lm (c : ConnectedComponents M) (e : OpenPartialHomeomorph (componentFiber c) E) :=
    e.lift_openEmbedding (componentFiberOpen c).isOpenEmbedding_subtypeVal
  let ch (x : M) : OpenPartialHomeomorph M E :=
    lm (ConnectedComponents.mk x) ((A _).chartAt ⟨x, rfl⟩)
  let U : ChartedSpace E M :=
    { atlas := {e | ∃ (c : ConnectedComponents M) (d : OpenPartialHomeomorph (componentFiber c) E),
        d ∈ (A c).atlas ∧ lm c d = e}
      chartAt := ch
      mem_chart_source := by
        intro x
        change x ∈ (lm _ ((A _).chartAt ⟨x, rfl⟩)).source
        rw [OpenPartialHomeomorph.lift_openEmbedding_source]
        exact ⟨⟨x, rfl⟩, (A _).mem_chart_source _, rfl⟩
      chart_mem_atlas := fun x => ⟨_, _, (A _).chart_mem_atlas _, rfl⟩ }
  refine ⟨U, ?_⟩
  let : ChartedSpace E M := U
  let : HasGroupoid M (contDiffGroupoid ∞ (𝓡 3)) := by
    constructor
    rintro _ _ ⟨c, e, he, rfl⟩ ⟨d, f, hf, rfl⟩
    by_cases hcd : c = d
    · subst d
      let : ChartedSpace E (componentFiber c) := A c
      let : IsManifold (𝓡 3) ∞ (componentFiber c) := hA c
      dsimp only [lm]
      rw [OpenPartialHomeomorph.lift_openEmbedding_trans]
      exact (contDiffGroupoid ∞ (𝓡 3)).compatible he hf
    · apply ContDiffGroupoid.mem_of_source_eq_empty
      apply disjointLiftedChartTransition
      rw [Set.disjoint_left]
      rintro x ⟨y, rfl⟩ ⟨z, hz⟩
      exact Set.disjoint_left.mp (componentFiberDisjoint hcd) y.property (hz ▸ z.property)
  exact IsManifold.mk' (𝓡 3) ∞ M


theorem OMA.solution : OMA.R_PoincareConjecture_poincare_conjecture_R1_H3_R2.H2 :=

  fun _ _ _ h => glueComponentAtlases h
