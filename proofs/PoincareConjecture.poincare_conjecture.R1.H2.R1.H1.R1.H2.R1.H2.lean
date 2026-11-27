import OMAReductions.R_PoincareConjecture_poincare_conjecture_R1_H2_R1_H1_R1_H2_R1
import Mathlib.CategoryTheory.Abelian.CommSq
import Mathlib.Topology.Category.TopCat.EpiMono

/-!
The canonical chain pushout presents the signed intersection map as a
cokernel sequence. The intersection inclusion is injective, so the
signed map is mono and the sequence is short exact.
-/

open CategoryTheory Limits AlgebraicTopology

theorem OMA.solution :
    OMA.R_PoincareConjecture_poincare_conjecture_R1_H2_R1_H1_R1_H2_R1.H2 := by
  intro X _ U V
  let C := (singularChainComplexFunctor AddCommGrpCat.{0}).obj (AddCommGrpCat.of ℤ)
  let i₀ : TopCat.of ↥(U ∩ V) ⟶ TopCat.of U :=
    TopCat.ofHom ⟨Set.inclusion Set.inter_subset_left, continuous_inclusion Set.inter_subset_left⟩
  let j₀ : TopCat.of ↥(U ∩ V) ⟶ TopCat.of V :=
    TopCat.ofHom ⟨Set.inclusion Set.inter_subset_right, continuous_inclusion Set.inter_subset_right⟩
  let i := C.map i₀
  let j := C.map j₀
  have : Mono i₀ := (TopCat.mono_iff_injective _).mpr
    (Set.inclusion_injective (Set.inter_subset_left (s := U) (t := V)))
  let : Mono i := by infer_instance
  have sq : IsPushout i j (pushout.inl i j) (pushout.inr i j) :=
    IsPushout.of_isColimit (c := PushoutCocone.mk _ _ pushout.condition) (pushoutIsPushout i j)
  let : Mono sq.shortComplex.f := by
    change Mono (biprod.lift i (-j))
    have hm : Mono (CategoryStruct.comp (biprod.lift i (-j)) biprod.fst) := by
      rw [biprod.lift_fst]
      infer_instance
    exact mono_of_mono (biprod.lift i (-j)) biprod.fst
  let : Epi sq.shortComplex.g := sq.epi_shortComplex_g
  have hs : sq.shortComplex.ShortExact := { exact := sq.exact_shortComplex }
  exact hs
