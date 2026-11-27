import OMAReductions.R_PoincareConjecture_poincare_conjecture_R1_H2_R1_H2_R1
import Mathlib.Algebra.Category.Grp.Zero
import Mathlib.Algebra.Category.Grp.Limits
import Mathlib.Algebra.Category.Grp.AB
import Mathlib.Topology.Category.TopCat.EpiMono
import Mathlib.Algebra.Homology.ConcreteCategory

/-! Lifts a chain carried by a complement to a complement cycle and transports
its homology class by naturality of `homologyπ`. -/

open AlgebraicTopology CategoryTheory Limits

theorem OMA.solution :
    OMA.R_PoincareConjecture_poincare_conjecture_R1_H2_R1_H2_R1.H2 := by
  intro M hM x z c hc
  let F := (singularChainComplexFunctor AddCommGrpCat).obj (AddCommGrpCat.of ℤ)
  let C := F.obj (TopCat.of M)
  let D := F.obj (TopCat.of ↥({x}ᶜ : Set M))
  let incl : TopCat.of ↥({x}ᶜ : Set M) ⟶ TopCat.of M :=
    TopCat.ofHom ⟨Subtype.val, continuous_subtype_val⟩
  let φ : D ⟶ C := F.map incl
  have hincl : Mono incl := by
    rw [TopCat.mono_iff_injective]
    intro a b hab
    exact Subtype.ext hab
  have hφ : Mono φ := by
    exact Functor.map_mono F incl
  have hφ2 : Mono (φ.f 2) := by
    let E := HomologicalComplex.eval AddCommGrpCat (ComplexShape.down ℕ) 2
    have h := Functor.map_mono E φ
    exact h
  have hcycle : D.d 3 2 c = 0 := by
    apply (AddCommGrpCat.mono_iff_injective (φ.f 2)).mp hφ2
    have hcomm := congrArg (fun f => f c) (HomologicalComplex.Hom.comm φ 3 2)
    have hcomm' : (φ.f 2) (D.d 3 2 c) = C.d 3 2 ((φ.f 3) c) := by
      simpa only [ConcreteCategory.comp_apply] using hcomm.symm
    have hz : C.d 3 2 ((φ.f 3) c) = 0 := by
      rw [hc]
      change (C.iCycles 3 ≫ C.d 3 2) z = 0
      rw [HomologicalComplex.iCycles_d]
      simp
    rw [hcomm']
    simpa using hz
  let k : AddCommGrpCat.of ℤ ⟶ D.X 3 :=
    AddCommGrpCat.ofHom (AddMonoidHom.mk' (fun n : ℤ => n • c) (by
      intro m n
      exact add_zsmul c m n))
  have hk : CategoryTheory.CategoryStruct.comp k (D.d 3 2) =
      (0 : AddCommGrpCat.of ℤ ⟶ D.X 2) := by
    apply AddCommGrpCat.ext
    intro n
    change (D.d 3 2) (n • c) = 0
    rw [map_zsmul, hcycle, zsmul_zero]
  have hnext : (ComplexShape.down ℕ).next 3 = 2 :=
    ComplexShape.next_eq' (ComplexShape.down ℕ)
      (ComplexShape.down_mk 3 2 (by norm_num))
  let lift := D.liftCycles k 2 hnext hk
  let b : D.cycles 3 := lift 1
  refine ⟨b, ?_⟩
  have hcycles : (HomologicalComplex.cyclesMap φ 3) b = z := by
    apply (AddCommGrpCat.mono_iff_injective (C.iCycles 3)).mp inferInstance
    have heval : (C.iCycles 3) ((HomologicalComplex.cyclesMap φ 3) b) =
        (φ.f 3) ((D.iCycles 3) b) := by
      have h := congrArg (fun f => f b) (HomologicalComplex.cyclesMap_i φ 3)
      simpa only [ConcreteCategory.comp_apply] using h
    rw [heval]
    have hlift : (D.iCycles 3) b = k 1 := by
      have h := congrArg (fun f => f 1) (HomologicalComplex.liftCycles_i D k 2 hnext hk)
      simpa only [ConcreteCategory.comp_apply, b, lift] using h
    rw [hlift]
    have hk1 : (ConcreteCategory.hom k) (1 : ℤ) = c := by
      change (1 : ℤ) • c = c
      simp
    rw [hk1, hc]
  have hnat := congrArg (fun f => f b) (HomologicalComplex.homologyπ_naturality φ 3)
  simpa only [ConcreteCategory.comp_apply, hcycles] using hnat
