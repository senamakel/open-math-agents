import OMAReductions.R_PoincareConjecture_poincare_conjecture_R1_H1_R1_H2_R1_H2_R1_H2_R1
import Mathlib.Algebra.Category.Grp.Abelian
import Mathlib.Algebra.Homology.HomologicalComplexAbelian
import Mathlib.Algebra.Homology.HomologySequenceLemmas

/-!
The relative comparison is the five-lemma argument on the cokernel sequences
of the two subcomplex inclusions. This is the algebraic step used by
`IntegralRelativeChains.lean` in FrenzyMath/PoincareConjecture at
62db01af9388dc1d9b56b66d6674f4c09b2318a2 (Apache-2.0).
-/

open CategoryTheory Limits HomologicalComplex

theorem OMA.solution :
    OMA.R_PoincareConjecture_poincare_conjecture_R1_H1_R1_H2_R1_H2_R1_H2_R1.H2 := by
  intro K L A i j f w _ _ hiso n
  have hf : QuasiIso f := (quasiIso_iff f).mpr
    (fun k => (quasiIsoAt_iff_isIso_homologyMap f k).mpr (hiso k))
  let S := ShortComplex.cokernelSequence i
  let T := ShortComplex.cokernelSequence j
  let : Mono S.f := by change Mono i; infer_instance
  let : Mono T.f := by change Mono j; infer_instance
  have hs : S.ShortExact := { exact := ShortComplex.cokernelSequence_exact _ }
  have ht : T.ShortExact := { exact := ShortComplex.cokernelSequence_exact _ }
  let u := cokernel.map i j (𝟙 A) f (by simpa [w])
  let φ : S ⟶ T :=
    { τ₁ := 𝟙 A
      τ₂ := f
      τ₃ := u
      comm₁₂ := by
        change CategoryStruct.comp (𝟙 A) j = CategoryStruct.comp i f
        simpa using w.symm
      comm₂₃ := by
        change CategoryStruct.comp f (cokernel.π j) =
          CategoryStruct.comp (cokernel.π i) u
        simp [u] }
  have h₁ : QuasiIso φ.τ₁ := by change QuasiIso (𝟙 A); infer_instance
  have h₃ : QuasiIso φ.τ₃ :=
    HomologicalComplex.HomologySequence.quasiIso_τ₃ φ hs ht h₁ hf
  exact (quasiIsoAt_iff_isIso_homologyMap u n).mp
    ((quasiIso_iff u).mp h₃ n)
