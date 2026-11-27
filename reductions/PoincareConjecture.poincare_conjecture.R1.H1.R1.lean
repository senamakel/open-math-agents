import OMAReductions.R_PoincareConjecture_poincare_conjecture_R1

/-!
Reduce the nonvanishing of the three-sphere's third integral singular homology
to the standard sphere recurrence and the circle base case.  This follows the
organization in frenzymath/PoincareConjecture at 62db01af9388dc1d9b56b66d6674f4c09b2318a2,
notably `IntegralSphereHomology.lean` and `IntegralSphereBase.lean` (Apache-2.0).
The recurrence uses a contractible two-chart cover and the Mayer-Vietoris sequence;
the base uses the corresponding circle cover and reduced H0 of the zero-sphere.
-/

namespace OMA.R_PoincareConjecture_poincare_conjecture_R1_H1_R1

open AlgebraicTopology CategoryTheory Limits
open scoped ContinuousMap EuclideanGeometry

def H1 : Prop :=
  Nonempty (((singularHomologyFunctor AddCommGrpCat 3).obj (AddCommGrpCat.of ℤ)).obj
      (TopCat.of (Metric.sphere (0 : EuclideanSpace ℝ (Fin 4)) 1)) ≅
    ((singularHomologyFunctor AddCommGrpCat 2).obj (AddCommGrpCat.of ℤ)).obj
      (TopCat.of (Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1)))

def H2 : Prop :=
  Nonempty (((singularHomologyFunctor AddCommGrpCat 2).obj (AddCommGrpCat.of ℤ)).obj
      (TopCat.of (Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1)) ≅
    ((singularHomologyFunctor AddCommGrpCat 1).obj (AddCommGrpCat.of ℤ)).obj
      (TopCat.of (Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1)))

def H3 : Prop :=
  Nonempty (((singularHomologyFunctor AddCommGrpCat 1).obj (AddCommGrpCat.of ℤ)).obj
      (TopCat.of (Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1)) ≅ AddCommGrpCat.of ℤ)

theorem main : H1 → H2 → H3 →
    OMA.R_PoincareConjecture_poincare_conjecture_R1.H1 := by
  intro hS3 hS2 hS1
  obtain ⟨eS3⟩ := hS3
  obtain ⟨eS2⟩ := hS2
  obtain ⟨eS1⟩ := hS1
  change ¬ IsZero (((singularHomologyFunctor AddCommGrpCat 3).obj
    (AddCommGrpCat.of ℤ)).obj
      (TopCat.of (Metric.sphere (0 : EuclideanSpace ℝ (Fin 4)) 1)))
  intro hz
  have hzZ : IsZero (AddCommGrpCat.of ℤ) :=
    hz.of_iso (eS3 ≪≫ eS2 ≪≫ eS1).symm
  have hsub : Subsingleton ℤ := AddCommGrpCat.subsingleton_of_isZero hzZ
  have h01 : (0 : ℤ) = 1 := hsub.elim _ _
  norm_num at h01

end OMA.R_PoincareConjecture_poincare_conjecture_R1_H1_R1
