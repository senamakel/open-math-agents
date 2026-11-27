import OMAReductions.R_Green100_green_100_parts_i_R1
import Mathlib.LinearAlgebra.Dual.Lemmas

/-! The finite-model core of sofic surjunctivity for linear cellular maps.

The first obligation identifies the transpose of right multiplication by a
group-ring element with the configuration-space cellular map. The second is
direct finiteness for finite-field group algebras of sofic groups. The final
obligation transports a two-sided inverse back to surjectivity of the
cellular map. The middle step uses Mathlib's algebraic duality
criterion to turn injectivity of the cellular transpose into a right inverse.
-/

namespace OMA.R_Green100_green_100_parts_i_R1_H2_R1

open OMA.R_Green100_green_100_parts_i_R1
open Green100

/-- Configuration injectivity gives injectivity of the transpose of right
multiplication on the group algebra. This is the finite-support/product
duality bridge for the cellular map. -/
def H1 : Prop :=
  ∀ (K : Type) [Field K] [Fintype K] (G : Type) [Group G]
    (b : MonoidAlgebra K G),
    Function.Injective (fun (x : G → K) (g : G) =>
      b.coeff.sum fun u c => c * x (g * u)) →
    Function.Injective (LinearMap.mulRight K b).dualMap

/-- A sofic group algebra over a finite field is directly finite. This is the
finite-model theorem supplied by the Gromov--Weiss/Elek--Szabó theory. -/
def H2 : Prop :=
  ∀ (K : Type) [Field K] [Fintype K] (G : Type) [Group G], IsSofic G →
    ∀ a b : MonoidAlgebra K G, a * b = 1 → b * a = 1

/-- A two-sided inverse for the local rule makes its cellular map surjective. -/
def H3 : Prop :=
  ∀ (K : Type) [Field K] [Fintype K] (G : Type) [Group G]
    (a b : MonoidAlgebra K G), b * a = 1 →
    Function.Surjective (fun (x : G → K) (g : G) =>
      b.coeff.sum fun u c => c * x (g * u))

theorem main : H1 → H2 → H3 → OMA.R_Green100_green_100_parts_i_R1.H2 := by
  intro hdual hfinite htransfer K instK fintypeK G instG hSofic b hinj
  have hdual_inj : Function.Injective (LinearMap.mulRight K b).dualMap :=
    hdual K G b hinj
  have hright_surj : Function.Surjective (LinearMap.mulRight K b) :=
    (LinearMap.dualMap_injective_iff).mp hdual_inj
  obtain ⟨a, ha⟩ := hright_surj 1
  have hab : a * b = 1 := by simpa using ha
  have hba : b * a = 1 := hfinite K G hSofic a b hab
  exact htransfer K G a b hba

end OMA.R_Green100_green_100_parts_i_R1_H2_R1
