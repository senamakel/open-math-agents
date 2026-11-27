import OMAReductions.R_Green100_green_100_parts_i_R1

/-! Split the finite-field cellular counterexample into its group-ring
construction and the algebraic transfer from a one-sided inverse. The second
obligation is the short all-configurations argument in OpenAI's
`OAI.OddKaplansky.Cellular` artifact. -/

namespace OMA.R_Green100_green_100_parts_i_R1_H1_R1

open OMA.R_Green100_green_100_parts_i_R1

/-- The group-algebra witness constructed in OpenAI's odd-Kaplansky proof. -/
def H1 : Prop :=
  ∃ (K : Type) (fK : Field K) (ftK : Fintype K) (G : Type) (gG : Group G),
    letI := fK
    letI := ftK
    letI := gG
    ∃ a b : MonoidAlgebra K G, a * b = 1 ∧ b * a ≠ 1

/-- A one-sided group-algebra inverse yields an injective nonsurjective
cellular map on all configurations over a finite field. -/
def H2 : Prop :=
  ∀ (K : Type) [Field K] [Fintype K] (G : Type) [Group G]
    (a b : MonoidAlgebra K G), a * b = 1 → b * a ≠ 1 →
      Function.Injective (fun (x : G → K) (g : G) =>
        b.coeff.sum fun u c => c * x (g * u)) ∧
      ¬ Function.Surjective (fun (x : G → K) (g : G) =>
        b.coeff.sum fun u c => c * x (g * u))

theorem main : H1 → H2 → OMA.R_Green100_green_100_parts_i_R1.H1 := by
  intro hRing hTransfer
  obtain ⟨K, fK, ftK, G, gG, a, b, hab, hba⟩ := hRing
  obtain ⟨hinj, hsurj⟩ := @hTransfer K fK ftK G gG a b hab hba
  exact ⟨K, fK, ftK, G, gG, b, hinj, hsurj⟩

end OMA.R_Green100_green_100_parts_i_R1_H1_R1
