import OMAReductions.R_PoincareConjecture_poincare_conjecture_R1_H1_R1_H3_R2
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.AlgebraicTopology.SingularHomology.HomologyZero
import Mathlib.Algebra.Category.Grp.Limits
import Mathlib.Algebra.Category.Grp.Colimits
import Mathlib.Algebra.Category.Grp.Abelian
import Mathlib.Topology.Homotopy.Path

open AlgebraicTopology CategoryTheory Limits

noncomputable section

private def realSphereTwoPoints : Metric.sphere (0 : ℝ) 1 ≃ Bool where
  toFun x := decide (x.val = 1)
  invFun b := ⟨if b then 1 else -1, by cases b <;> simp⟩
  left_inv x := by
    have hx : |x.val| = 1 := by
      have h : dist x.val (0 : ℝ) = 1 := x.property
      simpa only [Real.dist_eq, sub_zero] using h
    have h : x.val = 1 ∨ x.val = -1 :=
      abs_eq_abs.mp (by simpa using hx)
    apply Subtype.ext
    rcases h with h | h <;> norm_num [h]
  right_inv b := by cases b <;> norm_num

private def zeroSphereTwoPoints :
    Metric.sphere (0 : EuclideanSpace ℝ (Fin 1)) 1 ≃ Bool := by
  let e := (OrthonormalBasis.singleton (Fin 1) ℝ).repr.symm
  exact (e.toEquiv.subtypeEquiv (fun x => by
    simp only [Metric.mem_sphere, dist_zero_right]
    change (‖x‖ = 1) ↔ ‖e x‖ = 1
    rw [e.norm_map]
    rfl)).trans realSphereTwoPoints

private def zeroSphereComponents :
    ZerothHomotopy (Metric.sphere (0 : EuclideanSpace ℝ (Fin 1)) 1) ≃ Bool := by
  let S := Metric.sphere (0 : EuclideanSpace ℝ (Fin 1)) 1
  letI : Finite S := Finite.of_equiv Bool zeroSphereTwoPoints.symm
  let d : ZerothHomotopy S ≃ S :=
    { toFun := ZerothHomotopy.lift id (by
        intro x y p
        have h := TotallyDisconnectedSpace.eq_of_continuous p p.continuous 0 1
        simpa using h)
      invFun := ZerothHomotopy.mk
      left_inv := by
        intro q
        obtain ⟨x, rfl⟩ := ZerothHomotopy.mk_surjective q
        rfl
      right_inv := fun _ => rfl }
  exact d.trans zeroSphereTwoPoints

private def pairSum : AddCommGrpCat.of (ℤ × ℤ) ⟶ AddCommGrpCat.of ℤ :=
  AddCommGrpCat.ofHom
    { toFun := fun z => z.1 + z.2
      map_zero' := by simp
      map_add' := by intro x y; change (x.1 + y.1) + (x.2 + y.2) = _; abel }

private def pairSumKernelIso : kernel pairSum ≅ AddCommGrpCat.of ℤ := by
  let e : pairSum.hom.ker ≃+ ℤ :=
    { toFun := fun z => z.val.1
      invFun := fun a => ⟨(a, -a), by change a + -a = 0; simp⟩
      left_inv := by
        intro z
        have hz : z.val.1 + z.val.2 = 0 := z.property
        apply Subtype.ext
        apply Prod.ext
        · rfl
        · change -z.val.1 = z.val.2
          omega
      right_inv := fun _ => rfl
      map_add' := fun _ _ => rfl }
  exact AddCommGrpCat.kernelIsoKer pairSum ≪≫ e.toAddCommGrpIso

private theorem twoPointAugmentationKernel (X : Type) [TopologicalSpace X]
    (e : ZerothHomotopy X ≃ Bool) :
    Nonempty (kernel ((TopCat.of X).singularHomology₀ε (AddCommGrpCat.of ℤ)) ≅
      AddCommGrpCat.of ℤ) := by
  classical
  let R := AddCommGrpCat.of ℤ
  let D := fun (_ : ZerothHomotopy X) => R
  let P := AddCommGrpCat.of (ℤ × ℤ)
  let left : R ⟶ P := AddCommGrpCat.ofHom
    { toFun := fun z => (z, 0), map_zero' := rfl, map_add' := fun _ _ => by ext <;> simp }
  let right : R ⟶ P := AddCommGrpCat.ofHom
    { toFun := fun z => (0, z), map_zero' := rfl, map_add' := fun _ _ => by ext <;> simp }
  let toPair : (∐ D) ⟶ P := Sigma.desc (fun i => if e i then right else left)
  let fromPair : P ⟶ (∐ D) := AddCommGrpCat.ofHom
    { toFun := fun z => Sigma.ι D (e.symm false) z.1 + Sigma.ι D (e.symm true) z.2
      map_zero' := by simp
      map_add' := by intro x y; simp only [Prod.fst_add, Prod.snd_add, map_add]; abel }
  have toPairOn (i : ZerothHomotopy X) (z : ℤ) :
      toPair (Sigma.ι D i z) = if e i then (0, z) else (z, 0) := by
    change (Sigma.ι D i ≫ toPair) z = _
    rw [Sigma.ι_desc]
    split <;> rfl
  have h₁ : (toPair ≫ fromPair) = 𝟙 _ := by
    apply Sigma.hom_ext
    intro i
    apply AddCommGrpCat.hom_ext
    apply AddMonoidHom.ext
    intro z
    change fromPair (toPair (Sigma.ι D i z)) = Sigma.ι D i z
    rw [toPairOn]
    cases hi : e i
    · have h : e.symm false = i := by rw [← hi, e.symm_apply_apply]
      subst i
      simp [fromPair]
    · have h : e.symm true = i := by rw [← hi, e.symm_apply_apply]
      subst i
      simp [fromPair]
  have h₂ : (fromPair ≫ toPair) = 𝟙 _ := by
    apply AddCommGrpCat.hom_ext
    apply AddMonoidHom.ext
    intro z
    change toPair (Sigma.ι D (e.symm false) z.1 + Sigma.ι D (e.symm true) z.2) = z
    rcases z with ⟨a,b⟩
    simp [toPairOn]
    exact Prod.ext (add_zero _) (zero_add _)
  let iso : (∐ D) ≅ P := ⟨toPair, fromPair, h₁, h₂⟩
  have hsum : (toPair ≫ pairSum) = Sigma.desc (fun (_ : ZerothHomotopy X) => 𝟙 R) := by
    apply Sigma.hom_ext
    intro i
    apply AddCommGrpCat.hom_ext
    apply AddMonoidHom.ext
    intro z
    change pairSum (toPair (Sigma.ι D i z)) =
      (Sigma.ι D i ≫ Sigma.desc (fun (_ : ZerothHomotopy X) => 𝟙 R)) z
    rw [Sigma.ι_desc, toPairOn]
    cases e i <;> simp [pairSum] <;> rfl
  let eH := (TopCat.of X).singularHomology₀Iso R
  let E := eH ≪≫ iso
  have he : (((TopCat.of X).singularHomology₀ε R) ≫ (Iso.refl R).hom) =
      (E.hom ≫ pairSum) := by
    rw [Iso.refl_hom, Category.comp_id]
    change (TopCat.of X).singularHomology₀ε R = (eH.hom ≫ toPair) ≫ pairSum
    rw [Category.assoc, hsum, TopCat.singularHomology₀Iso_sigma_desc_id]
  exact ⟨kernel.mapIso _ _ E (Iso.refl R) he ≪≫ pairSumKernelIso⟩

private theorem zeroSphereAugmentationKernel :
    Nonempty (kernel (TopCat.singularHomology₀ε
      (TopCat.of (Metric.sphere (0 : EuclideanSpace ℝ (Fin 1)) 1)) (AddCommGrpCat.of ℤ)) ≅ AddCommGrpCat.of ℤ) :=
  twoPointAugmentationKernel _ zeroSphereComponents

theorem OMA.solution : OMA.R_PoincareConjecture_poincare_conjecture_R1_H1_R1_H3_R2.H4 :=
  zeroSphereAugmentationKernel

/-! The zero-sphere coordinate identification follows FrenzyMath's IntegralZeroSphere.lean at the Apache-2.0 revision 432c38f2aa5a30efb13871292d17b4a3309a496a. The augmentation calculation uses the coproduct in AddCommGrpCat. -/

/-
Source NOTICE

Poincare Conjecture

This distribution contains adapted portions of external Lean developments.
The following notices apply to those portions, not to the entire project.
See PoincareConjecture/MODIFICATIONS.md and the per-file source notices for
the scope of adaptations, authorship, comparison revisions, and changes.

DifferentialGeometry
Copyright 2026 The DifferentialGeometry contributors

DeGiorgi (including material incorporated through DifferentialGeometry)
Copyright 2026 Scott Armstrong and Julia Kempe

TauCeti (individual file notices determine which notice applies)
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.

ClassificationOfSurfaces
Copyright (c) 2026 ClassificationOfSurfaces contributors. All rights reserved.

Mathlib adaptations
Copyright (c) 2025 Yizheng Zhu. All rights reserved.
Copyright (c) 2025 Sébastien Gouëzel. All rights reserved.

These sources are distributed under Apache-2.0. Verbatim source licenses and
the DifferentialGeometry NOTICE are retained in
archive/PoincareConjecture/provenance/2026-09-29/licenses/.

Original license


                                 Apache License
                           Version 2.0, January 2004
                        http://www.apache.org/licenses/

   TERMS AND CONDITIONS FOR USE, REPRODUCTION, AND DISTRIBUTION

   1. Definitions.

      "License" shall mean the terms and conditions for use, reproduction,
      and distribution as defined by Sections 1 through 9 of this document.

      "Licensor" shall mean the copyright owner or entity authorized by
      the copyright owner that is granting the License.

      "Legal Entity" shall mean the union of the acting entity and all
      other entities that control, are controlled by, or are under common
      control with that entity. For the purposes of this definition,
      "control" means (i) the power, direct or indirect, to cause the
      direction or management of such entity, whether by contract or
      otherwise, or (ii) ownership of fifty percent (50%) or more of the
      outstanding shares, or (iii) beneficial ownership of such entity.

      "You" (or "Your") shall mean an individual or Legal Entity
      exercising permissions granted by this License.

      "Source" form shall mean the preferred form for making modifications,
      including but not limited to software source code, documentation
      source, and configuration files.

      "Object" form shall mean any form resulting from mechanical
      transformation or translation of a Source form, including but
      not limited to compiled object code, generated documentation,
      and conversions to other media types.

      "Work" shall mean the work of authorship, whether in Source or
      Object form, made available under the License, as indicated by a
      copyright notice that is included in or attached to the work
      (an example is provided in the Appendix below).

      "Derivative Works" shall mean any work, whether in Source or Object
      form, that is based on (or derived from) the Work and for which the
      editorial revisions, annotations, elaborations, or other modifications
      represent, as a whole, an original work of authorship. For the purposes
      of this License, Derivative Works shall not include works that remain
      separable from, or merely link (or bind by name) to the interfaces of,
      the Work and Derivative Works thereof.

      "Contribution" shall mean any work of authorship, including
      the original version of the Work and any modifications or additions
      to that Work or Derivative Works thereof, that is intentionally
      submitted to Licensor for inclusion in the Work by the copyright owner
      or by an individual or Legal Entity authorized to submit on behalf of
      the copyright owner. For the purposes of this definition, "submitted"
      means any form of electronic, verbal, or written communication sent
      to the Licensor or its representatives, including but not limited to
      communication on electronic mailing lists, source code control systems,
      and issue tracking systems that are managed by, or on behalf of, the
      Licensor for the purpose of discussing and improving the Work, but
      excluding communication that is conspicuously marked or otherwise
      designated in writing by the copyright owner as "Not a Contribution."

      "Contributor" shall mean Licensor and any individual or Legal Entity
      on behalf of whom a Contribution has been received by Licensor and
      subsequently incorporated within the Work.

   2. Grant of Copyright License. Subject to the terms and conditions of
      this License, each Contributor hereby grants to You a perpetual,
      worldwide, non-exclusive, no-charge, royalty-free, irrevocable
      copyright license to reproduce, prepare Derivative Works of,
      publicly display, publicly perform, sublicense, and distribute the
      Work and such Derivative Works in Source or Object form.

   3. Grant of Patent License. Subject to the terms and conditions of
      this License, each Contributor hereby grants to You a perpetual,
      worldwide, non-exclusive, no-charge, royalty-free, irrevocable
      (except as stated in this section) patent license to make, have made,
      use, offer to sell, sell, import, and otherwise transfer the Work,
      where such license applies only to those patent claims licensable
      by such Contributor that are necessarily infringed by their
      Contribution(s) alone or by combination of their Contribution(s)
      with the Work to which such Contribution(s) was submitted. If You
      institute patent litigation against any entity (including a
      cross-claim or counterclaim in a lawsuit) alleging that the Work
      or a Contribution incorporated within the Work constitutes direct
      or contributory patent infringement, then any patent licenses
      granted to You under this License for that Work shall terminate
      as of the date such litigation is filed.

   4. Redistribution. You may reproduce and distribute copies of the
      Work or Derivative Works thereof in any medium, with or without
      modifications, and in Source or Object form, provided that You
      meet the following conditions:

      (a) You must give any other recipients of the Work or
          Derivative Works a copy of this License; and

      (b) You must cause any modified files to carry prominent notices
          stating that You changed the files; and

      (c) You must retain, in the Source form of any Derivative Works
          that You distribute, all copyright, patent, trademark, and
          attribution notices from the Source form of the Work,
          excluding those notices that do not pertain to any part of
          the Derivative Works; and

      (d) If the Work includes a "NOTICE" text file as part of its
          distribution, then any Derivative Works that You distribute must
          include a readable copy of the attribution notices contained
          within such NOTICE file, excluding those notices that do not
          pertain to any part of the Derivative Works, in at least one
          of the following places: within a NOTICE text file distributed
          as part of the Derivative Works; within the Source form or
          documentation, if provided along with the Derivative Works; or,
          within a display generated by the Derivative Works, if and
          wherever such third-party notices normally appear. The contents
          of the NOTICE file are for informational purposes only and
          do not modify the License. You may add Your own attribution
          notices within Derivative Works that You distribute, alongside
          or as an addendum to the NOTICE text from the Work, provided
          that such additional attribution notices cannot be construed
          as modifying the License.

      You may add Your own copyright statement to Your modifications and
      may provide additional or different license terms and conditions
      for use, reproduction, or distribution of Your modifications, or
      for any such Derivative Works as a whole, provided Your use,
      reproduction, and distribution of the Work otherwise complies with
      the conditions stated in this License.

   5. Submission of Contributions. Unless You explicitly state otherwise,
      any Contribution intentionally submitted for inclusion in the Work
      by You to the Licensor shall be under the terms and conditions of
      this License, without any additional terms or conditions.
      Notwithstanding the above, nothing herein shall supersede or modify
      the terms of any separate license agreement you may have executed
      with Licensor regarding such Contributions.

   6. Trademarks. This License does not grant permission to use the trade
      names, trademarks, service marks, or product names of the Licensor,
      except as required for reasonable and customary use in describing the
      origin of the Work and reproducing the content of the NOTICE file.

   7. Disclaimer of Warranty. Unless required by applicable law or
      agreed to in writing, Licensor provides the Work (and each
      Contributor provides its Contributions) on an "AS IS" BASIS,
      WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or
      implied, including, without limitation, any warranties or conditions
      of TITLE, NON-INFRINGEMENT, MERCHANTABILITY, or FITNESS FOR A
      PARTICULAR PURPOSE. You are solely responsible for determining the
      appropriateness of using or redistributing the Work and assume any
      risks associated with Your exercise of permissions under this License.

   8. Limitation of Liability. In no event and under no legal theory,
      whether in tort (including negligence), contract, or otherwise,
      unless required by applicable law (such as deliberate and grossly
      negligent acts) or agreed to in writing, shall any Contributor be
      liable to You for damages, including any direct, indirect, special,
      incidental, or consequential damages of any character arising as a
      result of this License or out of the use or inability to use the
      Work (including but not limited to damages for loss of goodwill,
      work stoppage, computer failure or malfunction, or any and all
      other commercial damages or losses), even if such Contributor
      has been advised of the possibility of such damages.

   9. Accepting Warranty or Additional Liability. While redistributing
      the Work or Derivative Works thereof, You may choose to offer,
      and charge a fee for, acceptance of support, warranty, indemnity,
      or other liability obligations and/or rights consistent with this
      License. However, in accepting such obligations, You may act only
      on Your own behalf and on Your sole responsibility, not on behalf
      of any other Contributor, and only if You agree to indemnify,
      defend, and hold each Contributor harmless for any liability
      incurred by, or claims asserted against, such Contributor by reason
      of your accepting any such warranty or additional liability.

   END OF TERMS AND CONDITIONS

   APPENDIX: How to apply the Apache License to your work.

      To apply the Apache License to your work, attach the following
      boilerplate notice, with the fields enclosed by brackets "[]"
      replaced with your own identifying information. (Don't include
      the brackets!)  The text should be enclosed in the appropriate
      comment syntax for the file format. We also recommend that a
      file or class name and description of purpose be included on the
      same "printed page" as the copyright notice for easier
      identification within third-party archives.

   Copyright [yyyy] [name of copyright owner]

   Licensed under the Apache License, Version 2.0 (the "License");
   you may not use this file except in compliance with the License.
   You may obtain a copy of the License at

       http://www.apache.org/licenses/LICENSE-2.0

   Unless required by applicable law or agreed to in writing, software
   distributed under the License is distributed on an "AS IS" BASIS,
   WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
   See the License for the specific language governing permissions and
   limitations under the License.

-/
