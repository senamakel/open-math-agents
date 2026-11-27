import OMAReductions.R_PoincareConjecture_poincare_conjecture_R1_H4_R1
import Mathlib.AlgebraicTopology.FundamentalGroupoid.SimplyConnected
import Mathlib.Analysis.Normed.Module.Connected
import Mathlib.Analysis.Normed.Module.Normalize
import Mathlib.Geometry.Manifold.Instances.Sphere
import Mathlib.Geometry.Manifold.SmoothApprox
import Mathlib.Topology.Homotopy.Affine
import Mathlib.Topology.Homotopy.HomotopyGroup
import Mathlib.Topology.MetricSpace.HausdorffDimension

/-!
# Low homotopy groups of spheres

Support-controlled smooth approximation preserves the cube boundary. A
dimension bound supplies a point omitted by its normalized range, and
stereographic projection then contracts the loop relative to its boundary.
-/


open Set Metric Topology
open scoped unitInterval ContDiff

namespace Poincare.Topology

/-- Smooth approximation can fix the full inverse image of a chosen vector. -/
theorem exists_contDiff_approx_preserving_value
    {V E : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [FiniteDimensional ℝ V] [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : V → E} (hf : Continuous f) (x : E) {ε : ℝ} (hε : 0 < ε) :
    ∃ h : V → E, ContDiff ℝ ∞ h ∧ (∀ z, dist (h z) (f z) < ε) ∧
      ∀ z, f z = x → h z = x := by
  have hf' : Continuous (fun z => f z - x) := hf.sub continuous_const
  obtain ⟨g, hg, hdist, hsupp⟩ := hf'.exists_contDiff_approx (⊤ : ℕ∞)
    (ε := fun _ => ε) continuous_const (fun _ => hε)
  refine ⟨fun z => g z + x, hg.add contDiff_const, ?_, ?_⟩
  · intro z
    calc
      dist (g z + x) (f z) = dist (g z + x) ((f z - x) + x) := by
        rw [sub_add_cancel]
      _ = dist (g z) (f z - x) := dist_add_right _ _ _
      _ < ε := hdist z
  · intro z hz
    have hgz : g z = 0 := by
      by_contra hne
      have hmem := hsupp (show z ∈ Function.support g from hne)
      exact hmem (sub_eq_zero.mpr hz)
    simp only [hgz, zero_add]

/-- A smooth map with a lower-dimensional cone omits a normalized direction. -/
theorem exists_sphere_point_not_normalized_range
    {V E : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [FiniteDimensional ℝ V] [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] (h : V → E) (hh : ContDiff ℝ 1 h)
    (hdim : Module.finrank ℝ V + 1 < Module.finrank ℝ E) :
    ∃ v : sphere (0 : E) 1, ∀ z, NormedSpace.normalize (h z) ≠ (v : E) := by
  let F : ℝ × V → E := fun z => z.1 • h z.2
  have hF : ContDiff ℝ 1 F := contDiff_fst.smul (hh.comp contDiff_snd)
  have hdim' : Module.finrank ℝ (ℝ × V) < Module.finrank ℝ E := by
    simpa only [Module.finrank_prod, Module.finrank_self, Nat.add_comm 1] using hdim
  obtain ⟨w, hw⟩ := (hF.dense_compl_range_of_finrank_lt_finrank hdim').nonempty
  have hwzero : w ≠ 0 := by
    intro hzero
    apply hw
    exact ⟨(0, 0), by simp only [F, zero_smul, hzero]⟩
  refine ⟨⟨NormedSpace.normalize w, ?_⟩, ?_⟩
  · exact mem_sphere_zero_iff_norm.mpr (NormedSpace.norm_normalize hwzero)
  · intro z hz
    apply hw
    refine ⟨(‖w‖ * ‖h z‖⁻¹, z), ?_⟩
    change (‖w‖ * ‖h z‖⁻¹) • h z = w
    calc
      (‖w‖ * ‖h z‖⁻¹) • h z = ‖w‖ • NormedSpace.normalize (h z) := by
        rw [NormedSpace.normalize, mul_smul]
      _ = ‖w‖ • NormedSpace.normalize w := congrArg (fun a => ‖w‖ • a) hz
      _ = w := NormedSpace.norm_smul_normalize w

/-- A sphere loop omitting a point contracts through that point's
stereographic chart, with the entire cube boundary fixed. -/
theorem sphere_genLoop_homotopic_const_of_avoids
    {N E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {x : sphere (0 : E) 1} (v : sphere (0 : E) 1) (hx : x ≠ v)
    (p : GenLoop N (sphere (0 : E) 1) x) (hp : ∀ t, p t ≠ v) :
    GenLoop.Homotopic p GenLoop.const := by
  let e := stereographic (norm_eq_of_mem_sphere v)
  have htarget : e.target = univ := stereographic_target _
  have hxsource : x ∈ e.source := by
    simpa only [e, stereographic_source, mem_compl_iff, mem_singleton_iff] using hx
  have hpsource (t : I^N) : p t ∈ e.source := by
    simpa only [e, stereographic_source, mem_compl_iff, mem_singleton_iff] using hp t
  let f : C(I^N, (ℝ ∙ (v : E))ᗮ) :=
    ⟨fun t => e (p t), e.continuousOn.comp_continuous p.val.continuous hpsource⟩
  let H := ContinuousMap.Homotopy.affine f (ContinuousMap.const _ (e x))
  have hinverse : Continuous e.symm := by
    have he := e.continuousOn_symm
    rw [htarget] at he
    exact continuousOn_univ.mp he
  refine ⟨{
    toFun := fun z => e.symm (H z)
    continuous_toFun := hinverse.comp H.continuous
    map_zero_left := ?_
    map_one_left := ?_
    prop' := ?_ }⟩
  · intro t
    change e.symm (H (0, t)) = p t
    rw [H.apply_zero]
    exact e.left_inv (hpsource t)
  · intro t
    change e.symm (H (1, t)) = x
    rw [H.apply_one]
    exact e.left_inv hxsource
  · intro t a ha
    change e.symm (AffineMap.lineMap (e (p a)) (e x) (t : ℝ)) = p a
    rw [GenLoop.boundary p a ha, AffineMap.lineMap_same_apply]
    exact e.left_inv hxsource

/-- Every positive-dimensional cube loop below the sphere dimension has
an actual nullhomotopy relative to its coordinate boundary. -/
theorem sphere_genLoop_homotopic_const_of_dim_lt
    {N E : Type*} [Fintype N] [Nonempty N]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    (hdim : Fintype.card N + 1 < Module.finrank ℝ E)
    {x : sphere (0 : E) 1} (p : GenLoop N (sphere (0 : E) 1) x) :
    GenLoop.Homotopic p GenLoop.const := by
  let r : (N → ℝ) → I^N := fun z i => projIcc 0 1 zero_le_one (z i)
  have hr : Continuous r :=
    continuous_pi fun i => continuous_projIcc.comp (continuous_apply i)
  have hret (t : I^N) : r (fun i => (t i : ℝ)) = t := by
    funext i
    exact projIcc_val zero_le_one (t i)
  let f : (N → ℝ) → E := fun z => p (r z)
  have hf : Continuous f := continuous_subtype_val.comp (p.val.continuous.comp hr)
  obtain ⟨h, hh, hdist, hfix⟩ :=
    exists_contDiff_approx_preserving_value hf (x : E) (ε := 1 / 2) (by norm_num)
  let hc : C(I^N, E) :=
    ⟨fun t => h (fun i => (t i : ℝ)),
      hh.continuous.comp (continuous_pi fun i =>
        continuous_subtype_val.comp (continuous_apply i))⟩
  have hboundary (t : I^N) (ht : t ∈ Cube.boundary N) : hc t = (x : E) := by
    apply hfix
    change (p (r (fun i => (t i : ℝ))) : E) = (x : E)
    rw [hret, GenLoop.boundary p t ht]
  have hclose (t : I^N) : dist (hc t) (p t : E) < 1 := by
    have hd := hdist (fun i => (t i : ℝ))
    change dist (hc t) (p (r (fun i => (t i : ℝ))) : E) < 1 / 2 at hd
    rw [hret] at hd
    exact hd.trans (by norm_num)
  let pE : C(I^N, E) :=
    ⟨fun t => (p t : E), continuous_subtype_val.comp p.val.continuous⟩
  let H := ContinuousMap.Homotopy.affine pE hc
  have hH (z : unitInterval × I^N) : H z ≠ 0 := by
    have hd : dist (H z) (p z.2 : E) < 1 := by
      change dist (AffineMap.lineMap (p z.2 : E) (hc z.2) (z.1 : ℝ)) (p z.2 : E) < 1
      rw [dist_lineMap_left, Real.norm_of_nonneg z.1.2.1, dist_comm (p z.2 : E) (hc z.2)]
      exact (mul_le_of_le_one_left dist_nonneg z.1.2.2).trans_lt (hclose z.2)
    intro hzero
    simp only [hzero, dist_zero_left, norm_eq_of_mem_sphere, lt_self_iff_false] at hd
  have hhc (t : I^N) : hc t ≠ 0 := by
    simpa only [H.apply_one] using hH (1, t)
  have hunit (t : I^N) : NormedSpace.normalize (hc t) ∈ sphere (0 : E) 1 :=
    mem_sphere_zero_iff_norm.mpr (NormedSpace.norm_normalize (hhc t))
  have hunitH (z : unitInterval × I^N) :
      NormedSpace.normalize (H z) ∈ sphere (0 : E) 1 :=
    mem_sphere_zero_iff_norm.mpr (NormedSpace.norm_normalize (hH z))
  have hcont : Continuous (fun t => NormedSpace.normalize (hc t)) :=
    (hc.continuous.norm.inv₀ (fun t => norm_ne_zero_iff.mpr (hhc t))).smul hc.continuous
  have hcontH : Continuous (fun z => NormedSpace.normalize (H z)) :=
    (H.continuous.norm.inv₀ (fun z => norm_ne_zero_iff.mpr (hH z))).smul H.continuous
  let q : GenLoop N (sphere (0 : E) 1) x :=
    ⟨⟨fun t => ⟨NormedSpace.normalize (hc t), hunit t⟩, hcont.subtype_mk hunit⟩, by
      intro t ht
      apply Subtype.ext
      change NormedSpace.normalize (hc t) = (x : E)
      rw [hboundary t ht]
      exact NormedSpace.normalize_eq_self_of_norm_eq_one (norm_eq_of_mem_sphere x)⟩
  have hpq : GenLoop.Homotopic p q := by
    refine ⟨{
      toFun := fun z => ⟨NormedSpace.normalize (H z), hunitH z⟩
      continuous_toFun := hcontH.subtype_mk hunitH
      map_zero_left := ?_
      map_one_left := ?_
      prop' := ?_ }⟩
    · intro t
      apply Subtype.ext
      change NormedSpace.normalize (H (0, t)) = (p t : E)
      rw [H.apply_zero]
      exact NormedSpace.normalize_eq_self_of_norm_eq_one (norm_eq_of_mem_sphere (p t))
    · intro t
      apply Subtype.ext
      change NormedSpace.normalize (H (1, t)) = NormedSpace.normalize (hc t)
      rw [H.apply_one]
    · intro t a ha
      apply Subtype.ext
      change NormedSpace.normalize (AffineMap.lineMap (p a : E) (hc a) (t : ℝ)) = (p a : E)
      rw [hboundary a ha, GenLoop.boundary p a ha, AffineMap.lineMap_same_apply]
      exact NormedSpace.normalize_eq_self_of_norm_eq_one (norm_eq_of_mem_sphere x)
  obtain ⟨v, hv⟩ := exists_sphere_point_not_normalized_range h (hh.of_le (by simp))
    (by simpa only [Module.finrank_fintype_fun_eq_card] using hdim)
  have havoid (t : I^N) : q t ≠ v := by
    intro heq
    exact hv (fun i => (t i : ℝ)) (congrArg Subtype.val heq)
  have hx : x ≠ v := by
    intro heq
    apply havoid (fun _ => 0)
    exact (GenLoop.boundary q _
      ⟨Classical.choice (inferInstance : Nonempty N), Or.inl rfl⟩).trans heq
  exact hpq.trans (sphere_genLoop_homotopic_const_of_avoids v hx q havoid)

/-- Positive sphere homotopy groups below the sphere dimension are trivial. -/
theorem sphere_homotopyGroup_subsingleton_of_dim_lt
    {N E : Type*} [Fintype N] [Nonempty N]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    (hdim : Fintype.card N + 1 < Module.finrank ℝ E)
    (x : sphere (0 : E) 1) :
    Subsingleton (HomotopyGroup N (sphere (0 : E) 1) x) := by
  refine ⟨fun a b => Quotient.inductionOn₂ a b ?_⟩
  intro p q
  exact Quotient.sound ((sphere_genLoop_homotopic_const_of_dim_lt hdim p).trans
    (sphere_genLoop_homotopic_const_of_dim_lt hdim q).symm)

/-- A finite-dimensional real unit sphere of dimension at least two is
simply connected in the pinned fundamental-groupoid API. -/
theorem sphere_simplyConnectedSpace_of_two_lt_finrank
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] (hdim : 2 < Module.finrank ℝ E) :
    SimplyConnectedSpace (sphere (0 : E) 1) := by
  apply simply_connected_iff_loops_nullhomotopic.mpr
  refine ⟨?_, ?_⟩
  · exact isPathConnected_iff_pathConnectedSpace.mp (isPathConnected_sphere
      (Module.one_lt_rank_of_one_lt_finrank (by omega)) (0 : E) zero_le_one)
  · intro x p
    let : Subsingleton (HomotopyGroup.Pi 1 (sphere (0 : E) 1) x) :=
      sphere_homotopyGroup_subsingleton_of_dim_lt (N := Fin 1)
        (by simpa only [Fintype.card_fin] using hdim) x
    let e := HomotopyGroup.pi1EquivFundamentalGroup (X := sphere (0 : E) 1) (x := x)
    have heq : (⟦p⟧ : FundamentalGroup (sphere (0 : E) 1) x) = ⟦Path.refl x⟧ :=
      e.symm.injective (Subsingleton.elim _ _)
    exact Quotient.exact heq

end Poincare.Topology

theorem OMA.solution : OMA.R_PoincareConjecture_poincare_conjecture_R1_H4_R1.H1 := by
  exact Poincare.Topology.sphere_simplyConnectedSpace_of_two_lt_finrank (by
    rw [finrank_euclideanSpace_fin]
    norm_num)

/-!
The sphere-connectivity development above is adapted from the FrenzyMath
Poincare-Conjecture project at 432c38f2aa5a30efb13871292d17b4a3309a496a,
PoincareConjecture/PoincareLib/Topology/Homotopy/Sphere/SphereConnectivity.lean.
The source's global autoImplicit setting was removed, and the result was applied
to the exact registry step. See the original project for proof attribution.

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


Apache License 2.0


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
