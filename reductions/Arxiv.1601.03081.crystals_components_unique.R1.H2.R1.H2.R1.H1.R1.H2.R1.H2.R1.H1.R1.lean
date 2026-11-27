import OMAReductions.R_Arxiv_1601_03081_crystals_components_unique_R1_H2_R1_H2_R1_H1_R1_H2_R1_H2_R1

/-! A square congruence for the proper shared-sum divisor with unit cofactor. -/

namespace OMA.R_Arxiv_1601_03081_crystals_components_unique_R1_H2_R1_H2_R1_H1_R1_H2_R1_H2_R1_H1_R1

private theorem divisor_screen {y D q : ℕ} (hy : 0 < y)
    (hq : 5 ≤ q) (hdiv : D ∣ y^2-1) (hfloor : q = D/y+2)
    (hsquare : (q-2)^2 < y) (hqbound : 2*q ≤ y+3)
    (hw : (q-3)*(y*(q-1)-D) < y)
    (hlower : D+y < y*q) :
    let w := y*(q-1)-D
    (D=(q-1)*(y-1) ∧ (q-1) ∣ (y+1)) ∨
      ((q-1)^2+D ≤ w^2 ∧ (q-3)^2*(q-2)<y) := by
  let w := y*(q-1)-D
  let Q := q-1
  let V := q-2
  let U := q-3
  have hyQ : y*Q = y*q-y := by
    dsimp [Q]
    rw [Nat.mul_sub, Nat.mul_one]
  have hwEq : w+D = y*Q := by
    have hlt : D < y*Q := by omega
    dsimp [w,Q] at *
    omega
  have hV : V*y ≤ D := by
    have hd := Nat.div_mul_le_self D y
    have hv : V = D/y := by dsimp [V]; omega
    rwa [← hv] at hd
  have hQsmall : Q^2 < D := by
    have hvu : Q = V+1 := by dsimp [Q,V]; omega
    have hv3 : 3 ≤ V := by dsimp [V]; omega
    have h3 := Nat.mul_le_mul_right y hv3
    have hqb : 2*V+1 ≤ y := by dsimp [V]; omega
    change V^2 < y at hsquare
    have hsq := congrArg (fun n : ℕ => n^2) hvu
    nlinarith only [hsq, hsquare, h3, hV, hqb, Nat.zero_le V]
  have hc : (w : ZMod D)^2 = (Q : ZMod D)^2 := by
    have hDy : (y : ZMod D)^2 = 1 := by
      obtain ⟨m, hm⟩ := hdiv
      have he : y^2 = D*m+1 := by
        have hp : 0 < y^2 := by positivity
        omega
      have hm' := congrArg (fun n : ℕ => (n : ZMod D)) he
      simpa using hm'
    have he := congrArg (fun n : ℕ => (n : ZMod D)) hwEq
    push_cast at he
    have he' : (w : ZMod D) = (y : ZMod D)*(Q : ZMod D) := by simpa using he
    rw [he', mul_pow, hDy, one_mul]
  have hm : w^2 ≡ Q^2 [MOD D] := by
    apply (ZMod.natCast_eq_natCast_iff _ _ _).1
    simpa only [Nat.cast_pow] using hc
  by_cases heq : w=Q
  · left
    have hDeq : D = Q*(y-1) := by
      rw [Nat.mul_sub, Nat.mul_one]
      rw [heq, mul_comm y Q] at hwEq
      omega
    have he : y^2-1 = (y-1)*(y+1) := by
      have hh : 1 ≤ y := by omega
      rw [Nat.sub_mul, one_mul]
      have hsum : y*(y+1) = y^2+y := by ring
      omega
    have hy2 : 1 < y := by
      change V^2 < y at hsquare
      have : 3 ≤ V := by dsimp [V]; omega
      nlinarith
    refine ⟨hDeq, ?_⟩
    obtain ⟨m, hDme⟩ := hdiv
    have heq' : (y-1)*(y+1) = (y-1)*(Q*m) := by
      rw [he, hDeq] at hDme
      nlinarith only [hDme]
    exact ⟨m, Nat.eq_of_mul_eq_mul_left (by omega) heq'⟩
  · right
    have hlt : Q^2 < w^2 := by
      by_contra! h
      have hwsmall : w^2 < D := h.trans_lt hQsmall
      change w^2%D = Q^2%D at hm
      rw [Nat.mod_eq_of_lt hwsmall, Nat.mod_eq_of_lt hQsmall] at hm
      exact heq (by nlinarith)
    have hd : D ∣ w^2-Q^2 := (Nat.modEq_iff_dvd' hlt.le).1 hm.symm
    have hb := Nat.le_of_dvd (Nat.sub_pos_of_lt hlt) hd
    have hWbig : Q^2+D ≤ w^2 := by omega
    change U*w < y at hw
    have hUw : (U*w)^2 < y^2 := Nat.pow_lt_pow_left hw (by decide)
    have hDlow : V*y ≤ w^2 := hV.trans (by omega)
    have hmuls := Nat.mul_le_mul_left (U^2) hDlow
    have hv : (U^2*V)*y < y*y := by
      nlinarith only [hmuls,hUw]
    exact ⟨hWbig, Nat.lt_of_mul_lt_mul_right hv⟩

/-- The small square residue is forced to equal the distinguished root. -/
def H1 : Prop :=
  ∀ g y z d q : ℕ,
    1 < g → 33 ≤ y → Odd g → Odd y → Odd z → g*y ≤ z →
    (g+1)*(y*z+1) ∣ (g+y*z)^2 →
    0 < d → d < 2*(y-1) → d % 2 = 0 →
    (g+1 ∣ ((y+1)*(d+(y-1)*y*(1+2*y)))^2) →
    (g*y+1 ∣ ((y+1)*(d+(y-1)*(y+2)))^2) →
    5 ≤ q → (g*y+z)^2 = q*((g*y+1)*(z+1)) →
    g.Coprime y → g.Coprime z → y.Coprime z →
    (g+y*z ∣ g*y*z+1) → (g*y+z ∣ g*y*z+1) →
    let D := Nat.gcd (g+y*z) (g*y+z)
    D ∣ y^2-1 → D < y^2-1 →
    (g+y*z).lcm (g*y+z) = g*y*z+1 →
    z+g*y < g*D → D+y < y*q → y*q < D+2*y → q = D/y+2 → (q-3)*(y*(q-1)-D) < y →
    q ≤ (y^2-1)/D+2 → (q-2)^2 < y → 2*q ≤ y+3 → D = (q-1)*(y-1) → (q-1) ∣ (y+1) → False

/-- The remaining root gives a cubic lower bound on the shared factor. -/
def H2 : Prop :=
  ∀ g y z d q : ℕ,
    1 < g → 33 ≤ y → Odd g → Odd y → Odd z → g*y ≤ z →
    (g+1)*(y*z+1) ∣ (g+y*z)^2 →
    0 < d → d < 2*(y-1) → d % 2 = 0 →
    (g+1 ∣ ((y+1)*(d+(y-1)*y*(1+2*y)))^2) →
    (g*y+1 ∣ ((y+1)*(d+(y-1)*(y+2)))^2) →
    5 ≤ q → (g*y+z)^2 = q*((g*y+1)*(z+1)) →
    g.Coprime y → g.Coprime z → y.Coprime z →
    (g+y*z ∣ g*y*z+1) → (g*y+z ∣ g*y*z+1) →
    let D := Nat.gcd (g+y*z) (g*y+z)
    D ∣ y^2-1 → D < y^2-1 →
    (g+y*z).lcm (g*y+z) = g*y*z+1 →
    z+g*y < g*D → D+y < y*q → y*q < D+2*y → q = D/y+2 → (q-3)*(y*(q-1)-D) < y →
    q ≤ (y^2-1)/D+2 → (q-2)^2 < y → 2*q ≤ y+3 → (q-1)^2+D ≤ (y*(q-1)-D)^2 → (q-3)^2*(q-2)<y → False

theorem main : H1 → H2 → OMA.R_Arxiv_1601_03081_crystals_components_unique_R1_H2_R1_H2_R1_H1_R1_H2_R1_H2_R1.H1 := by
  intro hEq hLarge g y z d q hg hy hgo hyo hzo horder hcr hd hdb hde hdc hdc'
    hq heq hgy hgz hyz hfirst hsecond
  let D := Nat.gcd (g+y*z) (g*y+z)
  change D ∣ y^2-1 → D < y^2-1 → (g+y*z).lcm (g*y+z) = g*y*z+1 →
    z+g*y < g*D → D+y < y*q → y*q < D+2*y → q = D/y+2 →
    (q-3)*(y*(q-1)-D) < y → q ≤ (y^2-1)/D+2 → (q-2)^2 < y → 2*q ≤ y+3 → False
  intro hDd hDl hlcm hz hlow hu hfloor hw hquot hsq hb
  rcases divisor_screen (by omega) hq hDd hfloor hsq hb hw hlow with h | h
  · exact hEq g y z d q hg hy hgo hyo hzo horder hcr hd hdb hde hdc hdc'
      hq heq hgy hgz hyz hfirst hsecond hDd hDl hlcm hz hlow hu hfloor hw hquot hsq hb h.1 h.2
  · exact hLarge g y z d q hg hy hgo hyo hzo horder hcr hd hdb hde hdc hdc'
      hq heq hgy hgz hyz hfirst hsecond hDd hDl hlcm hz hlow hu hfloor hw hquot hsq hb h.1 h.2

end OMA.R_Arxiv_1601_03081_crystals_components_unique_R1_H2_R1_H2_R1_H1_R1_H2_R1_H2_R1_H1_R1
