import OMAReductions.R_Arxiv_1601_03081_crystals_components_unique_R2

/-! A crystal has unique components when its successor has at most one distinct odd prime divisor. -/

namespace CrystalVieta

theorem quotient_residues {q : ℕ} (hq : 2 ≤ q) :
    ∀ u v : ℕ, 0 < u → u ≤ v → (u+v-1)^2 = q*u*v →
      (u % q = 1 ∧ v % q = 0) ∨ (u % q = 0 ∧ v % q = 1) := by
  intro u
  induction u using Nat.strong_induction_on with
  | h u ih =>
    intro v hu huv heq
    by_cases hu1 : u = 1
    · subst u
      have hvPos : 0 < v := by omega
      have he : v*v = q*v := by simpa [pow_two] using heq
      have hvq : v = q := Nat.eq_of_mul_eq_mul_right hvPos (by simpa [Nat.mul_comm] using he)
      subst v
      left
      constructor
      · exact Nat.mod_eq_of_lt (by omega)
      · simp
    · have hu2 : 2 ≤ u := by omega
      let w : ℤ := ((q : ℤ)-2)*u+2-v
      have huvpos : 1 ≤ u+v := by omega
      have heqZ : ((u : ℤ)+(v : ℤ)-1)^2 = (q : ℤ)*u*v := by
        have hc := congrArg (fun n : ℕ => (n : ℤ)) heq
        simpa only [Nat.cast_pow, Nat.cast_sub huvpos, Nat.cast_add, Nat.cast_one,
          Nat.cast_mul] using hc
      have hwprod : (v : ℤ)*w = ((u : ℤ)-1)^2 := by
        dsimp [w]
        nlinarith [heqZ]
      have hvZ : 0 < (v : ℤ) := by exact_mod_cast (show 0 < v by omega)
      have huZ : 2 ≤ (u : ℤ) := by exact_mod_cast hu2
      have hwpos : 0 < w := by nlinarith [hwprod]
      have hwlt : w < u := by
        by_contra h
        have huw : (u : ℤ) ≤ w := by omega
        have huuv : (u : ℤ)*(u : ℤ) ≤ (u : ℤ)*(v : ℤ) :=
          mul_le_mul_of_nonneg_left (by exact_mod_cast huv) (by positivity)
        have huwprod : (u : ℤ)*(v : ℤ) ≤ w*(v : ℤ) :=
          mul_le_mul_of_nonneg_right huw (by positivity)
        nlinarith [hwprod]
      have hwCast : (w.toNat : ℤ) = w := Int.toNat_of_nonneg (le_of_lt hwpos)
      have hwNatPos : 0 < w.toNat := by
        have hwNatPosZ : (0 : ℤ) < (w.toNat : ℤ) := by rw [hwCast]; exact hwpos
        exact_mod_cast hwNatPosZ
      have hwNatLt : w.toNat < u := by
        have hwNatLtZ : (w.toNat : ℤ) < u := by rw [hwCast]; exact hwlt
        exact_mod_cast hwNatLtZ
      have hnewZ : (w+(u : ℤ)-1)^2 = (q : ℤ)*w*u := by
        dsimp [w]
        nlinarith [heqZ]
      have hNatCast : ((w.toNat+u-1 : ℕ) : ℤ) = (w.toNat : ℤ)+(u : ℤ)-1 := by
        rw [Nat.cast_sub (by omega : 1 ≤ w.toNat+u)]
        simp only [Nat.cast_add, Nat.cast_one]
      have hnewZ' : ((w.toNat+u-1 : ℕ) : ℤ)^2 =
          (q : ℤ)*(w.toNat : ℤ)*u := by
        calc
          _ = ((w.toNat : ℤ)+(u : ℤ)-1)^2 := by rw [hNatCast]
          _ = (w+(u : ℤ)-1)^2 := by rw [hwCast]
          _ = (q : ℤ)*w*u := hnewZ
          _ = (q : ℤ)*(w.toNat : ℤ)*u := by nlinarith [hwCast]
      have hnew : (w.toNat+u-1)^2 = q*w.toNat*u := by exact_mod_cast hnewZ'
      have hres := ih w.toNat hwNatLt u hwNatPos (Nat.le_of_lt hwNatLt) hnew
      have hsum : (w.toNat : ℕ)+v+2*u = q*u+2 := by
        dsimp [w] at hwCast
        have hwCastN : (w.toNat : ℤ) = ((q : ℤ)-2)*u+2-v := hwCast
        have hwCastN' : ((w.toNat : ℕ) : ℤ) + v + 2*u = (q : ℤ)*u+2 := by
          nlinarith [hwCastN]
        exact_mod_cast hwCastN'
      have hmod0 : (w.toNat+v+2*u) % q = 2 % q := by
        rw [hsum]
        simp [Nat.add_mod]
      have hmod : (((w.toNat % q)+(v % q)+2*(u % q)) % q) = 2 % q := by
        simpa [Nat.add_mod] using hmod0
      rcases hres with ⟨hwu, huv0⟩ | ⟨hwu0, huv1⟩
      · right
        have hv1 : v % q = 1 := by
          rw [hwu, huv0] at hmod
          simp only [Nat.add_zero, Nat.mul_zero] at hmod
          have hxlt : v % q < q := Nat.mod_lt _ (by omega)
          by_cases hq2 : q = 2
          · subst q
            norm_num at hmod
            omega
          · have hq3 : 3 ≤ q := by omega
            have hq2mod : 2 % q = 2 := Nat.mod_eq_of_lt (by omega)
            rw [hq2mod] at hmod
            have hmod1 : (1+v%q)%q = 2 := hmod
            by_cases hlt : 1+v%q < q
            · rw [Nat.mod_eq_of_lt hlt] at hmod1
              omega
            · have hx : 1+v%q=q := by omega
              rw [hx, Nat.mod_self] at hmod1
              omega
        exact ⟨huv0, hv1⟩
      · left
        have hv0 : v % q = 0 := by
          rw [hwu0, huv1] at hmod
          simp only [Nat.zero_add, Nat.mul_one] at hmod
          have hxlt : v % q < q := Nat.mod_lt _ (by omega)
          by_cases hq2 : q = 2
          · subst q
            norm_num at hmod
            omega
          · have hq3 : 3 ≤ q := by omega
            have hq2mod : 2 % q = 2 := Nat.mod_eq_of_lt (by omega)
            rw [hq2mod] at hmod
            have hmod1 : (v%q+2)%q = 2 := hmod
            by_cases hlt : v%q+2 < q
            · rw [Nat.mod_eq_of_lt hlt] at hmod1
              omega
            · have hqle : q ≤ v%q+2 := by omega
              have hqtop : v%q+2 ≤ q+1 := by omega
              by_cases heq : v%q+2=q
              · rw [heq, Nat.mod_self] at hmod1
                omega
              · have heq' : v%q+2=q+1 := by omega
                rw [heq'] at hmod1
                have hqplus : (q+1)%q=1 := by
                  rw [Nat.add_comm, Nat.add_mod_right 1 q]
                  exact Nat.mod_eq_of_lt (by omega)
                rw [hqplus] at hmod1
                omega
        exact ⟨huv1, hv0⟩

theorem quotient_sum_dvd {q u v : ℕ} (hq : 2 ≤ q) (hu : 0 < u)
    (huv : u ≤ v) (heq : (u+v-1)^2 = q*u*v) : q ∣ u+v-1 := by
  rcases quotient_residues hq u v hu huv heq with ⟨hu1,hv0⟩ | ⟨hu0,hv1⟩
  · have hsum : (u+v)%q = 1 := by
      rw [Nat.add_mod, hu1, hv0]
      exact Nat.mod_eq_of_lt (by omega)
    have hdecomp := Nat.mod_add_div (u+v) q
    rw [hsum] at hdecomp
    refine ⟨(u+v)/q, ?_⟩
    omega
  · have hsum : (u+v)%q = 1 := by
      rw [Nat.add_mod, hu0, hv1]
      exact Nat.mod_eq_of_lt (by omega)
    have hdecomp := Nat.mod_add_div (u+v) q
    rw [hsum] at hdecomp
    refine ⟨(u+v)/q, ?_⟩
    omega

theorem odd_crystal_factor {a b q : ℕ} (ha : Odd a) (hb : Odd b)
    (ha1 : 1 < a) (hb1 : 1 < b) (hq : 2 ≤ q)
    (heq : (a+b)^2 = q*((a+1)*(b+1))) :
    ∃ r : ℕ, Odd r ∧ (a+b)*r = a*b+1 ∧ r+1 ∣ a+b := by
  obtain ⟨x,hax⟩ := ha
  obtain ⟨y,hby⟩ := hb
  let u := x+1
  let v := y+1
  have hau : a+1=2*u := by dsimp [u]; omega
  have hbv : b+1=2*v := by dsimp [v]; omega
  have hu2 : 2 ≤ u := by dsimp [u]; omega
  have hv2 : 2 ≤ v := by dsimp [v]; omega
  have hsum : a+b=2*(u+v-1) := by omega
  have hquot : (u+v-1)^2=q*u*v := by
    have h := heq
    rw [hsum,hau,hbv] at h
    nlinarith [h]
  have hdiv : q ∣ u+v-1 := by
    by_cases huv : u ≤ v
    · exact quotient_sum_dvd hq (by omega) huv hquot
    · have hvu : v ≤ u := by omega
      have hquot' : (v+u-1)^2=q*v*u := by
        simpa [Nat.add_comm, Nat.mul_comm, Nat.mul_left_comm] using hquot
      have hdiv' := quotient_sum_dvd hq (by omega) hvu hquot'
      simpa [Nat.add_comm] using hdiv'
  obtain ⟨k,hk⟩ := hdiv
  have hn : u+v=q*k+1 := by omega
  have hquot' : (q*k)^2=q*u*v := by rw [← hk]; exact hquot
  have hcancel : q*(q*k^2)=q*(u*v) := by
    calc
      q*(q*k^2)=(q*k)^2 := by ring
      _=q*u*v := hquot'
      _=q*(u*v) := by ring
  have hqPos : 0 < q := by omega
  have huvprod : u*v=q*k^2 := (Nat.eq_of_mul_eq_mul_left hqPos hcancel).symm
  have hkpos : 1 ≤ k := by
    by_contra h
    have hk0 : k=0 := by omega
    rw [hk0] at hk
    omega
  let r := 2*k-1
  have hrplus : r+1=2*k := by dsimp [r]; omega
  have hrodd : Odd r := by
    refine ⟨k-1, ?_⟩
    dsimp [r]
    omega
  have hsum2 : a+b=2*q*k := by rw [hsum,hk]; ring
  have habprod : a*b+1=(a+b)*r := by
    dsimp [r]
    nlinarith [huvprod, hn, hau, hbv, hsum2]
  refine ⟨r, hrodd, habprod.symm, ?_⟩
  refine ⟨q, ?_⟩
  rw [hrplus, hsum2]
  ring

end CrystalVieta

namespace CrystalPrimePowerNeighbor

theorem odd_square_mod_four {x : ℕ} (hx : Odd x) : x^2 % 4 = 1 := by
  obtain ⟨k,rfl⟩ := hx
  rw [show (2*k+1)^2 = 1+(k*k+k)*4 by ring, Nat.add_mul_mod_self_right]

theorem odd_square_mod_twice_succ {x : ℕ} (hx : Odd x) :
    x^2 ≡ 1 [MOD 2*(x+1)] := by
  obtain ⟨k,rfl⟩ := hx
  unfold Nat.ModEq
  rw [show (2*k+1)^2 = 1+k*(2*((2*k+1)+1)) by ring, Nat.add_mul_mod_self_right]

/-- If an odd base at least three has a positive power whose successor is
a divisor of a power of two, that exponent is one. -/
theorem exponent_eq_one_of_successor_dvd_two_power {x i A : ℕ}
    (hx : Odd x) (hx3 : 3 ≤ x) (hi : 0 < i) (hd : x^i+1 ∣ 2^A) : i = 1 := by
  obtain ⟨a,_,ha⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hd
  have hpow : x ≤ x^i := by
    simpa only [pow_one] using
      Nat.pow_le_pow_right (show 0 < x by omega) (show 1 ≤ i from hi)
  rcases Nat.even_or_odd i with heven | hodd
  · obtain ⟨k,hk⟩ := heven
    have he : i = k*2 := by omega
    have hmod : (x^i+1)%4 = 2 := by
      rw [he, pow_mul, Nat.add_mod, odd_square_mod_four (hx.pow : Odd (x^k))]
    have ha2 : 2 ≤ a := by
      by_contra! ht
      interval_cases a <;> norm_num at ha <;> omega
    have hfour : 4 ∣ x^i+1 := by
      rw [ha]
      exact pow_dvd_pow 2 ha2
    have hz := Nat.dvd_iff_mod_eq_zero.mp hfour
    omega
  · by_contra hi1
    have hgt : x < x^i := by
      have hstep : x^2 ≤ x^i :=
        Nat.pow_le_pow_right (by omega) (show 2 ≤ i by omega)
      have hsq : x < x^2 := by nlinarith only [hx3]
      exact hsq.trans_le hstep
    have hsd : x+1 ∣ 2^a := by
      rw [← ha]
      simpa using hodd.nat_add_dvd_pow_add_pow (x := x) (y := 1)
    obtain ⟨b,hba,hb⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hsd
    have hlt : b < a := by
      apply lt_of_le_of_ne hba
      intro he
      rw [he, ← ha] at hb
      omega
    have hd2 : 2*(x+1) ∣ x^i+1 := by
      rw [hb, ha, ← pow_succ']
      exact pow_dvd_pow 2 (by omega)
    obtain ⟨k,hk⟩ := hodd
    have he : i = 2*k+1 := by omega
    have hoddpow : x^i ≡ x [MOD 2*(x+1)] := by
      rw [he, pow_add, pow_mul, pow_one]
      simpa only [one_pow, one_mul] using
        ((odd_square_mod_twice_succ hx).pow k).mul_right x
    have hmod := hoddpow.add_right 1
    have hbad := hmod.symm.trans (Nat.modEq_zero_iff_dvd.mpr hd2)
    unfold Nat.ModEq at hbad
    rw [Nat.mod_eq_of_lt (show x+1 < 2*(x+1) by omega), Nat.zero_mod] at hbad
    omega

/-- An odd cofactor larger than one whose successor divides its complementary
factor is uniquely determined when the product has only one odd prime. -/
theorem cofactor_eq_prime {r s ell A B : ℕ}
    (hp : ell.Prime) (hpodd : Odd ell) (hr : 1 < r) (hrodd : Odd r)
    (hprod : s*r = 2^A*ell^B) (hds : r+1 ∣ s) : r = ell := by
  have hrprod : r ∣ 2^A*ell^B := by
    rw [← hprod]
    exact dvd_mul_left _ _
  have hcp : r.Coprime (2^A) :=
    ((Nat.prime_two.coprime_iff_not_dvd).mpr hrodd.not_two_dvd_nat).symm.pow_right A
  obtain ⟨i,_,hri⟩ := (Nat.dvd_prime_pow hp).mp (hcp.dvd_of_dvd_mul_left hrprod)
  have hi : 0 < i := by
    by_contra! hn
    have hz : i = 0 := by omega
    simp [hz] at hri
    omega
  have hpdr : ell ∣ r := by
    rw [hri]
    simpa only [pow_one] using (pow_dvd_pow ell (show 1 ≤ i from hi))
  have hnpr : ¬ ell ∣ r+1 := by
    intro hd
    exact hp.not_dvd_one ((Nat.dvd_add_iff_right hpdr).mpr hd)
  have hds' : r+1 ∣ 2^A*ell^B := by
    rw [← hprod]
    exact dvd_mul_of_dvd_left hds _
  have hcp' : (r+1).Coprime (ell^B) :=
    ((hp.coprime_iff_not_dvd).mpr hnpr).symm.pow_right B
  have htwo := hcp'.dvd_of_dvd_mul_right hds'
  rw [hri] at htwo
  have hell : 3 ≤ ell := by
    have h2 := hp.two_le
    obtain ⟨k,hk⟩ := hpodd
    omega
  have hi1 := exponent_eq_one_of_successor_dvd_two_power hpodd hell hi htwo
  simpa only [hi1,pow_one] using hri

/-- An unordered pair of natural factors is determined by its sum and product. -/
theorem factor_pairs_eq_of_sum_prod {a b c d : ℕ}
    (hs : a+b = c+d) (hp : a*b = c*d) :
    ({a,b} : Finset ℕ) = {c,d} := by
  have hsz : (a : ℤ)+b = c+d := by exact_mod_cast hs
  have hpz : (a : ℤ)*b = c*d := by exact_mod_cast hp
  have hzero : ((a : ℤ)-c)*((a : ℤ)-d) = 0 := by
    linear_combination (a : ℤ)*hsz - hpz
  rcases mul_eq_zero.mp hzero with ha | hb
  · have hez : (a : ℤ) = c := sub_eq_zero.mp ha
    have he : a = c := by exact_mod_cast hez
    have hb : b = d := by omega
    rw [he,hb]
  · have hez : (a : ℤ) = d := sub_eq_zero.mp hb
    have he : a = d := by exact_mod_cast hez
    have hb : b = c := by omega
    rw [he,hb,Finset.pair_comm]

theorem cofactor_gt_one {a b r : ℕ} (ha : 1 < a) (hb : 1 < b)
    (hs : (a+b)*r = a*b+1) : 1 < r := by
  have hz : 0 < ((a : ℤ)-1)*((b : ℤ)-1) := mul_pos
    (sub_pos.mpr (by exact_mod_cast ha))
    (sub_pos.mpr (by exact_mod_cast hb))
  have hlt : a+b < a*b+1 := by
    exact_mod_cast (show (a : ℤ)+b < (a : ℤ)*b+1 by nlinarith only [hz])
  by_contra! hr
  have hm := Nat.mul_le_mul_left (a+b) hr
  simp only [mul_one, hs] at hm
  omega

/-- The two pairs are equal when their common product plus one has at most one
odd prime factor and both sum cofactors satisfy the crystal constraints. -/
theorem unique_of_neighbor_prime_power {a b c d ell A B r t : ℕ}
    (ha : 1 < a) (hb : 1 < b)
    (hc : 1 < c) (hd : 1 < d)
    (hp : ell.Prime) (hpo : Odd ell)
    (hprod : a*b = c*d) (hN : a*b+1 = 2^A*ell^B)
    (hr : Odd r) (ht : Odd t)
    (hrmul : (a+b)*r = a*b+1) (htmul : (c+d)*t = c*d+1)
    (hrdiv : r+1 ∣ a+b) (htdiv : t+1 ∣ c+d) :
    ({a,b} : Finset ℕ) = {c,d} := by
  have hrp : r = ell := cofactor_eq_prime hp hpo (cofactor_gt_one ha hb hrmul) hr
    (hrmul.trans hN) hrdiv
  have htp : t = ell := cofactor_eq_prime hp hpo (cofactor_gt_one hc hd htmul) ht
    (htmul.trans (by simpa only [hprod] using hN)) htdiv
  have heq : (a+b)*ell = (c+d)*ell := by
    calc
      _ = (a+b)*r := by rw [hrp]
      _ = a*b+1 := hrmul
      _ = c*d+1 := by rw [hprod]
      _ = (c+d)*t := htmul.symm
      _ = _ := by rw [htp]
  exact factor_pairs_eq_of_sum_prod (Nat.mul_right_cancel hp.pos heq) hprod


end CrystalPrimePowerNeighbor

namespace CrystalPrimePowerNeighbor

open Arxiv.«1601.03081»

theorem crystal_quotient_ge_two {a b q : ℕ} (ha : 1 < a) (hb : 1 < b)
    (heq : (a+b)^2 = q*((a+1)*(b+1))) : 2 ≤ q := by
  have hlt : (a+1)*(b+1) < (a+b)^2 := by
    calc
      _ < (a+b)*(b+1) := Nat.mul_lt_mul_of_pos_right (by omega) (by omega)
      _ ≤ (a+b)*(a+b) := Nat.mul_le_mul_left _ (by omega)
      _ = _ := by rw [pow_two]
  by_contra! hq
  have hle := Nat.mul_le_mul_right ((a+1)*(b+1)) (show q ≤ 1 by omega)
  simp only [one_mul, ← heq] at hle
  omega

theorem crystal_unique_of_neighbor_prime_power
    (hC : ∀ {a b q : ℕ}, Odd a → Odd b → 1 < a → 1 < b → 2 ≤ q →
      (a+b)^2 = q*((a+1)*(b+1)) →
      ∃ r : ℕ, Odd r ∧ (a+b)*r = a*b+1 ∧ r+1 ∣ a+b)
    (n a b c d : ℕ) (hab : IsCrystalWithComponents n a b)
    (hcd : IsCrystalWithComponents n c d)
    (hn : ∃ p A B : ℕ, p.Prime ∧ Odd p ∧ n+1 = 2^A*p^B) :
    ({a,b} : Finset ℕ) = {c,d} := by
  obtain ⟨p,A,B,hp,hpo,hn⟩ := hn
  obtain ⟨ho,ha,hb,habn,habq⟩ := (isCrystalWithComponents_iff_sum_sq_dvd n a b).mp hab
  obtain ⟨_,hc,hd,hcdn,hcdq⟩ := (isCrystalWithComponents_iff_sum_sq_dvd n c d).mp hcd
  obtain ⟨q,hq⟩ := habq
  obtain ⟨t,ht⟩ := hcdq
  have habodd : Odd (a*b) := habn ▸ ho
  have hcdodd : Odd (c*d) := hcdn ▸ ho
  have hqab : (a+b)^2 = q*((a+1)*(b+1)) := by simpa only [Nat.mul_comm] using hq
  have htcd : (c+d)^2 = t*((c+1)*(d+1)) := by simpa only [Nat.mul_comm] using ht
  obtain ⟨r,hr,hrval,hrdvd⟩ :=
    hC (Nat.Odd.of_mul_left habodd) (Nat.Odd.of_mul_right habodd) ha hb
      (crystal_quotient_ge_two ha hb hqab) hqab
  obtain ⟨s,hs,hsval,hsdvd⟩ :=
    hC (Nat.Odd.of_mul_left hcdodd) (Nat.Odd.of_mul_right hcdodd) hc hd
      (crystal_quotient_ge_two hc hd htcd) htcd
  exact unique_of_neighbor_prime_power ha hb hc hd hp hpo
    (habn.symm.trans hcdn) (by simpa only [habn] using hn)
    hr hs hrval hsval hrdvd hsdvd


end CrystalPrimePowerNeighbor

theorem OMA.solution : OMA.R_Arxiv_1601_03081_crystals_components_unique_R2.H1 := by
  exact CrystalPrimePowerNeighbor.crystal_unique_of_neighbor_prime_power CrystalVieta.odd_crystal_factor
