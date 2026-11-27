import OMAStatements.S_oeis_a072031

namespace LambertCounts

open Finset

def Solutions (n : ℕ) :=
  {t : ℕ × ℕ × ℕ × ℕ //
    0 < t.1 ∧ 0 < t.2.1 ∧ 0 < t.2.2.1 ∧ 0 < t.2.2.2 ∧
      t.1 * t.2.1 + t.2.2.1 * t.2.2.2 = n}

abbrev Splits (n : ℕ) :=
  Σ k : ↥(Icc 1 n), ↥(Nat.divisors k.1) × ↥(Nat.divisors (n - k.1))

private theorem splits_ext {n : ℕ} {x y : Splits n}
    (h₀ : x.1.val = y.1.val) (h₁ : x.2.1.val = y.2.1.val)
    (h₂ : x.2.2.val = y.2.2.val) : x = y := by
  rcases x with ⟨⟨k, hk⟩, ⟨a, ha⟩, ⟨c, hc⟩⟩
  rcases y with ⟨⟨k', hk'⟩, ⟨a', ha'⟩, ⟨c', hc'⟩⟩
  dsimp at h₀ h₁ h₂
  subst k' a' c'
  rfl

def solutionsEquivSplits (n : ℕ) : Solutions n ≃ Splits n where
  toFun := by
    rintro ⟨⟨a,b,c,d⟩, ha,hb,hc,hd,hn⟩
    change a*b+c*d=n at hn
    change 0<a at ha
    change 0<b at hb
    change 0<c at hc
    change 0<d at hd
    have hab := Nat.mul_pos ha hb
    have hcd := Nat.mul_pos hc hd
    have hdiff : n - a * b = c * d := by omega
    exact ⟨⟨a * b, Finset.mem_Icc.mpr ⟨by omega, by omega⟩⟩,
      ⟨a, Nat.mem_divisors.mpr ⟨⟨b, rfl⟩, hab.ne'⟩⟩,
      ⟨c, Nat.mem_divisors.mpr ⟨⟨d, hdiff⟩, by change n - a*b ≠ 0; omega⟩⟩⟩
  invFun := fun ⟨⟨k, hk⟩, ⟨a, ha⟩, ⟨c, hc⟩⟩ =>
    have ha' := Nat.mem_divisors.mp ha
    have hc' := Nat.mem_divisors.mp hc
    have hab : a * (k / a) = k := Nat.mul_div_cancel' ha'.1
    have hcd : c * ((n-k)/c) = n-k := Nat.mul_div_cancel' hc'.1
    have hapos : 0 < a := Nat.pos_of_mem_divisors ha
    have hcpos : 0 < c := Nat.pos_of_mem_divisors hc
    have hk0 : k ≠ 0 := ha'.2
    have hnk0 : n-k ≠ 0 := hc'.2
    have hkb : k ≤ n := (Finset.mem_Icc.mp hk).2
    ⟨⟨a, k / a, c, (n-k)/c⟩, hapos, by
        change 0 < k/a
        apply Nat.pos_of_ne_zero
        intro hz
        exact hk0 (by simpa [hz] using hab.symm),
      hcpos, by
        change 0 < (n-k)/c
        apply Nat.pos_of_ne_zero
        intro hz
        exact hnk0 (by simpa [hz] using hcd.symm),
      by rw [hab,hcd]; omega⟩
  left_inv := by
    rintro ⟨⟨a,b,c,d⟩, ha,hb,hc,hd,hn⟩
    apply Subtype.ext
    change a*b+c*d=n at hn
    dsimp
    have hdiff : n - a * b = c * d := by omega
    rw [hdiff, Nat.mul_div_cancel_left _ ha, Nat.mul_div_cancel_left _ hc]
  right_inv := by
    rintro ⟨⟨k, hk⟩, ⟨a, ha⟩, ⟨c, hc⟩⟩
    have hab : a * (k / a) = k := Nat.mul_div_cancel' (Nat.mem_divisors.mp ha).1
    exact splits_ext hab rfl rfl

noncomputable instance solutionsFintype (n : ℕ) : Fintype (Solutions n) :=
  Fintype.ofEquiv (Splits n) (solutionsEquivSplits n).symm

theorem card_solutions (n : ℕ) :
    Fintype.card (Solutions n) = ∑ k ∈ Icc 1 n, k.divisors.card * (n-k).divisors.card := by
  rw [Fintype.card_congr (solutionsEquivSplits n), Fintype.card_sigma]
  simp only [Fintype.card_prod, Fintype.card_coe, Finset.univ_eq_attach]
  exact Finset.sum_attach (Icc 1 n) (fun k => k.divisors.card * (n-k).divisors.card)


abbrev PrimitiveSolutions (n : ℕ) :=
  {t : Solutions n // t.val.1.Coprime t.val.2.2.1}

abbrev CoprimePairs (x y : ℕ) :=
  {t : ↥(Nat.divisors x) × ↥(Nat.divisors y) // t.1.val.Coprime t.2.val}

private def primitiveEquivSplits (n : ℕ) :
    PrimitiveSolutions n ≃ Σ k : ↥(Icc 1 n), CoprimePairs k.val (n - k.val) := by
  let e := solutionsEquivSplits n
  refine (e.subtypeEquiv (q := fun s : Splits n => s.2.1.val.Coprime s.2.2.val) ?_).trans ?_
  · rintro ⟨⟨a,b,c,d⟩, ha,hb,hc,hd,hn⟩
    rfl
  · exact {
      toFun := fun ⟨⟨k, pair⟩, h⟩ => ⟨k, ⟨pair, h⟩⟩
      invFun := fun ⟨k, ⟨pair, h⟩⟩ => ⟨⟨k, pair⟩, h⟩
      left_inv := by rintro ⟨⟨_,_⟩,_⟩; rfl
      right_inv := by rintro ⟨_,⟨_,_⟩⟩; rfl }

theorem card_primitive_solutions (n : ℕ)
    (localCount : ∀ x y, Fintype.card (CoprimePairs x y) = (Nat.divisors (x*y)).card) :
    Fintype.card (PrimitiveSolutions n) =
      ∑ k ∈ Icc 1 n, (Nat.divisors (k * (n-k))).card := by
  rw [Fintype.card_congr (primitiveEquivSplits n), Fintype.card_sigma]
  simp only [localCount, Finset.univ_eq_attach]
  exact Finset.sum_attach (Icc 1 n) (fun k => (Nat.divisors (k * (n-k))).card)


end LambertCounts

namespace LambertCounts

/-- Encode a choice of which side receives a prime, including the zero choice. -/
def exponentChoice (a b : ℕ) :
    Fin (a+b+1) ≃ {u : Fin (a+1) × Fin (b+1) // u.1.val = 0 ∨ u.2.val = 0} where
  toFun := fun k =>
    if h : k.val ≤ a then ⟨(⟨k.val, by omega⟩, 0), Or.inr rfl⟩
    else ⟨(0, ⟨k.val-a, by omega⟩), Or.inl rfl⟩
  invFun := fun u =>
    if h : u.val.2.val = 0 then ⟨u.val.1.val, by have := u.val.1.isLt; omega⟩
    else ⟨a+u.val.2.val, by have := u.val.2.isLt; omega⟩
  left_inv := by
    intro k
    apply Fin.ext
    dsimp
    split
    · simp
    · have h : k.val-a ≠ 0 := by omega
      simp [h]
      omega
  right_inv := by
    intro u
    have hsmall : u.val.1.val ≤ a := by have := u.val.1.isLt; omega
    by_cases h : u.val.2.val = 0
    · apply Subtype.ext
      apply Prod.ext <;> apply Fin.ext <;> simp [h, hsmall]
    · have hfirst := u.property.resolve_right h
      have hlarge : ¬ a + u.val.2.val ≤ a := by omega
      apply Subtype.ext
      apply Prod.ext <;> apply Fin.ext <;> simp [h, hlarge, hfirst]


end LambertCounts

namespace LambertCounts

private abbrev Exponents (n M : ℕ) :=
  (p : ↥(Nat.primeFactors M)) → Fin (n.factorization p.val + 1)

private noncomputable def extendExponents {n M : ℕ} (v : Exponents n M) : ℕ →₀ ℕ :=
  Finsupp.onFinset M.primeFactors
    (fun p => if hp : p ∈ M.primeFactors then (v ⟨p,hp⟩).val else 0)
    (by intro p hp; by_contra h; exact hp (dif_neg h))

theorem extendExponents_le {n M : ℕ} (v : Exponents n M) :
    extendExponents v ≤ n.factorization := by
  intro p
  simp only [extendExponents, Finsupp.onFinset_apply]
  split
  · exact Nat.le_of_lt_succ (v _).isLt
  · exact Nat.zero_le _

noncomputable def divisorExponents {n M : ℕ} (hn : n ≠ 0) (hM : M ≠ 0) (hnM : n ∣ M) :
    ↥(Nat.divisors n) ≃ Exponents n M := by
  have hle := (Nat.factorization_le_iff_dvd hn hM).mpr hnM
  have hj (v : Exponents n M) : (extendExponents v).prod (· ^ ·) ≠ 0 := by
    refine Finsupp.prod_ne_zero_iff.mpr ?_
    intro p hp
    exact pow_ne_zero _ (Nat.prime_of_mem_primeFactors
      (Finsupp.support_mono ((extendExponents_le v).trans hle) hp)).ne_zero
  let reconstruct : Exponents n M → ↥(Nat.divisors n) := fun v =>
    ⟨(extendExponents v).prod (· ^ ·),
      Nat.mem_divisors.mpr ⟨Nat.prod_pow_dvd_of_le_factorization (extendExponents_le v), hn⟩⟩
  let encode : ↥(Nat.divisors n) → Exponents n M := fun a p =>
    ⟨a.val.factorization p.val, Nat.lt_succ_of_le
      (((Nat.factorization_le_iff_dvd (Nat.pos_of_mem_divisors a.property).ne' hn).mpr
      (Nat.mem_divisors.mp a.property).1) p.val)⟩
  refine ⟨encode, reconstruct, ?_, ?_⟩
  · intro a
    apply Subtype.ext
    apply Nat.factorization_inj (hj (encode a)) (Nat.pos_of_mem_divisors a.property).ne'
    change ((extendExponents (encode a)).prod (· ^ ·)).factorization = a.val.factorization
    rw [Nat.factorization_prod_pow_eq_self_of_le_factorization (extendExponents_le (encode a))]
    ext p
    simp only [extendExponents, Finsupp.onFinset_apply]
    split
    · rfl
    · symm
      have ha : a.val ∣ M := (Nat.mem_divisors.mp a.property).1.trans hnM
      have le := (Nat.factorization_le_iff_dvd (Nat.pos_of_mem_divisors a.property).ne' hM).mpr ha p
      have hzero : M.factorization p = 0 := by
        simpa [← Nat.support_factorization, Finsupp.notMem_support_iff] using ‹p ∉ M.primeFactors›
      omega
  · intro v
    funext p
    apply Fin.ext
    change ((extendExponents v).prod (· ^ ·)).factorization p.val = (v p).val
    rw [Nat.factorization_prod_pow_eq_self_of_le_factorization (extendExponents_le v)]
    simp only [extendExponents, Finsupp.onFinset_apply, dif_pos p.property]


end LambertCounts
namespace LambertCounts

noncomputable def exponentPairEquiv {x y : ℕ} (hx : x ≠ 0) (hy : y ≠ 0) :
    CoprimePairs x y ≃ Exponents (x*y) (x*y) := by
  let M := x*y
  have hM : M ≠ 0 := mul_ne_zero hx hy
  let ex := divisorExponents hx hM (Nat.dvd_mul_right x y)
  let ey := divisorExponents hy hM (Nat.dvd_mul_left y x)
  let e := ex.prodCongr ey
  let P (f : Exponents x M × Exponents y M) :=
    ∀ p, (f.1 p).val = 0 ∨ (f.2 p).val = 0
  have he (a : ↥x.divisors × ↥y.divisors) :
      a.1.val.Coprime a.2.val ↔ P (e a) := by
    have h₁ : a.1.val ≠ 0 := (Nat.pos_of_mem_divisors a.1.property).ne'
    have h₂ : a.2.val ≠ 0 := (Nat.pos_of_mem_divisors a.2.property).ne'
    change a.1.val.Coprime a.2.val ↔ ∀ p : ↥M.primeFactors,
      a.1.val.factorization p.val = 0 ∨ a.2.val.factorization p.val = 0
    constructor
    · intro hc p
      have hp := Nat.prime_of_mem_primeFactors p.property
      by_cases hleft : p.val ∣ a.1.val
      · right
        apply Nat.factorization_eq_zero_of_not_dvd
        exact fun hright => (Nat.Prime.not_coprime_iff_dvd.mpr ⟨_, hp, hleft, hright⟩) hc
      · exact Or.inl (Nat.factorization_eq_zero_of_not_dvd hleft)
    · intro h
      by_contra hc
      obtain ⟨q, hq, hq₁, hq₂⟩ := Nat.Prime.not_coprime_iff_dvd.mp hc
      have hqx : q ∣ x := hq₁.trans (Nat.mem_divisors.mp a.1.property).1
      have hqM : q ∈ M.primeFactors := Nat.mem_primeFactors.mpr
        ⟨hq, hqx.trans (Nat.dvd_mul_right x y), hM⟩
      exact (h ⟨q, hqM⟩).elim
        (Nat.ne_of_gt (hq.factorization_pos_of_dvd h₁ hq₁))
        (Nat.ne_of_gt (hq.factorization_pos_of_dvd h₂ hq₂))
  refine (e.subtypeEquiv he).trans ?_
  let C (p : ↥M.primeFactors) :=
    {u : Fin (x.factorization p.val+1) × Fin (y.factorization p.val+1) //
      u.1.val = 0 ∨ u.2.val = 0}
  let transport : {f // P f} ≃ ((p : ↥M.primeFactors) → C p) := {
    toFun := fun f p => ⟨(f.val.1 p, f.val.2 p), f.property p⟩
    invFun := fun g => ⟨(fun p => (g p).val.1, fun p => (g p).val.2), fun p => (g p).property⟩
    left_inv := by intro f; cases f with | mk pair hp => cases pair; rfl
    right_inv := fun _ => rfl }
  refine transport.trans (Equiv.piCongrRight fun p => ?_)
  have hf : M.factorization p.val =
      x.factorization p.val + y.factorization p.val := by
    rw [Nat.factorization_mul hx hy]
    rfl
  exact (exponentChoice _ _).symm.trans (finCongr (by rw [hf]))

theorem localCount (x y : ℕ) :
    Fintype.card (CoprimePairs x y) = (Nat.divisors (x*y)).card := by
  by_cases hx : x = 0
  · subst x
    simp only [zero_mul, Nat.divisors_zero, Finset.card_empty]
    letI : IsEmpty (CoprimePairs 0 y) := ⟨fun t => by simpa using t.val.1.property⟩
    exact Fintype.card_eq_zero
  by_cases hy : y = 0
  · subst y
    simp only [mul_zero, Nat.divisors_zero, Finset.card_empty]
    letI : IsEmpty (CoprimePairs x 0) := ⟨fun t => by simpa using t.val.2.property⟩
    exact Fintype.card_eq_zero
  let e := (exponentPairEquiv hx hy).trans
    (divisorExponents (mul_ne_zero hx hy) (mul_ne_zero hx hy) (dvd_refl _)).symm
  exact (Fintype.card_congr e).trans (Fintype.card_coe _)


end LambertCounts

namespace LambertCounts
abbrev DivisorPrimitives (n : ℕ) :=
  Σ D : ↥(Nat.divisors n), PrimitiveSolutions D.1

private theorem divisorPrimitives_ext {n : ℕ} {x y : DivisorPrimitives n}
    (hD : x.1.val = y.1.val) (ht : x.2.val.val = y.2.val.val) : x = y := by
  rcases x with ⟨⟨D, hD'⟩, ⟨⟨t, ht'⟩, hc⟩⟩
  rcases y with ⟨⟨D', hD''⟩, ⟨⟨t', ht''⟩, hc'⟩⟩
  dsimp at hD ht
  subst D'
  subst t'
  rfl

def solutionsEquivDivisorPrimitives (n : ℕ) (hn : 0 < n) :
    Solutions n ≃ DivisorPrimitives n := by
  classical
  let forward : Solutions n → DivisorPrimitives n := fun x => by
    rcases x with ⟨⟨a, b, c, d⟩, ha, hb, hc, hd, habcd⟩
    let g := Nat.gcd a c
    let A := a / g
    let C := c / g
    let D := A * b + C * d
    have hgpos : 0 < g := by dsimp [g]; exact Nat.gcd_pos_of_pos_left c ha
    have hga : g * A = a := by
      dsimp [g, A]
      exact Nat.mul_div_cancel' (Nat.gcd_dvd_left a c)
    have hgc : g * C = c := by
      dsimp [g, C]
      exact Nat.mul_div_cancel' (Nat.gcd_dvd_right a c)
    have hA : 0 < A := by
      dsimp [A]
      apply Nat.div_pos (Nat.le_of_dvd ha (Nat.gcd_dvd_left a c))
      exact hgpos
    have hC : 0 < C := by
      dsimp [C]
      apply Nat.div_pos (Nat.le_of_dvd hc (Nat.gcd_dvd_right a c))
      exact hgpos
    have hDpos : 0 < D := by
      dsimp [D]
      have h₁ := Nat.mul_pos hA hb
      have h₂ := Nat.mul_pos hC hd
      exact add_pos h₁ h₂
    have hnfac : g * D = n := by
      dsimp [D]
      calc
        g * (A * b + C * d) = g * A * b + g * C * d := by ring
        _ = n := by rw [hga, hgc]; exact habcd
    refine ⟨⟨D, Nat.mem_divisors.mpr ⟨⟨g, by simpa [Nat.mul_comm] using hnfac.symm⟩, hn.ne'⟩⟩,
      ⟨⟨⟨A, b, C, d⟩, hA, hb, hC, hd, rfl⟩, ?_⟩⟩
    dsimp [A, C, g]
    exact Nat.coprime_div_gcd_div_gcd (Nat.gcd_pos_of_pos_left c ha)
  let backward : DivisorPrimitives n → Solutions n := fun y => by
    rcases y with ⟨⟨D, hDmem⟩, ⟨⟨⟨a, b, c, d⟩, ha, hb, hc, hd, habcd⟩, hcop⟩⟩
    have hD := Nat.mem_divisors.mp hDmem
    have hDpos : 0 < D := Nat.pos_of_mem_divisors hDmem
    let g := n / D
    have hgD : g * D = n := by
      dsimp [g]
      calc
        n / D * D = D * (n / D) := Nat.mul_comm _ _
        _ = n := Nat.mul_div_cancel' hD.1
    have hgpos : 0 < g := by dsimp [g]; exact Nat.div_pos (Nat.le_of_dvd hn hD.1) hDpos
    refine ⟨⟨g * a, b, g * c, d⟩, Nat.mul_pos hgpos ha, hb, Nat.mul_pos hgpos hc, hd, ?_⟩
    calc
      g * a * b + g * c * d = g * (a * b + c * d) := by ring
      _ = g * D := by rw [habcd]
      _ = n := hgD
  refine {
    toFun := forward
    invFun := backward
    left_inv := ?_
    right_inv := ?_ }
  · rintro ⟨⟨a, b, c, d⟩, ha, hb, hc, hd, habcd⟩
    let g := Nat.gcd a c
    let A := a / g
    let C := c / g
    let D := A * b + C * d
    have hgpos : 0 < g := by dsimp [g]; exact Nat.gcd_pos_of_pos_left c ha
    have hga : g * A = a := by dsimp [g, A]; exact Nat.mul_div_cancel' (Nat.gcd_dvd_left a c)
    have hgc : g * C = c := by dsimp [g, C]; exact Nat.mul_div_cancel' (Nat.gcd_dvd_right a c)
    have hfac : g * D = n := by
      dsimp [D]
      calc
        g * (A * b + C * d) = g * A * b + g * C * d := by ring
        _ = n := by rw [hga, hgc]; exact habcd
    have hDpos : 0 < D := by
      dsimp [D]
      exact add_pos (Nat.mul_pos (Nat.div_pos (Nat.le_of_dvd ha (Nat.gcd_dvd_left a c)) hgpos) hb)
        (Nat.mul_pos (Nat.div_pos (Nat.le_of_dvd hc (Nat.gcd_dvd_right a c)) hgpos) hd)
    have hq : n / D = g := by
      rw [← hfac]
      simpa [Nat.mul_comm] using Nat.mul_div_cancel_left g hDpos
    apply Subtype.ext
    change (n / D * (a / g), b, n / D * (c / g), d) = (a, b, c, d)
    rw [hq, hga, hgc]
  · intro y
    rcases y with ⟨⟨D, hDmem⟩, ⟨⟨⟨a, b, c, d⟩, ha, hb, hc, hd, habcd⟩, hcop⟩⟩
    have hDpos : 0 < D := Nat.pos_of_mem_divisors hDmem
    have hgpos : 0 < n / D := Nat.div_pos (Nat.le_of_dvd hn (Nat.mem_divisors.mp hDmem).1) hDpos
    change Nat.gcd a c = 1 at hcop
    have hgcd : (n / D * a).gcd (n / D * c) = n / D := by
      rw [Nat.gcd_mul_left, hcop, mul_one]
    have hqa : n / D * a / (n / D) = a := Nat.mul_div_cancel_left a hgpos
    have hqc : n / D * c / (n / D) = c := Nat.mul_div_cancel_left c hgpos
    apply divisorPrimitives_ext
    · simp [forward, backward, hgcd, hqa, hqc, habcd]
    · simp [forward, backward, hgcd, hqa, hqc]

end LambertCounts
namespace LambertCounts

open Finset

theorem divisor_convolution
    (scaling : ∀ n : ℕ, 0 < n →
      Solutions n ≃ Σ d : ↥(Nat.divisors n), PrimitiveSolutions d.val)
    (localCount : ∀ x y, Fintype.card (CoprimePairs x y) = (Nat.divisors (x*y)).card)
    (n : ℕ) (hn : 2 ≤ n) :
    (∑ k ∈ Icc 1 n, k.divisors.card * (n - k).divisors.card) =
      ∑ d ∈ n.divisors, ∑ k ∈ Icc 1 d, (Nat.divisors (k * (d-k))).card := by
  rw [← card_solutions n, Fintype.card_congr (scaling n (by omega)), Fintype.card_sigma]
  simp only [card_primitive_solutions _ localCount, Finset.univ_eq_attach]
  exact Finset.sum_attach n.divisors (fun d => ∑ k ∈ Icc 1 d, (Nat.divisors (k*(d-k))).card)


end LambertCounts

theorem OMA.solution : type_of% @OMA.S_oeis_a072031.main := by
  intro n hn
  exact LambertCounts.divisor_convolution LambertCounts.solutionsEquivDivisorPrimitives
    LambertCounts.localCount n hn
