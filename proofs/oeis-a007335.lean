import OMAStatements.S_oeis_a007335

/-!
The greedy set is parameterized by its exponents at 2 and 3. Classify the
unordered products in those coordinates, enumerate the resulting set in
increasing order, then sum the reciprocal weights on disjoint geometric regions.
-/


namespace ReciprocalGen

abbrev UniquePair := OMA.S_oeis_a007335.UniquePair

def ProductClosed (S : Set ℕ) : Prop :=
  2 ∈ S ∧ 3 ∈ S ∧ (∀ z ∈ S, 2 ≤ z) ∧ ∀ x, 3 < x → (x ∈ S ↔ UniquePair S x)

def Enumerates (a : ℕ → ℕ) (S : Set ℕ) : Prop :=
  a 0 = 2 ∧ a 1 = 3 ∧ StrictMono a ∧ Set.range a = S

abbrev IsMU := OMA.S_oeis_a007335.IsMU

lemma uniquePair_prefix_iff {a : ℕ → ℕ} {S : Set ℕ} {n x : ℕ}
    (hrange : Set.range a = S)
    (hlower : ∀ z ∈ S, 2 ≤ z)
    (hbelow : ∀ k, a k < x → k ≤ n) :
    UniquePair (a '' Set.Iic n) x ↔ UniquePair S x := by
  unfold UniquePair OMA.S_oeis_a007335.UniquePair
  apply existsUnique_congr
  intro p
  constructor
  · rintro ⟨⟨i, _, hi⟩, ⟨j, _, hj⟩, hlt, hmul⟩
    refine ⟨?_, ?_, hlt, hmul⟩
    · rw [← hrange]
      exact ⟨i, hi⟩
    · rw [← hrange]
      exact ⟨j, hj⟩
  · rintro ⟨h₁, h₂, hlt, hmul⟩
    have hl₁ := hlower _ h₁
    have hl₂ := hlower _ h₂
    have hlt₁ : p.1 < x := by
      rw [← hmul]
      nlinarith
    have hlt₂ : p.2 < x := by
      rw [← hmul]
      nlinarith
    rw [← hrange] at h₁ h₂
    obtain ⟨i, hi⟩ := h₁
    obtain ⟨j, hj⟩ := h₂
    exact ⟨⟨i, hbelow i (hi ▸ hlt₁), hi⟩, ⟨j, hbelow j (hj ▸ hlt₂), hj⟩, hlt, hmul⟩

theorem enumerates_productClosed_isMU {a : ℕ → ℕ} {S : Set ℕ}
    (ha : Enumerates a S) (hS : ProductClosed S) : IsMU a := by
  rcases ha with ⟨ha0, ha1, hmono, hrange⟩
  rcases hS with ⟨_, _, hlower, hclosed⟩
  refine ⟨ha0, ha1, ?_⟩
  intro n
  have hnext : a (n+1) < a (n+2) := hmono (by omega)
  have hprev : 3 ≤ a (n+1) := ha1 ▸ hmono.monotone (by omega : 1 ≤ n+1)
  have hbelow (y : ℕ) (hy : y ≤ a (n+2)) (k : ℕ) (hk : a k < y) : k ≤ n+1 := by
    by_contra! h
    have hle : a (n+2) ≤ a k := hmono.monotone (by omega)
    omega
  refine ⟨?_, ?_⟩
  · refine ⟨hnext, (uniquePair_prefix_iff hrange hlower
      (hbelow _ le_rfl)).2 ((hclosed _ (by omega)).1 ?_)⟩
    rw [← hrange]
    exact ⟨n+2, rfl⟩
  · intro y hy
    rcases hy with ⟨hy, hp⟩
    by_contra! hlt
    have hyS := (hclosed y (by omega)).2
      ((uniquePair_prefix_iff hrange hlower (hbelow y hlt.le)).1 hp)
    rw [← hrange] at hyS
    obtain ⟨k, rfl⟩ := hyS
    have hle := hmono.monotone (hbelow _ le_rfl k hlt)
    omega

theorem exists_enumeration (S : Set ℕ) (hinf : S.Infinite) (h2 : 2 ∈ S) (h3 : 3 ∈ S)
    (hl : ∀ z ∈ S, 2 ≤ z) :
    ∃ e : ℕ ≃ S, Enumerates (fun i => (e i : ℕ)) S := by
  classical
  letI : Infinite S := hinf.to_subtype
  let e := Nat.Subtype.orderIsoOfNat S
  let a (i : ℕ) : ℕ := (e i : ℕ)
  have hm : StrictMono a := fun _ _ h => e.strictMono h
  have hr : Set.range a = S := by
    ext x
    constructor
    · rintro ⟨n, rfl⟩
      exact (e n).property
    · intro hx
      obtain ⟨i, hi⟩ := e.surjective ⟨x, hx⟩
      exact ⟨i, congrArg Subtype.val hi⟩
  have h20 : a 0 = 2 := by
    have htwo := h2
    rw [← hr] at htwo
    obtain ⟨i, hi⟩ := htwo
    have hle : a 0 ≤ a i := hm.monotone (Nat.zero_le _)
    have hge : 2 ≤ a 0 := hl _ (e 0).property
    omega
  have h31 : a 1 = 3 := by
    have hthree := h3
    rw [← hr] at hthree
    obtain ⟨i, hi⟩ := hthree
    have hi0 : 1 ≤ i := by
      by_contra! h
      have : i = 0 := by omega
      subst i
      omega
    have hle : a 1 ≤ a i := hm.monotone hi0
    have hgt : a 0 < a 1 := hm (by decide)
    omega
  exact ⟨e.toEquiv, h20, h31, hm, hr⟩

end ReciprocalGen



namespace A007335

def value (p : ℕ × ℕ) : ℕ := 2 ^ p.1 * 3 ^ p.2

theorem value_pos (p : ℕ × ℕ) : 0 < value p := by
  unfold value
  positivity

theorem value_add (p q : ℕ × ℕ) :
    value (p.1 + q.1, p.2 + q.2) = value p * value q := by
  simp only [value, pow_add]
  ring

theorem factorization_value_two (p : ℕ × ℕ) : (value p).factorization 2 = p.1 := by
  rw [value, Nat.factorization_mul (by positivity) (by positivity)]
  simp [Nat.factorization_pow, Nat.prime_two, Nat.prime_three, Nat.Prime.factorization]

theorem factorization_value_three (p : ℕ × ℕ) : (value p).factorization 3 = p.2 := by
  rw [value, Nat.factorization_mul (by positivity) (by positivity)]
  simp [Nat.factorization_pow, Nat.prime_two, Nat.prime_three, Nat.Prime.factorization]

theorem value_injective : Function.Injective value := by
  intro a b h
  exact Prod.ext
    (by simpa only [factorization_value_two] using congrArg (fun n : ℕ => n.factorization 2) h)
    (by simpa only [factorization_value_three] using congrArg (fun n : ℕ => n.factorization 3) h)

theorem existsUnique_product_iff (S : Set (ℕ × ℕ)) (m : ℕ) :
    (∃! ab : ℕ × ℕ,
      ab.1 ∈ value '' S ∧ ab.2 ∈ value '' S ∧ ab.1 < ab.2 ∧ ab.1 * ab.2 = m) ↔
    (∃! ab : (ℕ × ℕ) × (ℕ × ℕ),
      ab.1 ∈ S ∧ ab.2 ∈ S ∧ value ab.1 < value ab.2 ∧
        value (ab.1.1 + ab.2.1, ab.1.2 + ab.2.2) = m) := by
  constructor
  · rintro ⟨⟨a, b⟩, ⟨⟨x, hx, rfl⟩, ⟨y, hy, rfl⟩, hlt, hm⟩, huniq⟩
    refine ⟨(x,y), ⟨hx, hy, hlt, (value_add _ _).trans hm⟩, ?_⟩
    rintro ⟨x', y'⟩ ⟨hx', hy', hlt', hm'⟩
    have h := huniq (value x', value y')
      ⟨⟨x', hx', rfl⟩, ⟨y', hy', rfl⟩, hlt', (value_add _ _).symm.trans hm'⟩
    exact Prod.ext (value_injective (congrArg Prod.fst h))
      (value_injective (congrArg Prod.snd h))
  · rintro ⟨⟨x, y⟩, ⟨hx, hy, hlt, hm⟩, huniq⟩
    refine ⟨(value x, value y),
      ⟨⟨x, hx, rfl⟩, ⟨y, hy, rfl⟩, hlt, (value_add _ _).symm.trans hm⟩, ?_⟩
    rintro ⟨a, b⟩ ⟨⟨x', hx', rfl⟩, ⟨y', hy', rfl⟩, hlt', hm'⟩
    have h := huniq (x', y') ⟨hx', hy', hlt', (value_add _ _).trans hm'⟩
    exact congrArg (fun ab => (value ab.1, value ab.2)) h

theorem unique_ordered_iff_unordered
    {α : Type*} (f : α → ℕ) (hf : Function.Injective f)
    (R : α → α → Prop) (symmR : ∀ a b, R a b → R b a)
    (neR : ∀ a b, R a b → a ≠ b) :
    (∃! ab : α × α, R ab.1 ab.2 ∧ f ab.1 < f ab.2) ↔
    ∃ a b, R a b ∧ ∀ c d, R c d → (c = a ∧ d = b) ∨ (c = b ∧ d = a) := by
  constructor
  · rintro ⟨⟨a,b⟩, ⟨hab, _⟩, huniq⟩
    refine ⟨a, b, hab, fun c d hcd => ?_⟩
    rcases lt_or_gt_of_ne (fun h => neR c d hcd (hf h)) with hlt | hgt
    · have h := huniq (c,d) ⟨hcd, hlt⟩
      exact Or.inl ⟨congrArg Prod.fst h, congrArg Prod.snd h⟩
    · have h := huniq (d,c) ⟨symmR c d hcd, hgt⟩
      exact Or.inr ⟨congrArg Prod.snd h, congrArg Prod.fst h⟩
  · rintro ⟨a,b,hab,huniq⟩
    rcases lt_or_gt_of_ne (fun h => neR a b hab (hf h)) with hlt | hgt
    · refine ⟨(a,b), ⟨hab,hlt⟩, ?_⟩
      rintro ⟨c,d⟩ ⟨hcd,hcdlt⟩
      rcases huniq c d hcd with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
      · rfl
      · exact (lt_asymm hlt hcdlt).elim
    · refine ⟨(b,a), ⟨symmR a b hab,hgt⟩, ?_⟩
      rintro ⟨c,d⟩ ⟨hcd,hcdlt⟩
      rcases huniq c d hcd with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
      · exact (lt_asymm hgt hcdlt).elim
      · rfl

end A007335



/-!
The proposed exponent set for A007335 and its additive representation structure.
Coordinates `(v,w)` stand for the integer `2^v * 3^w`.
-/

namespace ReciprocalArithmetic

abbrev Point := ℕ × ℕ

def Supported (p : Point) : Prop :=
  p.1 = 1 ∨ p.2 = 1 ∨
    (3 ≤ p.1 ∧ p.1 % 2 = 1 ∧ 3 ≤ p.2 ∧ p.2 % 2 = 1)

def A (n : ℕ) : Point := (1, n)
def B (n : ℕ) : Point := (n, 1)
def C (v w : ℕ) : Point := (v, w)

def Rep (z x y : Point) : Prop :=
  Supported x ∧ Supported y ∧ x ≠ y ∧ x.1 + y.1 = z.1 ∧ x.2 + y.2 = z.2

def SamePair (x y x' y' : Point) : Prop :=
  (x = x' ∧ y = y') ∨ (x = y' ∧ y = x')

def UniqueRep (z : Point) : Prop :=
  ∃ x y, Rep z x y ∧ ∀ x' y', Rep z x' y' → SamePair x y x' y'

def TwoReps (z : Point) : Prop :=
  ∃ x y x' y', Rep z x y ∧ Rep z x' y' ∧ ¬ SamePair x y x' y'

private theorem point_ne_of_snd {x y : Point} (h : x.2 ≠ y.2) : x ≠ y := by
  intro e
  exact h (congrArg Prod.snd e)

private theorem point_ne_of_fst {x y : Point} (h : x.1 ≠ y.1) : x ≠ y := by
  intro e
  exact h (congrArg Prod.fst e)

private theorem pred_add_one {n : ℕ} (hn : 1 ≤ n) : n - 1 + 1 = n :=
  Nat.sub_add_cancel hn

theorem supported_A (n : ℕ) : Supported (A n) := Or.inl rfl
theorem supported_B (n : ℕ) : Supported (B n) := Or.inr <| Or.inl rfl
theorem supported_C {v w : ℕ} (hv : 3 ≤ v) (hvodd : v % 2 = 1)
    (hw : 3 ≤ w) (hwodd : w % 2 = 1) : Supported (C v w) :=
  Or.inr <| Or.inr ⟨hv, hvodd, hw, hwodd⟩

theorem rep_AA {i j : ℕ} (hij : i ≠ j) : Rep (2, i + j) (A i) (A j) := by
  refine ⟨supported_A _, supported_A _, ?_, ?_, ?_⟩
  · exact point_ne_of_snd hij
  · simp [A]
  · simp [A]

theorem rep_BB {i j : ℕ} (hij : i ≠ j) : Rep (i + j, 2) (B i) (B j) := by
  refine ⟨supported_B _, supported_B _, ?_, ?_, ?_⟩
  · exact point_ne_of_fst hij
  · simp [B]
  · simp [B]

theorem rep_AB {i j : ℕ} (hij : A i ≠ B j) :
    Rep (j + 1, i + 1) (A i) (B j) := by
  refine ⟨supported_A _, supported_B _, hij, ?_, ?_⟩ <;> simp [A, B] <;> omega

theorem rep_CA {v w i : ℕ} (hv : 3 ≤ v) (hvodd : v % 2 = 1)
    (hw : 3 ≤ w) (hwodd : w % 2 = 1) :
    Rep (v + 1, w + i) (C v w) (A i) := by
  refine ⟨supported_C hv hvodd hw hwodd, supported_A _, ?_, ?_, ?_⟩
  · apply point_ne_of_fst
    simp [A, C]
    omega
  · simp [A, C]
  · simp [A, C]

theorem rep_CB {v w j : ℕ} (hv : 3 ≤ v) (hvodd : v % 2 = 1)
    (hw : 3 ≤ w) (hwodd : w % 2 = 1) :
    Rep (v + j, w + 1) (C v w) (B j) := by
  refine ⟨supported_C hv hvodd hw hwodd, supported_B _, ?_, ?_, ?_⟩
  · apply point_ne_of_snd
    simp [B, C]
    omega
  · simp [B, C]
  · simp [B, C]

theorem rep_CA11 {v w : ℕ} (hv : 3 ≤ v) (hvodd : v % 2 = 1)
    (hw : 3 ≤ w) (hwodd : w % 2 = 1) :
    Rep (v + 1, w + 1) (C v w) (A 1) := rep_CA hv hvodd hw hwodd

private theorem no_same_AA_AB {w : ℕ} (hw : 2 < w) :
    ¬ SamePair (A 0) (A w) (A (w - 1)) (B 1) := by
  simp [SamePair, A, B]
  omega

private theorem no_same_BB_AB {v : ℕ} (hv : 2 < v) :
    ¬ SamePair (B 0) (B v) (A 1) (B (v - 1)) := by
  simp [SamePair, A, B]
  omega

private theorem no_same_AB_CA {v w : ℕ} (hv : 3 ≤ v) (hw : 3 ≤ w)
    (hvEven : v % 2 = 0) (hwEven : w % 2 = 0) :
    ¬ SamePair (A (w - 1)) (B (v - 1)) (C (v - 1) (w - 1)) (A 1) := by
  simp [SamePair, A, B, C]
  omega

private theorem no_same_AB_CA0 {v w : ℕ} (hv : 3 ≤ v) (hw : 3 ≤ w)
    (hvEven : v % 2 = 0) (hwOdd : w % 2 = 1) :
    ¬ SamePair (A (w - 1)) (B (v - 1)) (C (v - 1) w) (A 0) := by
  simp [SamePair, A, B, C]
  omega

private theorem no_same_AB_CB0 {v w : ℕ} (hv : 3 ≤ v) (hw : 3 ≤ w)
    (hvOdd : v % 2 = 1) (hwEven : w % 2 = 0) :
    ¬ SamePair (A (w - 1)) (B (v - 1)) (C v (w - 1)) (B 0) := by
  simp [SamePair, A, B, C]
  omega

theorem unsupported_positive_has_two_reps {v w : ℕ}
    (hv : 2 ≤ v) (hw : 2 ≤ w) (hnot : ¬ Supported (v, w)) : TwoReps (v, w) := by
  by_cases hv2 : v = 2
  · subst v
    by_cases hw2 : w = 2
    · subst w
      refine ⟨A 0, A 2, B 0, B 2, ?_, ?_, ?_⟩
      · exact rep_AA (by decide)
      · exact rep_BB (by decide)
      · simp [SamePair, A, B]
    · have hw3 : 3 ≤ w := by omega
      refine ⟨A 0, A w, A (w - 1), B 1, ?_, ?_, ?_⟩
      · simpa [A] using (rep_AA (i := 0) (j := w) (by omega))
      · rw [← (Nat.sub_add_cancel (show 1 ≤ w by omega))]
        exact rep_AB (i := w - 1) (j := 1) (point_ne_of_snd (by change w - 1 ≠ 1; omega))
      · exact no_same_AA_AB hw3
  · by_cases hw2 : w = 2
    · subst w
      have hv3 : 3 ≤ v := by omega
      refine ⟨B 0, B v, A 1, B (v - 1), ?_, ?_, ?_⟩
      · simpa [B] using (rep_BB (i := 0) (j := v) (by omega))
      · rw [← (Nat.sub_add_cancel (show 1 ≤ v by omega))]
        exact rep_AB (i := 1) (j := v - 1) (point_ne_of_fst (by change 1 ≠ v - 1; omega))
      · intro h
        simp [SamePair, A, B] at h
        omega
    · have hv3 : 3 ≤ v := by omega
      have hw3 : 3 ≤ w := by omega
      by_cases hvEven : v % 2 = 0
      · by_cases hwEven : w % 2 = 0
        · refine ⟨A (w - 1), B (v - 1), C (v - 1) (w - 1), A 1, ?_, ?_, ?_⟩
          · rw [← (Nat.sub_add_cancel (show 1 ≤ v by omega)), ← (Nat.sub_add_cancel (show 1 ≤ w by omega))]
            exact rep_AB (i := w - 1) (j := v - 1)
              (point_ne_of_fst (by change 1 ≠ v - 1; omega))
          · rw [← (Nat.sub_add_cancel (show 1 ≤ v by omega)), ← (Nat.sub_add_cancel (show 1 ≤ w by omega))]
            exact rep_CA (v := v - 1) (w := w - 1) (i := 1)
              (by omega) (by omega) (by omega) (by omega)
          · exact no_same_AB_CA hv3 hw3 hvEven hwEven
        · have hwOdd : w % 2 = 1 := by omega
          refine ⟨A (w - 1), B (v - 1), C (v - 1) w, A 0, ?_, ?_, ?_⟩
          · rw [← (Nat.sub_add_cancel (show 1 ≤ v by omega)), ← (Nat.sub_add_cancel (show 1 ≤ w by omega))]
            exact rep_AB (i := w - 1) (j := v - 1)
              (point_ne_of_fst (by change 1 ≠ v - 1; omega))
          · rw [← (Nat.sub_add_cancel (show 1 ≤ v by omega))]
            exact rep_CA (v := v - 1) (w := w) (i := 0)
              (by omega) (by omega) hw3 hwOdd
          · exact no_same_AB_CA0 hv3 hw3 hvEven hwOdd
      · have hvOdd : v % 2 = 1 := by omega
        by_cases hwEven : w % 2 = 0
        · refine ⟨A (w - 1), B (v - 1), C v (w - 1), B 0, ?_, ?_, ?_⟩
          · rw [← (Nat.sub_add_cancel (show 1 ≤ v by omega)), ← (Nat.sub_add_cancel (show 1 ≤ w by omega))]
            exact rep_AB (i := w - 1) (j := v - 1)
              (point_ne_of_fst (by change 1 ≠ v - 1; omega))
          · rw [← (Nat.sub_add_cancel (show 1 ≤ w by omega))]
            exact rep_CB (v := v) (w := w - 1) (j := 0)
              hv3 hvOdd (by omega) (by omega)
          · exact no_same_AB_CB0 hv3 hw3 hvOdd hwEven
        · have hwOdd : w % 2 = 1 := by omega
          have hsupp : Supported (v, w) :=
            Or.inr <| Or.inr ⟨hv3, hvOdd, hw3, hwOdd⟩
          exact False.elim (hnot hsupp)

theorem no_rep_on_zero_axes {v w : ℕ} (hz : v = 0 ∨ w = 0) :
    ¬ ∃ x y, Rep (v, w) x y := by
  rintro ⟨x, y, hx, hy, hneq, hfst, hsnd⟩
  rcases hz with hv | hw
  · have hx0 : x.1 = 0 := by omega
    have hy0 : y.1 = 0 := by omega
    have hx1 : x.2 = 1 := by
      rcases hx with hx | hx | ⟨_, _, _, _⟩ <;> omega
    have hy1 : y.2 = 1 := by
      rcases hy with hy | hy | ⟨_, _, _, _⟩ <;> omega
    apply hneq
    apply Prod.ext <;> omega
  · have hx0 : x.2 = 0 := by omega
    have hy0 : y.2 = 0 := by omega
    have hx1 : x.1 = 1 := by
      rcases hx with hx | hx | ⟨_, _, _, _⟩ <;> omega
    have hy1 : y.1 = 1 := by
      rcases hy with hy | hy | ⟨_, _, _, _⟩ <;> omega
    apply hneq
    apply Prod.ext <;> omega

private theorem rep_left_ray {w : ℕ} (hw : 1 ≤ w) :
    Rep (1, w) (B 0) (A (w - 1)) := by
  refine ⟨supported_B 0, supported_A _, ?_, ?_, ?_⟩
  · exact point_ne_of_fst (by norm_num [A, B])
  · norm_num [A, B]
  · calc
      1 + (w - 1) = (w - 1) + 1 := Nat.add_comm _ _
      _ = w := Nat.sub_add_cancel hw

private theorem rep_right_ray {v : ℕ} (hv : 1 ≤ v) :
    Rep (v, 1) (A 0) (B (v - 1)) := by
  refine ⟨supported_A 0, supported_B _, ?_, ?_, ?_⟩
  · exact point_ne_of_snd (by norm_num [A, B])
  · calc
      1 + (v - 1) = (v - 1) + 1 := Nat.add_comm _ _
      _ = v := Nat.sub_add_cancel hv
  · norm_num [A, B]

theorem unique_left_ray {w : ℕ} (hw : 1 ≤ w) : UniqueRep (1, w) := by
  refine ⟨B 0, A (w - 1), rep_left_ray hw, ?_⟩
  intro x y hxy
  rcases hxy with ⟨hx, hy, hneq, hfst, hsnd⟩
  have hx0 : x.1 = 0 ∨ y.1 = 0 := by omega
  rcases hx0 with hx0 | hy0
  · have hx2 : x.2 = 1 := by
      rcases hx with hxA | hxB | hxC
      · omega
      · exact hxB
      · omega
    have hy1 : y.1 = 1 := by omega
    have hy2 : y.2 = w - 1 := by omega
    have hxeq : x = B 0 := by
      apply Prod.ext <;> simp [B] <;> assumption
    have hyeq : y = A (w - 1) := by
      apply Prod.ext <;> simp [A] <;> omega
    exact Or.inl ⟨hxeq.symm, hyeq.symm⟩
  · have hy2 : y.2 = 1 := by
      rcases hy with hyA | hyB | hyC
      · omega
      · exact hyB
      · omega
    have hx1 : x.1 = 1 := by omega
    have hx2 : x.2 = w - 1 := by omega
    have hxeq : x = A (w - 1) := by
      apply Prod.ext <;> simp [A] <;> omega
    have hyeq : y = B 0 := by
      apply Prod.ext <;> simp [B] <;> assumption
    exact Or.inr ⟨hyeq.symm, hxeq.symm⟩

theorem unique_right_ray {v : ℕ} (hv : 1 ≤ v) : UniqueRep (v, 1) := by
  refine ⟨A 0, B (v - 1), rep_right_ray hv, ?_⟩
  intro x y hxy
  rcases hxy with ⟨hx, hy, hneq, hfst, hsnd⟩
  have hx0 : x.2 = 0 ∨ y.2 = 0 := by omega
  rcases hx0 with hx0 | hy0
  · have hx1 : x.1 = 1 := by
      rcases hx with hxA | hxB | hxC
      · exact hxA
      · omega
      · omega
    have hy2 : y.2 = 1 := by omega
    have hy1 : y.1 = v - 1 := by omega
    have hxeq : x = A 0 := by
      apply Prod.ext <;> simp [A] <;> assumption
    have hyeq : y = B (v - 1) := by
      apply Prod.ext <;> simp [B] <;> omega
    exact Or.inl ⟨hxeq.symm, hyeq.symm⟩
  · have hy1 : y.1 = 1 := by
      rcases hy with hyA | hyB | hyC
      · exact hyA
      · omega
      · omega
    have hx2 : x.2 = 1 := by omega
    have hx1 : x.1 = v - 1 := by omega
    have hxeq : x = B (v - 1) := by
      apply Prod.ext <;> simp [B] <;> omega
    have hyeq : y = A 0 := by
      apply Prod.ext <;> simp [A] <;> assumption
    exact Or.inr ⟨hyeq.symm, hxeq.symm⟩

theorem unique_odd_interior {v w : ℕ} (hv : 3 ≤ v) (hvodd : v % 2 = 1)
    (hw : 3 ≤ w) (hwodd : w % 2 = 1) : UniqueRep (v, w) := by
  refine ⟨A (w - 1), B (v - 1), ?_, ?_⟩
  · refine ⟨supported_A _, supported_B _, ?_, ?_, ?_⟩
    · exact point_ne_of_fst (by change 1 ≠ v - 1; omega)
    · calc
        1 + (v - 1) = (v - 1) + 1 := Nat.add_comm _ _
        _ = v := Nat.sub_add_cancel (by omega)
    · change (w - 1) + 1 = w
      exact Nat.sub_add_cancel (by omega)
  · intro x y hxy
    rcases hxy with ⟨hx, hy, hneq, hfst, hsnd⟩
    by_cases hxA : x.1 = 1
    · by_cases hyA : y.1 = 1
      · omega
      · by_cases hyB : y.2 = 1
        · have hxeq : x = A (w - 1) := by
            apply Prod.ext hxA
            change x.2 = w - 1
            omega
          have hyeq : y = B (v - 1) := by
            apply Prod.ext
            · change y.1 = v - 1
              omega
            · exact hyB
          exact Or.inl ⟨hxeq.symm, hyeq.symm⟩
        · rcases hy with hyA | hyB | hyC
          · omega
          · omega
          · omega
    · by_cases hxB : x.2 = 1
      · by_cases hyA : y.1 = 1
        · have hxeq : x = B (v - 1) := by
            apply Prod.ext
            · change x.1 = v - 1
              omega
            · exact hxB
          have hyeq : y = A (w - 1) := by
            apply Prod.ext hyA
            change y.2 = w - 1
            omega
          exact Or.inr ⟨hyeq.symm, hxeq.symm⟩
        · by_cases hyB : y.2 = 1
          · omega
          · rcases hy with hyA | hyB | hyC
            · omega
            · omega
            · omega
      · rcases hx with hxA | hxB | hxC
        · omega
        · omega
        · by_cases hyA : y.1 = 1
          · omega
          · by_cases hyB : y.2 = 1
            · omega
            · rcases hy with hyA | hyB | hyC
              · omega
              · omega
              · omega

private theorem samePair_trans_anchor {a b x y u v : Point}
    (h₁ : SamePair a b x y) (h₂ : SamePair a b u v) : SamePair x y u v := by
  rcases h₁ with ⟨hax, hby⟩ | ⟨hay, hbx⟩ <;>
    rcases h₂ with ⟨hau, hbv⟩ | ⟨hav, hbu⟩
  · exact Or.inl ⟨hax.symm.trans hau, hby.symm.trans hbv⟩
  · exact Or.inr ⟨hax.symm.trans hav, hby.symm.trans hbu⟩
  · exact Or.inr ⟨hbx.symm.trans hbv, hay.symm.trans hau⟩
  · exact Or.inl ⟨hbx.symm.trans hbu, hay.symm.trans hav⟩

theorem supported_iff_uniqueRep_of_not_seed {z : Point}
    (h₁ : z ≠ (1, 0)) (h₂ : z ≠ (0, 1)) :
    Supported z ↔ UniqueRep z := by
  rcases z with ⟨v, w⟩
  constructor
  · intro hz
    rcases hz with hv | hw | ⟨hv, hvodd, hw, hwodd⟩
    · have hw' : 1 ≤ w := by
        by_contra hn
        have hw0 : w = 0 := by omega
        apply h₁
        exact Prod.ext hv hw0
      have hvEq : v = 1 := hv
      subst v
      exact unique_left_ray hw'
    · have hv' : 1 ≤ v := by
        by_contra hn
        have hv0 : v = 0 := by omega
        apply h₂
        exact Prod.ext hv0 hw
      have hwEq : w = 1 := hw
      subst w
      exact unique_right_ray hv'
    · exact unique_odd_interior hv hvodd hw hwodd
  · intro hu
    by_contra hnot
    by_cases hv0 : v = 0
    · rcases hu with ⟨x, y, hxy, _⟩
      exact (no_rep_on_zero_axes (Or.inl hv0)) ⟨x, y, hxy⟩
    · by_cases hw0 : w = 0
      · rcases hu with ⟨x, y, hxy, _⟩
        exact (no_rep_on_zero_axes (Or.inr hw0)) ⟨x, y, hxy⟩
      · have hv : 2 ≤ v := by
          by_contra hn
          have hv1 : v = 1 := by omega
          exact hnot (Or.inl hv1)
        have hw : 2 ≤ w := by
          by_contra hn
          have hw1 : w = 1 := by omega
          exact hnot (Or.inr (Or.inl hw1))
        obtain ⟨x, y, x', y', hxy, hx'y', hdiff⟩ :=
          unsupported_positive_has_two_reps hv hw hnot
        rcases hu with ⟨a, b, hab, hunique⟩
        apply hdiff
        exact samePair_trans_anchor (hunique x y hxy) (hunique x' y' hx'y')

end ReciprocalArithmetic

namespace A007335

private abbrev Supported := ReciprocalArithmetic.Supported

def targetSet : Set ℕ := value '' {p | Supported p}

private theorem two_mem : 2 ∈ targetSet := ⟨(1,0), Or.inl rfl, by decide⟩
private theorem three_mem : 3 ∈ targetSet := ⟨(0,1), Or.inr (Or.inl rfl), by decide⟩

private theorem lower (n : ℕ) (hn : n ∈ targetSet) : 2 ≤ n := by
  obtain ⟨⟨a,b⟩, hs, rfl⟩ := hn
  have hone : 1 ≤ a ∨ 1 ≤ b := by
    change a = 1 ∨ b = 1 ∨ (3 ≤ a ∧ a % 2 = 1 ∧ 3 ≤ b ∧ b % 2 = 1) at hs
    omega
  unfold value
  rcases hone with ha | hb
  · calc
      2 = (2:ℕ)^1 * 3^0 := by decide
      _ ≤ 2^a * 3^b := by gcongr <;> omega
  · calc
      2 ≤ (2:ℕ)^0 * 3^1 := by decide
      _ ≤ 2^a * 3^b := by gcongr <;> omega

private theorem infinite_targetSet : targetSet.Infinite := by
  apply Set.Infinite.mono _ (Set.infinite_range_of_injective
    (f := fun n : ℕ => value (1,n)) (by
      intro a b h
      exact congrArg Prod.snd (value_injective h)))
  rintro _ ⟨i, rfl⟩
  exact ⟨(1,i), Or.inl rfl, rfl⟩

private theorem support_iff_unique_product (x : ℕ) (hx : 3 < x) :
    x ∈ targetSet ↔ ReciprocalGen.UniquePair targetSet x := by
  unfold ReciprocalGen.UniquePair OMA.S_oeis_a007335.UniquePair targetSet
  rw [existsUnique_product_iff]
  by_cases h : ∃ z, value z = x
  · obtain ⟨z, rfl⟩ := h
    have hz1 : z ≠ (1,0) := by
      rintro rfl
      change 3 < 2 at hx
      omega
    have hz2 : z ≠ (0,1) := by
      rintro rfl
      change 3 < 3 at hx
      omega
    have hm : value z ∈ value '' {p | Supported p} ↔ Supported z := by
      constructor
      · rintro ⟨y, hy, heq⟩
        exact (value_injective heq) ▸ hy
      · intro hz
        exact ⟨z, hz, rfl⟩
    rw [hm]
    change ReciprocalArithmetic.Supported z ↔ _
    rw [ReciprocalArithmetic.supported_iff_uniqueRep_of_not_seed hz1 hz2]
    have he :
        (∃! ab : (ℕ × ℕ) × (ℕ × ℕ),
          ab.1 ∈ {p | Supported p} ∧ ab.2 ∈ {p | Supported p} ∧
          value ab.1 < value ab.2 ∧ value (ab.1.1 + ab.2.1, ab.1.2 + ab.2.2) = value z) ↔
        (∃! ab : (ℕ × ℕ) × (ℕ × ℕ),
          ReciprocalArithmetic.Rep z ab.1 ab.2 ∧ value ab.1 < value ab.2) := by
      apply existsUnique_congr
      rintro ⟨a,b⟩
      constructor
      · rintro ⟨ha,hb,hab,hval⟩
        have hp := value_injective hval
        exact ⟨⟨ha,hb,fun h => (ne_of_lt hab) (congrArg value h),
          congrArg Prod.fst hp, congrArg Prod.snd hp⟩, hab⟩
      · rintro ⟨⟨ha,hb,_,h1,h2⟩,hab⟩
        exact ⟨ha,hb,hab,congrArg value (Prod.ext h1 h2)⟩
    rw [he, unique_ordered_iff_unordered value value_injective
      (ReciprocalArithmetic.Rep z)]
    · constructor
      · rintro ⟨a,b,hab,hu⟩
        refine ⟨a,b,hab,fun c d h => ?_⟩
        rcases hu c d h with ⟨h₁,h₂⟩ | ⟨h₁,h₂⟩
        · exact Or.inl ⟨h₁.symm,h₂.symm⟩
        · exact Or.inr ⟨h₂.symm,h₁.symm⟩
      · rintro ⟨a,b,hab,hu⟩
        refine ⟨a,b,hab,fun c d h => ?_⟩
        rcases hu c d h with ⟨h₁,h₂⟩ | ⟨h₁,h₂⟩
        · exact Or.inl ⟨h₁.symm,h₂.symm⟩
        · exact Or.inr ⟨h₂.symm,h₁.symm⟩
    · rintro a b ⟨ha,hb,hab,h1,h2⟩
      exact ⟨hb,ha,Ne.symm hab, (Nat.add_comm _ _).trans h1, (Nat.add_comm _ _).trans h2⟩
    · intro a b hab
      exact hab.2.2.1
  · constructor
    · rintro ⟨z, _, he⟩
      exact (h ⟨z, he⟩).elim
    · rintro ⟨ab, ⟨_, _, _, he⟩, _⟩
      exact (h ⟨(ab.1.1 + ab.2.1, ab.1.2 + ab.2.2), he⟩).elim

theorem good_enumerator
    (huniq : ∀ x, 3 < x → (x ∈ targetSet ↔ ReciprocalGen.UniquePair targetSet x))
    (hsum : HasSum (fun z : {p : ℕ × ℕ // Supported p} =>
      ((value z.1 : ℕ) : ℝ)⁻¹) (181/144 : ℝ)) :
    ∃ a : ℕ → ℕ, ReciprocalGen.IsMU a ∧
      HasSum (fun n : ℕ => (a n : ℝ)⁻¹) (181/144 : ℝ) := by
  have hclosed : ReciprocalGen.ProductClosed targetSet := ⟨two_mem, three_mem, lower, huniq⟩
  obtain ⟨e, he⟩ := ReciprocalGen.exists_enumeration targetSet
    infinite_targetSet two_mem three_mem lower
  let f : {p : ℕ × ℕ // Supported p} ≃ targetSet :=
    Equiv.Set.image value {p | Supported p} value_injective
  have hf : HasSum (fun x : targetSet => (x.1 : ℝ)⁻¹) (181/144 : ℝ) := by
    apply (Equiv.hasSum_iff f).1
    exact hsum
  exact ⟨fun n => (e n).1, ReciprocalGen.enumerates_productClosed_isMU he hclosed,
    (Equiv.hasSum_iff e).2 hf⟩

end A007335

namespace ReciprocalSum

open scoped BigOperators

abbrev Pair := ℕ × ℕ

def Support (p : Pair) : Prop :=
  p.1 = 1 ∨ p.2 = 1 ∨ ∃ n m : ℕ, p.1 = 2*n+3 ∧ p.2 = 2*m+3

abbrev RegionIdx := ℕ ⊕ (Unit ⊕ (ℕ ⊕ (ℕ × ℕ)))

noncomputable def weight (p : Pair) : ℝ := (1/2 : ℝ)^p.1 * (1/3 : ℝ)^p.2

def regionPair : RegionIdx → Pair
  | Sum.inl w => (1,w)
  | Sum.inr (Sum.inl _) => (0,1)
  | Sum.inr (Sum.inr (Sum.inl n)) => (n+2,1)
  | Sum.inr (Sum.inr (Sum.inr (n,m))) => (2*n+3,2*m+3)

noncomputable def regionWeight (i : RegionIdx) : ℝ := weight (regionPair i)

def regionPair_mem (i : RegionIdx) : Support (regionPair i) := by
  cases i with
  | inl w => exact Or.inl rfl
  | inr i => cases i with
    | inl u => exact Or.inr (Or.inl rfl)
    | inr i => cases i with
      | inl n => exact Or.inr (Or.inl rfl)
      | inr p => exact Or.inr (Or.inr ⟨p.1, p.2, rfl, rfl⟩)

lemma regionPair_injective : Function.Injective regionPair := by
  intro a b h
  rcases a with a | u | n | p <;> rcases b with b | v | m | q <;> simp_all [regionPair] <;> try omega
  all_goals exact Prod.ext h.1 h.2

abbrev SupportPair := {p : Pair // Support p}

def regionEquivFun (i : RegionIdx) : SupportPair := ⟨regionPair i, regionPair_mem i⟩

lemma regionEquivFun_injective : Function.Injective regionEquivFun := by
  intro a b h
  apply regionPair_injective
  exact congrArg Subtype.val h

lemma regionEquivFun_surjective : Function.Surjective regionEquivFun := by
  rintro ⟨⟨v,w⟩, hp⟩
  rcases hp with hv | hw | ⟨n,m,hv,hw⟩
  · refine ⟨Sum.inl w, ?_⟩
    apply Subtype.ext
    exact Prod.ext hv.symm rfl
  · by_cases hone : v = 1
    · refine ⟨Sum.inl w, ?_⟩
      apply Subtype.ext
      exact Prod.ext hone.symm rfl
    · by_cases hzero : v = 0
      · refine ⟨Sum.inr (Sum.inl ()), ?_⟩
        apply Subtype.ext
        exact Prod.ext hzero.symm hw.symm
      · have hv' : ∃ n, v = n+2 := by
          cases v with
          | zero => contradiction
          | succ v => cases v with
            | zero => contradiction
            | succ v => exact ⟨v, rfl⟩
        rcases hv' with ⟨n, hn⟩
        refine ⟨Sum.inr (Sum.inr (Sum.inl n)), ?_⟩
        apply Subtype.ext
        exact Prod.ext hn.symm hw.symm
  · refine ⟨Sum.inr (Sum.inr (Sum.inr (n,m))), ?_⟩
    apply Subtype.ext
    exact Prod.ext hv.symm hw.symm

noncomputable def supportEquiv : RegionIdx ≃ SupportPair :=
  Equiv.ofBijective regionEquivFun ⟨regionEquivFun_injective, regionEquivFun_surjective⟩


lemma hasSum_congr_fn {α : Type*} [AddCommGroup α] [TopologicalSpace α] [T2Space α]
    {ι : Type*} {f g : ι → α} {a : α} (h : HasSum f a) (hfg : ∀ i, f i = g i) : HasSum g a := by
  have hg : Summable g := (summable_congr hfg).mp h.summable
  apply hg.hasSum_iff.mpr
  rw [← h.tsum_eq]
  exact tsum_congr (fun i => (hfg i).symm)

lemma hasSum_inv_three : HasSum (fun n : ℕ => (3 : ℝ)⁻¹ ^ n) (3/2 : ℝ) := by
  have h := hasSum_geometric_of_norm_lt_one (ξ := (3 : ℝ)⁻¹) (by norm_num)
  norm_num at h ⊢
  exact h

lemma hasSum_odd_two_tail : HasSum (fun n : ℕ => (2 : ℝ)⁻¹ ^ (2*n+3)) (1/6 : ℝ) := by
  have h := hasSum_geometric_of_norm_lt_one (ξ := (2 : ℝ)⁻¹ ^ 2) (by norm_num)
  have h' := h.mul_left ((2 : ℝ)⁻¹ ^ 3)
  norm_num at h'
  apply hasSum_congr_fn h'
  intro n
  rw [show 2*n+3 = 3+2*n by omega, pow_add, pow_mul]
  norm_num

lemma hasSum_odd_three_tail : HasSum (fun n : ℕ => (3 : ℝ)⁻¹ ^ (2*n+3)) (1/24 : ℝ) := by
  have h := hasSum_geometric_of_norm_lt_one (ξ := (3 : ℝ)⁻¹ ^ 2) (by norm_num)
  have h' := h.mul_left ((3 : ℝ)⁻¹ ^ 3)
  norm_num at h'
  apply hasSum_congr_fn h'
  intro n
  rw [show 2*n+3 = 3+2*n by omega, pow_add, pow_mul]
  norm_num

lemma hasSum_regionA : HasSum (fun w : ℕ => regionWeight (Sum.inl w)) (3/4 : ℝ) := by
  have h := hasSum_inv_three
  have h' := h.mul_left ((2 : ℝ)⁻¹)
  norm_num at h'
  apply hasSum_congr_fn h'
  intro w
  simp [regionWeight, weight, regionPair]

lemma hasSum_regionB : HasSum (fun _ : Unit => regionWeight (Sum.inr (Sum.inl ()))) (1/3 : ℝ) := by
  simpa [regionWeight, weight, regionPair, div_eq_mul_inv] using (hasSum_fintype (fun _ : Unit => (1/3 : ℝ)))

lemma hasSum_regionC : HasSum (fun n : ℕ => regionWeight (Sum.inr (Sum.inr (Sum.inl n)))) (1/6 : ℝ) := by
  have h := hasSum_geometric_of_norm_lt_one (ξ := (2 : ℝ)⁻¹) (by norm_num)
  have h' := h.mul_left ((2 : ℝ)⁻¹ ^ 2 * (3 : ℝ)⁻¹)
  norm_num at h'
  apply hasSum_congr_fn h'
  intro n
  norm_num [regionWeight, weight, regionPair, pow_add, mul_comm, mul_assoc] <;> ring

set_option maxHeartbeats 1000000 in
lemma hasSum_regionD : HasSum (fun p : ℕ × ℕ => regionWeight (Sum.inr (Sum.inr (Sum.inr p)))) (1/144 : ℝ) := by
  set_option maxHeartbeats 1000000 in
    have hprodSummable : Summable (fun p : ℕ × ℕ => (2 : ℝ)⁻¹ ^ (2*p.1+3) * (3 : ℝ)⁻¹ ^ (2*p.2+3)) :=
      Summable.mul_of_nonneg hasSum_odd_two_tail.summable hasSum_odd_three_tail.summable
        (by intro n; positivity) (by intro n; positivity)
  have h := hasSum_odd_two_tail.mul hasSum_odd_three_tail hprodSummable
  norm_num at h
  apply hasSum_congr_fn h
  intro p
  simp [regionWeight, weight, regionPair]

lemma hasSum_regionWeights : HasSum regionWeight (181/144 : ℝ) := by
  let fCD : ℕ ⊕ (ℕ × ℕ) → ℝ := fun x => match x with
    | Sum.inl n => regionWeight (Sum.inr (Sum.inr (Sum.inl n)))
    | Sum.inr p => regionWeight (Sum.inr (Sum.inr (Sum.inr p)))
  have hCD : HasSum fCD (1/6 + 1/144 : ℝ) := by
    apply HasSum.sum
    · change HasSum (fun n => fCD (Sum.inl n)) _
      exact hasSum_congr_fn hasSum_regionC (by intro n; rfl)
    · change HasSum (fun p => fCD (Sum.inr p)) _
      exact hasSum_congr_fn hasSum_regionD (by intro p; rfl)
  let fBCD : Unit ⊕ (ℕ ⊕ (ℕ × ℕ)) → ℝ := fun x => match x with
    | Sum.inl _ => regionWeight (Sum.inr (Sum.inl ()))
    | Sum.inr y => fCD y
  have hBCD : HasSum fBCD (1/3 + (1/6 + 1/144 : ℝ)) := by
    apply HasSum.sum
    · change HasSum (fun u => fBCD (Sum.inl u)) _
      exact hasSum_congr_fn hasSum_regionB (by intro u; rfl)
    · change HasSum (fun y => fBCD (Sum.inr y)) _
      exact hasSum_congr_fn hCD (by intro y; rfl)
  let fAll : ℕ ⊕ (Unit ⊕ (ℕ ⊕ (ℕ × ℕ))) → ℝ := fun x => match x with
    | Sum.inl w => regionWeight (Sum.inl w)
    | Sum.inr y => fBCD y
  have hAll : HasSum fAll (3/4 + (1/3 + (1/6 + 1/144 : ℝ))) := by
    apply HasSum.sum
    · change HasSum (fun w => fAll (Sum.inl w)) _
      exact hasSum_congr_fn hasSum_regionA (by intro w; rfl)
    · change HasSum (fun y => fAll (Sum.inr y)) _
      exact hasSum_congr_fn hBCD (by intro y; rfl)
  have hf : fAll = regionWeight := by
    funext x
    cases x with
    | inl w => rfl
    | inr y => cases y with
      | inl u => cases u; rfl
      | inr z => cases z with
        | inl n => rfl
        | inr p => rfl
  have hAll' : HasSum fAll (181/144 : ℝ) := by norm_num at hAll ⊢; exact hAll
  exact hasSum_congr_fn hAll' (by intro x; exact congrFun hf x)

noncomputable def supportWeight (p : SupportPair) : ℝ := weight p.1

lemma hasSum_supportWeight : HasSum supportWeight (181/144 : ℝ) := by
  apply supportEquiv.hasSum_iff.mp
  exact hasSum_congr_fn hasSum_regionWeights (by intro i; rfl)

end ReciprocalSum

namespace A007335

private theorem supported_iff_sum_support (p : ℕ × ℕ) :
    Supported p ↔ ReciprocalSum.Support p := by
  rcases p with ⟨v,w⟩
  change ReciprocalArithmetic.Supported (v,w) ↔ ReciprocalSum.Support (v,w)
  unfold ReciprocalArithmetic.Supported ReciprocalSum.Support
  constructor
  · rintro (hv | hw | ⟨hv, hvodd, hw, hwodd⟩)
    · exact Or.inl hv
    · exact Or.inr (Or.inl hw)
    · exact Or.inr (Or.inr ⟨(v-3)/2, (w-3)/2, by omega, by omega⟩)
  · rintro (hv | hw | ⟨i,j,hi,hj⟩)
    · exact Or.inl hv
    · exact Or.inr (Or.inl hw)
    · exact Or.inr (Or.inr ⟨by omega, by omega, by omega, by omega⟩)

private theorem exact_support_sum :
    HasSum (fun z : {p : ℕ × ℕ // Supported p} => ((value z.1 : ℕ) : ℝ)⁻¹)
      (181/144 : ℝ) := by
  let e : {p : ℕ × ℕ // Supported p} ≃ ReciprocalSum.SupportPair :=
    Equiv.subtypeEquivRight supported_iff_sum_support
  have h := (Equiv.hasSum_iff e).2 ReciprocalSum.hasSum_supportWeight
  apply ReciprocalSum.hasSum_congr_fn h
  intro z
  simp [e, ReciprocalSum.supportWeight, ReciprocalSum.weight, value, mul_inv, inv_pow, one_div, mul_comm]

theorem prove_main : ∃ a : ℕ → ℕ, ReciprocalGen.IsMU a ∧
    HasSum (fun n : ℕ => (a n : ℝ)⁻¹) (181/144 : ℝ) :=
  good_enumerator support_iff_unique_product exact_support_sum

end A007335
theorem OMA.solution : type_of% @OMA.S_oeis_a007335.main :=
  A007335.prove_main
