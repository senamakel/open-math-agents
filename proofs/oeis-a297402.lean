import OMAStatements.S_oeis_a297402

open Polynomial

namespace OMA.S_oeis_a297402

private theorem even_prime_term_lower (n p : ℕ) (hp : p.Prime) (hp2 : p ≠ 2)
    (hn : n ≠ 0) (heven : Even n) :
    2 ^ (padicValNat 2 n + 1) ∣ term n p := by
  have hodd : Odd p := hp.odd_of_ne_two hp2
  have hpowOdd : Odd (p ^ n) := Odd.pow hodd
  have hpowMod : p ^ n % 2 = 1 := Nat.odd_iff.mp hpowOdd
  have hsubEven : Even (p ^ n - 1) := by
    apply Nat.even_iff.mpr
    omega
  have hraw2 : 2 ∣ p ^ n - 1 := even_iff_two_dvd.mp hsubEven
  have hrawpos : p ^ n - 1 ≠ 0 := by
    apply Nat.sub_ne_zero_of_lt
    exact Nat.one_lt_pow hn hp.one_lt
  have hval := padicValNat.pow_two_sub_one_ge (n := n) (x := p)
    hp.one_lt (by
      intro hdiv
      have he : Even p := even_iff_two_dvd.mpr hdiv
      exact (Nat.not_even_iff_odd.mpr hodd) he) hn heven
  have hpow : 2 ^ (padicValNat 2 n + 2) ∣ p ^ n - 1 :=
    (padicValNat_dvd_iff_le hrawpos).2 (by omega)
  rw [term, Nat.dvd_div_iff_mul_dvd hraw2]
  convert hpow using 1
  ring_nf

private theorem card_nat_pow_eq_one_le (q n : ℕ) [Fact q.Prime] (hn : n ≠ 0)
    (s : Finset ℕ) (hs : ∀ a ∈ s, a < q)
    (hp : ∀ a ∈ s, (a : ZMod q)^n = 1) : s.card ≤ n := by
  classical
  let P : (ZMod q)[X] := X^n - C 1
  have hdegree : P.natDegree = n := natDegree_X_pow_sub_C
  have hP : P ≠ 0 := by
    intro h
    rw [h, natDegree_zero] at hdegree
    exact hn hdegree.symm
  let t := s.image (fun a : ℕ => (a : ZMod q))
  have hcard : t.card = s.card := Finset.card_image_of_injOn (by
    intro a ha b hb hab
    have h := congrArg ZMod.val hab
    rwa [ZMod.val_natCast_of_lt (hs _ ha), ZMod.val_natCast_of_lt (hs _ hb)] at h)
  have hsub : t ⊆ P.roots.toFinset := by
    intro a ha
    obtain ⟨b, hb, rfl⟩ := Finset.mem_image.mp ha
    rw [Multiset.mem_toFinset, mem_roots hP]
    simp [P, IsRoot, hp _ hb]
  calc
    s.card = t.card := hcard.symm
    _ ≤ P.roots.toFinset.card := Finset.card_le_card hsub
    _ ≤ P.roots.card := Multiset.toFinset_card_le _
    _ ≤ n := hdegree ▸ card_roots' P


private lemma term_mul_two_eq (n p : ℕ) (hp : p.Prime) (hp2 : p ≠ 2) :
    2 * term n p = p ^ n - 1 := by
  have hodd : Odd p := hp.odd_of_ne_two hp2
  have hpowOdd : Odd (p ^ n) := Odd.pow hodd
  have hpowMod : p ^ n % 2 = 1 := Nat.odd_iff.mp hpowOdd
  have hsubEven : Even (p ^ n - 1) := by
    apply Nat.even_iff.mpr
    have hpos : 1 ≤ p ^ n := Nat.one_le_pow n p hp.pos
    omega
  unfold term
  exact Nat.mul_div_cancel' (even_iff_two_dvd.mp hsubEven)

private theorem oddPrime_not_dvd_initialGcd (n q : ℕ) (hn : 0 < n)
    (hq : q.Prime) (hq2 : q ≠ 2) : ¬q ∣ initialGcd n := by
  classical
  intro hdiv
  letI : Fact q.Prime := ⟨hq⟩
  let P := Nat.nth Nat.Prime
  have hmono : StrictMono P := Nat.nth_strictMono Nat.infinite_setOfPred_prime
  have hP0 : P 0 = 2 := Nat.nth_prime_zero_eq_two
  have hbase (i : ℕ) (hi : i < n) : q ∣ P (i+1)^n - 1 := by
    have hp := Nat.prime_nth_prime (i+1)
    have hp2 : P (i+1) ≠ 2 := by
      have hh : P 0 < P (i+1) := hmono (by omega)
      omega
    have hd : initialGcd n ∣ term n (P (i+1)) :=
      Finset.gcd_dvd (Finset.mem_range.mpr hi)
    rw [← term_mul_two_eq n _ hp hp2]
    exact dvd_mul_of_dvd_right (hdiv.trans hd) 2
  obtain ⟨k, hk⟩ : q ∈ Set.range P := ⟨Nat.count Nat.Prime q, Nat.nth_count hq⟩
  have hk0 : k ≠ 0 := by
    intro h
    subst k
    exact hq2 (hk.symm.trans hP0)
  have hkn : n < k := by
    by_contra! hle
    have h := hbase (k-1) (by omega)
    have hh : k - 1 + 1 = k := by omega
    rw [hh, hk] at h
    have hzero : ((q ^ n - 1 : ℕ) : ZMod q) = 0 :=
      (ZMod.natCast_eq_zero_iff _ _).2 h
    rw [Nat.cast_sub (Nat.one_le_pow n q hq.pos)] at hzero
    simp [hn.ne'] at hzero
  let s := (Finset.range n).image (fun i => P (i+1))
  have hs (a : ℕ) (ha : a ∈ s) : a < q := by
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp ha
    rw [← hk]
    exact hmono (by have := Finset.mem_range.mp hi; omega)
  have hs1 : 1 ∉ s := by
    intro h
    obtain ⟨i, _, hi⟩ := Finset.mem_image.mp h
    exact (Nat.prime_nth_prime (i+1)).ne_one hi
  have hcard : s.card = n := by
    have hinj : Function.Injective (fun i : ℕ => P (i+1)) := by
      intro i j h
      have := hmono.injective h
      omega
    dsimp [s]
    rw [Finset.card_image_of_injective _ hinj, Finset.card_range]
  have hroots : ∀ a ∈ insert 1 s, (a : ZMod q)^n = 1 := by
    intro a ha
    rcases Finset.mem_insert.mp ha with rfl | ha
    · simp
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp ha
    have hzero : ((P (i+1)^n - 1 : ℕ) : ZMod q) = 0 :=
      (ZMod.natCast_eq_zero_iff _ _).2 (hbase i (Finset.mem_range.mp hi))
    rw [Nat.cast_sub (Nat.one_le_pow n _ (Nat.prime_nth_prime _).pos), Nat.cast_pow, Nat.cast_one, sub_eq_zero] at hzero
    exact hzero
  have h := card_nat_pow_eq_one_le q n hn.ne' (insert 1 s) (by
    intro a ha
    rcases Finset.mem_insert.mp ha with rfl | ha
    · exact hq.one_lt
    · exact hs a ha) hroots
  rw [Finset.card_insert_of_notMem hs1, hcard] at h
  omega

private theorem term_three_valuation_even {n : ℕ} (hn : n ≠ 0) (he : Even n) :
    padicValNat 2 (3^n - 1) = padicValNat 2 n + 2 := by
  have h := padicValNat.pow_two_sub_one (x := 3) (by decide) (by decide) hn he
  change padicValNat 2 (3^n - 1) + 1 =
    padicValNat 2 4 + padicValNat 2 2 + padicValNat 2 n at h
  have h2 : padicValNat 2 2 = 1 := padicValNat.self (by decide)
  have h4 : padicValNat 2 4 = 2 := by
    change padicValNat 2 (2^2) = 2
    rw [padicValNat.pow, h2, mul_one]
  rw [h4,h2] at h
  omega

private theorem term_three_odd_of_odd {n : ℕ} (ho : Odd n) :
    ¬ 2 ∣ term n 3 := by
  obtain ⟨k, rfl⟩ := ho
  have h : 3 ^ (2*k+1) ≡ 3 [MOD 4] := by
    have h9 : 3^2 ≡ 1 [MOD 4] := by decide
    simpa [pow_add, pow_mul] using (h9.pow k).mul (Nat.ModEq.refl 3)
  have he := term_mul_two_eq (2*k+1) 3 (by decide) (by decide)
  change 3 ^ (2*k+1) % 4 = 3 at h
  intro hd
  obtain ⟨m, hm⟩ := hd
  generalize hz : 3 ^ (2*k+1) = z at h he
  omega

private theorem prove_main (n : ℕ) (hn : 0 < n) (p : ℕ) (hp : p.Prime) (hp2 : p ≠ 2) :
    initialGcd n ∣ term n p := by
  have hthree : initialGcd n ∣ term n 3 := by
    simpa [initialGcd, Nat.nth_prime_one_eq_three] using
      (Finset.gcd_dvd (f := fun i => term n (Nat.nth Nat.Prime (i+1)))
        (Finset.mem_range.mpr hn))
  have hpos : term n 3 ≠ 0 := by
    have hh := term_mul_two_eq n 3 (by decide) (by decide)
    have ht : 1 < 3^n := Nat.one_lt_pow hn.ne' (by decide)
    omega
  have hg : initialGcd n ≠ 0 := by
    intro hz
    exact hpos (by simpa [hz] using hthree)
  have hpow := Nat.eq_prime_pow_of_unique_prime_dvd hg (p := 2) (by
    intro q hq hd
    by_contra hq2
    exact oddPrime_not_dvd_initialGcd n q hn hq hq2 hd)
  let k := (initialGcd n).primeFactorsList.length
  change initialGcd n = 2^k at hpow
  rw [hpow] at hthree ⊢
  by_cases he : Even n
  · have hr := term_mul_two_eq n 3 (by decide) (by decide)
    have hraw : 2^(k+1) ∣ 3^n - 1 := by
      rw [← hr, pow_succ, mul_comm (2^k)]
      exact Nat.mul_dvd_mul_left 2 hthree
    have hx : 3^n - 1 ≠ 0 :=
      Nat.sub_ne_zero_of_lt (Nat.one_lt_pow hn.ne' (by decide))
    have hk : k+1 ≤ padicValNat 2 (3^n - 1) :=
      (padicValNat_dvd_iff_le hx).mp hraw
    rw [term_three_valuation_even hn.ne' he] at hk
    exact (pow_dvd_pow 2 (by omega : k ≤ padicValNat 2 n + 1)).trans
      (even_prime_term_lower n p hp hp2 hn.ne' he)
  · have ho := Nat.not_even_iff_odd.mp he
    have hk : k = 0 := by
      by_contra hk
      have ht : 2 ∣ 2^k := by
        simpa only [pow_one] using (pow_dvd_pow 2 (by omega : 1 ≤ k))
      exact (term_three_odd_of_odd ho) (ht.trans hthree)
    simp [hk]

end OMA.S_oeis_a297402

theorem OMA.solution : type_of% @OMA.S_oeis_a297402.main :=
  OMA.S_oeis_a297402.prove_main
