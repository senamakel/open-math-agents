import OMAStatements.S_oeis_a306779

/-!
For dimensions 4368 and 1760, every possible full-length winding pair has
a common divisor greater than one. Partitioning the steps into equal blocks
and sliding a window to balance both step counts gives a repeated vertex.
-/

namespace OMA.S_oeis_a306779

def WindowBalance : Prop :=
  ∀ (w : ℕ → Bool) (L d W E : ℕ), L = d*W → eastCount w L = d*E →
    0 < d → 0 < W → ∃ i, i+W ≤ L ∧ eastCount w (i+W) - eastCount w i = E

private theorem eastCount_mono (w : ℕ → Bool) : Monotone (eastCount w) := by
  intro i j hij
  exact Finset.card_le_card (Finset.filter_subset_filter _ (Finset.range_mono hij))

private theorem eastCount_le (w : ℕ → Bool) (i : ℕ) : eastCount w i ≤ i := by
  unfold eastCount
  simpa using Finset.card_le_card
    (Finset.filter_subset (fun j => w j = true) (Finset.range i))

private theorem pos_zero (n k : ℕ) (w : ℕ → Bool) : pos n k w 0 = (0,0) := by
  simp [pos, eastCount]

theorem winding_primitive (balance : WindowBalance) (n k : ℕ)
    (hn : 0 < n) (hk : 0 < k) (w : ℕ → Bool)
    (hclose : pos n k w (n*k) = (0,0))
    (hinj : Set.InjOn (pos n k w) (Set.Iio (n*k)))
    (a b : ℕ) (ha : eastCount w (n*k) = n*a)
    (hb : n*k - eastCount w (n*k) = k*b) : Nat.gcd a b ≤ 1 := by
  by_contra! hd
  let d := Nat.gcd a b
  obtain ⟨r, hr⟩ : d ∣ a := Nat.gcd_dvd_left a b
  obtain ⟨s, hs⟩ : d ∣ b := Nat.gcd_dvd_right a b
  let W := n*r + k*s
  have htotal : n*k = n*a+k*b := by
    have := eastCount_le w (n*k)
    omega
  have hL : n*k = d*W := by rw [htotal, hr, hs]; dsimp [W]; ring
  have hE : eastCount w (n*k) = d*(n*r) := by rw [ha, hr]; ring
  have hd1 : 1 < d := hd
  have hW : 0 < W := by
    have hnk := Nat.mul_pos hn hk
    by_contra! hw
    rw [Nat.eq_zero_of_le_zero hw, mul_zero] at hL
    omega
  obtain ⟨i, hi, hdiff⟩ := balance w (n*k) d W (n*r) hL hE (by omega) hW
  have hsmall : W < n*k := by
    rw [hL]
    nlinarith
  have hi0 : i < n*k := by omega
  have hless : i < i+W := by omega
  have hcount : eastCount w (i+W) = eastCount w i + n*r := by
    have := eastCount_mono w hless.le
    omega
  have hnorth : i+W-eastCount w (i+W) = i-eastCount w i+k*s := by
    have := eastCount_le w i
    dsimp [W] at *
    omega
  have hpos : pos n k w (i+W) = pos n k w i := by
    apply Prod.ext
    · simp [pos, hcount, Nat.add_mod]
    · simp [pos, hnorth, Nat.add_mod]
  by_cases he : i+W = n*k
  · have hpos0 : pos n k w i = pos n k w 0 := by
      rw [he, hclose] at hpos
      rw [pos_zero]
      exact hpos.symm
    have heq : i = 0 := hinj hi0 (Nat.mul_pos hn hk) hpos0
    omega
  · exact (Nat.ne_of_gt hless) (hinj (lt_of_le_of_ne hi he) hi0 hpos)

theorem blocked_windings (a b : ℕ) (h : 4368*a + 1760*b = 4368*1760) :
    1 < Nat.gcd a b := by
  have hsum : 273*a + 110*b = 480480 := by omega
  have h110 : 110 ∣ 273*a := by omega
  have hcop : Nat.Coprime 110 273 := by decide
  obtain ⟨t, rfl⟩ := hcop.dvd_of_dvd_mul_left h110
  have ht : t ≤ 16 := by omega
  have hb : b = 273*(16-t) := by omega
  subst b
  interval_cases t <;> decide


private theorem closed_counts (n k : ℕ) (w : ℕ → Bool)
    (hclose : pos n k w (n*k) = (0,0)) :
    n ∣ eastCount w (n*k) ∧ k ∣ (n*k-eastCount w (n*k)) := by
  exact ⟨Nat.dvd_of_mod_eq_zero (congrArg Prod.fst hclose),
    Nat.dvd_of_mod_eq_zero (congrArg Prod.snd hclose)⟩

theorem no_full_loop (balance : WindowBalance) : ¬ HasFullLoop 4368 1760 := by
  rintro ⟨w, hclose, hinj⟩
  obtain ⟨⟨a, ha⟩, ⟨b, hb⟩⟩ := closed_counts 4368 1760 w hclose
  have hle := winding_primitive balance 4368 1760 (by decide) (by decide) w hclose hinj a b ha hb
  have htot : 4368*a + 1760*b = 4368*1760 := by
    have := eastCount_le w (4368*1760)
    omega
  exact (not_lt_of_ge hle) (blocked_windings a b htot)

end OMA.S_oeis_a306779


namespace TorusWindow

abbrev eastCount := OMA.S_oeis_a306779.eastCount

private theorem eastCount_mono (w : ℕ → Bool) : Monotone (eastCount w) := by
  intro i j hij
  exact Finset.card_le_card (Finset.filter_subset_filter _ (Finset.range_mono hij))

private theorem eastCount_succ (w : ℕ → Bool) (i : ℕ) :
    eastCount w (i + 1) = eastCount w i + if w i then 1 else 0 := by
  have hrange : Finset.range (i + 1) = insert i (Finset.range i) := by
    ext j
    simp only [Finset.mem_range, Finset.mem_insert]
    omega
  by_cases hwi : w i = true
  · simp [OMA.S_oeis_a306779.eastCount, hrange, Finset.filter_insert, hwi, Finset.mem_range]
  · simp [OMA.S_oeis_a306779.eastCount, hrange, Finset.filter_insert, hwi]

theorem balanced_window (w : ℕ → Bool) (L d W E : ℕ)
    (hL : L = d*W) (hE : eastCount w L = d*E)
    (hd : 0 < d) (_hW : 0 < W) :
    ∃ i, i+W ≤ L ∧ eastCount w (i+W) - eastCount w i = E := by
  let f (i : ℕ) := eastCount w (i+W) - eastCount w i
  have hadj (i : ℕ) : f (i+1) ≤ f i + 1 ∧ f i ≤ f (i+1) + 1 := by
    have h0 := eastCount_succ w i
    have h1 := eastCount_succ w (i+W)
    have ha : i+1+W = i+W+1 := by omega
    dsimp [f]
    rw [ha, h0, h1]
    split <;> split <;> omega
  have hsum (j : ℕ) : ∑ t ∈ Finset.range j, f (t*W) = eastCount w (j*W) := by
    induction j with
    | zero => simp [OMA.S_oeis_a306779.eastCount]
    | succ j ih =>
      rw [Finset.sum_range_succ, ih, Nat.succ_mul]
      have hm : eastCount w (j*W) ≤ eastCount w (j*W+W) :=
        eastCount_mono w (Nat.le_add_right _ _)
      dsimp [f]
      omega
  have ht (t : ℕ) (h : t < d) : t*W+W ≤ L := by
    rw [hL, ← Nat.succ_mul]
    exact Nat.mul_le_mul_right W h
  have hlin : ∑ t ∈ Finset.range d, f (t*W) = ∑ _t ∈ Finset.range d, E := by
    rw [hsum, ← hL, hE]
    simp
  by_contra! hmiss
  have hW0 : 0+W ≤ L := by simpa using ht 0 hd
  have hne0 : f 0 ≠ E := hmiss 0 hW0
  rcases lt_or_gt_of_ne hne0 with hlo | hhi
  · have hall (i : ℕ) : i+W ≤ L → f i < E := by
      induction i with
      | zero => intro _; exact hlo
      | succ i ih =>
          intro h
          have hp := ih (by omega)
          have hne : f (i+1) ≠ E := hmiss (i+1) h
          have hh := (hadj i).1
          omega
    have this := Finset.sum_lt_sum
      (s := Finset.range d) (f := fun t => f (t*W)) (g := fun _ => E)
      (fun t ht' => (hall _ (ht _ (Finset.mem_range.mp ht'))).le)
      ⟨0, Finset.mem_range.mpr hd, by simpa using hlo⟩
    omega
  · have hall (i : ℕ) : i+W ≤ L → E < f i := by
      induction i with
      | zero => intro _; exact hhi
      | succ i ih =>
          intro h
          have hp := ih (by omega)
          have hne : f (i+1) ≠ E := hmiss (i+1) h
          have hh := (hadj i).2
          omega
    have this := Finset.sum_lt_sum
      (s := Finset.range d) (f := fun _ => E) (g := fun t => f (t*W))
      (fun t ht' => (hall _ (ht _ (Finset.mem_range.mp ht'))).le)
      ⟨0, Finset.mem_range.mpr hd, by simpa using hhi⟩
    omega

end TorusWindow

theorem OMA.disproof : ¬ (type_of% @OMA.S_oeis_a306779.main) := by
  intro h
  have hloop := (h 4368 1760 (by decide) (by decide)).2 (Or.inr (by decide))
  exact OMA.S_oeis_a306779.no_full_loop TorusWindow.balanced_window hloop
