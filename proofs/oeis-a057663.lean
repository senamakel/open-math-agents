import OMAStatements.S_oeis_a057663

import Mathlib

/-! The missing residues of a composite modulus rule out the totient identity. -/

open Finset

theorem totient_prime_deficit (n d : ℕ) (hd : d.Prime) (hdiv : d ∣ n) :
    n.totient + n / d ≤ n := by
  let A := (Finset.range n).filter (fun m => n.Coprime m)
  let B := (Finset.range n).filter (fun m => ¬ n.Coprime m)
  have hbad : n / d ≤ B.card := by
    rw [← Finset.card_range (n / d)]
    apply Finset.card_le_card_of_injOn (fun j => d * j)
    · intro j hj
      have hj' : j < n / d := Finset.mem_range.mp hj
      have hb := Nat.mul_lt_mul_of_pos_left hj' hd.pos
      rw [Nat.mul_div_cancel' hdiv] at hb
      apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_range.mpr hb, ?_⟩
      intro hcp
      have hg : d ∣ n.gcd (d * j) := Nat.dvd_gcd hdiv (dvd_mul_right d j)
      change n.gcd (d * j) = 1 at hcp
      rw [hcp] at hg
      exact hd.ne_one (Nat.dvd_one.mp hg)
    · intro a _ b _ hab
      exact Nat.mul_left_cancel hd.pos hab
  have hcards : A.card + B.card = n := by
    simpa only [A, B, Finset.card_range] using
      (Finset.card_filter_add_card_filter_not (s := Finset.range n) (fun m => n.Coprime m))
  change A.card + n / d ≤ n
  omega
theorem totient_input_le (k : ℕ) : k ^ 2 ≤ k + 2 ^ k := by
  have step (n : ℕ) : (n + 2) * (n + 3) ≤ 2 ^ (n + 3) := by
    induction n with
    | zero => norm_num
    | succ n ih =>
      rw [show n + 1 + 3 = n + 3 + 1 by omega, pow_succ]
      calc
        (n + 1 + 2) * (n + 1 + 3) ≤ (n + 2) * (n + 3) * 2 := by nlinarith
        _ ≤ _ := Nat.mul_le_mul_right 2 ih
  by_cases h : k < 3
  · interval_cases k <;> decide
  obtain ⟨n, rfl⟩ := Nat.exists_eq_add_of_le (show 3 ≤ k by omega)
  have he := step n
  rw [Nat.add_comm 3 n]
  nlinarith

theorem totient_equiv_of_deficit
    (deficit : ∀ n d : ℕ, d.Prime → d ∣ n → n.totient + n / d ≤ n) :
    ∀ k : ℕ, 1 ≤ k →
      ((k + 2^k).totient = k.totient + 2^k ↔ k.Prime ∧ (k + 2^k).Prime) := by
  intro k hk
  let N := k + 2^k
  have hN : 1 < N := by
    have hpow : 1 < (2 : ℕ)^k := one_lt_pow₀ (by decide) (by omega)
    omega
  change N.totient = k.totient + 2^k ↔ k.Prime ∧ N.Prime
  constructor
  · intro h
    have hNP : N.Prime := by
      by_contra nh
      let d := N.minFac
      have hd : d.Prime := Nat.minFac_prime (by omega)
      have hddvd : d ∣ N := Nat.minFac_dvd _
      have hprod : d * (N / d) = N := Nat.mul_div_cancel' hddvd
      have hdsq : d ^ 2 ≤ N := Nat.minFac_sq_le_self (by omega) nh
      have hq : k ≤ N / d := by
        have hdle : d ≤ N / d := by
          by_contra! hb
          nlinarith [Nat.mul_lt_mul_of_pos_left hb hd.pos]
        have hkN : k ^ 2 ≤ N := totient_input_le k
        by_contra! hh
        have hm := Nat.mul_le_mul_right (N / d) hdle
        have hs := Nat.mul_lt_mul_of_pos_left hh (show 0 < k by omega)
        have hs' := Nat.mul_le_mul_right (N / d) (Nat.le_of_lt hh)
        nlinarith
      have hb := deficit N d hd hddvd
      have ht := Nat.totient_pos.mpr (show 0 < k by omega)
      rw [h] at hb
      omega
    have ht := Nat.totient_prime hNP
    have hkt : k.totient = k - 1 := by omega
    exact ⟨(Nat.totient_eq_iff_prime (by omega)).mp hkt, hNP⟩
  · rintro ⟨hkp, hNP⟩
    rw [Nat.totient_prime hkp, Nat.totient_prime hNP]
    omega

theorem OMA.solution : type_of% @OMA.S_oeis_a057663.main :=

  totient_equiv_of_deficit totient_prime_deficit
