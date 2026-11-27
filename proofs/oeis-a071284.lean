import OMAStatements.S_oeis_a071284

namespace OMA.S_oeis_a071284

theorem expandStream_period {n : Nat} (hn : 0 < n) (old : Nat → Symbol)
    (hold : ∀ i, old (i + n * (n + 1)) = old i) (i : Nat) :
    expandStream n old (i + (n + 1) * (n + 2)) = expandStream n old i := by
  have hmod : (i + (n + 1) * (n + 2)) % (n + 2) = i % (n + 2) := by
    exact Nat.add_mul_mod_self_right i (n + 1) (n + 2)
  have hdiv : (i + (n + 1) * (n + 2)) / (n + 2) = i / (n + 2) + (n + 1) := by
    exact Nat.add_mul_div_right i (n + 1) (z := n + 2) (by omega)
  have hjmod (q : Nat) : (((q + n + 2) * n) % 2) = (((q + 1) * n) % 2) := by
    have heven : Even (n * (n + 1)) := Nat.even_mul_succ_self n
    rcases heven with ⟨k, hk⟩
    have harith : (q + n + 2) * n = (q + 1) * n + 2 * k := by
      calc
        (q + n + 2) * n = (q + 1) * n + n * (n + 1) := by ring
        _ = (q + 1) * n + (k + k) := by rw [hk]
        _ = (q + 1) * n + 2 * k := by omega
    rw [harith]
    exact Nat.add_mul_mod_self_left ((q + 1) * n) 2 k
  have holdCopied (q r : Nat) :
      old ((q + n + 1) * n + r) = old (q * n + r) := by
    have hidx : (q + n + 1) * n + r = (q * n + r) + n * (n + 1) := by ring
    rw [hidx]
    exact hold _
  have holdLast (q : Nat) :
      old ((q + n + 2) * n - 1) = old ((q + 1) * n - 1) := by
    have hj : (q + n + 2) * n = (q + 1) * n + n * (n + 1) := by ring
    have hpos : 0 < (q + 1) * n := by positivity
    rw [hj]
    have hidx : (q + 1) * n + n * (n + 1) - 1 = ((q + 1) * n - 1) + n * (n + 1) := by omega
    rw [hidx]
    exact hold _
  have hq' : i / (n + 2) + (n + 1) + 1 = i / (n + 2) + n + 2 := by omega
  by_cases hfirst : i % (n + 2) + 1 < n
  · simp [expandStream, hdiv, hmod, hfirst]
    exact holdCopied (i / (n + 2)) (i % (n + 2))
  · by_cases hsecond : i % (n + 2) + 1 = n
    · have hpar := hjmod (i / (n + 2))
      have hlast := holdLast (i / (n + 2))
      simp [expandStream, hdiv, hmod, hsecond, hq', hpar, hlast]
    · by_cases hthird : i % (n + 2) = n
      · have hpar := hjmod (i / (n + 2))
        simp [expandStream, hdiv, hmod, hthird, hq', hpar]
      · simp [expandStream, hdiv, hmod, hfirst, hsecond, hthird, hq']
        exact holdLast (i / (n + 2))

theorem peirce_period : ∀ n i, peirce n (i + n * (n + 1)) = peirce n i
  | 0, i => by simp [peirce]
  | 1, i => by
      simp [peirce]

  | n + 2, i => by
      have hOld : ∀ j, peirce (n + 1) (j + (n + 1) * (n + 2)) = peirce (n + 1) j :=
        peirce_period (n + 1)
      simpa [peirce] using
        (expandStream_period (n := n + 1) (by omega) (peirce (n + 1)) hOld i)

theorem denominator_period (n : Nat) (i : Nat) :
    denominatorAt n (i + n * (n + 1) / 2) = denominatorAt n i := by
  have heven : Even (n * (n + 1)) := Nat.even_mul_succ_self n
  rcases heven with ⟨k, hk⟩
  have hperiod : 2 * (n * (n + 1) / 2) = n * (n + 1) := by omega
  unfold denominatorAt
  rw [show 2 * (i + n * (n + 1) / 2) = 2 * i + n * (n + 1) by omega]
  rw [peirce_period]


private theorem denominator_mod (n i : ℕ) :
    denominatorAt n i = denominatorAt n (i % (n*(n+1)/2)) := by
  let p := n*(n+1)/2
  have hshift (j k : ℕ) : denominatorAt n (j + p*k) = denominatorAt n j := by
    induction k with
    | zero => simp
    | succ k ih =>
      rw [Nat.mul_succ, ← Nat.add_assoc, denominator_period n, ih]
  have h := hshift (i%p) (i/p)
  rwa [Nat.mod_add_div] at h

private theorem prove_main : ∀ i : ℕ, denominatorAt 4 i = ([2, 4, 3, 1, 4, 3, 4, 2, 3, 4] : List ℕ)[i % 10]! := by
  intro i
  have hsmall : ∀ j : Fin 10,
      denominatorAt 4 j = ([2, 4, 3, 1, 4, 3, 4, 2, 3, 4] : List ℕ)[j.val]! := by decide
  rw [denominator_mod 4 i]
  exact hsmall ⟨i % 10, Nat.mod_lt _ (by decide)⟩

end OMA.S_oeis_a071284

theorem OMA.solution : type_of% @OMA.S_oeis_a071284.main :=
  OMA.S_oeis_a071284.prove_main
