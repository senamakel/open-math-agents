import OMAStatements.S_oeis_a110166

namespace KaryWords

open Finset PowerSeries

private noncomputable def invOneAdd : PowerSeries ℤ :=
  PowerSeries.rescale (-1 : ℤ) (PowerSeries.invOneSubPow ℤ 1).val

noncomputable def countingSeries (k : ℕ) : PowerSeries ℤ :=
  C (k : ℤ) * X + invOneAdd

def centralSum (k n : ℕ) : ℤ :=
  ∑ j ∈ range (n+1), (n.choose j : ℤ) * (k : ℤ) ^ (n-j) *
    ((-1 : ℤ) ^ j * ((2*j).choose j : ℤ))

private theorem invOneSubPow_one_pow (j : ℕ) :
    ((invOneSubPow ℤ 1).val : PowerSeries ℤ) ^ j = (invOneSubPow ℤ j).val := by
  induction j with
  | zero => simp [invOneSubPow_zero]
  | succ j ih =>
    rw [pow_succ, ih, invOneSubPow_add, Units.val_mul]

private theorem coeff_invOneAdd_pow (j : ℕ) (h : 0 < j) :
    coeff j (invOneAdd ^ j) =
      (-1 : ℤ) ^ j * (((j-1+j).choose (j-1) : ℕ) : ℤ) := by
  rw [invOneAdd, ← map_pow, invOneSubPow_one_pow, coeff_rescale,
    invOneSubPow_val_eq_mk_sub_one_add_choose_of_pos ℤ j h, coeff_mk]

private theorem central_choose_twice (j : ℕ) (hj : 0 < j) :
    (2*j).choose j = 2 * (j-1+j).choose (j-1) := by
  obtain ⟨j,rfl⟩ := Nat.exists_eq_succ_of_ne_zero hj.ne'
  simp only [Nat.succ_sub_one]
  rw [show 2 * (j+1) = (j+(j+1)) + 1 by omega, Nat.choose_succ_succ]
  have hs : (j + (j+1)).choose (j+1) = (j+(j+1)).choose j := by
    rw [← Nat.choose_symm (show j+1 ≤ j+(j+1) by omega)]
    congr 1
    omega
  rw [hs, two_mul]

theorem coeff_twice (k n : ℕ) :
    2 * coeff n (countingSeries k ^ n) = (k : ℤ)^n + centralSum k n := by
  rw [countingSeries, add_comm, add_pow, map_sum, Finset.mul_sum]
  unfold centralSum
  have hdelta : (∑ j ∈ range (n+1), if j = 0 then (k : ℤ)^n else 0) =
      (k : ℤ)^n := by
    rw [Finset.sum_eq_single 0]
    · simp
    · intro b _ hb
      simp [hb]
    · simp
  rw [← hdelta, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro j hj
  have hjn : j ≤ n := by simpa using Finset.mem_range.mp hj
  rw [mul_pow, ← map_pow]
  have hreorder : invOneAdd ^ j * (C ((k : ℤ) ^ (n-j)) * X ^ (n-j)) *
      (n.choose j : PowerSeries ℤ) =
      C ((n.choose j : ℤ) * (k : ℤ) ^ (n-j)) * (invOneAdd ^ j * X ^ (n-j)) := by
    simp only [map_mul, map_natCast]
    ring
  rw [hreorder, coeff_C_mul]
  have hshift : coeff n (invOneAdd ^ j * X ^ (n-j)) = coeff j (invOneAdd ^ j) := by
    rw [coeff_mul_X_pow']
    simp [show n-j ≤ n by omega, show n-(n-j)=j by omega]
  rw [hshift]
  by_cases hj0 : j = 0
  · subst j
    simp [two_mul]
  · rw [if_neg hj0, zero_add, coeff_invOneAdd_pow j (Nat.pos_of_ne_zero hj0),
      central_choose_twice j (Nat.pos_of_ne_zero hj0)]
    push_cast
    ring


end KaryWords

namespace KaryDerivative

open Polynomial

noncomputable def P (s : ℤ) : Polynomial ℤ := X^2 + C s * X + 1
noncomputable def mid (s : ℤ) (n : ℕ) : ℤ := (P s ^ n).coeff n
noncomputable def upper (s : ℤ) (n : ℕ) : ℤ := (P s ^ n).coeff (n+1)

private theorem derivative_P (s : ℤ) : derivative (P s) = C 2 * X + C s := by
  simp [P]

private theorem derivative_expanded (s : ℤ) (n : ℕ) :
    derivative (P s ^ (n+1)) =
      C ((n : ℤ)+1) * (C 2 * (X * P s ^ n) + C s * P s ^ n) := by
  rw [derivative_pow_succ, derivative_P]
  push_cast
  ring

private theorem middle_step (s : ℤ) (n : ℕ) :
    mid s (n+1) = s * mid s n + 2 * upper s n := by
  let t := (X * P s ^ n).coeff n
  have hder := congrArg (fun f : Polynomial ℤ => f.coeff n) (derivative_expanded s n)
  have hd : ((n : ℤ)+1) * mid s (n+1) = ((n : ℤ)+1) * (2*t+s*mid s n) := by
    simpa only [coeff_derivative, coeff_C_mul, coeff_add, Nat.cast_add, Nat.cast_one,
      mid, t, mul_comm ((P s ^ (n+1)).coeff (n+1))] using hder
  have hd' : mid s (n+1) = 2*t+s*mid s n :=
    mul_left_cancel₀ (by omega : (n : ℤ)+1 ≠ 0) hd
  have hprod : P s ^ (n+1) =
      X * (X * P s ^ n) + C s * (X * P s ^ n) + P s ^ n := by
    calc
      P s ^ (n+1) = (X^2 + C s * X + 1) * P s ^ n := by
        rw [← P, pow_succ']
      _ = _ := by ring
  have hmid : mid s (n+1) = t + s * mid s n + upper s n := by
    simp [mid, upper, hprod, t, coeff_X_mul]
  omega

private theorem upper_step (s : ℤ) (n : ℕ) :
    ((n : ℤ)+2)*upper s (n+1) =
      ((n : ℤ)+1)*(2*mid s n+s*upper s n) := by
  have hder := congrArg (fun f : Polynomial ℤ => f.coeff (n+1)) (derivative_expanded s n)
  simp only [coeff_derivative, coeff_C_mul, coeff_add, coeff_X_mul, Nat.cast_add,
    Nat.cast_one] at hder
  simp only [mid, upper]
  convert hder using 1 <;> ring

theorem middleRecurrence (s : ℤ) (n : ℕ) :
    ((n : ℤ)+2)*mid s (n+2) =
      s*(2*(n : ℤ)+3)*mid s (n+1) + (4-s^2)*((n : ℤ)+1)*mid s n := by
  have h₀ := middle_step s n
  have h₁ := middle_step s (n+1)
  have hu := upper_step s n
  linear_combination ((n : ℤ)+2)*h₁ + 2*hu - s*((n : ℤ)+1)*h₀


end KaryDerivative
namespace KaryWords

open Polynomial Finset

noncomputable def tiePoly (k : ℕ) : Polynomial ℤ :=
  X^2 + C ((k : ℤ)-2) * X + 1

theorem tiePoly_coeff (k n : ℕ) :
    (tiePoly k ^ n).coeff n = centralSum k n := by
  have hp : tiePoly k = ((X : Polynomial ℤ) + C (-1)) ^ 2 + C (k : ℤ) * X := by
    rw [tiePoly, map_sub]
    simp
    ring
  rw [hp, add_pow, finsetSum_coeff, centralSum]
  apply sum_congr rfl
  intro j hj
  have hjn : j ≤ n := Nat.le_of_lt_succ (mem_range.mp hj)
  rw [mul_pow, ← map_pow, ← pow_mul]
  have ht :
      (X + C (-1 : ℤ)) ^ (2*j) * (C ((k : ℤ)^(n-j)) * X^(n-j)) *
        (n.choose j : Polynomial ℤ) =
      C ((n.choose j : ℤ)*(k : ℤ)^(n-j)) *
        ((X + C (-1 : ℤ))^(2*j) * X^(n-j)) := by
    simp only [map_mul, map_natCast]
    ring
  rw [ht, coeff_C_mul, coeff_mul_X_pow']
  simp only [show n-j ≤ n by omega, if_pos, show n-(n-j)=j by omega]
  rw [coeff_X_add_C_pow]
  rw [show 2*j-j=j by omega]


end KaryWords
namespace KaryWords

theorem recurrence_of_tie_count (u : ℕ → ℕ) (k : ℕ) (hk : 2 ≤ k)
    (hcount : ∀ n, 2 * (u n : ℤ) = (k : ℤ)^n + centralSum k n)
    (hrec : ∀ n : ℕ, ((n : ℤ) + 2) * centralSum k (n+2) =
      ((k : ℤ)-2) * (2*(n : ℤ)+3) * centralSum k (n+1) -
      (k : ℤ)*((k : ℤ)-4)*((n : ℤ)+1)*centralSum k n) :
    (∀ n, (u n : ℤ) = PowerSeries.coeff n (countingSeries k ^ n)) ∧
      u 0 = 1 ∧ u 1 = k-1 ∧
      (∀ n : ℕ, ((n : ℤ)+2) * (u (n+2) : ℤ) =
      ((k : ℤ)-2)*(2*(n : ℤ)+3)*(u (n+1) : ℤ) -
        (k : ℤ)*((k : ℤ)-4)*((n : ℤ)+1)*(u n : ℤ) + (k : ℤ)^(n+1)) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro n
    have ha := hcount n
    have hb := coeff_twice k n
    omega
  · have h := hcount 0
    norm_num [centralSum] at h
    omega
  · have h := hcount 1
    norm_num [centralSum, Finset.sum_range_succ] at h
    omega
  · intro n
    have h₀ := hcount n
    have h₁ := hcount (n+1)
    have h₂ := hcount (n+2)
    have hr := hrec n
    have hlinear : ((n : ℤ)+2) * (k : ℤ)^(n+2) =
        ((k : ℤ)-2)*(2*(n : ℤ)+3)*(k : ℤ)^(n+1) -
          (k : ℤ)*((k : ℤ)-4)*((n : ℤ)+1)*(k : ℤ)^n + 2*(k : ℤ)^(n+1) := by
      rw [show n+2=(n+1)+1 by omega, pow_succ _ (n+1), pow_succ _ n]
      ring
    have ht : 2 * (((n : ℤ)+2) * (u (n+2) : ℤ)) =
        2 * (((k : ℤ)-2)*(2*(n : ℤ)+3)*(u (n+1) : ℤ) -
          (k : ℤ)*((k : ℤ)-4)*((n : ℤ)+1)*(u n : ℤ) + (k : ℤ)^(n+1)) := by
      linear_combination ((n : ℤ)+2)*h₂ -
        ((k : ℤ)-2)*(2*(n : ℤ)+3)*h₁ +
        (k : ℤ)*((k : ℤ)-4)*((n : ℤ)+1)*h₀ + hr + hlinear
    omega


end KaryWords
namespace KaryWords

theorem centralRecurrence (k n : ℕ) :
    ((n : ℤ) + 2) * centralSum k (n+2) =
      ((k : ℤ)-2) * (2*(n : ℤ)+3) * centralSum k (n+1) -
      (k : ℤ)*((k : ℤ)-4)*((n : ℤ)+1)*centralSum k n := by
  have h (m : ℕ) : KaryDerivative.mid ((k : ℤ)-2) m = centralSum k m :=
    tiePoly_coeff k m
  have hrec := KaryDerivative.middleRecurrence ((k : ℤ)-2) n
  simp only [h] at hrec
  linear_combination hrec

end KaryWords

theorem OMA.fromTieCount
    (hcount : ∀ k : ℕ, 2 ≤ k → ∀ n : ℕ,
      2 * (OMA.S_oeis_a110166.wordCount k n : ℤ) = (k : ℤ)^n + KaryWords.centralSum k n) :
    type_of% @OMA.S_oeis_a110166.main := by
  intro k hk
  exact KaryWords.recurrence_of_tie_count (OMA.S_oeis_a110166.wordCount k) k hk
    (hcount k hk) (KaryWords.centralRecurrence k)


open Finset

namespace OMA.S_oeis_a110166.Words

/-- Number of occurrences of a digit in a word. -/
def occurrences {k n : ℕ} (w : Fin n → Fin k) (i : ℕ) : ℕ :=
  (Finset.univ.filter (fun j => (w j).val = i)).card

/-- Number of k-ary words of length n with no more ones than zeros. -/
def wordCount (k n : ℕ) : ℕ :=
  (Finset.univ.filter (fun w : Fin n → Fin k => occurrences w 1 ≤ occurrences w 0)).card

/-- Number of k-ary words of length n with the same number of zeros and ones. -/
def tieCount (k n : ℕ) : ℕ :=
  (Finset.univ.filter (fun w : Fin n → Fin k => occurrences w 0 = occurrences w 1)).card

/-- Interchange the two distinguished digits and leave every other digit fixed. -/
def swapDigit (k : ℕ) (hk : 2 ≤ k) (a : Fin k) : Fin k :=
  if ha : a.val = 0 then ⟨1, by omega⟩
  else if ha : a.val = 1 then ⟨0, by omega⟩
  else a

private def digitZero (k : ℕ) (hk : 2 ≤ k) : Fin k := ⟨0, by omega⟩
private def digitOne (k : ℕ) (hk : 2 ≤ k) : Fin k := ⟨1, by omega⟩

theorem swapDigit_zero (k : ℕ) (hk : 2 ≤ k) :
    swapDigit k hk (digitZero k hk) = digitOne k hk := by
  apply Fin.ext
  simp [swapDigit, digitZero, digitOne]

theorem swapDigit_one (k : ℕ) (hk : 2 ≤ k) :
    swapDigit k hk (digitOne k hk) = digitZero k hk := by
  apply Fin.ext
  simp [swapDigit, digitZero, digitOne]

theorem swapDigit_involutive (k : ℕ) (hk : 2 ≤ k) (a : Fin k) :
    swapDigit k hk (swapDigit k hk a) = a := by
  by_cases h0 : a.val = 0
  · have ha : a = digitZero k hk := Fin.ext (by simpa [digitZero] using h0)
    rw [ha, swapDigit_zero, swapDigit_one]
  · by_cases h1 : a.val = 1
    · have ha : a = digitOne k hk := Fin.ext (by simpa [digitOne] using h1)
      rw [ha, swapDigit_one, swapDigit_zero]
    · simp [swapDigit, h0, h1]

def swapWord {k n : ℕ} (hk : 2 ≤ k) (w : Fin n → Fin k) : Fin n → Fin k :=
  fun i => swapDigit k hk (w i)

theorem swapWord_involutive {k n : ℕ} (hk : 2 ≤ k) (w : Fin n → Fin k) :
    swapWord hk (swapWord hk w) = w := by
  funext i
  exact swapDigit_involutive k hk (w i)

theorem swapDigit_eq_zero_iff (k : ℕ) (hk : 2 ≤ k) (a : Fin k) :
    swapDigit k hk a = digitZero k hk ↔ a = digitOne k hk := by
  constructor
  · intro h
    have h' := congrArg (swapDigit k hk) h
    rw [swapDigit_involutive, swapDigit_zero] at h'
    exact h'
  · rintro rfl
    exact swapDigit_one k hk

theorem swapDigit_eq_one_iff (k : ℕ) (hk : 2 ≤ k) (a : Fin k) :
    swapDigit k hk a = digitOne k hk ↔ a = digitZero k hk := by
  constructor
  · intro h
    have h' := congrArg (swapDigit k hk) h
    rw [swapDigit_involutive, swapDigit_one] at h'
    exact h'
  · rintro rfl
    exact swapDigit_zero k hk

theorem occurrences_swap_zero {k n : ℕ} (hk : 2 ≤ k) (w : Fin n → Fin k) :
    occurrences (swapWord hk w) 0 = occurrences w 1 := by
  unfold occurrences
  congr 1
  ext i
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  change (swapDigit k hk (w i)).val = 0 ↔ (w i).val = 1
  have hzero : (swapDigit k hk (w i)).val = 0 ↔
      swapDigit k hk (w i) = digitZero k hk := by
    constructor
    · intro h
      exact Fin.ext (by simpa [digitZero] using h)
    · intro h
      exact congrArg Fin.val h
  have hone : (w i).val = 1 ↔ w i = digitOne k hk := by
    constructor
    · intro h
      exact Fin.ext (by simpa [digitOne] using h)
    · intro h
      exact congrArg Fin.val h
  rw [hzero, swapDigit_eq_zero_iff, hone]

theorem occurrences_swap_one {k n : ℕ} (hk : 2 ≤ k) (w : Fin n → Fin k) :
    occurrences (swapWord hk w) 1 = occurrences w 0 := by
  unfold occurrences
  congr 1
  ext i
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  change (swapDigit k hk (w i)).val = 1 ↔ (w i).val = 0
  have hone : (swapDigit k hk (w i)).val = 1 ↔
      swapDigit k hk (w i) = digitOne k hk := by
    constructor
    · intro h
      exact Fin.ext (by simpa [digitOne] using h)
    · intro h
      exact congrArg Fin.val h
  have hzero : (w i).val = 0 ↔ w i = digitZero k hk := by
    constructor
    · intro h
      exact Fin.ext (by simpa [digitZero] using h)
    · intro h
      exact congrArg Fin.val h
  rw [hone, swapDigit_eq_one_iff, hzero]

private def fewer (k n : ℕ) : Finset (Fin n → Fin k) :=
  Finset.univ.filter (fun w => occurrences w 1 < occurrences w 0)

private def more (k n : ℕ) : Finset (Fin n → Fin k) :=
  Finset.univ.filter (fun w => occurrences w 0 < occurrences w 1)

private def tied (k n : ℕ) : Finset (Fin n → Fin k) :=
  Finset.univ.filter (fun w => occurrences w 0 = occurrences w 1)

private theorem fewer_card_eq_more_card (k n : ℕ) (hk : 2 ≤ k) :
    (fewer k n).card = (more k n).card := by
  apply le_antisymm
  · apply Finset.card_le_card_of_injOn (swapWord hk) (s := fewer k n) (t := more k n)
    · intro w hw
      have hw' : occurrences w 1 < occurrences w 0 := by simpa [fewer] using hw
      apply Finset.mem_filter.mpr
      constructor
      · exact Finset.mem_univ _
      · rw [occurrences_swap_zero, occurrences_swap_one]
        exact hw'
    · intro w hw v hv heq
      have := congrArg (swapWord hk) heq
      simpa [swapWord_involutive] using this
  · apply Finset.card_le_card_of_injOn (swapWord hk) (s := more k n) (t := fewer k n)
    · intro w hw
      have hw' : occurrences w 0 < occurrences w 1 := by simpa [more] using hw
      apply Finset.mem_filter.mpr
      constructor
      · exact Finset.mem_univ _
      · rw [occurrences_swap_zero, occurrences_swap_one]
        exact hw'
    · intro w hw v hv heq
      have := congrArg (swapWord hk) heq
      simpa [swapWord_involutive] using this

private theorem wordCount_eq_fewer_add_tied (k n : ℕ) :
    wordCount k n = (fewer k n).card + (tied k n).card := by
  classical
  let S : Finset (Fin n → Fin k) := Finset.univ.filter (fun w =>
    occurrences w 1 ≤ occurrences w 0)
  have hsplit := Finset.card_filter_add_card_filter_not
    (s := S) (p := fun w => occurrences w 1 < occurrences w 0)
  have hfirst : S.filter (fun w => occurrences w 1 < occurrences w 0) = fewer k n := by
    ext w
    simp [S, fewer, Finset.filter_filter]
    omega
  have hsecond : S.filter (fun w => ¬ occurrences w 1 < occurrences w 0) = tied k n := by
    ext w
    simp [S, tied, Finset.filter_filter]
    omega
  rw [hfirst, hsecond] at hsplit
  simpa [wordCount, S] using hsplit.symm

private theorem wordCount_add_more_eq_allWords (k n : ℕ) :
    wordCount k n + (more k n).card =
      (Finset.univ : Finset (Fin n → Fin k)).card := by
  classical
  have hsplit := Finset.card_filter_add_card_filter_not
    (s := (Finset.univ : Finset (Fin n → Fin k)))
    (p := fun w => occurrences w 1 ≤ occurrences w 0)
  have hneg : Finset.univ.filter (fun w : Fin n → Fin k =>
      ¬ occurrences w 1 ≤ occurrences w 0) = more k n := by
    ext w
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, more]
    omega
  rw [hneg] at hsplit
  simpa [wordCount] using hsplit

theorem twice_wordCount_eq_pow_add_tieCount (k n : ℕ) (hk : 2 ≤ k) :
    2 * wordCount k n = k ^ n + tieCount k n := by
  classical
  have hgood := wordCount_eq_fewer_add_tied k n
  have hall := wordCount_add_more_eq_allWords k n
  have hswap := fewer_card_eq_more_card k n hk
  have hcard : (Finset.univ : Finset (Fin n → Fin k)).card = k ^ n := by
    simp
  have htie : (tied k n).card = tieCount k n := rfl
  rw [hcard] at hall
  rw [hgood]
  nlinarith [htie]

end OMA.S_oeis_a110166.Words
namespace KaryWords

open Polynomial Finset
open OMA.S_oeis_a110166 (occurrences)

private def weight {k : ℕ} (a : Fin k) : ℕ :=
  if a.val = 0 then 2 else if a.val = 1 then 0 else 1

private theorem weight_sum {k n : ℕ} (w : Fin n → Fin k) :
    (∑ j : Fin n, weight (w j)) + occurrences w 1 = n + occurrences w 0 := by
  have h (a : Fin k) : weight a + (if a.val = 1 then 1 else 0) =
      1 + (if a.val = 0 then 1 else 0) := by
    unfold weight
    split <;> split <;> omega
  have hsum := Finset.sum_congr (s₁ := (Finset.univ : Finset (Fin n))) rfl (fun j _ => h (w j))
  simp only [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    nsmul_eq_mul, mul_one] at hsum
  simpa [occurrences, Finset.sum_ite] using hsum

private theorem alphabet_polynomial (k : ℕ) (hk : 2 ≤ k) :
    (∑ a : Fin k, (X : Polynomial ℤ) ^ weight a) = tiePoly k := by
  obtain ⟨r, rfl⟩ := Nat.exists_eq_add_of_le hk
  have e : 2+r = r+2 := by omega
  rw [e, Fin.sum_univ_succ, Fin.sum_univ_succ]
  simp [tiePoly, weight, Fin.val_succ]
  ring

private theorem mark_words (k n : ℕ) (hk : 2 ≤ k) :
    tiePoly k ^ n = ∑ w : Fin n → Fin k,
      (X : Polynomial ℤ) ^ (∑ j : Fin n, weight (w j)) := by
  rw [← alphabet_polynomial k hk]
  calc
    (∑ a : Fin k, (X : Polynomial ℤ)^weight a)^n =
        ∏ _j : Fin n, ∑ a : Fin k, (X : Polynomial ℤ)^weight a := by simp
    _ = _ := by
      rw [Fintype.prod_sum]
      simp only [Finset.prod_pow_eq_pow_sum]

theorem tie_count_eq_middle (k n : ℕ) (hk : 2 ≤ k) :
    ((Finset.univ.filter (fun w : Fin n → Fin k =>
      occurrences w 0 = occurrences w 1)).card : ℤ) = (tiePoly k ^ n).coeff n := by
  rw [mark_words k n hk, finsetSum_coeff]
  simp only [coeff_X_pow]
  have hi (w : Fin n → Fin k) :
      n = (∑ j : Fin n, weight (w j)) ↔ occurrences w 0 = occurrences w 1 := by
    have := weight_sum w
    omega
  simp_rw [hi]
  simp


end KaryWords

theorem OMA.solution : type_of% @OMA.S_oeis_a110166.main := by
  apply OMA.fromTieCount
  intro k hk n
  have hparity := OMA.S_oeis_a110166.Words.twice_wordCount_eq_pow_add_tieCount k n hk
  have h := congrArg (fun z : ℕ => (z : ℤ)) hparity
  push_cast at h
  change 2 * (OMA.S_oeis_a110166.wordCount k n : ℤ) =
    (k : ℤ)^n + ((Finset.univ.filter (fun w : Fin n → Fin k =>
      OMA.S_oeis_a110166.occurrences w 0 = OMA.S_oeis_a110166.occurrences w 1)).card : ℤ) at h
  rw [KaryWords.tie_count_eq_middle k n hk, KaryWords.tiePoly_coeff] at h
  exact h
