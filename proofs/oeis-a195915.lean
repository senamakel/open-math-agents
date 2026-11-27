import OMAStatements.S_oeis_a195915

namespace OMA.S_oeis_a195915

/-- The first XOR difference of a sequence. -/
def deltaOp (f : ℕ → ℕ) : ℕ → ℕ := fun n => Nat.xor (f (n + 1)) (f n)

/-- The XOR difference between values separated by `d`. -/
def jump (d : ℕ) (f : ℕ → ℕ) : ℕ → ℕ := fun n => Nat.xor (f (n + d)) (f n)

private theorem xor_cancel_middle (a b c : ℕ) :
    Nat.xor (Nat.xor a b) (Nat.xor b c) = Nat.xor a c := by
  simp [Nat.xor_comm, Nat.xor_left_comm]

/-- Composing a step-`d` XOR jump with itself doubles its step. -/
theorem jump_comp_self (d : ℕ) (f : ℕ → ℕ) :
    jump d (jump d f) = jump (d + d) f := by
  funext n
  simp [jump, Nat.add_assoc, Nat.xor_comm, Nat.xor_left_comm]

private theorem deltaOp_iterate_zero (m : ℕ) :
    deltaOp^[m] (fun _ : ℕ => 0) = (fun _ : ℕ => 0) := by
  induction m with
  | zero => rfl
  | succ m ih =>
      rw [Function.iterate_succ_apply]
      have hzero : deltaOp (fun _ : ℕ => 0) = (fun _ : ℕ => 0) := by
        funext n
        simp [deltaOp]
      rw [hzero]
      exact ih

/-- At a power-of-two iterate, the iterated difference is just the endpoint XOR. -/
theorem deltaOp_iterate_pow_two (f : ℕ → ℕ) (j : ℕ) :
    deltaOp^[2^j] f = jump (2^j) f := by
  induction j generalizing f with
  | zero =>
      funext n
      simp [deltaOp, jump]
  | succ j ih =>
      have hp : 2 ^ (j + 1) = 2 ^ j + 2 ^ j := by
        simp [pow_succ]
        omega
      rw [hp, Function.iterate_add_apply]
      calc
        deltaOp^[2 ^ j] (deltaOp^[2 ^ j] f) =
            jump (2 ^ j) (jump (2 ^ j) f) := by rw [ih, ih]
        _ = jump (2 ^ j + 2 ^ j) f := jump_comp_self _ _

/-- If an iterate of the XOR difference vanishes, all later iterates vanish too. -/
theorem deltaOp_iterate_eq_zero_of_le {f : ℕ → ℕ} {k j : ℕ}
    (hzero : deltaOp^[k] f = (fun _ : ℕ => 0)) (hk : k ≤ 2^j) :
    ∀ n, f (n + 2^j) = f n := by
  have hsum : (2^j - k) + k = 2^j := by omega
  have hpow : deltaOp^[2^j] f = (fun _ : ℕ => 0) := by
    rw [← hsum, Function.iterate_add_apply, hzero]
    exact deltaOp_iterate_zero _
  have hjump : jump (2^j) f = (fun _ : ℕ => 0) := by
    rw [← deltaOp_iterate_pow_two]
    exact hpow
  intro n
  have h := congrFun hjump n
  simpa [jump, Nat.xor_eq_zero_iff] using h

end OMA.S_oeis_a195915

namespace OMA.S_oeis_a195915

/-- The ray at distance `k` from the left edge of the XOR triangle. -/
def ray (k d : ℕ) : ℕ := entry (k + d) d

/-- The forward shift on sequences. -/
def shift (f : ℕ → ℕ) : ℕ → ℕ := fun d => f (d + 1)

/-- The XOR finite-difference operator. -/
def delta (f : ℕ → ℕ) : ℕ → ℕ := fun d => Nat.xor (f (d + 1)) (f d)

/-- Entries strictly above the diagonal vanish. -/
theorem entry_eq_zero_of_le (n k : ℕ) (hk : n ≤ k) : entry n k = 0 := by
  induction n generalizing k with
  | zero => rfl
  | succ n ih =>
      cases k with
      | zero => omega
      | succ k =>
          simp only [entry]
          rw [ih k (by omega), ih (k + 1) (by omega)]
          simp

/-- The zeroth ray is zero, since it lies outside the triangle. -/
theorem ray_zero : ray 0 = 0 := by
  funext d
  simp only [ray, Nat.zero_add]
  exact entry_eq_zero_of_le d d le_rfl

theorem entry_succ_col (n k : ℕ) :
    entry (n + 1) (k + 1) = Nat.xor (entry n k) (entry n (k + 1)) := by
  rfl

/-- Taking one XOR difference of the next ray gives the shift of this ray. -/
theorem delta_ray_succ (k : ℕ) : delta (ray (k + 1)) = shift (ray k) := by
  funext d
  simp only [delta, ray, shift]
  have h1 : k + 1 + (d + 1) = (k + d + 1) + 1 := by omega
  have h2 : k + 1 + d = k + d + 1 := by omega
  have h3 : k + (d + 1) = k + d + 1 := by omega
  rw [h1, h2, h3, entry_succ_col]
  simp

end OMA.S_oeis_a195915
namespace OMA.S_oeis_a195915

theorem from_ray_period
    (period : ∀ j s : ℕ, s ≤ 2^j → ∀ d : ℕ,
      entry (s+(d+2^j)) (d+2^j) = entry (s+d) d) :
    type_of% @main := by
  intro j n k hk hn
  have h := period j (n-k) (by omega) k
  rw [show n-k+(k+2^j)=2^j+n by omega,
    show k+2^j=2^j+k by omega, show n-k+k=n by omega] at h
  exact h


end OMA.S_oeis_a195915
namespace OMA.S_oeis_a195915

open Function

private theorem deltaOp_shift (f : ℕ → ℕ) : deltaOp (shift f) = shift (deltaOp f) := by
  rfl

private theorem iter_shift (m : ℕ) (f : ℕ → ℕ) :
    (deltaOp^[m]) (shift f) = shift ((deltaOp^[m]) f) := by
  induction m generalizing f with
  | zero => rfl
  | succ m ih =>
    rw [Function.iterate_succ_apply, Function.iterate_succ_apply, deltaOp_shift, ih]

private theorem ray_iter_zero (s : ℕ) : (deltaOp^[s]) (ray s) = (fun _ => 0) := by
  induction s with
  | zero => exact ray_zero
  | succ s ih =>
    rw [Function.iterate_succ_apply]
    have h : deltaOp (ray (s+1)) = shift (ray s) := delta_ray_succ s
    rw [h, iter_shift, ih]
    rfl

end OMA.S_oeis_a195915

theorem OMA.solution : type_of% @OMA.S_oeis_a195915.main := by
  open OMA.S_oeis_a195915 in
  apply from_ray_period
  intro j s hs d
  exact deltaOp_iterate_eq_zero_of_le (j := j) (ray_iter_zero s) hs d
