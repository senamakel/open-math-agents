import OMAStatements.S_oeis_a384309

namespace OMA.S_oeis_a384309

theorem leading_of_block (k : ℕ) (d : Digit) (r : ℕ) (hr : r < 10^k) :
    leading ((d.val + 1) * 10^k + r) = d := by
  have hpos : 0 < (10 : ℕ)^k := by positivity
  have hlow : 10 ^ k ≤ (d.val + 1) * 10 ^ k + r := by
    calc
      10 ^ k = 1 * 10 ^ k := by simp
      _ ≤ (d.val + 1) * 10 ^ k := Nat.mul_le_mul_right _ (by omega)
      _ ≤ _ := Nat.le_add_right _ _
  have hhigh : (d.val + 1) * 10 ^ k + r < 10 ^ (k + 1) := by
    calc
      (d.val + 1) * 10 ^ k + r < (d.val + 1) * 10 ^ k + 10^k :=
        Nat.add_lt_add_left hr _
      _ = (d.val + 2) * 10 ^ k := by ring
      _ ≤ 10 * 10 ^ k := Nat.mul_le_mul_right _ (by omega)
      _ = 10 ^ (k + 1) := by rw [pow_succ, Nat.mul_comm]
  apply Fin.ext
  change ((((d.val+1)*10^k+r) / 10^Nat.log 10 ((d.val+1)*10^k+r) - 1) % 9) = d.val
  rw [Nat.log_eq_of_pow_le_of_lt_pow hlow hhigh,
    Nat.add_comm, Nat.mul_comm (d.val+1), Nat.add_mul_div_left _ _ hpos, Nat.div_eq_of_lt hr,
    Nat.zero_add, Nat.add_sub_cancel, Nat.mod_eq_of_lt d.isLt]

end OMA.S_oeis_a384309
namespace OMA.S_oeis_a384309

def digitCount (d : Digit) (m : ℕ) : ℕ :=
  Nat.count (fun i => leading (i+1) = d) m

theorem prefix_decade (k : ℕ) (d : Digit) (j : ℕ) (hj : j ≤ 9) :
    digitCount d ((j + 1) * 10^k - 1) =
      digitCount d (10^k-1) + if d.val < j then 10^k else 0 := by
  induction j with
  | zero => simp
  | succ j ih =>
    have hj9 : j < 9 := by omega
    let q : Digit := ⟨j,hj9⟩
    have hpos : 0 < (10 : ℕ)^k := by positivity
    have hsplit : (j+1+1)*10^k-1 = ((j+1)*10^k-1)+10^k := by
      rw [Nat.add_mul]
      have hbase : 0 < (j+1)*10^k := by positivity
      omega
    rw [hsplit, digitCount, Nat.count_add, ← digitCount, ih (by omega)]
    have hblock : Nat.count (fun i => leading ((j+1)*10^k-1+i+1) = d) (10^k) =
        if q = d then 10^k else 0 := by
      have hbase : 0 < (j+1)*10^k := by positivity
      have hlead (i : ℕ) (hi : i < 10^k) :
          leading ((j+1)*10^k-1+i+1) = q := by
        rw [show (j+1)*10^k-1+i+1 = (j+1)*10^k+i by omega]
        exact leading_of_block k q i hi
      split_ifs with h
      · exact Nat.count_of_forall (fun i hi => (hlead i hi).trans h)
      · exact Nat.count_iff_forall_not.mpr (fun i hi he => h ((hlead i hi).symm.trans he))
    rw [hblock]
    by_cases hlt : d.val < j
    · have hne : q ≠ d := fun h => by
        have he := congrArg Fin.val h
        change j = d.val at he
        omega
      simp [hlt, show d.val < j+1 by omega, hne]
    · by_cases he : d.val = j
      · have heq : q = d := Fin.ext he.symm
        simp [hlt, show d.val < j+1 by omega, heq]
      · have hne : q ≠ d := fun h => he (congrArg Fin.val h).symm
        simp [hlt, show ¬ d.val < j+1 by omega, hne]

end OMA.S_oeis_a384309
namespace OMA.S_oeis_a384309

theorem decimal_count_uniform (k : ℕ) (d : Digit) :
    9 * digitCount d (10^k-1) = 10^k-1 := by
  induction k with
  | zero => simp [digitCount]
  | succ k ih =>
    rw [show 10 ^ (k + 1) = (9+1) * 10^k by rw [pow_succ]; ring,
      prefix_decade k d 9 (by decide)]
    simp only [d.isLt, if_true]
    have hpos : 0 < (10 : ℕ)^k := by positivity
    omega

def quota (B : ℕ) (d : Digit) : ℕ :=
  if d = 0 then 9*B else if d = 8 then B-1 else 2*B-1

theorem quota_sum (k : ℕ) :
    (∑ d : Digit, quota (10^k) d) = 24 * 10^k - 8 := by
  have hpos : 0 < (10 : ℕ)^k := by positivity
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, quota]
  norm_num [Fin.ext_iff, Fin.val_succ]
  omega

theorem quota_balance (k : ℕ) (d : Digit) :
    quota (10^k) d + (if d=8 then 1 else 0) =
      (if d=0 then 1 else 0) + ∑ v : Digit, digitCount d (quota (10^k) v) := by
  have hpos : 0 < (10 : ℕ)^k := by positivity
  have hu := decimal_count_uniform k d
  have h2 := prefix_decade k d 1 (by decide)
  have h9 := prefix_decade k d 8 (by decide)
  have h9head : leading (9*10^k) = (8 : Digit) := by
    simpa using leading_of_block k (8 : Digit) 0 hpos
  have h9step : digitCount d (9*10^k) =
      digitCount d (9*10^k-1) + if d=8 then 1 else 0 := by
    have h : 9*10^k-1+1=9*10^k := by omega
    unfold digitCount
    have hh := Nat.count_succ (p := fun i => leading (i+1) = d) (9*10^k-1)
    simpa only [h, h9head, show (8 : Digit) = d ↔ d = 8 from eq_comm] using hh
  have hsum :
      (∑ v : Digit, digitCount d (quota (10^k) v)) =
        digitCount d (9*10^k) + 7*digitCount d (2*10^k-1) +
          digitCount d (10^k-1) := by
    simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, quota]
    norm_num [Fin.ext_iff, Fin.val_succ]
    omega
  rw [hsum, h9step, h9, h2]
  by_cases hd0 : d=0
  · subst d
    norm_num [quota, Fin.ext_iff, Fin.val_succ]
    omega
  · by_cases hd8 : d=8
    · subst d
      norm_num [quota, Fin.ext_iff, Fin.val_succ] at hd0 ⊢
      omega
    · have hv0 : ¬ d.val < 1 := by
        intro h
        exact hd0 (Fin.ext (by simpa using (show d.val=0 by omega)))
      have hv8 : d.val < 8 := by
        by_contra! h
        exact hd8 (Fin.ext (show d.val=8 by omega))
      simp only [quota, hd0, hd8, hv0, hv8, if_true, if_false, add_zero]
      omega

end OMA.S_oeis_a384309
namespace OMA.S_oeis_a384309

theorem leading_one : leading 1 = (0 : Digit) := by decide

theorem state_count_sum (t : ℕ) : (∑ d : Digit, (state t).2 d) = t := by
  induction t with
  | zero => simp [state]
  | succ t ih =>
    simp only [state, Finset.sum_add_distrib, ih, Finset.sum_ite_eq', Finset.mem_univ, if_true]

theorem state_flow (t : ℕ) (d : Digit) :
    (state t).2 d + (if leading (state t).1=d then 1 else 0) =
      (if d=0 then 1 else 0) + ∑ v : Digit, digitCount d ((state t).2 v) := by
  induction t with
  | zero => simp [state, digitCount, leading_one, eq_comm]
  | succ t ih =>
    let h := leading (state t).1
    let c := (state t).2
    let nh := leading (c h + 1)
    change c d + (if d = h then 1 else 0) + (if nh=d then 1 else 0) =
      (if d=0 then 1 else 0) + ∑ v : Digit, digitCount d (c v + if v=h then 1 else 0)
    have hupdate (v : Digit) :
        digitCount d (c v + if v=h then 1 else 0) =
          digitCount d (c v) + if v=h then (if nh=d then 1 else 0) else 0 := by
      by_cases hv : v=h
      · subst v
        simp [digitCount, Nat.count_succ, nh]
      · simp [hv]
    simp only [hupdate, Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.mem_univ, if_true]
    change c d + (if h=d then 1 else 0) =
      (if d=0 then 1 else 0) + ∑ v : Digit, digitCount d (c v) at ih
    simp only [show d = h ↔ h = d from eq_comm]
    omega

end OMA.S_oeis_a384309
namespace OMA.S_oeis_a384309

theorem last_exit_of_0 (k : ℕ) : leading (quota (10^k) 0) = 8 := by
  have hp : 0 < (10 : ℕ)^k := by positivity
  simpa [quota] using leading_of_block k (8 : Digit) 0 hp

theorem last_exit_middle (k : ℕ) (d : Digit) (h0 : d ≠ 0) (h8 : d ≠ 8) :
    leading (quota (10^k) d) = 0 := by
  have hp : 0 < (10 : ℕ)^k := by positivity
  have h : 2*10^k-1 = 1*10^k + (10^k-1) := by omega
  have hr : (10 : ℕ)^k - 1 < 10^k := by omega
  have hl := leading_of_block k (0 : Digit) (10^k-1) hr
  change leading (1*10^k + (10^k-1)) = 0 at hl
  simpa only [quota, if_neg h0, if_neg h8, h] using hl

theorem quota_next_ge (k : ℕ) (d : Digit) :
    10^k ≤ quota (10^k) d + if d=8 then 1 else 0 := by
  have hp : 0 < (10 : ℕ)^k := by positivity
  by_cases h0 : d=0
  · subst d
    norm_num [quota]
    omega
  · by_cases h8 : d=8 <;> simp [quota, h0, h8] <;> omega

end OMA.S_oeis_a384309

namespace OMA.S_oeis_a384309

theorem last_exit_of_8 (k : ℕ) (hk : 0 < k) :
    leading (quota (10^k) 8) = 8 := by
  obtain ⟨j,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : k ≠ 0)
  have hp : 0 < (10 : ℕ)^j := by positivity
  have hr : (10 : ℕ)^j - 1 < 10^j := by omega
  have h : 10^(j+1)-1 = 9*10^j+(10^j-1) := by
    rw [pow_succ]
    omega
  have hq : quota (10^(j+1)) 8 = 10^(j+1)-1 := by
    simp [quota, Fin.ext_iff]
  rw [hq, h]
  exact leading_of_block j (8 : Digit) (10^j-1) hr

end OMA.S_oeis_a384309
namespace OMA.S_oeis_a384309

private theorem counter_mono (d : Digit) : Monotone fun t => (state t).2 d := by
  apply monotone_nat_of_le_succ
  intro t
  simp only [state]
  omega

theorem last_term_of_quota (k : ℕ) (hk : 0 < k)
    (hbound : ∀ t ≤ 24*10^k-8, ∀ d, (state t).2 d ≤ quota (10^k) d)
    (hreach : (state (24*10^k-8)).2 = quota (10^k))
    (hbefore : ∀ t < 24*10^k-8,
      (state t).2 (leading (state t).1) < quota (10^k) (leading (state t).1)) :
    entry (24*10^k-7)=10^k-1 ∧ ∀ n > 24*10^k-7, 10^k ≤ entry n := by
  let T := 24*10^k-8
  let B := 10^k
  have hB : 1 < B := by
    have : 10 ^ 1 ≤ 10 ^ k := Nat.pow_le_pow_right (by decide) hk
    dsimp [B]
    omega
  have hex : ∃ t, quota B 8 ≤ (state t).2 8 := ⟨T, by rw [hreach]⟩
  let u := Nat.find hex
  have hu : quota B 8 ≤ (state u).2 8 := Nat.find_spec hex
  have huT : u ≤ T := Nat.find_min' hex (by rw [hreach])
  have hu0 : u ≠ 0 := by
    intro he
    rw [he, state] at hu
    simp [quota, Fin.ext_iff] at hu
    omega
  obtain ⟨v,hv⟩ := Nat.exists_eq_succ_of_ne_zero hu0
  have hprev : (state v).2 8 < quota B 8 := by
    exact Nat.lt_of_not_ge (Nat.find_min hex (show v < u by omega))
  have hhead : leading (state v).1 = 8 := by
    by_contra hn
    have hne : (8 : Digit) ≠ leading (state v).1 := Ne.symm hn
    rw [hv, state] at hu
    simp [hne] at hu
    omega
  have hval : (state u).1 = quota B 8 := by
    have huEq : (state u).2 8 = quota B 8 := le_antisymm (hbound u huT 8) hu
    rw [hv, state] at huEq ⊢
    simpa [hhead] using huEq
  have hterminal : leading (state u).1 = 8 := by rw [hval]; exact last_exit_of_8 k hk
  have huEqT : u = T := by
    by_contra hne
    have hh := hbefore u (lt_of_le_of_ne huT hne)
    rw [hterminal] at hh
    exact (Nat.not_lt_of_ge hu) hh
  have hvalT : (state T).1 = B-1 := by
    rw [← huEqT, hval]
    simp [quota, Fin.ext_iff]
  have hheadT : leading (state T).1 = 8 := by rwa [← huEqT]
  have hreachT : (state T).2 = quota B := hreach
  have hindex : 24*10^k-7 = T+1 := by
    change 24*B-7 = (24*B-8)+1
    omega
  refine ⟨?_,?_⟩
  · simpa only [hindex, entry, Nat.add_sub_cancel] using hvalT
  · intro n hn
    have hn' : T+1 < n := hindex ▸ hn
    have hc (d : Digit) : B ≤ (state (T+1)).2 d := by
      simpa only [state, hreachT, hheadT] using quota_next_ge k d
    have hx : (state (T+1)).1 = B := by
      change (state T).2 (leading (state T).1) + 1 = B
      rw [hheadT, hreachT]
      unfold quota
      rw [if_neg (by decide : (8 : Digit) ≠ 0), if_pos rfl]
      omega
    by_cases he : n-1=T+1
    · simp [entry, he, hx, B]
    · have hge : T+1 ≤ n-2 := by omega
      rw [entry, show n-1=(n-2)+1 by omega, state]
      exact (hc _).trans ((counter_mono _ hge).trans (Nat.le_succ _))

end OMA.S_oeis_a384309

/-!
# A finite stack-walk stopping lemma

The flow equations for a prefix say that each vertex's used edges account for
its initial chip and incoming edges, less the current head.  This lemma is the
finite-vertex part of the last-exit argument: if the head has used its entire
quota, the residual flow forces the head to be the terminal; and a strict
residual quota propagates along the final-exit map until it contradicts the
terminal quota.
-/

namespace OMA.S_oeis_a384309

variable {V : Type*} [DecidableEq V]

/-- If two count vectors satisfy the same initial-flow law, the prefix vector
is pointwise below the target vector, and final exits from residual vertices
strictly increase the incoming flow, then a prefix that has exhausted its head
quota is already the complete target vector. -/
theorem prefix_flow_eq_of_head_quota
    (base : V → ℕ) (incomingQ incomingC : V → ℕ)
    (lastExit : V → V) (q c : V → ℕ) (head terminal : V)
    (hqflow : ∀ v, q v + (if head = v then 1 else 0) =
      base v + incomingQ v)
    (hcflow : ∀ v, c v + (if terminal = v then 1 else 0) =
      base v + incomingC v)
    (hqle : ∀ v, q v ≤ c v)
    (hincoming_mono : ∀ v, incomingQ v ≤ incomingC v)
    (hlast_strict : ∀ v, q v < c v →
      incomingQ (lastExit v) < incomingC (lastExit v))
    (hreach : ∀ v, ∃ n, (lastExit^[n]) v = terminal)
    (hhead : q head = c head) : q = c := by
  classical
  have hhead_terminal : head = terminal := by
    by_contra hne
    have hq : q head + 1 = base head + incomingQ head := by
      simpa only [if_pos rfl, if_true] using hqflow head
    have hterm_ne : terminal ≠ head := fun heq => hne heq.symm
    have hc : c head = base head + incomingC head := by
      simpa only [if_neg hterm_ne, if_false, Nat.add_zero] using hcflow head
    have hle := hincoming_mono head
    rw [hhead] at hq
    omega
  have hresidual : ∀ v, q v < c v → False := by
    intro v hv
    obtain ⟨n, hn⟩ := hreach v
    have hiter : ∀ n, q ((lastExit^[n]) v) < c ((lastExit^[n]) v) := by
      intro n
      induction n with
      | zero => simpa using hv
      | succ n ih =>
          have hstep := hlast_strict ((lastExit^[n]) v) ih
          have hflowQ0 := hqflow (lastExit ((lastExit^[n]) v))
          have hflowC0 := hcflow (lastExit ((lastExit^[n]) v))
          have hflowQ : q ((lastExit^[n + 1]) v) +
              (if head = lastExit ((lastExit^[n]) v) then 1 else 0) =
              base (lastExit ((lastExit^[n]) v)) +
                incomingQ (lastExit ((lastExit^[n]) v)) := by
            simpa only [Function.iterate_succ_apply'] using hflowQ0
          have hflowC : c ((lastExit^[n + 1]) v) +
              (if terminal = lastExit ((lastExit^[n]) v) then 1 else 0) =
              base (lastExit ((lastExit^[n]) v)) +
                incomingC (lastExit ((lastExit^[n]) v)) := by
            simpa only [Function.iterate_succ_apply'] using hflowC0
          have hsame : (if head = lastExit ((lastExit^[n]) v) then 1 else 0) =
              (if terminal = lastExit ((lastExit^[n]) v) then 1 else 0) := by
            rw [hhead_terminal]
          rw [hsame] at hflowQ
          omega
    have hterminal_res := hiter n
    rw [hn, ← hhead_terminal, hhead] at hterminal_res
    omega
  have hpoint : ∀ v, q v = c v := by
    intro v
    by_contra hne
    have hnotle : ¬ q v < c v := hresidual v
    have hle := hqle v
    omega
  funext v
  exact hpoint v

end OMA.S_oeis_a384309
open Function

namespace OMA.S_oeis_a384309

private theorem not_exhausted (k t : ℕ) (ht : t < 24*10^k-8)
    (hle : ∀ d, (state t).2 d ≤ quota (10^k) d) :
    (state t).2 (leading (state t).1) < quota (10^k) (leading (state t).1) := by
  let q := (state t).2
  let c := quota (10^k)
  let h := leading (state t).1
  let out : Digit → Digit := fun v => leading (c v)
  have hle' : ∀ d, q d ≤ c d := hle
  apply lt_of_le_of_ne (hle' h)
  intro hex
  have hqeq : q = c := by
    apply prefix_flow_eq_of_head_quota (fun d : Digit => if d=0 then 1 else 0)
      (fun d => ∑ v : Digit, digitCount d (q v))
      (fun d => ∑ v : Digit, digitCount d (c v)) out q c h 8
    · exact state_flow t
    · intro d
      simpa only [show (8 : Digit) = d ↔ d = 8 from eq_comm] using quota_balance k d
    · exact hle'
    · intro d
      exact Finset.sum_le_sum (fun v _ => Nat.count_monotone (fun n => leading (n+1) = d) (hle' v))
    · intro v hv
      apply Finset.sum_lt_sum
      · exact fun w _ => Nat.count_monotone (fun n => leading (n+1) = out v) (hle' w)
      · refine ⟨v, Finset.mem_univ _, ?_⟩
        have hpos : 0 < c v := by omega
        have hv' : q v ≤ c v - 1 := by omega
        have hs : c v - 1 + 1 = c v := by omega
        have hstep := Nat.count_strict_mono
          (p := fun n => leading (n+1) = out v) (m := c v - 1) (n := c v)
          (by rw [hs]) (by omega)
        exact (Nat.count_monotone (fun n => leading (n+1) = out v) hv').trans_lt hstep
    · intro v
      by_cases h8 : v=8
      · exact ⟨0,h8⟩
      · by_cases h0 : v=0
        · subst v
          exact ⟨1,last_exit_of_0 k⟩
        · refine ⟨2, ?_⟩
          change out (out v) = 8
          have hh : out v = 0 := last_exit_middle k v h0 h8
          rw [hh]
          exact last_exit_of_0 k
    · exact hex
  have hsum := state_count_sum t
  change (∑ d : Digit, q d) = t at hsum
  rw [hqeq] at hsum
  have hsum' : (∑ d : Digit, c d) = 24*10^k-8 := quota_sum k
  omega

theorem state_le_quota (k : ℕ) (t : ℕ) (ht : t ≤ 24*10^k-8) :
    ∀ d, (state t).2 d ≤ quota (10^k) d := by
  induction t with
  | zero => simp [state]
  | succ t ih =>
    have hlt : t < 24*10^k-8 := by omega
    have hle := ih (Nat.le_of_lt hlt)
    have hhead := not_exhausted k t hlt hle
    intro d
    rw [state]
    by_cases hd : d = leading (state t).1
    · subst d
      simpa using hhead
    · simp [hd, hle d]

theorem state_eq_quota (k : ℕ) :
    (state (24*10^k-8)).2 = quota (10^k) := by
  have hle := state_le_quota k _ le_rfl
  have hstate := state_count_sum (24*10^k-8)
  have hquota := quota_sum k
  funext d
  apply le_antisymm (hle d)
  by_contra! hd
  have hlt := Finset.sum_lt_sum (s := Finset.univ)
    (fun (v : Digit) _ => hle v) ⟨d, Finset.mem_univ _, hd⟩
  omega

theorem last_short_term (k : ℕ) (hk : 0 < k) :
    entry (24*10^k-7)=10^k-1 ∧ ∀ n > 24*10^k-7, 10^k ≤ entry n :=
  last_term_of_quota k hk (state_le_quota k) (state_eq_quota k)
    (fun t ht => not_exhausted k t ht (state_le_quota k t ht.le))

end OMA.S_oeis_a384309
namespace OMA.S_oeis_a384309

theorem all_counters_unbounded (x : ℕ) : ∃ t, ∀ d, x ≤ (state t).2 d := by
  refine ⟨24*10^x-8, ?_⟩
  intro d
  rw [state_eq_quota]
  have hpow : x < 10^x := Nat.lt_two_pow_self.trans_le
    (Nat.pow_le_pow_left (by decide : 2 ≤ 10) _)
  have hq := quota_next_ge x d
  by_cases h : d=8
  · subst d
    change 10^x ≤ quota (10^x) 8 + 1 at hq
    omega
  · simp only [if_neg h, Nat.add_zero] at hq
    exact hpow.le.trans hq

end OMA.S_oeis_a384309
namespace OMA.S_oeis_a384309

private theorem frequency_at (x : ℕ) (hx : 0 < x) (t : ℕ) :
    ((Finset.range (t+1)).filter (fun i => (state i).1=x)).card =
      (if x=1 then 1 else 0) + ∑ d : Digit, if x ≤ (state t).2 d then 1 else 0 := by
  simp only [← Nat.count_eq_card_filter_range]
  induction t with
  | zero => simp only [Nat.zero_add, Nat.count_one, state, eq_comm (a := 1), not_le_of_gt hx, if_false,
      Finset.sum_const_zero, Nat.add_zero]
  | succ t ih =>
    let h := leading (state t).1
    let c := (state t).2
    rw [Nat.count_succ, ih]
    change ((if x=1 then 1 else 0) + ∑ d : Digit, if x ≤ c d then 1 else 0) +
      (if c h + 1 = x then 1 else 0) =
      (if x=1 then 1 else 0) + ∑ d : Digit, if x ≤ c d+(if d=h then 1 else 0) then 1 else 0
    have point (d : Digit) : (if x ≤ c d+(if d=h then 1 else 0) then 1 else 0) =
        (if x ≤ c d then 1 else 0) + if d=h then (if c h+1=x then 1 else 0) else 0 := by
      by_cases hd : d=h
      · subst d
        split_ifs <;> omega
      · simp [hd]
    simp only [point, Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.mem_univ, if_true]
    omega

theorem exact_multiplicity (x : ℕ) (hx : 0 < x) :
    ∃ M, ∀ m ≥ M,
      ((Finset.range m).filter (fun t => (state t).1=x)).card = if x=1 then 10 else 9 := by
  obtain ⟨T,hT⟩ := all_counters_unbounded x
  refine ⟨T+1, fun m hm => ?_⟩
  obtain ⟨t,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : m ≠ 0)
  have ht : T ≤ t := by omega
  have hall (d : Digit) : x ≤ (state t).2 d := (hT d).trans (counter_mono d ht)
  rw [frequency_at x hx t]
  simp only [hall, if_true, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    nsmul_eq_mul, mul_one]
  split_ifs <;> decide

end OMA.S_oeis_a384309
open OMA.S_oeis_a384309 in
theorem OMA.solution : type_of% @OMA.S_oeis_a384309.main :=
  ⟨exact_multiplicity, last_short_term⟩
