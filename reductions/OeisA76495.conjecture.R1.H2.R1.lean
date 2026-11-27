import OMAReductions.R_OeisA76495_conjecture_R1
import Mathlib.Tactic
import Mathlib.NumberTheory.ArithmeticFunction.Misc

/-! The even remainder-five case splits by the 2-adic valuation. If four
divides the candidate, a proved mod-four constraint forces a suitable odd prime. -/

open ArithmeticFunction Finset

namespace OMA.R_OeisA76495_conjecture_R1_H2_R1

def H1 : Prop :=
  ∀ n : ℕ, Even n → 3 ≤ n.primeFactors.card → Odd (sigma 1 n) →
    n % 4 = 2 → sigma 1 n % n ≠ 5

def H2 : Prop :=
  ∀ n : ℕ, Even n → 3 ≤ n.primeFactors.card → Odd (sigma 1 n) →
    4 ∣ n →
    (∃ p : ℕ, p ∈ n.primeFactors ∧ Nat.Prime p ∧ p % 4 = 1 ∧
      n.factorization p % 4 = 2) →
    sigma 1 n % n ≠ 5

theorem factorizationEvenOfOddSigma {n : ℕ} (hs : Odd (sigma 1 n))
    (p : ℕ) (hp : p ∈ n.primeFactors) (hp2 : p ≠ 2) :
    Even (n.factorization p) := by
  have hn0 : n ≠ 0 := by
    intro hz
    simp [hz] at hs
  have hpr := Nat.prime_of_mem_primeFactors hp
  have hodd := hpr.odd_of_ne_two hp2
  let e := n.factorization p
  let f := fun q => sigma 1 (q ^ n.factorization q)
  have hf : f p ∣ sigma 1 n := by
    rw [ArithmeticFunction.isMultiplicative_sigma.multiplicative_factorization _ hn0]
    exact Finset.dvd_prod_of_mem f hp
  have hos : Odd (f p) := Nat.not_even_iff_odd.mp fun he => hs.not_two_dvd_nat (he.two_dvd.trans hf)
  change Odd (sigma 1 (p ^ e)) at hos
  rw [ArithmeticFunction.sigma_one_apply_prime_pow hpr, Finset.odd_sum_iff_odd_card_odd] at hos
  have hall : (Finset.range (e + 1)).filter (fun i => Odd (p ^ i)) = Finset.range (e + 1) :=
    Finset.filter_true_of_mem fun i _ => hodd.pow
  rw [hall, Finset.card_range] at hos
  have hm := Nat.odd_iff.mp hos
  change Even e
  rw [Nat.even_iff]
  omega

theorem odd_prime_powers_mod_four {p : ℕ} (hp : p % 4 = 3) (b : ℕ) :
    p ^ (2*b) % 4 = 1 ∧ p ^ (2*b+1) % 4 = 3 := by
  have hpdiv := Nat.mod_add_div p 4
  rw [hp] at hpdiv
  have hpsq : p ^ 2 % 4 = 1 := by
    have heq : p = 4 * (p / 4) + 3 := by omega
    have hrepr : p ^ 2 = 4 * (4 * (p / 4)^2 + 6 * (p / 4) + 2) + 1 := by nlinarith
    rw [hrepr]
    omega
  induction b with
  | zero => simp [hp]
  | succ b ih =>
    constructor
    · have he : 2 * (b+1) = 2*b+2 := by omega
      rw [he, pow_add, Nat.mul_mod]
      simp [ih.1, hpsq]
    · have he : 2 * (b+1) + 1 = (2*b+1)+2 := by omega
      rw [he, pow_add, Nat.mul_mod]
      simp [ih.2, hpsq]

theorem sigma_odd_prime_square_mod_four {p b : ℕ} (hprime : Nat.Prime p)
    (hp : p % 4 = 3) : sigma 1 (p^(2*b)) % 4 = 1 := by
  rw [sigma_one_apply_prime_pow hprime]
  have hsum : ∀ b, (∑ i ∈ Finset.range (2*b+1), p^i) % 4 = 1 := by
    intro b
    induction b with
    | zero => simp
    | succ b ih =>
      have he : 2*(b+1)+1 = (2*b+1)+2 := by omega
      rw [he, Finset.sum_range_succ, Finset.sum_range_succ]
      have hpow := odd_prime_powers_mod_four hp b
      have hpow2 : p^(2*b+2)%4=1 := by
        have hh := (odd_prime_powers_mod_four hp (b+1)).1
        simpa only [Nat.mul_succ] using hh
      simp only [Nat.add_mod, ih, hpow.2, hpow2, Nat.mod_mod]
  exact hsum b

theorem sigma_prime_power_one_mod_four {p e : ℕ} (hprime : Nat.Prime p)
    (hp : p % 4 = 1) : sigma 1 (p^e) % 4 = (e+1) % 4 := by
  rw [sigma_one_apply_prime_pow hprime]
  have hpow : ∀ i, p^i % 4 = 1 := by
    intro i
    induction i with
    | zero => simp
    | succ i ih =>
      rw [pow_succ, Nat.mul_mod, ih, hp]
  have hsum : ∀ e, (∑ i ∈ Finset.range (e+1), p^i) % 4 = (e+1)%4 := by
    intro e
    induction e with
    | zero => simp
    | succ e ih =>
      rw [Finset.sum_range_succ, Nat.add_mod, ih, hpow]
      omega
  exact hsum e

theorem sigma_two_power_mod_four (a : ℕ) (ha : 1 ≤ a) :
    sigma 1 (2^a) % 4 = 3 := by
  have hsum : ∀ a, 1 ≤ a → (∑ i ∈ Finset.range (a+1), 2^i) % 4 = 3 := by
    intro a
    induction a with
    | zero => intro h; omega
    | succ a ih =>
      intro h
      by_cases ha0 : a = 0
      · subst a
        norm_num
      · have ha1 : 1 ≤ a := by omega
        rw [Finset.sum_range_succ, Nat.add_mod, ih ha1]
        have hd : 4 ∣ 2^(a+1) := by
          have hx : 4 = 2^2 := by norm_num
          rw [hx]
          exact Nat.pow_dvd_pow 2 (by omega)
        rw [Nat.mod_eq_zero_of_dvd hd]
  rw [sigma_one_apply_prime_pow Nat.prime_two]
  exact hsum a ha

theorem four_dvd_candidate_forces_prime {n : ℕ} (hn0 : n ≠ 0)
    (hn : Even n) (hodd : Odd (sigma 1 n)) (hfour : 4 ∣ n)
    (hmod : sigma 1 n % n = 5) :
    ∃ p : ℕ, p ∈ n.primeFactors ∧ Nat.Prime p ∧ p % 4 = 1 ∧ n.factorization p % 4 = 2 := by
  let f : ℕ → ℕ := fun p => sigma 1 (p ^ n.factorization p)
  let S := n.primeFactors
  have h2dvd : 2 ∣ n := by
    obtain ⟨k, hk⟩ := hn
    exact ⟨k, by simpa [two_mul] using hk⟩
  have h2mem : 2 ∈ S := Nat.Prime.mem_primeFactors Nat.prime_two h2dvd hn0
  have h2exp : 1 ≤ n.factorization 2 := by
    exact Nat.prime_two.factorization_pos_of_dvd hn0 h2dvd
  have hprod : sigma 1 n = ∏ p ∈ S, f p := by
    rw [ArithmeticFunction.sigma_eq_prod_primeFactors_sum_range_factorization_pow_mul hn0]
    apply Finset.prod_congr rfl
    intro p hp
    simpa [f, Nat.mul_one] using
      (sigma_one_apply_prime_pow (Nat.prime_of_mem_primeFactors hp)).symm
  by_contra hno
  have hnotbad : ∀ p, p ∈ S → Nat.Prime p → p % 4 = 1 → n.factorization p % 4 ≠ 2 := by
    intro p hp hprime hpmod hval
    exact hno ⟨p, hp, hprime, hpmod, hval⟩
  have hlocal : ∀ p ∈ S.erase 2, f p % 4 = 1 := by
    intro p hp
    rcases Finset.mem_erase.mp hp with ⟨hp2, hpmem⟩
    have hprime := Nat.prime_of_mem_primeFactors hpmem
    have heven := factorizationEvenOfOddSigma hodd p hpmem hp2
    have hpmod : p % 4 = 1 ∨ p % 4 = 3 := by
      have hpodd := hprime.odd_of_ne_two hp2
      rcases hpodd with ⟨k, hk⟩
      have hpdiv := Nat.mod_add_div p 4
      have hplt := Nat.mod_lt p (by decide : 0 < 4)
      omega
    rcases hpmod with hp1 | hp3
    · have hnot := hnotbad p hpmem hprime hp1
      have he4 : n.factorization p % 4 = 0 := by
        have he2 := Nat.even_iff.mp heven
        omega
      have hl := sigma_prime_power_one_mod_four (e := n.factorization p) hprime hp1
      change sigma 1 (p ^ n.factorization p) % 4 = 1
      rw [hl]
      omega
    · obtain ⟨b, hb⟩ := heven
      change sigma 1 (p ^ n.factorization p) % 4 = 1
      have hl := sigma_odd_prime_square_mod_four (b := b) hprime hp3
      simpa [hb, two_mul] using hl
  have hrest : (∏ p ∈ S.erase 2, f p) % 4 = 1 := by
    rw [Finset.prod_nat_mod]
    have hprodone : ∏ p ∈ S.erase 2, f p % 4 = 1 :=
      Finset.prod_eq_one (fun p hp => hlocal p hp)
    rw [hprodone]
  have htwo : f 2 % 4 = 3 := by
    dsimp [f]
    exact sigma_two_power_mod_four (n.factorization 2) h2exp
  have hsigmod : sigma 1 n % 4 = 3 := by
    rw [hprod, ← Finset.prod_erase_mul S f h2mem, Nat.mul_mod, hrest, htwo]
  have hmodfour := Nat.mod_mod_of_dvd (sigma 1 n) hfour
  rw [hmod, hsigmod] at hmodfour
  norm_num at hmodfour

 theorem main : H1 → H2 → OMA.R_OeisA76495_conjecture_R1.H2 := by
  intro hcase2 hcase4 n hn hcard hodd hmod
  have hn4 : n % 4 = 0 ∨ n % 4 = 2 := by
    have hn2 := Nat.even_iff.mp hn
    have hlt := Nat.mod_lt n (by decide : 0 < 4)
    omega
  rcases hn4 with hzero | htwo
  · have hfour : 4 ∣ n := Nat.dvd_of_mod_eq_zero hzero
    have hn0 : n ≠ 0 := by
      intro hz
      subst n
      simp at hcard
    have hmodWitness := four_dvd_candidate_forces_prime hn0 hn hodd hfour hmod
    exact (hcase4 n hn hcard hodd hfour hmodWitness) hmod
  · exact (hcase2 n hn hcard hodd htwo) hmod

end OMA.R_OeisA76495_conjecture_R1_H2_R1
