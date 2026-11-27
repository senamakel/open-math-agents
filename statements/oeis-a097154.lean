import Mathlib

/-!
# A097154: Iterations of f(x) = reverse(x) - maxdigit(x) needed to reach zero

Source: https://oeis.org/A097154
Credit: @niclorusso

Conjecture (in the comments of A097154): 0 and 89 are the only fixed points of f, where
f(x) = reverse(x) - maxdigit(x).

Conventions:
* Everything is in base 10; x ranges over the natural numbers.
* reverse(x) is the digit reversal of x: `Nat.ofDigits 10 (Nat.digits 10 x).reverse`
  (`Nat.digits 10 x` lists the digits of x, least significant first; reverse(0) = 0).
* maxdigit(x) is the largest decimal digit of x, with maxdigit(0) = 0.
* reverse(x) >= maxdigit(x) always (every digit of x is a digit of reverse(x), except trailing zeros
  of x, which are 0), so the subtraction in the natural numbers is exact.
* "the only fixed points" is stated as a set equality; 89 is one: 98 - 9 = 89.
-/

namespace OMA.S_oeis_a097154

/-- The decimal digit reversal of `x`. -/
def reverse (x : ℕ) : ℕ := Nat.ofDigits 10 (Nat.digits 10 x).reverse

/-- The largest decimal digit of `x` (`0` for `x = 0`). -/
def maxDigit (x : ℕ) : ℕ := (Nat.digits 10 x).foldr max 0

/-- `f(x) = reverse(x) - maxdigit(x)`. -/
def f (x : ℕ) : ℕ := reverse x - maxDigit x

/-- The conjecture on A097154: the fixed points of `f` are exactly `0` and `89`. -/
theorem main : {x : ℕ | f x = x} = {0, 89} := by
  sorry

end OMA.S_oeis_a097154
