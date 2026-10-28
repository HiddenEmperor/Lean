import MyNumbers.Int
import MyNumbers.Rat
import MyNumbers.Real
import MyNumbers.Complex
import MyNumbers.Overview

/-!
# MyNumbers

A from-scratch construction of the number systems, in Lean 4 + Mathlib:

* `MyNumbers.Int`     — `MyInt`,  ℤ as a quotient of `ℕ × ℕ`
* `MyNumbers.Rat`     — `MyRat`,  ℚ as the field of fractions of `MyInt`
* `MyNumbers.Real`    — `MyReal`, ℝ as a quotient of Cauchy sequences of `MyRat`
* `MyNumbers.Complex` — `MyComplex`, ℂ as `MyReal × MyReal` (work in progress)
* `MyNumbers.Overview` — compile-checked summary of the main results

Importing this file gives you the whole development.
-/
