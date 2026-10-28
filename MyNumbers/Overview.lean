import MyNumbers.Complex

/-!
# Overview: a compile-checked table of contents

Every `example` below restates a main theorem of the development, and every
`inferInstance` certifies one of the type class instances that each stage of
the construction provides.  Since these are `example`s rather than comments,
this file doubles as a regression test: if a proof somewhere in
`MyNumbers/Int.lean`, `MyNumbers/Rat.lean` or `MyNumbers/Real.lean` breaks,
`lake build` fails here too.

The construction chain is

`ℕ` → `MyInt` (difference of naturals) → `MyRat` (fractions) →
`MyReal` (Cauchy sequences) → `MyComplex` (pairs of reals).
The whole file is `noncomputable`, because several of the instances it checks
(`MyRat.field`, `MyReal.linearOrder`, ...) are noncomputable.
-/

noncomputable section

/-! ## ℤ — `MyInt := Quotient (ℕ × ℕ) ~`, with `(a, b) ~ (c, d) ↔ a + d = b + c` -/

namespace MyInt

example : CommRing MyInt := inferInstance
example : Nontrivial MyInt := inferInstance
example : IsStrictOrderedRing MyInt := inferInstance

/-- `ℤ` is linearly ordered. -/
example (a b : MyInt) : a ≤ b ∨ b ≤ a := le_total a b

/-- The canonical embedding `ℕ → ℤ`. -/
example : Function.Injective i := i_injective

/-- `ℤ` has no zero divisors (and hence cancellation). -/
example (x y : MyInt) (hx : x ≠ 0) (hy : y ≠ 0) : x * y ≠ 0 :=
  mul_ne_zero x y hx hy

end MyInt

/-! ## ℚ — `MyRat := Quotient (MyInt × {x // x ≠ 0}) ~` -/

namespace MyRat

example : Field MyRat := inferInstance
example : IsOrderedRing MyRat := inferInstance

/-- `ℚ` is linearly ordered. -/
example (a b : MyRat) : a ≤ b ∨ b ≤ a := le_total a b

/-- `ℚ` is archimedean. -/
example (x : MyRat) : ∃ n : ℕ, x ≤ i n := archimedean x

/-- The canonical embedding `ℤ → ℚ` is injective and preserves the order (up to
`i`). -/
example (a b : MyInt) : j a = j b ↔ a = b := j_injective a b

end MyRat

/-! ## ℝ — `MyReal := Quotient (Cauchy sequences of MyRat) ~` -/

namespace MyReal

example : Field MyReal := inferInstance
example : LinearOrder MyReal := inferInstance
example : IsStrictOrderedRing MyReal := inferInstance

/-- `ℝ` is linearly ordered. -/
example (a b : MyReal) : a ≤ b ∨ b ≤ a := le_total a b

/-- `ℝ` is archimedean. -/
example (x : MyReal) : ∃ n : ℕ, x ≤ k (MyRat.i (n + 1)) := archimedean x

/-- Every real number can be approximated arbitrarily well by a rational. -/
example (x : MyReal) {ε : MyReal} (hε : 0 < ε) : ∃ r, |x - k r| < ε :=
  myRat_dense_rat x hε

/-- **Cauchy completeness.** Every Cauchy sequence of reals converges. -/
example {f : ℕ → MyReal} (hf : IsCauchy f) : IsConvergent f := complete hf

/-- `ℚ` embeds into `ℝ`, preserving `0`, `1`, `+`, `*`, inversion and the order. -/
example : Function.Injective k := k_injective
example (x y : MyRat) : k (x + y) = k x + k y := k_add x y
example (x y : MyRat) : k (x * y) = k x * k y := k_mul x y
example (x : MyRat) : k x⁻¹ = (k x)⁻¹ := k_inv x
example (x y : MyRat) : k x ≤ k y ↔ x ≤ y := k_le_iff x y

end MyReal

/-! ## ℂ — `MyComplex := Quotient (MyReal × MyReal) ~` (work in progress) -/

namespace MyComplex

example : Zero MyComplex := inferInstance
example : One MyComplex := inferInstance
example : Neg MyComplex := inferInstance

end MyComplex

/-!
## Roadmap

`MyComplex` currently stops at the quotient type with `0`, `1` and negation.
To finish the tower one would

1. push `MyPrecomplex.add` / `MyPrecomplex.mul` through the quotient to get
   `Add` / `Mul` (and `Sub`, `OfNat`) instances on `MyComplex`;
2. prove `CommRing MyComplex` and `Field MyComplex` (`mul_inv_cancel` uses
   `(a + bi)(a - bi) = a² + b²`, so it needs the order on `MyReal` to know
   `a² + b² ≠ 0`);
3. define `Complex.abs` / `IsNonneg` on `MyComplex` in order to get a
   `LinearOrder`-free `StarRing` structure;
4. build the ring isomorphism `MyComplex ≃+* ℂ` against Mathlib's complex
   numbers, which is the natural "this really is ℂ" sanity check.
-/

end
