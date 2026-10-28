import MyNumbers.Real

/-!
# From-scratch complex numbers (work in progress)

ℂ built as a quotient of `MyReal × MyReal` by componentwise equality.
Currently only the additive/multiplicative *pre*-structure and the quotient
type with `0`, `1` and negation are defined; see the `TODO`s at the end of
the file.
-/


noncomputable section complex

abbrev MyPrecomplex := MyReal × MyReal

namespace MyPrecomplex

def R (x y : MyPrecomplex) := (x.1 = y.1 ∧ x.2 = y.2)

lemma R_def (a b c d : MyReal) : R (a, b) (c, d) ↔ (a = c ∧ b = d) := by
  rfl

lemma R_refl : ∀ x, R x x := by
  simp [R]

lemma R_symm : ∀ {x y}, R x y → R y x := by
  intro x y h
  simp [R] at h
  simp [R]
  nth_rw 1 [eq_comm]
  nth_rw 2 [eq_comm]
  exact h

lemma R_trans : ∀ {x y z}, R x y → R y z → R x z := by
  intro x y z
  intro h1 h2
  simp [R] at h1 h2
  simp [R]
  rcases h1 with ⟨h11, h12⟩
  rcases h2 with ⟨h21, h22⟩
  rw [h11, h21, h12, h22]
  exact ⟨rfl, rfl⟩

instance R_equiv : Setoid MyPrecomplex where
  r := R
  iseqv := ⟨R_refl, R_symm, R_trans⟩

@[simp] lemma equiv_def (a b c d : MyReal) : (a, b) ≈ (c, d) ↔ a = c ∧ b = d := by
  rfl

@[simp] lemma equiv_def' (a b c d : MyReal) : Setoid.r (a, b) (c, d) ↔ a = c ∧ b = d := by
  rfl

def neg (x : MyPrecomplex) : MyPrecomplex := (-x.1, -x.2)

@[simp] lemma neg_def (a b : MyReal) : neg (a, b) = (-a, -b) := by
  simp [neg]

lemma neg_quotient ⦃x x' : MyPrecomplex⦄ (h : x ≈ x') : neg x ≈ neg x' := by
  simp [neg]
  rw [equiv_def] at h
  exact h

def add (x y : MyPrecomplex) : MyPrecomplex := (x.1 + y.1, x.2 + y.2)

@[simp] lemma add_def (a b c d : MyReal) : add (a, b) (c, d) = (a + c, b + d) := by
  rfl

lemma add_quotient ⦃x x' : MyPrecomplex⦄ (h : x ≈ x') ⦃y y' : MyPrecomplex⦄ (h' : y ≈ y') :
    add x y ≈ add x' y' := by
  rw [equiv_def] at h h'
  simp [add]
  rcases h with ⟨h1, h2⟩
  rcases h' with ⟨h1', h2'⟩
  rw [h1, h2, h1', h2']
  exact ⟨rfl, rfl⟩

def mul (x y : MyPrecomplex) : MyPrecomplex := (x.1 * y.1 - x.2 * y.2, x.1 * y.2 + x.2 * y.1)

@[simp] lemma mul_def (a b c d : MyReal) : mul (a, b) (c, d) = (a * c - b * d, a * d + b * c) := by
  rfl

lemma mul_quotient ⦃x x' : MyPrecomplex⦄ (h : x ≈ x') ⦃y y' : MyPrecomplex⦄ (h' : y ≈ y') :
    mul x y ≈ mul x' y' := by
  rw [equiv_def] at h h'
  simp [mul]
  rcases h with ⟨h1, h2⟩
  rcases h' with ⟨h1', h2'⟩
  rw [h1, h2, h1', h2']
  exact ⟨rfl, rfl⟩

end MyPrecomplex

open MyPrecomplex

abbrev MyComplex := Quotient R_equiv

namespace MyComplex

@[simp] lemma Quot_eq_Quotient (a b : MyReal) : Quot.mk Setoid.r (a, b) = ⟦(a, b)⟧ := by
  rfl

instance zero : Zero MyComplex where zero := ⟦(0, 0)⟧

lemma zero_def : (0 : MyComplex) = ⟦(0, 0)⟧ := by
  rfl

instance one : One MyComplex where one := ⟦(1, 0)⟧

lemma one_def : (1 : MyComplex) = ⟦(1, 0)⟧ := by
  rfl

def neg : MyComplex → MyComplex := Quotient.map MyPrecomplex.neg neg_quotient

instance : Neg MyComplex where neg := neg

end MyComplex

end complex
