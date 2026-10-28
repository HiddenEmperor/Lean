import Mathlib.Tactic

/-!
# From-scratch integers

ℤ built as a quotient of `ℕ × ℕ` by the equivalence
`(a, b) ~ (c, d) ↔ a + d = b + c`, together with its
`CommRing` and ordered-ring structure.
-/


section integers

abbrev MyPreint := ℕ × ℕ

namespace MyPreint

def R(x y : MyPreint) : Prop := x.1 + y.2 = x.2 + y.1

lemma R_def (a b c d : ℕ) : R (a,b) (c,d) ↔ a + d = b + c := by
  rfl

lemma R_refl : ∀ x, R x x := by
  simp [R]
  intro a b
  rw [add_comm]

lemma R_symm : ∀ {x y}, R x y → R y x := by
  simp [R]
  intro a b a_1 b_1
  intro h
  rw [add_comm a b_1] at h
  rw [add_comm b a_1] at h
  exact h.symm

lemma R_trans : ∀ {x y z}, R x y → R y z → R x z := by
  simp [R]
  intro a b a_1 b_1 a_2 b_2
  intro h1 h2
  have h3 : a + b_1 + (a_1 + b_2) = b + a_1 + (b_1 + a_2) := by
    rw [h1]
    rw [h2]
  repeat rw [←add_assoc] at h3
  rw [add_comm] at h3
  rw [add_assoc a b_1 a_1] at h3
  rw [←add_assoc b_2 a (b_1+a_1)] at h3
  rw [add_comm (b+a_1+b_1) a_2] at h3
  rw [add_assoc b a_1 b_1] at h3
  rw [←add_assoc a_2 b (a_1+b_1)] at h3
  rw [add_comm a_1 b_1] at h3
  apply add_right_cancel at h3
  rw [add_comm a b_2]
  rw [add_comm b a_2]
  exact h3

instance R_equiv : Setoid MyPreint where
  r := R
  iseqv := ⟨R_refl, R_symm, R_trans⟩

@[simp] lemma equiv_def (a b c d : ℕ) : (a, b) ≈ (c, d) ↔ a + d = b + c := by
  rfl

@[simp] lemma equiv_def' (a b c d : ℕ) : Setoid.r (a, b) (c, d) ↔ a + d = b + c := by
  rfl

def neg (x : MyPreint) : MyPreint := (x.2, x.1)

@[simp] lemma neg_def (a b : ℕ) : neg (a, b) = (b, a) := by
  simp [neg]

lemma neg_quotient ⦃x x' : MyPreint⦄ (h : x ≈ x') : neg x ≈ neg x' := by
  simp [neg]
  rw [equiv_def] at h
  exact h.symm

@[simp] def add (x y : MyPreint) : MyPreint := (x.1 + y.1, x.2 + y.2)

@[simp] lemma add_def (a b c d : ℕ) : add (a, b) (c, d) = (a + c, b + d) := by
  rfl

lemma add_quotient ⦃x x' : MyPreint⦄ (h : x ≈ x') ⦃y y' : MyPreint⦄ (h' : y ≈ y') :
    add x y ≈ add x' y' := by
  simp [add_def]
  rw [equiv_def] at h h'
  rw [add_assoc]
  rw [add_comm x'.2 y'.2]
  rw [←add_assoc y.1 y'.2 x'.2]
  rw [add_comm (y.1+y'.2) x'.2]
  rw [←add_assoc]
  rw [h]
  rw [h']
  ring

@[simp] def mul (x y : MyPreint) : MyPreint :=
  (x.1 * y.1 + x.2 * y.2, x.1 * y.2 + x.2 * y.1)


@[simp] lemma mul_def (a b c d : ℕ) : mul (a, b) (c, d) = (a * c + b * d, a * d + b * c) := by
  rfl

lemma mul_quotient ⦃x x' : MyPreint⦄ (h : x ≈ x') ⦃y y' : MyPreint⦄ (h' : y ≈ y') :
    mul x y ≈ mul x' y' := by
  simp [mul_def]
  rw [equiv_def] at h h'
  have x_le_total : x.1 ≤ x.2 ∨ x.2 ≤ x.1 := Nat.le_total x.1 x.2
  have y_le_total : y.1 ≤ y.2 ∨ y.2 ≤ y.1 := Nat.le_total y.1 y.2
  cases x_le_total with
  |
    inl k =>
    rw [le_iff_exists_add] at k
    rcases k with ⟨c, hc⟩
    ·
      rw [hc] at h
      rw [add_assoc] at h
      apply add_left_cancel at h
      cases y_le_total with
      |
        inl l =>
        rw [le_iff_exists_add] at l
        rcases l with ⟨d, hd⟩
        ·
          rw [hd] at h'
          rw [add_assoc] at h'
          apply add_left_cancel at h'
          rw [hc , h , hd, h']
          ring
      |
        inr l =>
        rw [le_iff_exists_add] at l
        rcases l with ⟨d, hd⟩
        ·
          rw [hd] at h'
          rw [add_assoc] at h'
          apply add_left_cancel at h'
          rw [eq_comm] at h'
          rw [hc , h , hd, h']
          ring
  |
    inr k =>
    rw [le_iff_exists_add] at k
    rcases k with ⟨c, hc⟩
    ·
      rw [hc] at h
      rw [add_assoc] at h
      apply add_left_cancel at h
      cases y_le_total with
      |
        inl l =>
        rw [le_iff_exists_add] at l
        rcases l with ⟨d, hd⟩
        ·
          rw [hd] at h'
          rw [add_assoc] at h'
          apply add_left_cancel at h'
          rw [eq_comm] at h
          rw [hc , h , hd, h']
          ring
      |
        inr l =>
        rw [le_iff_exists_add] at l
        rcases l with ⟨d, hd⟩
        ·
          rw [hd] at h'
          rw [add_assoc] at h'
          apply add_left_cancel at h'
          rw [eq_comm] at h
          rw [eq_comm] at h'
          rw [hc , h , hd, h']
          ring

end MyPreint

open MyPreint

abbrev MyInt := Quotient R_equiv

namespace MyInt

@[simp] lemma Quot_eq_Quotient (a b : ℕ) : Quot.mk Setoid.r (a, b) = ⟦(a, b)⟧ := by
  rfl

instance zero : Zero MyInt where zero := ⟦(0, 0)⟧

lemma zero_def : (0 : MyInt) = ⟦(0, 0)⟧ := by
  rfl

instance one : One MyInt where one := ⟦(1, 0)⟧

lemma one_def : (1 : MyInt) = ⟦(1, 0)⟧ := by
  rfl

def neg : MyInt → MyInt := Quotient.map MyPreint.neg neg_quotient

instance : Neg MyInt where neg := neg

lemma neg_def (a b : ℕ) : -(⟦(a, b)⟧ : MyInt) = ⟦(b, a)⟧ := by
  rfl

def add : MyInt → MyInt → MyInt  := Quotient.map₂ MyPreint.add add_quotient

instance : Add MyInt where add := add

lemma add_def (a b c d : ℕ) : (⟦(a, b)⟧ : MyInt) + ⟦(c, d)⟧ = ⟦(a + c, b + d)⟧ := by
  rfl

def mul : MyInt → MyInt → MyInt  := Quotient.map₂ MyPreint.mul mul_quotient

instance : Mul MyInt where mul := mul

lemma mul_def (a b c d : ℕ) : (⟦(a, b)⟧ : MyInt) * ⟦(c, d)⟧ = ⟦(a * c + b * d, a * d + b * c)⟧ := by
  rfl

lemma add_assoc : ∀ (x y z : MyInt), (x + y) + z = x + (y + z) := by
  intro x y z
  refine Quot.induction_on₃ x y z ?_
  rintro ⟨a , b⟩
  rintro ⟨c , d⟩
  rintro ⟨e , f⟩
  simp [R]
  simp [add_def]
  ring


macro "quot_proof₁" : tactic =>
  `(tactic|
  focus
    intro x
    refine Quot.induction_on x ?_
    rintro ⟨a, b⟩
    apply Quot.sound
    simp [Setoid.r, R]
    try ring)

macro "quot_proof₂" : tactic =>
  `(tactic|
  focus
    intro x y
    refine Quot.induction_on₂ x y ?_
    rintro ⟨a, b⟩ ⟨c, d⟩
    apply Quot.sound
    simp [Setoid.r, R]
    try ring)

macro "quot_proof₃" : tactic =>
  `(tactic|
  focus
    intro x y z
    refine Quot.induction_on₃ x y z ?_
    rintro ⟨a, b⟩ ⟨c, d⟩ ⟨e, f⟩
    apply Quot.sound
    simp [Setoid.r, R]
    try ring)

macro "quot_proof" : tactic =>
  `(tactic|
  focus
    try quot_proof₁
    try quot_proof₂
    try quot_proof₃)

instance commRing : CommRing MyInt where
  add := (· + ·)
  add_assoc := by quot_proof₃
  zero := 0
  zero_add := by quot_proof₁
  add_zero := by quot_proof₁
  add_comm := by quot_proof₂
  mul := (· * ·)
  left_distrib := by quot_proof₃
  right_distrib := by quot_proof₃
  zero_mul := by quot_proof₁
  mul_zero := by quot_proof₁
  mul_assoc := by quot_proof₃
  one := 1
  one_mul := by quot_proof₁
  mul_one := by quot_proof₁
  neg := (- ·)
  mul_comm := by quot_proof₂
  neg_add_cancel := by quot_proof₁
  nsmul := nsmulRec --ignore this
  zsmul := zsmulRec --ignore this


lemma zero_ne_one : (0 : MyInt) ≠ 1 := by
  by_contra h
  simp [zero_def , one_def] at h

lemma aux_mul_lemma (a b c d : ℕ) (h : a * d + b * c = a * c + b * d) : a = b ∨ c = d := by
  induction a generalizing b with
  | zero =>
    simp_all
    tauto
  | succ e he =>
    cases b with
    | zero =>
      simp_all
    | succ f =>
      specialize he f
      simp
      apply he
      simp [Nat.succ_mul] at h
      linarith

lemma mul_ne_zero (x y : MyInt) : x ≠ 0 → y ≠ 0 → x * y ≠ 0 := by
  refine Quot.induction_on₂ x y ?_
  intro x y
  rcases x with ⟨a , b⟩
  rcases y with ⟨c , d⟩
  simp [R]
  intro h1 h2
  by_contra h
  simp [zero_def] at h1
  simp [zero_def] at h2
  rw [mul_def] at h
  simp [zero_def] at h
  apply aux_mul_lemma at h
  tauto

lemma eq_of_mul_eq_mul_right (x y z : MyInt) : x ≠ 0 → y * x = z * x → y = z := by
  refine Quot.induction_on₃ x y z ?_
  intro x y z
  rcases x with ⟨a , b⟩
  rcases y with ⟨c , d⟩
  rcases z with ⟨e , f⟩
  simp [R]
  intro h1 h2
  simp [zero_def] at h1
  simp [mul_def] at h2
  rw [Nat.add_comm (e * b) (f * a)] at h2
  rw [Nat.add_right_comm] at h2
  rw [←Nat.add_assoc] at h2
  rw [←Nat.add_mul c f a] at h2
  rw [Nat.add_assoc] at h2
  rw [←Nat.add_mul e d b] at h2
  rw [Nat.add_comm (e * a) (f * b)] at h2
  rw [Nat.add_right_comm] at h2
  rw [←Nat.add_assoc] at h2
  rw [←Nat.add_mul c f b] at h2
  rw [Nat.add_assoc] at h2
  rw [←Nat.add_mul e d a] at h2
  apply aux_mul_lemma at h2
  rw [add_comm e d] at h2
  tauto


def i (n : ℕ) : MyInt := ⟦(n, 0)⟧

lemma i_zero : i 0 = 0 := by
  rfl


lemma i_one : i 1 = 1 := by
  rfl

lemma i_add (a b : ℕ) : i (a + b) = i a + i b := by
  simp [i]
  rfl

lemma i_mul (a b : ℕ) : i (a * b) = i a * i b := by
  simp [i]
  simp [mul_def]

lemma i_injective : Function.Injective i := by
  intro a b h
  simp [i] at h
  exact h

def le (x y : MyInt) : Prop := ∃ a : ℕ, y = x + i a

instance : LE MyInt where
  le := le

lemma le_refl (x : MyInt) : x ≤ x := by
  use 0
  simp [zero_def]
  rfl

lemma le_trans (x y z : MyInt) : x ≤ y → y ≤ z → x ≤ z := by
  refine Quot.induction_on₃ x y z ?_
  rintro ⟨a, b⟩ ⟨c, d⟩ ⟨e, f⟩
  simp [le, i, add_def]
  rintro ⟨n, h1⟩ ⟨m, h2⟩
  use n + m
  rw [h2 , h1]
  simp [i]
  simp [add_def]
  ring

lemma le_antisymm (x y : MyInt) : x ≤ y → y ≤ x → x = y := by
  refine Quot.induction_on₂ x y ?_
  rintro ⟨a , b⟩ ⟨c , d⟩
  simp
  rintro ⟨n, h1⟩ ⟨m, h2⟩
  rw [h1] at h2
  simp [i] at h2
  simp [add_def] at h2
  rw [add_comm] at h2
  apply add_left_cancel at h2
  nth_rw 1 [←add_zero a] at h2
  rw [Nat.add_assoc] at h2
  apply add_left_cancel at h2
  rw [eq_comm] at h2
  rw [add_eq_zero] at h2
  rw [h2.left] at h1
  simp [i] at h1
  simp [add_def] at h1
  rw [add_comm c b] at h1
  rw [add_comm d a] at h1
  exact h1.symm


lemma le_total (x y : MyInt) : x ≤ y ∨ y ≤ x := by
  refine Quot.induction_on₂ x y ?_
  rintro ⟨a, b⟩ ⟨c, d⟩
  simp [R]
  have nat_le_total : a + d ≤ b + c ∨ b + c ≤ a + d :=
    Nat.le_total (a + d) (b + c)
  cases nat_le_total with
  |
    inl h =>
    left
    rw [le_iff_exists_add ] at h
    rcases h with ⟨k, hk⟩
    use k
    simp [i, add_def]
    rw [add_comm] at hk
    rw [hk]
    ring
  |
    inr h =>
    right
    rw [le_iff_exists_add ] at h
    rcases h with ⟨k, hk⟩
    use k
    simp [i, add_def]
    rw [hk]
    ring

noncomputable instance linearOrder : LinearOrder MyInt where
  le := (· ≤ ·)
  le_refl := le_refl
  le_trans := le_trans
  le_antisymm := le_antisymm
  le_total := le_total
  toDecidableLE := fun _ _ => Classical.propDecidable _ --ignore this

lemma zero_le_one : (0 : MyInt) ≤ 1 := by
  use 1
  simp [one_def]
  rfl

lemma i_le_iff (a b : ℕ) : i a ≤ i b ↔ a ≤ b := by
  constructor
  ·
    rintro ⟨n , h⟩
    simp [i , add_def] at h
    linarith
  ·
    intro h
    cases Nat.le.dest h with
    | intro n hn =>
      use n
      simp [i, add_def]
      rw [hn]


lemma add_le_add_left (x y : MyInt) : x ≤ y → ∀ (z : MyInt) , z + x ≤ z + y := by
  refine Quot.induction_on₂ x y ?_
  rintro ⟨a, b⟩ ⟨c, d⟩
  simp [le, i, add_def]
  rintro ⟨n, hn⟩
  intro z
  refine Quot.induction_on z ?_
  rintro ⟨e, f⟩
  use n
  simp [i, add_def] at hn
  simp [i, add_def]
  rw [Nat.add_assoc]
  rw [add_comm]
  rw [add_comm f b]
  rw [←Nat.add_assoc]
  rw [hn]
  ring

lemma mul_pos (x y : MyInt) : 0 < x →  0 < y → 0 < x * y := by
  refine Quot.induction_on₂ x y ?_
  rintro ⟨a, b⟩ ⟨c, d⟩
  simp [R, zero_def]
  intro hx hy
  rw [lt_iff_le_and_ne] at hx hy ⊢
  obtain ⟨hx_le, hx_ne⟩ := hx
  obtain ⟨hy_le, hy_ne⟩ := hy
  simp [mul_def]
  simp [zero_def] at hx_ne  hy_ne
  constructor
  ·
    rcases hx_le with ⟨n, hn⟩
    rcases hy_le with ⟨m, hm⟩
    simp [i, add_def] at hn hm
    rw [hn, hm]
    use n * m
    simp [i, add_def]
    ring
  ·
    by_contra h
    apply aux_mul_lemma at h
    tauto


instance : Nontrivial MyInt := ⟨0, 1, zero_ne_one⟩

instance : ZeroLEOneClass MyInt := ⟨zero_le_one⟩

instance : IsOrderedAddMonoid MyInt where
  add_le_add_left := add_le_add_left

instance : IsStrictOrderedRing MyInt :=
  IsStrictOrderedRing.of_mul_pos mul_pos

end MyInt

end integers
