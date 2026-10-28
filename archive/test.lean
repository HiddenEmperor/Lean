import Mathlib.Tactic

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

section rationals

instance : Mul {x : MyInt // x ≠ 0} where
  mul a b := ⟨a.1 * b.1, mul_ne_zero a.2 b.2⟩

@[simp, norm_cast] lemma Int.ne_zero_coe_mul (a b : {x : MyInt // x ≠ 0}) :
    ((a * b : {x : MyInt // x ≠ 0}) : MyInt) = a * b := by
  rfl


abbrev MyPrerat := MyInt × {x : MyInt // x ≠ 0}

namespace MyPrerat


def R (x y : MyPrerat) : Prop := x.1 * y.2 = x.2 * y.1


lemma R_def (a : MyInt) (b : {x : MyInt // x ≠ 0}) (c : MyInt) (d : {x : MyInt // x ≠ 0}) :
    R (a,b) (c,d) ↔ a * d = b * c := by
  rfl

lemma R_refl : ∀ x, R x x := by
  simp [R]
  intro a b h
  ring

lemma R_symm : ∀ {x y}, R x y → R y x := by
  simp [R]
  intro a b h
  intro a1 b1 h1
  intro k
  rw [mul_comm]
  rw [mul_comm b1 a]
  exact k.symm

lemma R_trans : ∀ {x y z}, R x y → R y z → R x z := by
  simp [R]
  intro a1 b1 h1 a2 b2 h2 a3 b3 h3
  intro k1 k2
  have k3 : b1 * a2 * b3 = b1 * b2 * a3 := by
    rw [mul_assoc]
    rw [mul_assoc]
    rw [k2]
  rw [k1.symm] at k3
  rw [mul_right_comm] at k3
  rw [mul_right_comm b1 b2 a3] at k3
  have c : b2 ≠ 0 := h2
  exact MyInt.eq_of_mul_eq_mul_right b2 (a1 * b3) (b1 * a3) c k3

instance R_equiv : Setoid MyPrerat where
  r := R
  iseqv := ⟨R_refl, R_symm, R_trans⟩


@[simp] lemma equiv_def (a : MyInt) (b : {x : MyInt // x ≠ 0}) (c : MyInt) (d : {x : MyInt // x ≠ 0}) :
    (a, b) ≈ (c, d) ↔ a * d = b * c := by
  rfl

@[simp] lemma equiv_def' (a : MyInt) (b : {x : MyInt // x ≠ 0}) (c : MyInt) (d : {x : MyInt // x ≠ 0}) :
    Setoid.r (a, b) (c, d) ↔ a * d = b * c := by
  rfl


def neg (x : MyPrerat) : MyPrerat := (-x.1, x.2)


@[simp] lemma neg_def (a : MyInt) (b : {x : MyInt // x ≠ 0}) : neg (a, b) = (-a, b) := by
  rfl

lemma neg_quotient ⦃x x' : MyPrerat⦄ (h : x ≈ x') : neg x ≈ neg x' := by
  simp [neg]
  exact h


def add (ab cd : MyPrerat) : MyPrerat := (ab.1 * cd.2 + ab.2 * cd.1, ab.2 * cd.2)

@[simp] lemma add_def (a : MyInt) (b : {x : MyInt // x ≠ 0}) (c : MyInt) (d : {x : MyInt // x ≠ 0}) :
    add (a, b) (c, d) = (a * d + b * c, b * d) := by
  rfl

lemma add_quotient ⦃x x' : MyPrerat⦄ (h : x ≈ x') ⦃y y' : MyPrerat⦄ (h' : y ≈ y') :
    add x y ≈ add x' y' := by
  simp [add]
  rw [equiv_def] at h h'
  rw [add_mul]
  repeat rw [←mul_assoc]
  rw [mul_right_comm x.1]
  rw [mul_right_comm (↑x.2 * y.1)]
  rw [mul_assoc ↑x.2 y.1]
  rw [h, h']
  ring

def mul (ab cd : MyPrerat) : MyPrerat := (ab.1 * cd.1, ab.2 * cd.2)


@[simp] lemma mul_def (a : MyInt) (b : {x : MyInt // x ≠ 0}) (c : MyInt) (d : {x : MyInt // x ≠ 0}) :
    mul (a, b) (c, d) = (a * c, b * d) := by
  rfl

lemma mul_quotient ⦃x x' : MyPrerat⦄ (h : x ≈ x') ⦃y y' : MyPrerat⦄ (h' : y ≈ y') :
    mul x y ≈ mul x' y' := by
  simp [mul]
  rw [equiv_def] at h h'
  rw [mul_assoc]
  rw [mul_comm y.1 _]
  rw [mul_assoc ↑x'.2 ↑y'.2 y.1]
  rw [mul_comm ↑y'.2 y.1]
  repeat rw [←mul_assoc x.1 _ _]
  rw [h, h']
  ring


noncomputable
def inv (x : MyPrerat) : MyPrerat := if ha : x.1 ≠ 0 then ⟨x.2, x.1, ha⟩ else ⟨0, 1, by simp⟩



@[simp] lemma inv_def {a : MyInt} (b : {x : MyInt // x ≠ 0}) (ha : a ≠ 0) :
    inv (a, b) = (b.1, ⟨a, ha⟩) := by
  unfold inv
  simp [ha]


lemma inv_def' (a : MyInt) (b : {x : MyInt // x ≠ 0}) :
    inv (a, b) = if ha : a ≠ 0 then ⟨b, a, ha⟩ else ⟨0, 1, by simp⟩ := by
  rfl

lemma inv_quotient ⦃x x' : MyPrerat⦄ (h : x ≈ x') : inv x ≈ inv x' := by
  unfold inv
  cases x with | mk a b =>
  cases x' with | mk a' b' =>
  simp only
  split_ifs with ka kb
  ·
    simp
    simp at h
    exact h.symm
  ·
    exfalso
    rw [MyPrerat.equiv_def] at h
    have c : a * ↑b' ≠ 0 := mul_ne_zero ka b'.property
    simp at kb
    rw [kb, mul_zero] at h
    tauto
  ·
    rename_i kb
    exfalso
    rw [MyPrerat.equiv_def] at h
    simp at h
    simp at ka
    have c : ↑b * a' ≠ 0 := mul_ne_zero ↑b.property kb
    rw [ka,zero_mul] at h
    tauto
  ·
    rename_i hb
    simp

end MyPrerat


open MyPrerat


abbrev MyRat := Quotient R_equiv

namespace MyRat

@[simp] lemma Quot_eq_Quotient (a : MyInt) (b : {x : MyInt // x ≠ 0}) :
    Quot.mk Setoid.r (a, b) = ⟦(a, b)⟧ := by
  rfl

instance zero : Zero MyRat where zero := ⟦(0, ⟨1, one_ne_zero⟩)⟧

lemma zero_def : (0 : MyRat) = ⟦(0, ⟨1, one_ne_zero⟩)⟧ := by
  rfl

instance one : One MyRat where one := ⟦(1, ⟨1, one_ne_zero⟩)⟧

lemma one_def : (1 : MyRat) = ⟦(1, ⟨1, one_ne_zero⟩)⟧ := by
  rfl


def neg : MyRat → MyRat := Quotient.map MyPrerat.neg neg_quotient

instance : Neg MyRat where neg := neg

lemma neg_def (a : MyInt) (b : {x : MyInt // x ≠ 0}) :
    -(⟦(a, b)⟧ : MyRat) = ⟦(-a, b)⟧ := by
  rfl

def add : MyRat → MyRat → MyRat := Quotient.map₂ MyPrerat.add add_quotient

instance : Add MyRat where add := add

lemma add_def (a : MyInt) (b : {x : MyInt // x ≠ 0}) (c : MyInt) (d : {x : MyInt // x ≠ 0}) :
    (⟦(a, b)⟧ : MyRat) + ⟦(c, d)⟧ = ⟦(a * d + b * c, b * d)⟧ :=
  rfl

def mul : MyRat → MyRat → MyRat  := Quotient.map₂ MyPrerat.mul mul_quotient

instance : Mul MyRat where mul := mul

lemma mul_def (a : MyInt) (b : {x : MyInt // x ≠ 0}) (c : MyInt) (d : {x : MyInt // x ≠ 0}) :
    (⟦(a, b)⟧ : MyRat) * ⟦(c, d)⟧ = ⟦(a * c, b * d)⟧ :=
  rfl

noncomputable
def inv : MyRat → MyRat := Quotient.map MyPrerat.inv inv_quotient

noncomputable
instance : Inv MyRat := ⟨inv⟩

lemma inv_def (a : MyInt) (b : {x : MyInt // x ≠ 0}) :
    (⟦(a, b)⟧ : MyRat)⁻¹ = ⟦MyPrerat.inv (a, b)⟧ := by
  rfl

section tactic_hackery


macro "quot_proof₁" : tactic =>
  `(tactic|
  focus
    intro x
    refine Quot.induction_on x ?_
    rintro ⟨a, b⟩
    apply Quot.sound
    simp
    try ring)

macro "quot_proof₂" : tactic =>
  `(tactic|
  focus
    intro x y
    refine Quot.induction_on₂ x y ?_
    rintro ⟨a, b⟩ ⟨c, d⟩
    apply Quot.sound
    simp
    try ring)

macro "quot_proof₃" : tactic =>
  `(tactic|
  focus
    intro x y z
    refine Quot.induction_on₃ x y z ?_
    rintro ⟨a, b⟩ ⟨c, d⟩ ⟨e, f⟩
    apply Quot.sound
    simp
    try ring)

macro "quot_proof" : tactic =>
  `(tactic|
  focus
    try quot_proof₁
    try quot_proof₂
    try quot_proof₃
  )

end tactic_hackery

instance commRing : CommRing MyRat where
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
  nsmul := nsmulRec --ignore
  zsmul := zsmulRec --ignore

lemma sub_def (a : MyInt) (b : {x : MyInt // x ≠ 0}) (c : MyInt) (d : {x : MyInt // x ≠ 0}) :
    (⟦(a, b)⟧ : MyRat) - ⟦(c, d)⟧ = ⟦(a * d - b * c, b * d)⟧ := by
  simp [sub_eq_add_neg, neg_def, add_def]

lemma zero_ne_one : (0 : MyRat) ≠ 1 := by
  simp [zero_def, one_def]

lemma mul_inv_cancel (x : MyRat):  x ≠ 0 → x * x⁻¹ = 1 := by
  refine Quot.induction_on x ?_
  rintro ⟨a, b⟩
  intro h
  simp [inv_def]
  unfold MyPrerat.inv
  simp at h
  split_ifs with ha
  ·
    simp [mul_def]
    simp [zero_def] at h
    simp [one_def]
    ring
  ·
    simp [zero_def] at h
    simp  at ha
    tauto


noncomputable
instance field : Field MyRat where
  exists_pair_ne := ⟨0, 1, zero_ne_one⟩
  mul_inv_cancel := mul_inv_cancel
  inv_zero := by
    rw [zero_def]
    simp [inv_def, MyPrerat.inv]
  qsmul := _ --ignore
  nnqsmul := _ --ignore

def i (n : ℕ) : MyRat := ⟦(MyInt.i n, ⟨1, by simp⟩)⟧

lemma i_zero : i 0 = 0 := by
  rfl

lemma i_one : i 1 = 1 := by
  rfl

lemma i_add (a b : ℕ) : i (a + b) = i a + i b := by
  simp [i, add_def]
  simp [MyInt.i, MyInt.add_def]

lemma i_mul (a b : ℕ) : i (a * b) = i a * i b := by
  simp [i, mul_def]
  simp [MyInt.i, MyInt.mul_def]

lemma i_injective : Function.Injective i := by
  intro x y h
  simp [i, MyInt.i] at h
  exact h

def j (n : MyInt) : MyRat := ⟦(n, ⟨1, by simp⟩)⟧

lemma j_zero : j 0 = 0 := by
  rfl

lemma j_one : j 1 = 1 := by
  rfl

lemma j_add (a b : MyInt) : j (a + b) = j a + j b := by
  simp [j, add_def]

lemma j_mul (a b : MyInt) : j (a * b) = j a * j b := by
  simp [j, mul_def, MyInt.mul_def]

lemma j_injective (a b : MyInt) : j a = j b ↔ a = b := by
  simp [j]

lemma j_comp_eq_i (n : ℕ) : j (MyInt.i n) = i n := by
  simp [MyInt.i, j, i]


theorem Quotient.mk_def (a : MyInt) (b : {x : MyInt // x ≠ 0}) :
    ⟦(a, b)⟧ = j a * (j b)⁻¹ := by
  simp [j, inv_def, MyPrerat.inv_def']
  split_ifs with h
  ·
    simp [mul_def]
    let a := b.property
    tauto
  ·
    simp [mul_def]
    ring

def IsNonneg (x : MyRat) : Prop :=
  ∃ (a b : MyInt) (_ : 0 ≤ a) (hb : 0 < b), x = ⟦(a, ⟨b, hb.ne'⟩)⟧


@[simp]
lemma zero_nonneg : IsNonneg 0 := by
  simp [IsNonneg]
  use 0
  constructor
  ·
    rfl
  ·
    use 1
    simp
    rfl

@[simp]
lemma one_nonneg : IsNonneg 1 := by
  simp [IsNonneg]
  use 1
  constructor
  ·
    exact MyInt.zero_le_one
  ·
    use 1
    simp
    rfl

lemma nonneg_neg {x : MyRat} (h : IsNonneg x) (h' : IsNonneg (-x)) :
    x = 0 := by
  simp [IsNonneg] at h h'
  cases h with | intro k hk
  cases h' with | intro l hl
  cases hk.right with | intro k1 hk1
  cases hk1 with | intro k2 hk2
  cases hl.right with | intro l1 hl1
  cases hl1 with | intro l2 hl2
  by_cases c1 : 0 < k
  ·
    by_cases c2 : 0 < l
    ·
      rw [hk2] at hl2
      simp [neg_def] at hl2
      rw [neg_eq_iff_add_eq_zero] at hl2
      have k_mul_l1 : 0 < k * l1 := mul_pos c1 l2
      have k1_mul_l : 0 < k1 * l := mul_pos k2 c2
      have final : 0 < k * l1 + k1 * l := add_pos k_mul_l1 k1_mul_l
      exfalso
      rw [hl2] at final
      simp [lt_iff_le_and_ne] at final
    ·
      simp at c2
      have l_eq_zero : l = 0 := le_antisymm c2 hl.left
      rw [l_eq_zero] at hl2
      rw [neg_eq_iff_add_eq_zero, add_comm] at hl2
      rw [←neg_eq_iff_add_eq_zero] at hl2
      simp [neg_def] at hl2
      rw [eq_comm] at hl2
      rw [zero_def, hl2]
      simp
  ·
    simp at c1
    have k_eq_zero : k = 0 := le_antisymm c1 hk.left
    rw [k_eq_zero] at hk2
    rw [zero_def, hk2]
    simp


lemma nonneg_neg_of_not_nonneg {x : MyRat} : ¬ IsNonneg x → IsNonneg (-x) := by
  rw [imp_iff_not_or]
  rw [not_not]
  refine Quot.induction_on x ?_
  rintro ⟨a, b⟩
  simp [IsNonneg]
  by_cases  ha : 0 ≤ a
  ·
    let b' : MyInt := b
    by_cases hb : 0 < b'
    ·
      left
      use a
      use b
      constructor
      ·
        exact hb
      ·
        constructor
        ·
          exact ha
        ·
          ring
    ·
      simp at hb
      have c : b' ≠ 0 := b.property
      have d : b' < 0 := lt_of_le_of_ne hb c
      apply neg_pos_of_neg at d
      right
      use a
      constructor
      ·
        exact ha
      ·
        use -b'
        use d
        simp [neg_def]
        ring
  ·
    simp at ha
    apply neg_pos_of_neg at ha
    apply le_of_lt at ha
    let b' : MyInt := b
    by_cases hb : 0 < b'
    ·
      right
      use -a
      constructor
      ·
        exact ha
      ·
        use b'
        use hb
        simp [neg_def]
        ring
    ·
      simp at hb
      have c : b' ≠ 0 := b.property
      have d : b' < 0 := lt_of_le_of_ne hb c
      apply neg_pos_of_neg at d
      left
      use -a
      use -b'
      constructor
      ·
        exact d
      ·
        constructor
        ·
          exact ha
        ·
          ring


lemma isNonneg_add_isNonneg {x y : MyRat} (hx : IsNonneg x) (hy : IsNonneg y) :
    IsNonneg (x + y) := by
  simp [IsNonneg] at hx hy
  cases hx with | intro x1 hx1
  cases hx1.right with | intro x2 hx2
  cases hx2 with | intro hx3 hx4
  cases hy with | intro y1 hy1
  cases hy1.right with | intro y2 hy2
  cases hy2 with | intro hy3 hy4
  simp [IsNonneg]
  use x1 * y2 + x2 * y1
  constructor
  ·
    have c1 : 0 ≤ x1 * y2 := mul_nonneg hx1.left (le_of_lt hy3)
    have c2 : 0 ≤ x2 * y1 := mul_nonneg (le_of_lt hx3) hy1.left
    linarith
  ·
    use x2 * y2
    have c : 0 < x2 * y2 := mul_pos hx3 hy3
    use c
    rw [hx4, hy4]
    simp [add_def]
    ring



lemma isNonneg_mul_isNonneg {x y : MyRat} (hx : IsNonneg x) (hy : IsNonneg y) :
    IsNonneg (x * y) := by
  simp [IsNonneg] at hx hy
  cases hx with | intro x1 hx1
  cases hx1.right with | intro x2 hx2
  cases hx2 with | intro hx3 hx4
  cases hy with | intro y1 hy1
  cases hy1.right with | intro y2 hy2
  cases hy2 with | intro hy3 hy4
  simp [IsNonneg]
  use x1 * y1
  constructor
  ·
    exact mul_nonneg hx1.left hy1.left
  ·
    use x2 * y2
    have c : 0 < x2 * y2 := mul_pos hx3 hy3
    use c
    rw [hx4, hy4]
    simp [mul_def]
    ring


lemma isNonneg_inv_isNonneg {x : MyRat} : IsNonneg x → IsNonneg x⁻¹ := by
  refine Quot.induction_on  x ?_
  simp [inv_def]
  unfold MyPrerat.inv
  intro a b hb
  split_ifs with hc
  ·
    simp at hc
    intro h
    simp [IsNonneg] at h
    cases h with | intro a_1 h1
    cases h1 with | intro b_1 h2
    simp [IsNonneg]
    use b_1
    use a_1
    constructor
    ·
      have b_1_not_zero : b_1 ≠ 0 := by
        let temp := h2.left
        rw [lt_iff_le_and_ne] at temp
        exact temp.right.symm
      have a_1_not_zero : a_1 ≠ 0 := by
        by_contra wrongc
        let k := h2.right.right
        rw [wrongc, mul_zero] at k
        rw [mul_eq_zero] at k
        contrapose! k
        constructor
        ·
          exact hc
        ·
          exact b_1_not_zero
      exact lt_of_le_of_ne h2.right.left a_1_not_zero.symm
    ·
      constructor
      ·
        exact le_of_lt h2.left
      ·
        rw [h2.right.right]
  ·
    simp at hc
    intro h
    simp [IsNonneg]
    use 1
    linarith


def le (x y : MyRat) : Prop := IsNonneg (y - x)

instance : LE MyRat where
  le := le

lemma le_def (x y : MyRat) : x ≤ y ↔ IsNonneg (y - x) := by
  rfl

lemma zero_le_iff_IsNonneg (x : MyRat) : 0 ≤ x ↔ IsNonneg x := by
  simp [le_def]

lemma zero_le_one : (0 : MyRat) ≤ 1 := by
  simp [le_def]


lemma le_refl (x : MyRat) : x ≤ x := by
  simp [le_def]

lemma le_trans (x y z : MyRat) (h1 : x ≤ y) (h2 : y ≤ z) : x ≤ z := by
  simp [le_def] at h1 h2
  simp [le_def]
  have h3 : IsNonneg (y - x + (z - y)) :=isNonneg_add_isNonneg h1 h2
  simp at h3
  exact h3

lemma le_antisymm (x y : MyRat) (hxy : x ≤ y) (hyx : y ≤ x) : x = y := by
  simp [le_def] at hxy hyx
  rw [sub_eq_add_neg] at hyx
  rw [add_comm] at hyx
  rw [←neg_neg x] at hyx
  rw [←neg_add] at hyx
  rw [←sub_eq_add_neg] at hyx
  have c : y - x = 0 := nonneg_neg hxy hyx
  rw [←zero_add x]
  rw [c.symm]
  ring

instance : PartialOrder MyRat where
  le := (. ≤ .)
  le_refl := le_refl
  le_trans := le_trans
  le_antisymm := le_antisymm

instance : ZeroLEOneClass MyRat := ⟨zero_le_one⟩

lemma add_le_add_left (x y : MyRat) (h : x ≤ y) (t : MyRat) : t + x ≤ t + y := by
  simp_all [le_def]

lemma mul_nonneg (x y : MyRat) (hx : 0 ≤ x) (hy : 0 ≤ y) : 0 ≤ x * y := by
  simp [le_def] at hx hy
  simp [le_def]
  exact isNonneg_mul_isNonneg hx hy

instance : IsOrderedAddMonoid MyRat where
  add_le_add_left := add_le_add_left

instance : IsOrderedRing MyRat :=
  IsOrderedRing.of_mul_nonneg mul_nonneg


lemma j_le_iff (p q : MyInt) : j p ≤ j q ↔ p ≤ q := by
  simp [j]
  constructor
  ·
    intro h
    rcases h with ⟨k, hk⟩
    cases hk with | intro b h1
    cases h1 with | intro c h2
    cases h2 with | intro hb h3
    simp [sub_def] at h3
    rw [h3.symm] at c
    rw [←zero_mul b] at c
    rw [mul_le_mul_right hb] at c
    rw [sub_nonneg] at c
    exact c
  ·
    intro h
    rcases h with ⟨k, hk⟩
    use MyInt.i k
    use 1
    simp
    constructor
    ·
      rw [MyInt.i, MyInt.zero_def]
      use k
      rw [MyInt.i, MyInt.add_def]
      simp
    ·
      simp [sub_def]
      rw [hk]
      ring

lemma i_le_iff (a b : ℕ) : i a ≤ i b ↔ a ≤ b := by
  simp [i]
  rw [←MyInt.i_le_iff]
  constructor
  ·
    intro h
    rcases h with ⟨k, hk⟩
    cases hk with | intro l h1
    cases h1 with | intro c h2
    cases h2 with | intro hl h3
    simp [sub_def] at h3
    rw [h3.symm] at c
    rw [←zero_mul l] at c
    rw [mul_le_mul_right hl] at c
    rw [sub_nonneg] at c
    exact c
  ·
    intro h
    rcases h with ⟨k, hk⟩
    use MyInt.i k
    use 1
    simp
    constructor
    ·
      rw [MyInt.i, MyInt.zero_def]
      use k
      rw [MyInt.i, MyInt.add_def]
      simp
    ·
      simp [sub_def]
      rw [hk]
      ring

lemma i_lt_iff (a b : ℕ) : i a < i b ↔ a < b := by
  constructor
  ·
    intro h
    rw [lt_iff_le_and_ne] at h
    have c : a ≠ b := by
      by_contra temp
      let fal := h.right
      rw [temp] at fal
      tauto
    let d := h.left
    rw [i_le_iff] at d
    exact lt_of_le_of_ne d c
  ·
    intro h
    rw [lt_iff_le_and_ne] at h
    rw [lt_iff_le_and_ne]
    constructor
    ·
      let temp := h.left
      rw [←i_le_iff] at temp
      exact temp
    ·
      by_contra cc
      apply i_injective at cc
      tauto

lemma le_total (a b : MyRat) : a ≤ b ∨ b ≤ a := by
  simp [le_def, sub_def]
  rw [sub_eq_add_neg, add_comm]
  nth_rw 1 [←neg_neg b, ←neg_add]
  rw [←sub_eq_add_neg]
  by_cases h : (a - b).IsNonneg
  ·
    right
    exact h
  ·
    left
    exact nonneg_neg_of_not_nonneg h


noncomputable instance linearOrder : LinearOrder MyRat where
  le_total := le_total
  toDecidableLE := Classical.decRel _

lemma mul_pos (a b : MyRat) (ha : 0 < a) (hb : 0 < b) : 0 < a * b := by
  rw [lt_iff_le_and_ne] at ha hb
  have c : 0 ≤ a * b := mul_nonneg a b ha.left hb.left
  have d : 0 ≠ a * b := by
    by_contra d'
    rw [eq_comm] at d'
    rw [mul_eq_zero] at d'
    tauto
  exact lt_of_le_of_ne c d

noncomputable instance : IsStrictOrderedRing MyRat :=
  IsStrictOrderedRing.of_mul_pos mul_pos


lemma archimedean (x : MyRat) : ∃ (n : ℕ), x ≤ i n := by
  refine Quot.induction_on x ?_
  simp [i, MyInt.i]
  intro a b
  refine Quot.induction_on₂ a b ?_
  simp
  intro a1 a2 b1 b2 hb
  simp [MyInt.zero_def] at hb

  by_cases h : b2 < b1
  ·
    use a1
    simp [le_def, IsNonneg, sub_def, MyInt.mul_def]
    rw [sub_eq_add_neg, MyInt.neg_def, MyInt.add_def]
    apply Nat.succ_le_of_lt at h
    rw [Nat.succ_eq_add_one, le_iff_exists_add] at h
    rcases h with ⟨delta, h'⟩
    let a' : MyInt := ⟦(a1 * delta + a2, 0)⟧
    let b' : MyInt := ⟦(delta + 1, 0)⟧
    have a'_def : a' = ⟦(a1 * delta + a2, 0)⟧ := by rfl
    have b'_def : b' = ⟦(delta + 1, 0)⟧ := by rfl
    use a'
    use b'
    constructor
    ·
      rw [b'_def, MyInt.zero_def]
      rw [lt_iff_le_and_ne]
      constructor
      ·
        use (delta + 1)
        simp [MyInt.i, MyInt.zero_def]
      ·
        by_contra j
        simp at j

    ·
      constructor
      ·
        rw [a'_def, MyInt.zero_def]
        use (a1 * delta + a2)
        simp [MyInt.i, MyInt.zero_def]
      ·
        rw [a'_def, b'_def]
        simp [MyInt.mul_def]
        rw [h']
        ring
  ·
    use a2
    simp [le_def, IsNonneg, sub_def, MyInt.mul_def]
    rw [sub_eq_add_neg, MyInt.neg_def, MyInt.add_def]
    simp at h
    let k := lt_of_le_of_ne h hb
    apply Nat.succ_le_of_lt at k
    rw [Nat.succ_eq_add_one, le_iff_exists_add] at k
    rcases k with ⟨delta, k'⟩
    let a' : MyInt := ⟦(a2 * delta + a1, 0)⟧
    let b' : MyInt := ⟦(delta + 1, 0)⟧
    have a'_def : a' = ⟦(a2 * delta + a1, 0)⟧ := by rfl
    have b'_def : b' = ⟦(delta + 1, 0)⟧ := by rfl
    use a'
    use b'
    constructor
    ·
      rw [b'_def, MyInt.zero_def]
      rw [lt_iff_le_and_ne]
      constructor
      ·
        use (delta + 1)
        simp [MyInt.i, MyInt.zero_def]
      ·
        by_contra j
        simp at j
    ·
      constructor
      ·
        rw [a'_def, MyInt.zero_def]
        use (a2 * delta + a1)
        simp [MyInt.i, MyInt.zero_def]
      ·
        rw [a'_def, b'_def]
        simp [MyInt.mul_def]
        rw [k']
        ring


end MyRat

end rationals

section reals

abbrev IsCauchy (x : ℕ → MyRat) : Prop :=
  ∀ ε, 0 < ε → ∃ N, ∀ p q, N ≤ p → N ≤ q → |x p - x q| ≤ ε

--open Finset in

lemma List.le_foldr_max_of_mem {α : Type} [LinearOrder α] {a : α} {l : List α} {init : α}
    (h : a ∈ l) (hinit : ∀ b ∈ l, init ≤ b) : a ≤ l.foldr max init := by
  induction l with
  | nil => cases h
  | cons x xs ih =>
    cases h with
    | head => simp [max_le_iff, le_refl]
    | tail _ h =>
      simp [foldr]
      right
      simp [cons] at hinit
      exact (ih h hinit.right)

lemma IsCauchy.bounded {x : ℕ → MyRat} (hx : IsCauchy x) : ∃ B, 0 < B ∧ ∀ n, |x n| ≤ B := by
  simp [IsCauchy] at hx
  obtain ⟨N, hN⟩ := hx 1 zero_lt_one
  have tail_bound : ∀ n ≥ N, |x n| ≤ |x N| + 1 := by
    intro n hn
    let temp1 := hN n N hn (le_refl N)
    let temp2 := abs_add (x n - x N) (x N)
    simp at temp2
    linarith
  let lst := ((List.range N).map (fun n => |x n|))
  let B' : MyRat := lst.foldr max 0
  let B := max B' (|x N| + 1)

  have B_pos : 0 < B := by
    have temp: |x N| + 1 ≤ B := by
      let why := le_max_right B' (|x N| + 1)
      exact why
    have temp' : 0 < |x N| + 1 := by
      let u := abs_nonneg (x N)
      let v := add_le_add_right u 1
      linarith
    exact lt_of_lt_of_le temp' temp

  use B
  constructor
  ·
    exact B_pos
  ·
    intro n
    by_cases h : n < N
    ·
      unfold B
      have temp : |x n| ≤ B' := by
        unfold B'
        have h_mem : |x n| ∈ lst := by
          unfold lst
          simp [List.mem_map, List.mem_range]
          exact ⟨n, h, rfl⟩
        have hinit : ∀ b ∈ lst, 0 ≤ b := by
          unfold lst
          simp [List.mem_map, List.mem_range]
        exact List.le_foldr_max_of_mem h_mem hinit

      exact le_trans temp (le_max_left B' (|x N| + 1))
    ·
      simp at h
      let w := tail_bound n h
      let w' := le_max_right B' (|x N| + 1)
      exact le_trans w w'

abbrev MyPrereal := {x // IsCauchy x}

namespace MyPrereal

open MyPrereal

instance funLike : FunLike MyPrereal ℕ MyRat where
  coe := Subtype.val
  coe_injective' _ _ := Subtype.ext

lemma prop (x : MyPrereal) : ∀ ε, 0 < ε → ∃ N, ∀ p q, N ≤ p → N ≤ q → |x p - x q| ≤ ε :=
  x.2

@[simp] lemma coe_apply {x : ℕ → MyRat} (hx : IsCauchy x) (n : ℕ) :
    (⟨x, hx⟩ : MyPrereal) n = x n := by
  rfl

lemma bounded (x : MyPrereal) : ∃ B, 0 < B ∧ ∀ n, |x n| ≤ B :=
  x.2.bounded

def R (x y : MyPrereal) : Prop := ∀ ε, 0 < ε → ∃ N, ∀ n, N ≤ n → |x n - y n| ≤ ε

lemma R_def (x y : MyPrereal) : R x y ↔ ∀ ε, 0 < ε → ∃ N, ∀ n, N ≤ n → |x n - y n| ≤ ε := by
  rfl

lemma R_refl : ∀ x, R x x := by
  intro x
  simp [R]
  intro ε hε
  use 0
  simp
  linarith

lemma R_symm : ∀ {x y}, R x y → R y x := by
  intro x y
  simp [R]
  intro h ε hε
  rcases h ε (by linarith) with ⟨N, hN⟩
  use N
  intro n hn
  rw [abs_sub_comm]
  exact hN n hn


lemma R_trans : ∀ {x y z}, R x y → R y z → R x z := by
  intro x y z hxy hyz
  simp [R] at hxy hyz
  simp [R]
  intro ε hε
  rcases hxy (ε/2) (by linarith) with ⟨N, hN⟩
  rcases hyz (ε/2) (by linarith) with ⟨M, hM⟩
  use max N M
  intro n hn
  have c1 : |x n - y n| ≤ ε/2 := hN n (le_trans (le_max_left N M) hn)
  have c2 : |y n - z n| ≤ ε/2 := hM n (le_trans (le_max_right N M) hn)
  have c : |(x n - y n) + (y n - z n)| ≤ |x n - y n| + |y n - z n| := abs_add (x n - y n) (y n - z n)
  have final : |(x n - y n) + (y n - z n)| ≤ ε/2 + ε/2:= by
    exact le_trans c (add_le_add c1 c2)
  simp at final
  exact final

instance R_equiv : Setoid MyPrereal where
  r := R
  iseqv := ⟨R_refl, R_symm, R_trans⟩

@[simp] lemma equiv_def (x y : MyPrereal) : x ≈ y ↔
    ∀ ε, 0 < ε → ∃ N, ∀ n, N ≤ n → |x n - y n| ≤ ε := by
  rfl

@[simp] lemma equiv_def' (x y : MyPrereal) : Setoid.r x y ↔
    ∀ ε, 0 < ε → ∃ N, ∀ n, N ≤ n → |x n - y n| ≤ ε := by
  rfl

lemma IsCauchy.const (x : MyRat) : IsCauchy (fun _ ↦ x) := by
  intro ε hε
  use 0
  simp
  linarith

instance zero : Zero MyPrereal where
  zero := ⟨0, IsCauchy.const 0⟩

@[simp] lemma zero_def (n : ℕ) : (0 : MyPrereal) n = 0 := by
  rfl

instance one : One MyPrereal where
  one := ⟨1, IsCauchy.const 1⟩

@[simp] lemma one_def (n : ℕ) : (1 : MyPrereal) n = 1 := by
  rfl

lemma IsCauchy.neg {x : ℕ → MyRat} (hx : IsCauchy x) : IsCauchy (-x) := by
  simp [IsCauchy] at hx
  simp [IsCauchy]
  intro ε hε
  rcases hx ε hε with ⟨N, hN⟩
  use N
  intro p q hp hq
  let final := hN p q hp hq
  rw [←neg_neg (x q), ←neg_add, ←sub_eq_add_neg, abs_neg]
  exact final

instance : Neg MyPrereal where
  neg x := ⟨-x, x.2.neg⟩

@[simp] lemma neg_def (x : MyPrereal) (n : ℕ) : (-x) n = -x n := by
  rfl

lemma neg_quotient ⦃x x' : MyPrereal⦄ (h : x ≈ x') : -x ≈ -x' := by
  simp [neg_def] at h
  simp [neg_def]
  intro ε hε
  rcases h ε hε with ⟨N, hN⟩
  use N
  intro n hn
  rw [←neg_neg (x' n), ←neg_add, ←sub_eq_add_neg]
  let temp := hN n hn
  rw [←abs_neg] at temp
  exact temp

lemma IsCauchy.add {x y : ℕ → MyRat} (hx : IsCauchy x) (hy : IsCauchy y) : IsCauchy (x + y) := by
  simp [IsCauchy] at hx hy
  simp [IsCauchy]
  intro ε hε
  rcases hx (ε/2) (by linarith) with ⟨N, hN⟩
  rcases hy (ε/2) (by linarith) with ⟨M, hM⟩
  use max N M
  intro p q hp hq
  let h1 := hN p q (le_trans (le_max_left N M) hp) (le_trans (le_max_left N M) hq)
  let h2 := hM p q (le_trans (le_max_right N M) hp) (le_trans (le_max_right N M) hq)
  let final := le_trans (abs_add (x p - x q) (y p - y q)) (add_le_add h1 h2)
  simp at final
  rw [sub_add_eq_add_sub] at final
  rw [←add_sub_assoc] at final
  rw [sub_eq_add_neg (x p + y p) (y q)] at final
  rw [sub_eq_add_neg] at final
  rw [add_assoc, ←neg_add] at final
  rw [add_comm (y q) (x q), ←sub_eq_add_neg] at final
  exact final

instance : Add MyPrereal where
  add x y := ⟨x + y, x.2.add y.2⟩

instance : Sub MyPrereal where
  sub x y := x + -y

@[simp] lemma add_def (x y : MyPrereal) (n : ℕ) : (x + y) n = x n + y n := by
  rfl

@[simp] lemma sub_def (x y : MyPrereal) (n : ℕ) : (x - y) n = x n - y n := by
  rfl

lemma add_quotient ⦃x x' : MyPrereal⦄ (h : x ≈ x') ⦃y y' : MyPrereal⦄ (h' : y ≈ y') :
    x + y ≈ x' + y' := by
  simp at h h'
  simp
  intro ε hε
  rcases h (ε/2) (by linarith) with ⟨N, hN⟩
  rcases h' (ε/2) (by linarith) with ⟨M, hM⟩
  use max N M
  intro n hn
  let h1 := hN n (le_trans (le_max_left N M) hn)
  let h2 := hM n (le_trans (le_max_right N M) hn)
  let final := le_trans (abs_add (x n - x' n) (y n - y' n)) (add_le_add h1 h2)
  simp at final
  rw [sub_add_eq_add_sub] at final
  rw [←add_sub_assoc] at final
  rw [sub_eq_add_neg (x n + y n) (y' n)] at final
  rw [sub_eq_add_neg] at final
  rw [add_assoc, ←neg_add] at final
  rw [add_comm (y' n) (x' n), ←sub_eq_add_neg] at final
  exact final


lemma IsCauchy.mul {x y : ℕ → MyRat} (hx : IsCauchy x) (hy : IsCauchy y) : IsCauchy (x * y) := by
  let h1 := IsCauchy.bounded hx
  let h2 := IsCauchy.bounded hy
  rcases h1 with ⟨Mx, h3⟩
  rcases h2 with ⟨My, h4⟩
  simp [IsCauchy] at hx hy
  simp [IsCauchy]
  intro ε hε
  have Mx_My_nonneg : 0 < Mx + My := by
    exact add_lt_add h3.left h4.left

  obtain ⟨N, hN⟩ := hx (ε/(Mx + My)) (div_pos hε Mx_My_nonneg)
  obtain ⟨M, hM⟩ := hy (ε/(Mx + My)) (div_pos hε Mx_My_nonneg)
  use max N M
  intro p q hp hq
  let h5 := hN p q (le_trans (le_max_left N M) hp) (le_trans (le_max_left N M) hq)
  let h6 := hM p q (le_trans (le_max_right N M) hp) (le_trans (le_max_right N M) hq)
  let y_p_le := h4.right p
  let x_q_le := h3.right q
  let h7 := mul_le_mul h5 y_p_le (abs_nonneg y p) (le_of_lt (div_pos hε Mx_My_nonneg))
  let h8 := mul_le_mul h6 x_q_le (abs_nonneg x q) (le_of_lt (div_pos hε Mx_My_nonneg))
  simp [←abs_mul] at h7 h8
  let temp := add_le_add h7 h8
  rw [←mul_add] at temp
  rw [add_comm My Mx] at temp
  rw [div_eq_mul_inv, mul_assoc, mul_comm _ (Mx + My)] at temp
  let fuck := ne_of_gt Mx_My_nonneg
  have temp' : (Mx + My) * (Mx + My)⁻¹ = 1 := MyRat.mul_inv_cancel (Mx + My) fuck
  rw [temp', mul_one] at temp
  let final := le_trans (abs_add ((x p - x q) * y p) ((y p - y q) * x q)) temp
  simp [sub_mul, mul_sub]at final
  rw [mul_comm (y p) (x q)] at final
  have key : x p * y p - x q * y p + (x q * y p - y q * x q) = x p * y p - x q * y q := by ring
  rw [key] at final
  exact final


instance : Mul MyPrereal where
  mul x y := ⟨x * y, x.2.mul y.2⟩

@[simp] lemma mul_def (x y : MyPrereal) (n : ℕ) : (x * y) n = x n * y n := by
  rfl

lemma mul_quotient ⦃x x' : MyPrereal⦄ (h : x ≈ x') ⦃y y' : MyPrereal⦄ (h' : y ≈ y') :
    x * y ≈ x' * y' := by
  simp at h h'
  simp
  have c1 := IsCauchy.bounded x.2
  have c2 := IsCauchy.bounded y'.2
  intro ε hε
  rcases c1 with ⟨b1, hb1, hc1⟩
  rcases c2 with ⟨b2, hb2, hc2⟩
  have b1_b2_pos := add_lt_add hb1 hb2
  simp at b1_b2_pos
  rcases h (ε / (b1 + b2)) (div_pos hε b1_b2_pos) with ⟨N1, hN1⟩
  rcases h' (ε / (b1 + b2)) (div_pos hε b1_b2_pos) with ⟨N2, hN2⟩
  use max N1 N2
  intro n hn
  have h1 := hN1 n (le_trans (le_max_left N1 N2) hn)
  have h2 := hN2 n (le_trans (le_max_right N1 N2) hn)
  have h3 := hc1 n
  have h4 := hc2 n
  have temp : x n * y n - x' n * y' n = (y n - y' n) * x n + (x n - x' n) * y' n := by ring
  rw [temp]
  have b1_b2_ne_zero : b1 + b2 ≠ 0 := by
    rw [lt_iff_le_and_ne] at b1_b2_pos
    exact b1_b2_pos.right.symm
  have obvious : ε = ε / (b1 + b2) * b1 + ε / (b1 + b2) * b2 := by
    rw [←mul_add, div_eq_mul_inv, mul_assoc, mul_comm _ (b1 + b2)]
    rw [MyRat.mul_inv_cancel (b1 + b2) b1_b2_ne_zero, mul_one]
  rw [obvious]
  have temp1 : |(x n - x' n) * y' n| ≤ ε / (b1 + b2) * b2 := by
    rw [abs_mul]
    exact mul_le_mul h1 h4 (abs_nonneg (y' n)) (le_of_lt (div_pos hε b1_b2_pos))
  have temp2 : |(y n - y' n) * x n| ≤ ε / (b1 + b2) * b1 := by
    rw [abs_mul]
    exact mul_le_mul h2 h3 (abs_nonneg (x n)) (le_of_lt (div_pos hε b1_b2_pos))
  exact le_trans (abs_add ((y n - y' n) * x n) ((x n - x' n) * y' n)) (add_le_add temp2 temp1)

lemma pos_of_not_equiv_zero {x : MyPrereal} (H : ¬(x ≈ 0)) :
    ∃ δ, 0 < δ ∧ ∃ N, ∀ n, N ≤ n → δ < |x n| := by
  let h := x.2
  simp [IsCauchy] at h
  simp at H
  rcases H with ⟨δ, hδ, H'⟩
  rcases h (δ/2) (by linarith) with ⟨N, hN⟩
  use (δ/2)
  constructor
  ·
    linarith
  ·
    rcases H' N with ⟨N', hn⟩
    use N'
    intro n cn
    let final := hN N' n hn.left (le_trans hn.left cn)
    have temp : |x N'| - |x n| ≤ δ/2 := by
      exact le_trans (abs_sub_abs_le_abs_sub (x N') (x n)) final
    linarith

lemma IsCauchy.inv {x : MyPrereal} (H : ¬(x ≈ 0)) : IsCauchy (x⁻¹) := by
  apply pos_of_not_equiv_zero at H
  simp [IsCauchy]
  intro ε hε
  rcases H with ⟨δ, hδ, N, h'⟩
  have C := x.2
  simp [IsCauchy] at C
  rcases C (ε * δ * δ) (mul_pos (mul_pos hε hδ) hδ) with ⟨N', hN⟩
  use max N N'
  intro p q hp hq
  have δp := h' p (le_trans (le_max_left N N') hp)
  have δq := h' q (le_trans (le_max_left N N') hq)
  have temp : |x p - x q| ≤ ε * δ *δ := by
    exact hN p q (le_trans (le_max_right N N') hp) (le_trans (le_max_right N N') hq)
  have final : δ * δ < |x p * x q| := by
    have temp' : |x p * x q| = |x p| * |x q| := abs_mul (x p) (x q)
    rw [temp']
    have c1 : δ * δ < |x p| * δ := by gcongr
    have x_p_pos := lt_trans hδ δp
    have c2 : |x p| * δ < |x p| * |x q| := by gcongr
    exact lt_trans c1 c2
  have final' : 1 / |x p * x q| < 1 / (δ * δ) := by
    gcongr
  have final'' : |(x q - x p) / (x p * x q)| < ε := by
    simp [abs_div, abs_sub_comm]
    have o0 : 0 < 1 / |x p * x q| := by
      simp
      constructor
      ·
        let x_p_pos := lt_trans hδ δp
        rw [abs_pos] at x_p_pos
        exact x_p_pos
      ·
        let x_q_pos := lt_trans hδ δq
        rw [abs_pos] at x_q_pos
        exact x_q_pos
    have o1 : |x p - x q| * (1 / |x p * x q|) ≤ ε * δ * δ * (1 / |x p * x q|) := by gcongr
    have o2 : ε * δ * δ * (1 / |x p * x q|) < ε * δ * δ * (1 / (δ * δ)) := by gcongr
    simp at o2
    have o3 : ε * δ * δ * (δ⁻¹ * δ⁻¹) = ε := by
      rw [mul_assoc, ←mul_assoc δ, MyRat.mul_inv_cancel, one_mul, mul_assoc, MyRat.mul_inv_cancel, mul_one]
      ·
        rw [lt_iff_le_and_ne] at hδ
        exact hδ.right.symm
      ·
        rw [lt_iff_le_and_ne] at hδ
        exact hδ.right.symm
    rw [o3] at o2
    rw [div_eq_mul_inv, one_mul] at o1
    let final''' := lt_of_le_of_lt o1 o2
    rw [div_eq_mul_inv]
    exact final'''
  rw [inv_sub_inv]
  ·
    exact le_of_lt final''
  ·
    let temp := lt_trans hδ δp
    rw [lt_iff_le_and_ne] at temp
    rw [←abs_ne_zero]
    exact temp.right.symm
  ·
    let temp := lt_trans hδ δq
    rw [lt_iff_le_and_ne] at temp
    rw [←abs_ne_zero]
    exact temp.right.symm

open Classical in
noncomputable def inv (x : MyPrereal) : MyPrereal := if H : ¬(x ≈ 0) then ⟨_, IsCauchy.inv H⟩ else 0

@[simp] lemma inv_def {x : MyPrereal} (H : ¬(x ≈ 0)) (n : ℕ) :
    inv x n = (x n)⁻¹ := by
  simp [inv]
  split_ifs
  ·
    simp

@[simp] lemma inv_def' {x : MyPrereal} (H : ¬(x ≈ 0)) (n : ℕ) :
    (⟨x⁻¹, IsCauchy.inv H⟩ : MyPrereal) n = (x n)⁻¹ := by
  rfl

lemma inv_quotient ⦃x x' : MyPrereal⦄ (h : x ≈ x') : inv x ≈ inv x' := by
  simp only [inv]
  split_ifs
  ·
    rfl
  ·
    rename_i ha hb
    have temp : x' ≈ 0 := by
      apply R_trans (R_symm h) ha
    tauto
  ·
    rename_i ha hb
    have temp : x ≈ 0 := by
      apply R_trans h hb
    tauto
  ·
    rename_i hx hx'
    simp at h
    simp
    apply pos_of_not_equiv_zero at hx
    apply pos_of_not_equiv_zero at hx'
    rcases hx with ⟨δ1, hδ1, N1, hN1⟩
    rcases hx' with ⟨δ2, hδ2, N2, hN2⟩
    intro ε hε
    rcases h (ε * δ1 * δ2) (mul_pos (mul_pos hε hδ1) hδ2) with ⟨N, hN⟩
    let M := max (max N1 N2) N
    have N1_le_M : N1 ≤ M := by
      exact le_trans (le_max_left N1 N2) (le_max_left (max N1 N2) N)
    have N2_le_M : N2 ≤ M := by
      exact le_trans (le_max_right N1 N2) (le_max_left (max N1 N2) N)
    have N_le_M : N ≤ M := by
      exact le_max_right (max N1 N2) N
    use M
    intro n hn
    have c1 := hN1 n (by linarith)
    have c2 := hN2 n (by linarith)
    have c := hN n (by linarith)
    rw [inv_sub_inv]
    ·
      rw [abs_div, div_eq_mul_inv, abs_mul, abs_sub_comm]
      have x_n_pos := lt_trans hδ1 c1
      have x'_n_pos := lt_trans hδ2 c2
      have temp : δ1 * δ2 < |x n| * |x' n| :=by gcongr
      rw [mul_assoc] at c
      have δ1_δ2_pos := mul_pos hδ1 hδ2
      have xn_x'n_pos := mul_pos x_n_pos x'_n_pos
      have next : ε = ε * (δ1 * δ2) * (δ1 * δ2)⁻¹ := by
        rw [mul_assoc, MyRat.mul_inv_cancel, mul_one]
        rw [lt_iff_le_and_ne] at δ1_δ2_pos
        exact δ1_δ2_pos.right.symm
      rw [next]
      have final : (|x n| * |x' n|)⁻¹ < (δ1 * δ2)⁻¹ :=by
        rw [inv_lt_inv₀ (by linarith) (by linarith)]
        linarith
      gcongr
    ·
      apply (lt_trans hδ1) at c1
      rw [lt_iff_le_and_ne] at c1
      rw [←abs_ne_zero]
      exact c1.right.symm
    ·
      apply (lt_trans hδ2) at c2
      rw [lt_iff_le_and_ne] at c2
      rw [←abs_ne_zero]
      exact c2.right.symm

end MyPrereal

open MyPrereal

abbrev MyReal := Quotient R_equiv

namespace MyReal

@[simp] lemma Quot_eq_Quotient (x : MyPrereal) : Quot.mk Setoid.r x = ⟦x⟧ := by
  rfl

instance zero : Zero MyReal where
  zero := ⟦0⟧

lemma zero_def : (0 : MyReal) = ⟦0⟧ := by
  rfl

instance one : One MyReal where
  one := ⟦1⟧

lemma one_def : (1 : MyReal) = ⟦1⟧ := by
  rfl

def neg : MyReal → MyReal := Quotient.map _ neg_quotient

instance : Neg MyReal where
  neg := neg

lemma neg_def (x : MyPrereal) : -(⟦x⟧ : MyReal) = ⟦-x⟧ := by
  rfl

def add : MyReal → MyReal → MyReal  := Quotient.map₂ _ add_quotient

instance : Add MyReal
  where add := add

lemma add_def (x y : MyPrereal) : (⟦x⟧ : MyReal) + (⟦y⟧ : MyReal) = ⟦x + y⟧ := by
  rfl

def mul : MyReal → MyReal → MyReal  := Quotient.map₂ _ mul_quotient

instance : Mul MyReal where
  mul := mul

lemma mul_def (x y : MyPrereal) : (⟦x⟧ : MyReal) * (⟦y⟧ : MyReal) = ⟦x * y⟧ := by
  rfl

noncomputable
def inv : MyReal → MyReal := Quotient.map _ inv_quotient

noncomputable
instance : Inv MyReal := ⟨inv⟩

lemma inv_def (x : MyPrereal) : (⟦x⟧ : MyReal)⁻¹ = ⟦MyPrereal.inv x⟧ := by
  rfl

macro "quot_proof₁" : tactic =>
  `(tactic|
  focus
    intro x
    refine Quot.induction_on x ?_
    intro a
    apply Quot.sound
    simp
    intro ε hε
    use 0
    intro n hn
    try {ring_nf; simp [hε.le]})

macro "quot_proof₂" : tactic =>
  `(tactic|
  focus
    intro x y
    refine Quot.induction_on₂ x y ?_
    intro a b
    apply Quot.sound
    simp
    intro ε hε
    use 0
    intro n hn
    try {ring_nf; simp [hε.le]})

macro "quot_proof₃" : tactic =>
  `(tactic|
  focus
    intro x y z
    refine Quot.induction_on₃ x y z ?_
    intro a b c
    apply Quot.sound
    simp
    intro ε hε
    use 0
    intro n hn
    try { ring_nf; simp [hε.le] })

macro "quot_proof" : tactic =>
  `(tactic|
  focus
    try quot_proof₁
    try quot_proof₂
    try quot_proof₃)

instance commRing : CommRing MyReal where
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
  nsmul := nsmulRec
  zsmul := zsmulRec

lemma sub_def (x y : MyPrereal) : (⟦x⟧ : MyReal) - (⟦y⟧ : MyReal) = ⟦x - y⟧ := by
  rfl

lemma zero_ne_one : (0 : MyReal) ≠ 1 := by
  simp [zero_def, one_def]
  use 0.5
  constructor
  ·
    linarith
  ·
    intro x
    constructor
    ·
      use x
    ·
      linarith

lemma mul_inv_cancel (x : MyReal) : x ≠ 0 → x * x⁻¹ = 1 := by
  refine Quot.induction_on x ?_
  rintro ⟨a, ha⟩
  simp [inv_def, MyPrereal.inv]
  intro h
  split_ifs with c
  ·
    contrapose! h
    exact Quot.sound c
  ·
    rw [one_def, mul_def]
    simp [MyPrereal.inv_def]
    apply pos_of_not_equiv_zero at c
    simp at c
    rcases c with ⟨min, hn, h'⟩
    intro ε hε
    rcases h' with ⟨N, hN⟩
    use N
    intro n cn
    let final := hN n cn
    let final' := (lt_trans hn final)
    rw [lt_iff_le_and_ne] at final'
    rcases final' with ⟨hx, hy⟩
    let temp := Ne.symm hy
    rw [abs_ne_zero] at temp
    rw [MyRat.mul_inv_cancel (a n) temp]
    simp
    exact le_of_lt hε



noncomputable
instance field : Field MyReal where
  exists_pair_ne := ⟨0, 1, zero_ne_one⟩
  mul_inv_cancel := mul_inv_cancel
  inv_zero := by
    apply Quot.sound
    simp only [MyPrereal.inv, Setoid.refl, not_true_eq_false, reduceDIte, equiv_def',
      MyPrereal.zero_def, sub_self, abs_zero]
    intro ε hε
    exact ⟨0, fun _ _ ↦ hε.le⟩
  qsmul := _
  nnqsmul := _

def k (x : MyRat) : MyReal := ⟦⟨_, IsCauchy.const x⟩⟧

@[simp] lemma k_zero : k 0 = 0 := by
  rfl

@[simp] lemma k_one : k 1 = 1 := by
  rfl

@[simp] lemma k_neg (x : MyRat) : k (-x) = -(k x) := by
  rfl

lemma k_add (x y : MyRat) : k (x + y) = k x + k y := by
  rfl

lemma k_sub (x y : MyRat) : k (x - y) = k x - k y := by
  rfl

lemma k_mul (x y : MyRat) : k (x * y) = k x * k y := by
  rfl

lemma k_injective : Function.Injective k := by
  intro x y h
  simp [k] at h
  by_contra h''
  have h' : x ≠ y := h''
  rw [←sub_ne_zero] at h'
  rw [←abs_ne_zero] at h'
  let temp := abs_nonneg (x - y)
  let x_y_lt := lt_of_le_of_ne temp h'.symm
  rcases h (|x - y|/2) (by linarith) with ⟨N, hN⟩
  let final := hN N (by linarith)
  linarith

lemma k_inv (x : MyRat) : k x⁻¹ = (k x)⁻¹ := by
  simp only [k, inv_def, MyPrereal.inv]
  split_ifs
  ·
    rename_i h
    simp [Quotient.eq]
    simp at h
    by_cases h' : x = 0
    ·
      rw [h', inv_zero]
      intro ε hε
      use 0
      intro n hn
      simp
      exact le_of_lt hε
    ·
      have h'' : x ≠ 0 := h'
      rw [←abs_ne_zero] at h''
      have temp : 0 < |x| := by
        exact lt_of_le_of_ne (abs_nonneg x) h''.symm
      rcases h (|x|/2) (by linarith) with ⟨N, hN⟩
      have final : |x| ≤ |x|/2 := by
        exact hN N (by linarith)
      have final' : |x| - (|x|/2) ≤ 0 := by
        linarith
      have final'' : |x| ≤ 0 := by
        linarith
      have final''' : |x| = 0 := (le_antisymm final'' (abs_nonneg x))
      rw [abs_eq_zero] at final'''
      tauto
  ·
    rename_i h
    simp [Quotient.eq]
    simp at h
    intro ε hε
    use 0
    intro n hn
    exact le_of_lt hε


@[simp] lemma k_inj {x y : MyRat} : k x = k y ↔ x = y :=
  k_injective.eq_iff

end MyReal

namespace MyPrereal

def IsPos (x : MyPrereal) : Prop :=
  ∃ δ, 0 < δ ∧ ∃ N, ∀ n, N ≤ n → δ ≤ x n

lemma pos_of_isPos {x : MyPrereal} (hx : IsPos x) :
    ∃ N, ∀ n, N ≤ n → 0 < x n := by
  rcases hx with ⟨δ, h1, h2⟩
  rcases h2 with ⟨N, hN⟩
  use N
  intro n hn
  exact lt_of_lt_of_le h1 (hN n hn)

@[simp] lemma one_pos : IsPos 1 := by
  simp [IsPos]
  use 1
  simp

lemma not_isPos_zero {x : MyPrereal} (hx : x ≈ 0) : ¬ IsPos x := by
  by_contra hy
  simp [IsPos] at hy
  simp at hx
  rcases hy with ⟨δ, hδ, N1, hN1⟩
  rcases hx (δ/2) (by linarith) with ⟨N2, hN2⟩
  rcases hN1 (max N1 N2) (le_max_left N1 N2) with h1
  rcases hN2 (max N1 N2) (le_max_right N1 N2) with h2
  simp [abs] at h2
  let final := le_trans h1 h2.left
  linarith


lemma not_isPos_zero' {x : MyPrereal} (hx : (⟦x⟧ : MyReal) = 0) : ¬ IsPos x := by
  rw [MyReal.zero_def, Quotient.eq] at hx
  exact not_isPos_zero hx

lemma not_equiv_zero_of_isPos {x : MyPrereal} (hx : IsPos x) : ¬(x ≈ 0) := by
  contrapose! hx
  exact not_isPos_zero hx

lemma not_equiv_zero_of_isPos' {x : MyPrereal} (hx : IsPos x) : (⟦x⟧ : MyReal) ≠ 0 := by
  simp
  rw [MyReal.zero_def, Quotient.eq]
  exact not_equiv_zero_of_isPos hx

lemma isPos_quotient ⦃x x' : MyPrereal⦄ (h : x ≈ x') (hx : IsPos x) : IsPos x' := by
  simp at h
  simp [IsPos] at hx
  simp [IsPos]
  rcases hx with ⟨δ, hδ, N, hN⟩
  use (δ/2)
  constructor
  ·
    linarith
  ·
    rcases h (δ/2) (by linarith) with ⟨N1, h1⟩
    use max N N1
    intro n' hn
    have temp : |x n' - x' n'| ≤ δ/2 := by
      exact h1 n' (le_trans (le_max_right N N1) hn)
    simp [abs] at temp
    rcases temp with ⟨c1, c2⟩
    have temp' : δ ≤ x n' := by
      exact hN n' (le_trans (le_max_left N N1) hn)
    let final :=le_trans temp' c1
    linarith


lemma IsPos.add {x y : MyPrereal} (hx : IsPos x) (hy : IsPos y) : IsPos (x + y) := by
  simp [IsPos] at hx hy
  simp [IsPos]
  rcases hx with ⟨δ1, hδ1, N1, hN1⟩
  rcases hy with ⟨δ2, hδ2, N2, hN2⟩
  use δ1 + δ2
  constructor
  ·
    linarith
  ·
    use max N1 N2
    intro n hn
    have temp1 := hN1 n (le_trans (le_max_left N1 N2) hn)
    have temp2 := hN2 n (le_trans (le_max_right N1 N2) hn)
    linarith

lemma IsPos.mul {x y : MyPrereal} (hx : IsPos x) (hy : IsPos y) : IsPos (x * y) := by
  simp [IsPos] at hx hy
  simp [IsPos]
  rcases hx with ⟨δ1, hδ1, N1, hN1⟩
  rcases hy with ⟨δ2, hδ2, N2, hN2⟩
  use δ1 * δ2
  constructor
  ·
    exact MyRat.mul_pos δ1 δ2 hδ1 hδ2
  ·
    use max N1 N2
    intro n hn
    have temp1 := hN1 n (le_trans (le_max_left N1 N2) hn)
    have temp2 := hN2 n (le_trans (le_max_right N1 N2) hn)
    gcongr
    exact le_of_lt (lt_of_lt_of_le hδ1 temp1)


def IsNonneg (x : MyPrereal) : Prop :=
  IsPos x ∨ x ≈ 0

lemma IsNonneg_of_equiv_zero {x : MyPrereal} (hx : x ≈ 0) : IsNonneg x := by
  simp only [IsNonneg]
  right
  exact hx

lemma IsNonneg_of_nonneg {x : MyPrereal} (N : ℕ) (hx : ∀ n, N ≤ n → 0 ≤ x n) : IsNonneg x := by
  simp [IsNonneg, IsPos]
  by_cases h : x ≈ 0
  ·
    simp at h
    right
    exact h
  ·
    left
    apply pos_of_not_equiv_zero at h
    rcases h with ⟨δ, hδ, N', hN⟩
    use δ
    constructor
    ·
      linarith
    ·
      use max N N'
      intro n hn
      have temp1 := hx n (le_trans (le_max_left N N') hn)
      have temp2 := hN n (le_trans (le_max_right N N') hn)
      rw [abs_of_nonneg temp1] at temp2
      exact le_of_lt temp2

@[simp]
lemma zero_nonneg : IsNonneg 0 := by
  simp [IsNonneg]

@[simp]
lemma one_nonneg : IsNonneg 1 := by
  simp [IsNonneg]

lemma isNonneg_quotient ⦃x x' : MyPrereal⦄ (h : x ≈ x') (hx : IsNonneg x) : IsNonneg x' := by
  simp only [IsNonneg] at hx
  simp only [IsNonneg]
  rcases hx with hx1 | hx2
  ·
    left
    exact isPos_quotient h hx1
  ·
    right
    exact R_trans (R_symm h) hx2


lemma eq_zero_of_isNonneg_of_isNonneg_neg {x : MyPrereal} (h : IsNonneg x) (h' : IsNonneg (-x)) :
    x ≈ 0 := by
  simp only [IsNonneg] at h h'
  rcases h with h1 | h2
  ·
    rcases h' with h1' | h2'
    ·
      apply pos_of_isPos at h1
      apply pos_of_isPos at h1'
      rcases h1 with ⟨N, hN⟩
      rcases h1' with ⟨N', hN'⟩
      have temp := hN (max N N') (le_max_left N N')
      have temp' := hN' (max N N') (le_max_right N N')
      simp at temp'
      linarith
    ·
      simp at h2'
      simp
      exact h2'
  ·
    exact h2

lemma isNonneg_neg_of_not_isNonneg {x : MyPrereal} : ¬ IsNonneg x → IsNonneg (-x) := by
  intro h
  simp only [IsNonneg, not_or] at h
  rcases h with ⟨ha, hb⟩
  simp [IsPos] at ha
  apply pos_of_not_equiv_zero at hb
  have temp : ∃ N, ∀ n, N ≤ n → 0 ≤ -(x n) := by
    rcases hb with ⟨δ, hδ, N, hN⟩
    have h' := x.2
    simp [IsCauchy] at h'
    rcases h' (δ/2) (by linarith) with ⟨N', hN'⟩
    use max N N'
    intro n hn
    have c1 := hN n (le_trans (le_max_left N N') hn)
    simp [abs] at c1
    rcases c1 with hx | hy
    ·
      rcases ha (δ/2) (by linarith) (max N N') with ⟨K, hk, c2⟩
      have c3 := hN' n K (le_trans (le_max_right N N') hn) (le_trans (le_max_right N N') hk)
      simp [abs] at c3
      rcases c3 with ⟨h1, h2⟩
      have final := add_lt_add_left c2 (δ/2)
      have final' := le_of_lt (lt_of_le_of_lt h1 final)
      simp at final'
      have final'' := lt_of_lt_of_le hx final'
      linarith
    ·
      exact le_of_lt (lt_trans hδ hy)
  rcases temp with ⟨N, hN⟩
  exact IsNonneg_of_nonneg N hN



end MyPrereal

namespace MyReal

def IsNonneg : MyReal →  Prop := Quotient.lift (MyPrereal.IsNonneg) <| fun _ _ h ↦
  propext ⟨fun hx ↦ isNonneg_quotient h hx, fun hy ↦ isNonneg_quotient (symm h) hy⟩

lemma isNonneg_def {x : MyPrereal} : IsNonneg ⟦x⟧ ↔ x.IsNonneg := by
  rfl

@[simp]
lemma zero_nonneg : IsNonneg 0 := by
  simp [zero_def, isNonneg_def]

lemma eq_zero_of_isNonneg_of_isNonneg_neg {x : MyReal} : IsNonneg x → IsNonneg (-x) →
    x = 0 := by
  refine Quot.induction_on x ?_
  rintro x'
  simp
  simp only [isNonneg_def, neg_def, zero_def]
  intro ha hb
  have temp := MyPrereal.eq_zero_of_isNonneg_of_isNonneg_neg ha hb
  simp
  simp at temp
  exact temp

lemma IsNonneg.add {x y : MyReal} : IsNonneg x → IsNonneg y → IsNonneg (x + y) := by
  refine Quot.induction_on₂ x y ?_
  rintro x' y'
  simp
  simp only [isNonneg_def, add_def, MyPrereal.IsNonneg]
  intro hx hy
  rcases hx with hx1 | hx2
  ·
    rcases hy with hy1 | hy2
    ·
      left
      exact IsPos.add hx1 hy1
    ·
      left
      have temp : x' + y' ≈ x' + 0 := MyPrereal.add_quotient (R_refl x') hy2
      have temp' : x' + 0 ≈ x' := by
        simp
        intro δ hδ
        use 0
        intro n hn
        exact le_of_lt hδ
      have temp'' := R_symm (R_trans temp temp')
      exact isPos_quotient temp'' hx1
  ·
    rcases hy with hy1 | hy2
    ·
      left
      have temp : x' + y' ≈ 0 + y' := MyPrereal.add_quotient hx2 (R_refl y')
      have temp' : 0 + y' ≈ y' := by
        simp
        intro δ hδ
        use 0
        intro n hn
        exact le_of_lt hδ
      have temp'' := R_symm (R_trans temp temp')
      exact isPos_quotient temp'' hy1
    ·
      right
      have temp := MyPrereal.add_quotient hx2 hy2
      simp
      simp at temp
      exact temp


lemma IsNonneg.mul {x y : MyReal} : IsNonneg x → IsNonneg y → IsNonneg (x * y) := by
  refine Quot.induction_on₂ x y ?_
  rintro x' y'
  simp
  simp only [isNonneg_def, mul_def, MyPrereal.IsNonneg]
  intro hx hy
  rcases hx with hx1 | hx2
  ·
    rcases hy with hy1 | hy2
    ·
      left
      exact IsPos.mul hx1 hy1
    ·
      right
      have temp : x' * y' ≈ x' * 0 := MyPrereal.mul_quotient (R_refl x') hy2
      have temp' : x' * 0 ≈ 0 := by
        simp
        intro δ hδ
        use 0
        intro n hn
        exact le_of_lt hδ
      exact R_trans temp temp'
  ·
    right
    have temp : x' * y' ≈ 0 * y' := MyPrereal.mul_quotient hx2 (R_refl y')
    have temp' : 0 * y' ≈ 0 := by
      simp
      intro δ hδ
      use 0
      intro n hn
      exact le_of_lt hδ
    exact R_trans temp temp'




def le (x y : MyReal) : Prop := IsNonneg (y - x)

instance : LE MyReal where
  le := le

lemma le_def (x y : MyReal) : x ≤ y ↔ IsNonneg (y - x) := by
  rfl

lemma zero_le_iff_isNonneg (x : MyReal) : 0 ≤ x ↔ IsNonneg x := by
  nth_rw 2 [←sub_zero x]
  rfl

lemma zero_le_one : (0 : MyReal) ≤ 1 := by
  simp [le_def, one_def, isNonneg_def]

lemma le_refl (x : MyReal) : x ≤ x := by
  simp [le_def]

lemma le_trans (x y z : MyReal) (h1 : x ≤ y) (h2 : y ≤ z) : x ≤ z := by
  simp [le_def] at h1 h2
  simp [le_def]
  let temp := IsNonneg.add h1 h2
  simp at temp
  exact temp

lemma le_antisymm (x y : MyReal) (hxy : x ≤ y) (hyx : y ≤ x) : x = y := by
  simp [le_def] at hxy hyx
  have temp : x - y = -(y - x) := by ring
  rw [temp] at hyx
  let final := eq_zero_of_isNonneg_of_isNonneg_neg hxy hyx
  rw [←zero_add x, final.symm]
  ring

instance : PartialOrder MyReal where
  le := (. ≤ .)
  le_refl := le_refl
  le_trans := le_trans
  le_antisymm := le_antisymm

instance : ZeroLEOneClass MyReal := ⟨zero_le_one⟩

lemma pos_def {x : MyPrereal} : IsPos x ↔ 0 < (⟦x⟧ : MyReal) := by
  constructor
  ·
    intro h
    simp only [lt_iff_le_and_ne, le_def, sub_zero, isNonneg_def]
    simp only [MyPrereal.IsNonneg]
    constructor
    ·
      left
      exact h
    ·
      apply not_equiv_zero_of_isPos at h
      simp at h
      simp [zero_def]
      exact h
  ·
    intro h
    simp only [lt_iff_le_and_ne, le_def, sub_zero, isNonneg_def] at h
    simp only [MyPrereal.IsNonneg] at h
    rcases h with ⟨h1, h2⟩
    rcases h1 with hx | hy
    ·
      exact hx
    ·
      simp only [zero_def] at h2
      exfalso
      apply h2
      simp at hy
      simp
      exact hy

lemma pos_def' {x y : MyPrereal} : IsPos (y - x) ↔ (⟦x⟧ : MyReal) < ⟦y⟧ := by
  simp only [lt_iff_le_and_ne, le_def, sub_def, isNonneg_def, MyPrereal.IsNonneg]
  constructor
  ·
    intro h
    constructor
    ·
      left
      exact h
    ·
      apply not_equiv_zero_of_isPos' at h
      by_contra c
      rw [←sub_def, c] at h
      simp at h
  ·
    intro h
    rcases h with ⟨h1, h2⟩
    rcases h1 with hx | hy
    ·
      exact hx
    ·
      exfalso
      apply h2.symm
      simp at hy
      simp
      exact hy


lemma add_le_add_left (x y : MyReal) (h : x ≤ y) (t : MyReal) : t + x ≤ t + y := by
  simp [le_def] at h
  simp [le_def]
  exact h

lemma mul_nonneg (x y : MyReal) (hx : 0 ≤ x) (hy : 0 ≤ y) : 0 ≤ x * y := by
  simp [le_def] at hx hy
  simp [le_def]
  exact IsNonneg.mul hx hy

instance : IsOrderedAddMonoid MyReal where
  add_le_add_left := add_le_add_left

instance : IsOrderedRing MyReal :=
  IsOrderedRing.of_mul_nonneg mul_nonneg

lemma k_le_iff (x y : MyRat) : k x ≤ k y ↔ x ≤ y := by
  constructor
  ·
    intro h
    simp [le_def, ←k_sub, k, sub_def, IsNonneg] at h
    simp [MyPrereal.IsNonneg, MyPrereal.IsPos] at h
    rcases h with h1 | h2
    ·
      rcases h1 with ⟨δ, hδ, N, hN⟩
      rcases hN N (by linarith) with h1'
      have temp := le_of_lt (lt_of_lt_of_le hδ h1')
      linarith
    ·
      by_cases c : x = y
      ·
        linarith
      ·
        have c' : x ≠ y := c
        rw [←sub_ne_zero, ←abs_ne_zero, abs_sub_comm] at c'
        have temp : 0 < |y - x| := lt_of_le_of_ne (abs_nonneg (y - x)) c'.symm
        rcases h2 (|y - x| / 2) (by linarith) with ⟨N, hN⟩
        rcases hN N (by linarith) with final
        linarith
  ·
    intro h
    simp [le_def, ←k_sub, k, sub_def, IsNonneg]
    simp [MyPrereal.IsNonneg, MyPrereal.IsPos]
    by_cases c : x < y
    ·
      left
      rw [←sub_zero y, lt_sub_comm] at c
      use (y - x)
      constructor
      ·
        exact c
      ·
        use 0
        intro n hn
        linarith
    ·
      simp at c
      have temp : x = y := by linarith
      right
      intro ε hε
      use 0
      intro n hn
      rw [temp]
      simp
      exact le_of_lt hε

lemma k_lt_iff (x y : MyRat) : k x < k y ↔ x < y := by
  simp [lt_iff_le_and_ne, k_le_iff, k_injective.ne_iff]

lemma le_total (x y : MyReal) : x ≤ y ∨ y ≤ x := by
  simp [le_def]
  have temp : x - y = -(y - x) := by ring
  rw [temp]
  refine Quot.induction_on₂ x y ?_
  rintro x' y'
  simp [sub_def, isNonneg_def, neg_def]
  by_cases h : (y' - x').IsNonneg
  ·
    left
    exact h
  ·
    apply isNonneg_neg_of_not_isNonneg at h
    right
    exact h

noncomputable instance linearOrder : LinearOrder MyReal where
  le_total := le_total
  toDecidableLE := Classical.decRel _

lemma mul_pos (a b : MyReal) (ha : 0 < a) (hb : 0 < b) : 0 < a * b := by
  rw [lt_iff_le_and_ne] at ha hb
  rw [lt_iff_le_and_ne]
  constructor
  ·
    exact mul_nonneg a b ha.left hb.left
  ·
    apply Ne.symm
    by_contra h
    rw [mul_eq_zero] at h
    tauto


noncomputable instance : IsStrictOrderedRing MyReal :=
  IsStrictOrderedRing.of_mul_pos mul_pos

lemma myRat_dense_rat' (x : MyReal) {ε : MyRat} (hε : 0 < ε) : ∃ r, |x - k r| < k ε := by
  refine Quot.induction_on x ?_
  intro ⟨f, hf⟩
  simp [k]
  obtain ⟨N, hN⟩ := hf (ε/2) (by linarith)
  use f N
  simp [abs]
  constructor
  ·
    rw [sub_def, ←pos_def', IsPos]
    simp
    use (ε / 2)
    constructor
    ·
      linarith
    ·
      use N
      intro n hn
      have temp := hN n N hn (by linarith)
      simp [abs] at temp
      linarith
  ·
    rw [sub_def, ←pos_def', IsPos]
    simp
    use (ε / 2)
    constructor
    ·
      linarith
    ·
      use N
      intro n hn
      have temp := hN n N hn (by linarith)
      simp [abs] at temp
      linarith

lemma myRat_dense_of_pos {x : MyReal} : 0 < x → ∃ r, 0 < r ∧ k r < x := by
  refine Quot.induction_on x ?_
  intro ⟨f, hf⟩
  simp [k, ←pos_def']
  intro hx
  simp [←pos_def, IsPos] at hx
  simp [IsPos]
  rcases hx with ⟨δ, hδ, N, hN⟩
  use (δ / 2)
  constructor
  ·
    linarith
  ·
    use (δ / 2)
    constructor
    ·
      linarith
    ·
      use N
      intro n hn
      have temp := hN n hn
      linarith

lemma myRat_dense_rat (x : MyReal) {ε : MyReal} (hε : 0 < ε) : ∃ r, |x - k r| < ε := by
  apply myRat_dense_of_pos at hε
  rcases hε with ⟨a, ha, h1⟩
  apply (myRat_dense_rat' x) at ha
  rcases ha with ⟨r, hr⟩
  use r
  exact lt_trans hr h1

abbrev TendsTo (f : ℕ → MyReal) (x : MyReal) : Prop :=
  ∀ ε, 0 < ε → ∃ N, ∀ n, N ≤ n → |f n - x| ≤ ε

lemma tendsTo_of_myRat_tendsTo {f : ℕ → MyReal} {x : MyReal}
    (h : ∀ (ε : MyRat), 0 < ε → ∃ N, ∀ n, N ≤ n → |f n - x| ≤ k ε) : TendsTo f x := by
  simp [TendsTo]
  intro ε hε
  apply myRat_dense_of_pos at hε
  rcases hε with ⟨ε', hε', h'⟩
  rcases h ε' hε' with ⟨N, hN⟩
  use N
  intro n hn
  exact le_of_lt (lt_of_le_of_lt (hN n hn) h')

abbrev IsConvergent (f : ℕ → MyReal) : Prop :=
  ∃ x, TendsTo f x

abbrev IsCauchy (f : ℕ → MyReal) : Prop :=
  ∀ ε, 0 < ε → ∃ N, ∀ p q, N ≤ p → N ≤ q → |f p - f q| ≤ ε

lemma tendsTo_myRat (x : MyPrereal) : TendsTo (fun n ↦ k (x n)) ⟦x⟧ := by
  intro ε hε
  obtain ⟨δ, hδ, hδ_lt⟩ := myRat_dense_of_pos hε
  have δ_pos : (0 : MyRat) < δ := hδ
  obtain ⟨N, hN⟩ := x.property δ δ_pos
  use N
  intro n hn
  simp
  have h1 : k (x n) - ⟦x⟧ ≤ k δ := by
    rw [le_def]
    apply MyPrereal.IsNonneg_of_nonneg N (fun m hm => ?_)
    have h := hN n m hn hm
    rw [abs_le] at h
    simp
    linarith!
  have h2 : -k δ ≤ k (x n) - ⟦x⟧ := by
    rw [le_def]
    apply MyPrereal.IsNonneg_of_nonneg N (fun m hm => ?_)
    have h := hN n m hn hm
    rw [abs_le] at h
    simp
    linarith!
  rw [abs_le]
  have hδ_lt' : -ε < -k δ := by linarith
  exact ⟨le_of_lt (lt_of_lt_of_le hδ_lt' h2), le_of_lt (lt_of_le_of_lt h1 hδ_lt)⟩

section completeness

lemma ex_approx_punctual (x : MyReal) (n : ℕ) :
    ∃ (r : MyRat), |x - k r| < k ((MyRat.i (n + 1))⁻¹) := by
  have temp : 0 < n + 1 := by linarith
  rw [←MyRat.i_lt_iff, MyRat.i_zero, ←inv_pos] at temp
  apply (myRat_dense_rat' x) at temp
  exact temp

lemma ex_approx (f : ℕ → MyReal) :
    ∃ (g : ℕ → MyRat), ∀ n, |f n - k (g n)| < k ((MyRat.i (n+1))⁻¹) := by
  let g(f : ℕ → MyReal) : ℕ → MyRat := λ n => Classical.choose (ex_approx_punctual (f n) n)
  use g f
  intro n
  exact Classical.choose_spec (ex_approx_punctual (f n) n)

noncomputable def approx (f : ℕ → MyReal) : ℕ → MyRat := (ex_approx f).choose

lemma approx_spec (f : ℕ → MyReal) : ∀ n, |f n - k ((approx f) n)| < k ((MyRat.i (n+1))⁻¹) :=
  (ex_approx f).choose_spec

lemma archimedean (x : MyReal) : ∃ (n : ℕ), x ≤ k (MyRat.i (n + 1)) := by
  have temp : (0 : MyRat) < 1 := by linarith
  apply (myRat_dense_rat' x) at temp
  rcases temp with ⟨r, hr⟩
  simp [abs] at hr
  rcases hr with ⟨h1, h2⟩
  rw [←k_one] at h1
  have temp' : x < k r + k 1 := by linarith
  rw [←k_add] at temp'
  have h := MyRat.archimedean r
  rcases h with ⟨n, hn⟩
  use n
  have h' : r + 1 ≤ MyRat.i n + 1 := by linarith
  rw [←MyRat.i_one, ←MyRat.i_add, MyRat.i_one, ←k_le_iff] at h'
  exact le_of_lt (lt_of_lt_of_le temp' h')

lemma archimedean₀ {x : MyReal} (hx : 0 < x) : ∃ (n : ℕ), k (MyRat.i (n + 1))⁻¹ ≤ x := by
  have h := archimedean x⁻¹
  rcases h with ⟨n, hn⟩
  use n
  rw [k_inv]
  have temp : 0 < n + 1 := by linarith
  rw [←MyRat.i_lt_iff] at temp
  simp [MyRat.i_zero] at temp
  rw [←k_lt_iff] at temp
  simp [k_zero] at temp
  rw [inv_le_comm₀ hx temp] at hn
  exact hn

lemma approx_cauchy {f : ℕ → MyReal} (hf : IsCauchy f) : _root_.IsCauchy (approx f) := by
  simp [_root_.IsCauchy]
  intro ε hε
  have hε' : 0 < ε / 3 := by linarith
  obtain ⟨N1, hN1⟩ := hf (k (ε / 3)) (by rwa [←k_lt_iff] at hε')
  obtain ⟨N2, hN2⟩ := archimedean₀ (by rwa [←k_lt_iff] at hε')
  use max N1 N2
  intro p q hp hq
  have hp1 : N1 ≤ p := le_of_max_le_left hp
  have hq1 : N1 ≤ q := le_of_max_le_left hq
  have hp2 : N2 ≤ p := le_of_max_le_right hp
  have hq2 : N2 ≤ q := le_of_max_le_right hq
  have h1 := approx_spec f p
  have h2 := approx_spec f q
  have h3 := hN1 p q hp1 hq1
  have h4 : k (MyRat.i (p + 1))⁻¹ ≤ k (ε / 3) := by
    simp [k_le_iff] at hN2
    simp [k_le_iff]
    have temp : MyRat.i (N2 + 1) ≤ MyRat.i (p + 1) := by
      simp [MyRat.i_le_iff]
      linarith
    have temp' : (MyRat.i (p + 1))⁻¹ ≤ (MyRat.i (N2 + 1))⁻¹ := by
      rw [inv_le_inv₀]
      exact temp
      ·
        rw [←MyRat.i_zero]
        simp [MyRat.i_lt_iff]
      ·
        rw [←MyRat.i_zero]
        simp [MyRat.i_lt_iff]
    exact MyRat.le_trans (MyRat.i (p + 1))⁻¹ (MyRat.i (N2 + 1))⁻¹ (ε / 3) temp' hN2
  have h5 : k (MyRat.i (q + 1))⁻¹ ≤ k (ε / 3) := by
    simp [k_le_iff] at hN2
    simp [k_le_iff]
    have temp : MyRat.i (N2 + 1) ≤ MyRat.i (q + 1) := by
      simp [MyRat.i_le_iff]
      linarith
    have temp' : (MyRat.i (q + 1))⁻¹ ≤ (MyRat.i (N2 + 1))⁻¹ := by
      rw [inv_le_inv₀]
      exact temp
      ·
        rw [←MyRat.i_zero]
        simp [MyRat.i_lt_iff]
      ·
        rw [←MyRat.i_zero]
        simp [MyRat.i_lt_iff]
    exact MyRat.le_trans (MyRat.i (q + 1))⁻¹ (MyRat.i (N2 + 1))⁻¹ (ε / 3) temp' hN2
  rw [abs_sub_comm] at h1
  apply lt_of_lt_of_le h1 at h4
  apply lt_of_lt_of_le h2 at h5
  apply le_of_lt at h4
  apply le_of_lt at h5
  have temp : |k (approx f p) - f p + (f p - f q) + (f q - k (approx f q))| ≤ |k (approx f p) - f p| + |f p - f q| + |f q - k (approx f q)| := by
    calc
        |(k (approx f p) - f p) + (f p - f q) + (f q - k (approx f q))| ≤
            |(k (approx f p) - f p) + (f p - f q)| + |f q - k (approx f q)| := abs_add _ _
        _ ≤ (|k (approx f p) - f p| + |f p - f q|) + |f q - k (approx f q)| := by
            apply add_le_add_right
            exact abs_add (k (approx f p) - f p) (f p - f q)
        _ = |k (approx f p) - f p| + |f p - f q| + |f q - k (approx f q)| := by simp [add_assoc]
  simp [←k_sub] at temp
  have temp' : k (ε / 3) + k (ε / 3) + k (ε / 3) = k ε := by
    repeat rw [←k_add]
    simp
    linarith
  have final : |k (approx f p - approx f q)| ≤ k ε := by linarith
  rw [abs_le, ←k_neg, k_le_iff, k_le_iff] at final
  rw [abs_le]
  exact final

noncomputable
def IsCauchy.approx {f : ℕ → MyReal} (hf : IsCauchy f) : MyPrereal := ⟨_, approx_cauchy hf⟩

nonrec lemma IsCauchy.approx_spec {f : ℕ → MyReal} (hf : IsCauchy f) :
    ∀ n, |f n - k (hf.approx n)| < k ((MyRat.i (n+1))⁻¹) :=
  approx_spec f

theorem complete {f : ℕ → MyReal} (hf : IsCauchy f) : IsConvergent f := by
  have hg := approx_cauchy hf
  let x : MyReal := ⟦{ val := approx f, property := hg }⟧
  use x
  intro ε hε
  have hε3 : 0 < ε / 2 := by linarith
  obtain ⟨N3, hN3⟩ := archimedean₀ hε3
  have hN3' : ∀ n ≥ N3, k ((MyRat.i (n + 1))⁻¹) ≤ ε / 2 := by
    intro n hn
    have : N3 + 1 ≤ n + 1 := by linarith
    have i_le : MyRat.i (N3 + 1) ≤ MyRat.i (n + 1) := by
      rw [MyRat.i_le_iff]
      exact this
    have pos1 : 0 < MyRat.i (N3 + 1) := by
      rw [←MyRat.i_zero, MyRat.i_lt_iff]
      linarith
    have pos2 : 0 < MyRat.i (n + 1) := by
      rw [←MyRat.i_zero, MyRat.i_lt_iff]
      linarith
    have temp : (MyRat.i (n + 1))⁻¹ ≤ (MyRat.i (N3 + 1))⁻¹ := by
      rw [inv_le_inv₀]
      exact i_le
      ·
        exact pos2
      ·
        exact pos1
    rw [←k_le_iff] at temp
    exact le_trans (k (MyRat.i (n + 1))⁻¹) (k (MyRat.i (N3 + 1))⁻¹) (ε / 2) temp hN3
  have ht := tendsTo_myRat { val := approx f, property := hg } (ε / 2) hε3
  rcases ht with ⟨N4, hN4⟩
  let N := max N3 N4
  use N
  intro n hn
  have hn3 : N3 ≤ n := le_of_max_le_left hn
  have hn4 : N4 ≤ n := le_of_max_le_right hn
  have A : |f n - k ((approx f) n)| < ε / 2 := by
    have := approx_spec f n
    have := hN3' n hn3
    linarith
  have B : |k ((approx f) n) - x| ≤ ε / 2 := hN4 n hn4
  calc
    |f n - x| = |(f n - k ((approx f) n)) + (k ((approx f) n) - x)| := by ring_nf
    _ ≤ |f n - k ((approx f) n)| + |k ((approx f) n) - x| := abs_add (f n - k ((approx f) n)) (k ((approx f) n) - x)
    _ ≤ ε / 2 + ε / 2 := by linarith
    _ = ε := by ring

end completeness

end MyReal

end reals


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
