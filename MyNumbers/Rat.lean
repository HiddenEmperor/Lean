import MyNumbers.Int

/-!
# From-scratch rationals

ℚ built as the field of fractions of `MyInt`, i.e. a quotient
of `MyInt × {x // x ≠ 0}`, with its `Field` and `LinearOrder` structure.
-/


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
