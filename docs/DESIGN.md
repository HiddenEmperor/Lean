# 设计说明

这份文档解释「为什么这样写」，以及每一层里最容易卡住的地方。代码本身在
`MyNumbers/` 目录，`MyNumbers/Overview.lean` 是它的可编译目录。

---

## 0. 总原则：商构造的三件套

每一步都是同一个套路，`Int.lean` / `Rat.lean` / `Real.lean` 完全同构：

1. **前结构（pre-structure）**：比如 `MyPreint := ℕ × ℕ`、`MyPrerat := MyInt × {x // x ≠ 0}`、
   `MyPrereal := {x // IsCauchy x}`。这里还是「能抄就能算」的裸数据。
2. **等价关系**：在自己的 `namespace` 里定义 `def R`，然后证 `R_refl` / `R_symm` /
   `R_trans`，打包成 `instance R_equiv : Setoid _`。
3. **定义真正想要的类型**：`abbrev MyInt := Quotient R_equiv`。

之后每个运算都要付两笔账：

* **运算要能下到商上**：`add_quotient` / `mul_quotient` / `neg_quotient` /
  `inv_quotient` 这类「良定性」引理，形式统一为
  `x ≈ x' → y ≈ y' → f x y ≈ f x' y'`，然后用
  `Quotient.map`（一元）或 `Quotient.map₂`（二元）把它提升成 `MyInt → MyInt → MyInt`。
* **运算定律要在商上证**：用 `Quotient.sound` 回到代表元，再把代表元之间的
  算术交给 `ring` / `linarith`。`Real.lean` 里因为涉及绝对值和 ε，额外用了
  `abs_add` / `abs_sub_comm` / `abs_le` 这些不等式工具。

### `quot_proof` 系列 tactic（`Rat.lean` 的 `tactic_hackery`）

`CommRing` / `Field` 的每个字段形如「∀ x y z, ...」的等式，证明永远是
「`Quot.induction_on₃` → 拆成 `⟨a,b⟩ ⟨c,d⟩ ⟨e,f⟩` → `Quot.sound` → `simp; ring`」。
所以写成了 4 个 macro：

```lean
macro "quot_proof₁" : tactic => ...   -- intro x, induction_on x
macro "quot_proof₂" : tactic => ...   -- intro x y, induction_on₂
macro "quot_proof₃" : tactic => ...   -- intro x y z, induction_on₃
macro "quot_proof"  : tactic => ...   -- 依次 try 上面三个
```

它们只依赖 `Quot` 的结构，跟具体是 ℤ 还是 ℚ 无关，换一层照样能用；
`CommRing MyRat` 里 17 个字段基本就是一行一个 `quot_proof₃`。
（`Int.lean` 里同样的一批 `CommRing` 字段是展开手写的，因为 ℕ 上的加法/乘法
交换律还需要 `omega` / `ring` 级别的具体论证。）

---

## 1. `MyInt`：ℤ 是自然数对的差

`(a, b)` 想表示 `a - b`，于是定义

```lean
def R (x y : MyPreint) : Prop := x.1 + y.2 = x.2 + y.1
@[simp] lemma R_def (a b c d : ℕ) : R (a,b) (c,d) ↔ a + d = b + c := by rfl
```

`R_trans` 是唯一需要点技巧的：把 `a + d = b + c` 和 `c + f = d + e` 相加后
要把中间项消掉。这里靠一串 `rw [add_assoc]` + `add_right_cancel` 完成
（`omega` 也能证，但那会让证明失去教学价值）。

关键后续：

| 目标 | 手段 |
| --- | --- |
| `neg` | `(a, b) ↦ (b, a)`，用 `neg_quotient` 下到商 |
| `add` / `mul` | `Quotient.map₂`，`⋆_quotient` 逐分量算 |
| `CommRing` | `add_assoc` 等 12 条定律各自 `intro` + `rfl`/`simp`/`ring` |
| `zero_ne_one` | `(0,0) ≈ (1,0)` 会推出 `0 = 1`，`omega` 收尾 |
| 无零因子 `mul_ne_zero` | 需要 `aux_mul_lemma : a*d + b*c = a*c + b*d → a = b ∨ c = d` |
| 序 `x ≤ y ↔ ∃ a, y = x + ↑a` | 用 `i : ℕ → MyInt` 嵌入，`le_total` 靠 `i` 上的自然数比较 |
| `IsStrictOrderedRing` | `mul_pos` 由「正 = 差的平方类」推 |

`i_le_iff : i a ≤ i b ↔ a ≤ b` 是把 `ℕ` 上的 `Nat` 排序搬到 `MyInt` 上的桥，
`mul_pos`、`le_total` 都靠它。

---

## 2. `MyRat`：ℚ 是 ℤ 的分数域

```lean
abbrev MyPrerat := MyInt × {x : MyInt // x ≠ 0}
def R (x y : MyPrerat) : Prop := x.1 * y.2 = x.2 * y.1
```

* 分母用 `Subtype` 而不是 `x ≠ 0 → ...`，这样 `MyPrerat` 自身永远合法，
  商的构造不用反复处理「分母可能为零」。
* 需要先给 `{x // x ≠ 0}` 一个 `Mul`（`mul_ne_zero` 在这里第一次派上用场），
  否则 `add` 的分母 `b.2 * d.2` 拼不出来。
* `inv` 是唯一带条件的定义：

  ```lean
  def inv (x : MyPrerat) : MyPrerat :=
    if ha : x.1 ≠ 0 then ⟨x.2, x.1, ha⟩ else ⟨0, 1, by simp⟩
  ```

  商上调用 `inv_quotient` 时要分四种情况（分子是否为零 × 两个代表元），
  本质上是「`x ≈ 0` 与 `x' ≈ 0` 一致」。
* 序没有用 `∃ a, y = x + i a` 那套，而是先定义

  ```lean
  def IsNonneg (x : MyRat) : Prop := ...   -- 代表元的分母可正、分子非负
  def le (x y : MyRat) : Prop := IsNonneg (y - x)
  ```

  好处是 `le_total` 只需要在 `IsNonneg` 上做一次分类讨论
  （`nonneg_neg` / `nonneg_neg_of_not_nonneg` 这一对引理）。
* 阿基米德性：`archimedean : ∀ x, ∃ n, x ≤ i n`，先把 `x` 写成
  `a / b`，再取 `n := a * b`（用 `Nat` 上的整除不等式收尾）。

---

## 3. `MyReal`：ℝ 是有理柯西序列的商

这一层是全部工作量的一半，也最值得看。

### 3.1 为什么 `MyPrereal` 是 `Subtype`

```lean
abbrev IsCauchy (x : ℕ → MyRat) : Prop := ∀ ε, 0 < ε → ∃ N, ∀ p q, N ≤ p → N ≤ q → |x p - x q| ≤ ε
abbrev MyPrereal := {x // IsCauchy x}
```

柯西性是**性质**不是结构，用 `Subtype` 把它钉在数据上，就再也不会出现
「随手拿一条序列去算」的非法对象。为了方便 `x n` 这种写法，配了

```lean
instance funLike : FunLike MyPrereal ℕ MyRat
lemma prop (x : MyPrereal) : ∀ ε, 0 < ε → ∃ N, ...   -- 柯西性直接取用
```

### 3.2 需要先把 ℚ 上的柯西性封闭

`IsCauchy.const / neg / add / mul / inv`：前四个靠 `abs_add`、
`abs_mul` 和「柯西列有界」（`IsCauchy.bounded`）；`inv` 最麻烦，需要

```lean
lemma pos_of_not_equiv_zero {x : MyPrereal} (H : ¬(x ≈ 0)) :
    ∃ δ, 0 < δ ∧ ∃ N, ∀ n, N ≤ n → δ < |x n|
```

即「非零的柯西列，最终会被某个正数 δ 顶住」，然后
`|1/x n - 1/x' n| = |x' n - x n| / (|x n| * |x' n|)` 用 `δ₁ * δ₂` 控制。

`MyPrereal.inv` 用 `if H : ¬(x ≈ 0)` 定义：非零类走倒数序列，零类直接取 `0`。
`inv_quotient` 里那四个 `split_ifs` 分支就是在证「这个 if 和代表元无关」。

### 3.3 完备性：`complete`

```lean
theorem complete {f : ℕ → MyReal} (hf : IsCauchy f) : IsConvergent f
```

思路是教科书的对角线：

1. `ex_approx_punctual`：对每个 `n`，把 `f n` 用一个有理数逼到 `1/(n+1)` 以内
   （用有理数在实数里的稠密性 `myRat_dense_rat'` + 阿基米德性造 `n+1`）。
2. `approx f`：把上面的选择函数用 `Classical.choose` 拼成一条**有理**序列。
3. `approx_cauchy`：`f` 是柯西的 ⟹ `approx f` 是柯西的（三角不等式，拆成
   `|a_p - f p| + |f p - f q| + |f q - a_q| ≤ ε/3 + ε/3 + ε/3`）。
4. `x := ⟦⟨approx f, _⟩⟧`，再用 `tendsTo_myRat`（有理序列收敛到自己所在的类）
   和 `archimedean₀`（`1/(n+1)` 可以任意小）夹出 `|f n - x| ≤ ε`。

`archimedean₀` 和 `complete` 里大量出现的
`k : MyRat → MyReal`（有理常数序列所在的类）是这一层的「类型转换器」，
它的同态性是分开证的：`k_add / k_sub / k_mul / k_inv / k_injective /
k_le_iff / k_lt_iff`。**`k_le_iff` / `k_lt_iff` 尤其重要**：任何
「在 ℝ 里成立、想在 ℚ 里用」的不等式都要先过它。

### 3.4 序与 `IsPos` / `IsNonneg`

先在最底层给 `MyPrereal` 定义 `IsPos`（存在 δ > 0，最终所有项都 > δ），
再证它与 `≈` 相容（`isPos_quotient`），然后 `Quotient.lift` 到 `MyReal` 上；
`IsNonneg` 用「`IsPos` 或 `≈ 0`」定义，`le x y := IsNonneg (y - x)`。

于是 `le_total` 变成一次 `by_cases h : (y' - x').IsNonneg`，
`LinearOrder` 用 `Classical.decRel` 补 `DecidableLE`，
`IsStrictOrderedRing` 由 `mul_pos`（乘积非负 + 非零）得到。

---

## 4. `MyComplex`：还没做完

`MyPrecomplex := MyReal × MyReal`，分量相等作等价关系，
`add` / `mul`（`(a+bi)(c+di) = (ac-bd) + (ad+bc)i`）与
`neg` 的良定性都已经证完，`MyComplex` 上已经有 `Zero` / `One` / `Neg`。

**还差**：把 `add` / `mul` 提升成 `MyComplex` 的实例，然后

```lean
instance : CommRing MyComplex
instance : Field MyComplex   -- 需要 a² + b² ≠ 0，靠 MyReal 的 mul_pos
```

完成之后最漂亮的一步是 `MyComplex ≃+* ℂ`，那是「我真的造出了 ℂ」的最终凭证。

---

## 5. 一些工程上的注意点

* **`autoImplicit`**：这份代码是在 `autoImplicit = true` 下写的（`lakefile.toml`
  里刻意没有关掉它，MIL 官方仓库是关掉的）。想打开严格的
  `autoImplicit = false`，需要给一批引理补全没写的隐式参数。
* **`_root_.IsCauchy`**：`Real.lean` 在根命名空间定义了 `IsCauchy`，
  而 `MyReal` 命名空间中后来又定义了一个（关于实数列的）同名版本，
  所以文件里出现 `_root_.IsCauchy` 的写法——这是有意为之的消歧。
* **`set_option pp.unicode.fun = true`**：只为显示 `fun a ↦ b`，没有语义影响。
* 定理名一律保留 `*_def`（定义展开）、`*_quotient`（良定性）的后缀习惯，
  方便在大文件里搜索。
