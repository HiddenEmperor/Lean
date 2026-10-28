# MyNumbers · 从零构造数系

[![Build](https://github.com/HiddenEmperor/Lean/actions/workflows/build.yml/badge.svg)](https://github.com/HiddenEmperor/Lean/actions/workflows/build.yml)

用 Lean 4 + Mathlib，把中间那层「数」的定义全部自己写一遍：

```
ℕ  ──(差的等价类)──▶  MyInt (ℤ)  ──(分数域)──▶  MyRat (ℚ)
                                                        │
                                                        │(柯西序列 + 商的等价类)
                                                        ▼
                                                     MyReal (ℝ)  ──(有序对)──▶  MyComplex (ℂ, 进行中)
```

不 `import Mathlib.Data.Real.Basic`，`MyInt` / `MyRat` / `MyReal` 是真正的
`Quotient` 构造出来的新类型；Mathlib 在这里只提供「调料」：`Quotient` 的 API、
`Setoid`、`linarith` / `ring` / `simp` 这些 tactic，以及最后用来对照的标准库。

主结果（全部经过 `lake build` 机器检查）：

| 数系 | 定义方式 | 证明的代数结构 | 证明的有序结构 |
| --- | --- | --- | --- |
| `MyInt` | `Quotient (ℕ × ℕ) ~`，`(a,b) ~ (c,d) ↔ a + d = b + c` | `CommRing`，`Nontrivial`，无零因子 `mul_ne_zero` | `IsOrderedAddMonoid`，`IsStrictOrderedRing`，`le_total` |
| `MyRat` | `MyInt × {x // x ≠ 0}` 的商，即分数域 | `Field`，`mul_inv_cancel` | `IsOrderedRing`，`le_total`，阿基米德性 `archimedean` |
| `MyReal` | 有理柯西序列的商 | `Field`，`mul_inv_cancel` | `LinearOrder`，`IsStrictOrderedRing`，`le_total`，阿基米德性，**柯西完备性 `complete`** |
| `MyComplex` | `MyReal × MyReal` 的商 | `Zero` / `One` / `Neg`（进行中） | — |

---

## 目录结构

```
MyNumbers.lean            总入口，import 下面全部模块
MyNumbers/
├── Int.lean              MyPreint / MyInt：ℤ 的构造、CommRing、序
├── Rat.lean              MyPrerat / MyRat：ℚ 的构造、Field、序、阿基米德性
├── Real.lean             IsCauchy / MyPrereal / MyReal：ℝ 的构造、完备性
├── Complex.lean          MyPrecomplex / MyComplex：ℂ 的构造（未完成）
└── Overview.lean         可编译的「目录」：每个 example 都是一条主定理
docs/DESIGN.md             构造思路与关键引理说明
archive/test.lean          最初那份单文件版本（保留作历史存档）
```

`MyNumbers/Overview.lean` 值得先读：它把每一层的 `instance` 和主定理用
`example` / `inferInstance` 复述一遍，既是文档，也是回归测试——任何一层证明
坏掉，它都会跟着编译失败。

## 快速开始

```bash
git clone https://github.com/HiddenEmperor/Lean
cd Lean
lake exe cache get    # 拉 Mathlib 预编译缓存，别自己编译，要一小时
lake build            # 编译 MyNumbers 全部模块
```

想只检查某一层：

```bash
lake env lean MyNumbers/Overview.lean
```

在 VS Code 里打开任意 `.lean` 文件，等 Lean 服务加载完（第一次要几分钟）后，
把光标放到 `Quotient.map₂`、`Quotient.sound` 之类的地方按 `F12` 可以一路看到
Mathlib 里对应实现。

## 规模

| 文件 | 行数 | theorem/lemma | def/abbrev | instance |
| --- | --- | --- | --- | --- |
| `Int.lean` | 521 | 30 | 9 | 12 |
| `Rat.lean` | 891 | 51 | 15 | 15 |
| `Real.lean` | 1570 | 78 | 17 | 21 |
| `Complex.lean` | 119 | 9 | 7 | 4 |
| 合计 | ~3100 | **168** | **48** | **52** |

## 路线图

- [x] ℤ：`CommRing` + `IsStrictOrderedRing`
- [x] ℚ：`Field` + `IsOrderedRing` + 阿基米德性
- [x] ℝ：`Field` + `LinearOrder` + `IsStrictOrderedRing` + 柯西完备性
- [ ] ℂ：补 `Add` / `Mul` / `CommRing` / `Field`，然后证 `MyComplex ≃+* ℂ`
- [ ] 收尾：`MyReal ≃+* ℝ`（需要先证 `MyReal` 的 `abs` / `IsNonneg` 与
      Mathlib 版本相容，或直接走 Cauchy 完备性 + 阿基米德性的唯一性）
- [ ] 给关键引理补 `@[simp]` 与 docstring，方便后来者复用

详见 [`docs/DESIGN.md`](docs/DESIGN.md)。

## 致谢

题目思路来自 [Mathematics in Lean](https://leanprover-community.github.io/mathematics_in_lean/)
与 Mathlib 的 quotient / 分数域文档；代码全部为本仓库自写。

## License

Apache License 2.0，见 [`LICENSE`](LICENSE)。
