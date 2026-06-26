# 迷你表示论与李理论

一套**从零开始、零依赖的 Lean 4 实现**，涵盖大学层次的表示论与李理论。每个模块形式化了核心定义、定理、经典示例与应用——从代数群和特征标表到量子群、顶点代数与 Kac-Moody 代数——构建了一个可验证、可运行的数学知识库。

## 子模块

| 子模块 | 主题 | 核心课程 |
|--------|------|----------|
| [mini-algebraic-groups](mini-algebraic-groups/) | 线性代数群、结构理论（可解/幂零/半单/约化）、根系数据、Dynkin图、Borel-Tits理论、Lie-Kolchin定理 | MIT 18.755, Stanford MATH 210B, 剑桥 Part III 代数几何 |
| [mini-character-theory](mini-character-theory/) | 有限群特征标理论、正交性关系、Frobenius互反律、特征标表、Burnside p^a q^b 定理、Brauer诱导、模特征标 | MIT 18.704/18.715, 哈佛 Math 55/251, 剑桥 Part III 表示论 |
| [mini-kac-moody-algebras](mini-kac-moody-algebras/) | 广义Cartan矩阵、仿射/双曲根系、Weyl群、Verma模、Weyl-Kac特征标公式、分母恒等式、Macdonald恒等式 | MIT 18.785, 伯克利 MATH 274, 牛津 Part C 李代数 |
| [mini-lie-algebras](mini-lie-algebras/) | 李代数、子代数/理想、导出列、下中心列、Killing型、根空间、Cartan子代数、Dynkin图、分类、PBW定理 | MIT 18.755, 哈佛 Math 210B, 剑桥 Part III 李代数 |
| [mini-lie-groups](mini-lie-groups/) | 李群与李代数、光滑流形、指数映射、伴随表示、经典群（GL/SL/O/SO/U/SU/Sp/Spin）、例外群、规范场论 | MIT 18.755, 斯坦福 MATH 210C, 剑桥 Part III 李群 |
| [mini-quantum-groups](mini-quantum-groups/) | Drinfeld-Jimbo量子群、Hopf代数、R-矩阵、Yang-Baxter方程、辫子张量范畴、纽结不变量（Jones多项式）、拓扑量子计算 | 伯克利 MATH 256, 普林斯顿 MAT 560, 剑桥 Part III 量子群 |
| [mini-representation-theory](mini-representation-theory/) | 半单李代数表示论、最高权理论、Weyl特征标/维数公式、BGG范畴O、Verma模、Clebsch-Gordan分解、角动量 | MIT 18.715, 哈佛 Math 251, 斯坦福 MATH 210C |
| [mini-vertex-algebras](mini-vertex-algebras/) | 顶点代数与顶点算子代数（VOA）、Goddard唯一性、Dong引理、Zhu定理、Heisenberg/Virasoro/格/魔群VOA、共形场论 | MIT 18.785, 伯克利 MATH 274, 剑桥 Part III 顶点代数 |

## 设计哲学

- **零外部依赖** — 纯 Lean 4 (v4.7.0+)，代数基础结构全部内部定义，自包含
- **模块独立自洽** — 每个目录包含独立的 `lakefile.lean`、`Main.lean`、模块聚合器、源码树及文档
- **理论到代码的映射** — 每个模块遵循 9 级知识层次（L1 定义 → L9 研究前沿）
- **可计算验证** — 核心定理通过 `#eval` 和 `native_decide` 验证，所有模块零 `sorry`

## 构建

每个模块独立运行。进入模块目录并执行：

```bash
cd mini-algebraic-groups
lake build         # 构建所有内容
lean --run Main.lean  # 运行模块入口点
```

需要 **Lean 4** (v4.7.0+) 通过 [elan](https://github.com/leanprover/elan) 安装。

## 项目结构

```
mini-representation-lie-theory/
├── mini-algebraic-groups/       # 线性代数群、Borel-Tits结构理论、分类
├── mini-character-theory/       # 有限群特征标理论、Frobenius互反律、模特征标
├── mini-kac-moody-algebras/     # 广义Cartan矩阵、Weyl-Kac公式、仿射/双曲类型
├── mini-lie-algebras/           # 李代数、根系、Killing型、Cartan判别、分类
├── mini-lie-groups/             # 李群、指数映射、经典/例外群、规范场论
├── mini-quantum-groups/         # 量子群、R-矩阵、Yang-Baxter、纽结不变量、任意子
├── mini-representation-theory/  # 最高权理论、Weyl公式、BGG范畴O、Verma模
└── mini-vertex-algebras/        # 顶点算子代数、Goddard/Zhu定理、魔群月光
```

## 许可证

MIT
