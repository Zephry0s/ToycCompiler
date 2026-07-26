# ToyC 编译器

ToyC 语言的完整编译器，使用 OCaml 实现，将 ToyC 源文件编译为 RISC-V32 汇编代码。

## 项目结构

```
.
├── Makefile              # 构建系统
├── dune-project          # Dune 项目配置
├── src/
│   ├── token.ml          # Token 类型定义
│   ├── lexer.mll         # 词法分析器（ocamllex）
│   ├── ast.ml            # AST 节点类型定义
│   ├── parser.ml         # 语法分析器（递归下降）
│   ├── print_ast.ml      # AST 树形打印（调试用）
│   ├── semant.ml         # 语义分析、符号表构建
│   ├── ir.ml             # 中间表示（IR）类型定义
│   ├── irgen.ml          # AST → IR 生成
│   ├── reg_alloc.ml      # 寄存器分配（干涉图着色）
│   ├── opt.ml            # IR 优化（DCE、CSE）
│   ├── codegen.ml        # IR → RISC-V32 汇编生成
│   └── main.ml           # 编译器入口
├── test/                 # 测试用例（.tc 源文件）
├── result/               # 汇编输出样例
├── Toyc.md               # ToyC 语言定义
└── 编译系统实践.pdf        # 实验任务要求
```

## 构建

需要 OCaml 4.x / 5.x 及 ocamllex：

```bash
make
```

如需重新构建：

```bash
make clean && make
```

## 使用

从标准输入（或文件）读取 ToyC 源码，向标准输出输出 RISC-V32 汇编：

```bash
# 从文件读取
./toyc test/02_add.tc > result/output.s

# 从 stdin 读取
./toyc < test/02_add.tc > result/output.s

# 开启优化
./toyc -opt test/38_prime.tc > result/output.s
```

## 编译流水线

```
源码
 └─ Lexer (lexer.mll)        词法分析
 └─ Parser (parser.ml)       语法分析 → AST
 └─ Semant (semant.ml)       语义分析、符号表
 └─ Irgen (irgen.ml)         IR 生成（虚拟寄存器 IR）
 └─ Opt (opt.ml)             IR 优化（仅 -opt 模式）
 └─ Reg_alloc (reg_alloc.ml) 寄存器分配
 └─ Codegen (codegen.ml)     RISC-V32 汇编生成
```

## 已实现的功能

### 语言特性

- **词法**：关键字、标识符、十进制整数、算术/逻辑/关系运算符、分隔符、单行与多行注释
- **语法**：完整 ToyC 文法，包括全局/局部常量变量声明、函数定义、`if/else`、`while`、`break`、`continue`、`return`
- **语义**：类型检查、作用域与遮蔽、常量约束、`const` 初始化表达式编译期求值、所有路径必须有返回值检查

### 后端优化

| 优化 | 实现位置 | 说明 |
|------|----------|------|
| 常量折叠 | `semant.ml` / `irgen.ml` | 编译期求值 `const` 表达式，不产生运行时指令 |
| 短路求值 | `irgen.ml` | `&&` / `\|\|` 使用跳转指令实现 lazy 求值 |
| 干涉图着色寄存器分配 | `reg_alloc.ml` | CFG 活跃分析 + 循环深度加权 spill；调用感知着色并按需保存 `s0`–`s11` |
| 死代码删除（DCE） | `opt.ml` | 删除定义了从未被使用的虚拟寄存器的纯计算指令，迭代至不动点 |
| CFG 死存储删除（DSE） | `opt.ml` | 通过局部槽内存活跃分析删除跨基本块也不可观察的栈写入 |
| CFG 全局值传播 | `opt.ml` | 跨基本块传播常量与复写，并删除不可达块 |
| 全局公共子表达式消除（CSE） | `opt.ml` | 可用表达式数据流分析、交换律规范化和局部栈槽转发 |
| 模块级全局量优化 | `opt.ml` | 只读全局常量化；无调用函数中的热点可变全局寄存器化 |
| 自底向上叶函数内联 | `opt.ml` | 六轮内联，支持局部变量、全局副作用、分支、循环、多返回点和 `void` helper |
| 直接尾递归消除 | `opt.ml` | 参数槽更新后跳回函数体入口，复用当前栈帧 |
| 循环优化 | `opt.ml` | 不变量外提、仿射闭式归约、归纳变量强度削弱、预算式展开和安全旋转 |
| 函数级局部槽提升 | `opt.ml` | 将所有不逃逸局部槽提升为虚拟寄存器，由图着色决定实际 spill |
| 调用开销优化 | `reg_alloc.ml` / `codegen.ml` | 跨调用值使用 `s` 寄存器或 spill，取消固定保存全部 `t` 寄存器 |
| RISC-V 指令选择 | `codegen.ml` | 立即数、移位加减、magic 常量除模、商余复用、比较—分支融合及栈帧收缩 |

完整的优化流程、正确性条件和回归测试见 [OPTIMIZATIONS.md](OPTIMIZATIONS.md)。

## 测试

```bash
# 运行单个测试
./toyc test/22_recursion.tc

# 运行示例
./toyc < test/02_add.tc > result/output.s
./toyc -opt < test/02_add.tc > result/output.s

# 批量测试（无优化）
for f in test/*.tc; do ./toyc "$f" > /dev/null && echo "OK: $f" || echo "FAIL: $f"; done

# 批量测试（开优化）
for f in test/*.tc; do ./toyc -opt "$f" > /dev/null && echo "OK: $f" || echo "FAIL: $f"; done
```
