# ToyC 编译器前端

ToyC 语言的词法分析和语法分析前端，使用 OCaml 实现。后端（类型检查、IR、代码生成）留给后续设计。

## 项目结构

```
.
├── Makefile          # 构建系统
├── dune-project      # Dune 项目配置
├── src/
│   ├── dune          # Dune 子目录配置
│   ├── token.ml      # Token 类型定义
│   ├── ast.ml        # AST 节点类型定义
│   ├── lexer.mll     # 词法分析器（ocamllex）
│   ├── parser.ml     # 语法分析器（递归下降）
│   ├── print_ast.ml  # AST 树形打印
│   └── main.ml       # 入口：从 stdin 读取源码，输出 AST
├── Toyc.md           # ToyC 语言定义
└── 编译系统实践.pdf    # 实验任务要求
```

## 构建

需要 OCaml 5.x、ocamllex：

```bash
make
```

如需重新构建：

```bash
make clean && make
```

## 使用

从标准输入读取 ToyC 源码，解析后在标准输出打印 AST：

```bash
./toyc < input.tc
```

## 已实现的语言特性

- **词法**：关键字（`const`, `int`, `void`, `if`, `else`, `while`, `break`, `continue`, `return`），标识符，十进制整数，运算符（`+ - * / % ! && || < > <= >= == != =`），分隔符，单行注释（`//`）和多行注释（`/* */`）
- **语法**：完整 ToyC 文法
  - 编译单元：全局常量/变量声明 + 函数定义
  - 语句：块、空语句、表达式语句、赋值、`if`/`if-else`、`while`、`break`、`continue`、`return`、局部声明
  - 表达式：逻辑或/与、关系、加减、乘除模、一元、括号、函数调用、标识符/字面量
- **错误处理**：词法错误和语法错误输出行号列号，非零退出码

## 架构

```
stdin → Lexer (lexer.mll) → token stream
       → Parser (递归下降, parser.ml) → AST (ast.ml)
       → Print (print_ast.ml) → stdout
```

Token 类型定义在 `token.ml`，lexer 和 parser 共享该模块。

### AST 节点

| 类型 | 构造器 | 说明 |
|------|--------|------|
| `comp_unit` | `top list` | 编译单元，顶层声明/函数列表 |
| `top` | `TopDecl` / `TopFunc` | 顶层元素 |
| `func_def` | `{ ret_type; name; params; body }` | 函数定义 |
| `decl` | `ConstDecl` / `VarDecl` | 常量/变量声明（带初始化） |
| `stmt` | `Block / Empty / Expr / Assign / If / While / Break / Continue / Return / Decl` | 语句 |
| `exp` | `Binary / Unary / Id / Num / Call` | 表达式 |

`Binary` 记录具体运算符（`Add, Sub, Mul, Div, Mod, And, Or, Eq, Neq, Lt, Gt, Le, Ge`），`Unary` 记录 `Neg, Pos, Not`。
