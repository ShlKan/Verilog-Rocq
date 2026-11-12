# ITree semantics: constructs, in order

The order in which the constructs of `src/Lang/Syntax.v` get an ITree denotation over
the events of `src/Semantics/Core/Events.v`. Each construct is added on its own; anything not
yet done denotes to an error, `throw "not supported: ..."`, never to nothing.

Status: `todo`, `done`, or `reject` (outside the synthesizable subset; denotes to an
error permanently).

## Layout

The semantics lives in `src/Semantics/`, one folder per group of constructs. A file is
created when its construct is written.

| Folder | Contents | Stages |
|---|---|---|
| `Core/` | events, scheduler, value type | 0 |
| `Decl/` | declaration table, ports, parameters | 7 |
| `Expr/` | literals, reads, operators, selects, concatenation, casts | 1, 2, 5, 6 |
| `Stmt/` | assignments, `begin ... end`, `if`, `case`, loops | 1, 3, 5, 8 |
| `Proc/` | `assign`, `always_comb`, edge-triggered `always` | 4 |
| `Func/` | functions, tasks | 9 |
| `Module/` | generate, levels and step, instances | 10 |
| `Test/` | `TestLib.v` (shared setup), `WidthTest.v` (`self_width`), `ValueTest.v` (operators and literal-only expressions on stdpp bit-vectors, against the simulator tables), `TreeTest.v` (statements with variables, event for event) | |

Within `Expr/` and `Stmt/`, each construct's meaning is a definition in its own file
(for example `sem_binop` in `Expr/Ops.v`), and one `Denote.v` per folder holds the
recursive function over the AST that calls them.

## 0. Prerequisites (not constructs)

| # | Piece | What it provides | Status |
|---|---|---|---|
| 0.1 | Events | `sigE`, `stepE`, `chooseE`, `portE` (`Core/Events.v`); errors are the ITree library's `exceptE string`, abbreviated `errE`, raised with its `throw` | done |
| 0.2 | Scheduler | `sched`, `round`, `rounds` (`Core/Sched.v`) | done |
| 0.3 | Value type | `value := { n : N & bv n }`, `mk`, `resize` (`Core/Value.v`) | done |
| 0.4 | Declaration table | `sigs` and `iface` of a module, plus the list of port names | todo |

0.4 is built up with the declaration constructs of stage 7; until then examples supply
a hand-written table.

## 1. First slice: straight-line code

| # | Construct | AST constructor | Denotation | Status |
|---|---|---|---|---|
| 1 | Number literal: `8'hFF`, `4'b1010`, `12` | `VExprPriLiteral` | `sem_literal` (`Expr/Literal.v`): a value, no event | done |
| 1a | Fill literal: `'0`, `'1` | `VPriLiteralUU` | needs the width of the context | todo |
| 2 | Variable read: `x` | `VExprId` | `sem_var` (`Expr/Var.v`): `Get x`, or error if undeclared | done |
| 3 | Blocking assignment: `x = e` | `VStatementItemBlockingAssignNormal` | `sem_assign_b` (`Stmt/Assign.v`): resize, `SetB x v`, or error if undeclared | done |
| 4 | Nonblocking assignment: `x <= e` | `VStatementItemNonblockingAssign` | `sem_assign_nb` (`Stmt/Assign.v`): resize, `SetNB x v`, or error if undeclared | done |
| 5 | Sequential block: `begin ... end` | `VStatementSeqBlock` | `sem_seq` (`Stmt/Block.v`): the statements in order | done |

## 2. Operators

| # | Construct | AST constructor | Denotation | Status |
|---|---|---|---|---|
| 6 | Unary: `+ - ! ~` | `VExprUniOp` | `sem_unop` (`Expr/Ops.v`): pure function of the operand | done |
| 7 | Reduction: `& ~& \| ~\| ^ ~^` | `VExprUniOp` | `sem_unop` (`Expr/Ops.v`): one-bit result | done |
| 8 | Bitwise: `& \| ^ ~^` | `VExprBinOp` | `sem_binop` (`Expr/Ops.v`): operands extended to the wider width | done |
| 9 | Arithmetic: `+ - *` | `VExprBinOp` | `sem_binop` (`Expr/Ops.v`): at the computation width, wrapping | done |
| 9a | Arithmetic: `/ %` | `VExprBinOp` | `sem_binop`, unsigned; a zero divisor is `throw "division by zero"` (`docs/notes-division-by-zero.md`) | done |
| 9b | Power: `**` | `VExprBinOp` | | todo |
| 10 | Comparison: `== != < <= > >=` | `VExprBinOp` | one-bit result | todo |
| 11 | Logical: `&& \|\|` | `VExprBinOp` | one-bit result; right operand is evaluated only if needed | todo |
| 12 | Shift: `<< >> <<< >>>` | `VExprBinOp` | `>>>` needs signedness | todo |
| 13 | Conditional: `c ? a : b` | `VExprCond` | branch on `c`, evaluate one side | todo |
| 14 | Four-state equality: `=== !== ==? !=?` | `VExprBinOp` (`VBinFEq`, `VBinWEq`, ...) | same as `==`/`!=` in a two-state model, or reject; to decide | todo |

## 3. Control flow

| # | Construct | AST constructor | Denotation | Status |
|---|---|---|---|---|
| 15 | `if (c) s else t` | `VStatementCond` | branch on `c` | todo |
| 16 | `case` | `VStatementCase` with `VCaseTypeD` | first matching item, else default | todo |
| 17 | `casez`, `casex` | `VStatementCase` with `VCaseTypeZ`, `VCaseTypeX` | wildcard match on literal items | todo |
| 18 | `e inside { ... }` | `VExprInside` | disjunction of comparisons | todo |

## 4. Blocks: the module's processes

| # | Construct | AST constructor | Denotation | Status |
|---|---|---|---|---|
| 19 | Continuous assignment: `assign x = e` | `VModuleCommonItemContAssign` | an unguarded block | todo |
| 20 | `always_comb`, `always @*` | `VModuleCommonItemAlways` (`VAlwaysComb`; `VAlways` with `VEventControlAny`) | an unguarded block | todo |
| 21 | `always @(posedge clk)`, `always_ff`, `negedge`, `or` lists | `VModuleCommonItemAlways` with `VStatementProcTimingControl`, `VEventExpr` | `Fired` guards around the body | todo |
| 22 | Level-sensitive list: `always @(a or b)` | `VEventExprExpr None` | treat as combinational if the list is complete, else reject; to decide | todo |

**Milestone A:** after 1 to 5, 15, and 19 to 21, the counter example runs end to end
with a hand-written declaration table.

## 5. Selects and structured values

| # | Construct | AST constructor | Denotation | Status |
|---|---|---|---|---|
| 23 | Array element read: `m[i]` | `VExprPriSelect` on an array | evaluate `i`, `Get (m, [i])`; out of range needs a decision | todo |
| 24 | Bit select: `x[i]` | `VExprPriSelect` on a vector | `Get x`, extract one bit | todo |
| 25 | Part select: `x[7:4]` | `VExprPriSelectConstRange` | `Get x`, extract a slice | todo |
| 26 | Indexed part select: `x[i +: W]`, `x[i -: W]` | `VExprPriSelectIdxRangeAdd`, `...Sub` | `Get x`, shift and extract | todo |
| 27 | Concatenation: `{a, b}` | `VExprPriConcat` | append | todo |
| 28 | Replication: `{4{a}}` | `VExprPriMultConcat` | constant count, append | todo |
| 29 | Assignment to an array element: `m[i] = e` | l-value `VExprPriSelect` | `SetB (m, [i]) v` | todo |
| 30 | Assignment to bits or a slice: `x[i] = e`, `x[7:4] = e` | l-value selects | `Get x`, update the slice, `SetB x`; for `<=` the read is of the pending value | todo |
| 31 | Assignment to a concatenation: `{a, b} = e` | l-value `VExprPriConcat` | split `e`, one write per part | todo |

## 6. Types and conversions

| # | Construct | AST constructor | Denotation | Status |
|---|---|---|---|---|
| 32 | Size cast: `W'(e)` | `VExprCast` | resize | todo |
| 33 | `$signed`, `$unsigned` | `VExprSystemTfCall` | changes how the operand is extended and compared | todo |
| 34 | Signedness of declarations | not in the AST (`VDataType` has no `signed` field) | add the field, then sign-extension in resize, `<`, `>>>`, `/`, `%` | todo |
| 35 | Increment, decrement: `i++`, `i--` | `VExprIncOrDec` | `Get`, add, `SetB`; in practice only in `for` steps | todo |
| 36 | Compound assignment: `+=`, `<<=`, ... | `VOpAssign` (only in `VForStep`) | `Get`, operate, `SetB` | todo |

## 7. Declarations

These are handled by the declaration pass (0.4), not by events.

| # | Construct | AST constructor | Effect | Status |
|---|---|---|---|---|
| 37 | Variable: `reg [7:0] x`, `logic x`, `integer i` | `VVarDecl`, `VDataType` | entry in `sigs` | todo |
| 38 | Net: `wire [7:0] w` | `VNetDecl` | entry in `sigs` | todo |
| 39 | Declaration with initialiser: `wire w = e`, `logic x = e` | `ve : option VExpr` | net: a continuous assignment; variable: initial value, to decide | todo |
| 40 | Array dimensions | `VVarDims` | `Array lo hi` per dimension | todo |
| 41 | Ports: `input`, `output` | `VPortDecl`, `VAnsiPortDecl` | entries in `in_sigs`, `out_sigs` | todo |
| 42 | `parameter`, `localparam` | `VParamDecl`, `VLocalParamDecl` | constants, evaluated before any width | todo |

**Milestone B:** after stages 1 to 7, a single module without loops, functions or
instances is denoted entirely from its AST.

## 8. Loops

| # | Construct | AST constructor | Denotation | Status |
|---|---|---|---|---|
| 43 | `for` | `VStatementItemFor` | `iter` | todo |
| 44 | `while`, `do ... while` | `VStatementItemWhile`, `VStatementItemDoWhile` | `iter` | todo |
| 45 | `repeat (n)` | `VStatementItemRepeat` | `iter` with a counter | todo |
| 46 | `forever` | `VStatementItemForever` | never returns within a step | reject |

## 9. Functions and tasks

| # | Construct | AST constructor | Denotation | Status |
|---|---|---|---|---|
| 47 | Function declaration and call | `VFuncDecl`, `VExprTfCall` | body over its own local table, interpreted away at the call | todo |
| 48 | `return e` | `VStatementItemReturn` | early exit from the body | todo |
| 49 | Task declaration and call | `VTaskDecl` | inlined body; the AST has no task-call statement yet | todo |

## 10. Structure above a block

| # | Construct | AST constructor | Denotation | Status |
|---|---|---|---|---|
| 50 | Generate `if`, generate block | `VGenerateModuleItemCond`, `VGenerateModuleItemBlock` | resolved before denotation: constant condition selects the items | todo |
| 51 | Module: its blocks, levels, one step | `VModuleDecl` | levelize, `rounds`, `In` and `Out` around it | todo |
| 52 | Instance: `sub u (.a(x), .b(y))` | `VModuleInst`, `VNamedPortConn` | the child's step with its port events handled by the parent's store | todo |
| 53 | Parameter override on an instance | `VParamValueAssigns` (only `Nil` in the AST) | specialise the child's table | todo |

**Milestone C:** a design with several modules is one tree.

## 11. Rejected

| # | Construct | AST constructor | Reason |
|---|---|---|---|
| 54 | `inout` and `ref` ports | `VPortDirectionInout`, `VPortDirectionRef` | not in the two-state synthesizable model |
| 55 | Hierarchical reference: `u.x` | `VExprHier` | breaks the per-module table |
| 56 | `initial` | `VModuleCommonItemInitial` | not synthesizable in general; initial values, if wanted, come from 39 |
| 57 | `always_latch` | `VAlwaysLatch` | latches; could be supported later as level-sensitive blocks |
| 58 | Concurrent assertions: `assert property`, `assume`, `cover` | `VConcurAssert`, `VPExpr` | specifications, not behaviour; to decide whether to ignore with a warning or reject |

## Open decisions

- Packed multi-dimensional vectors (`logic [31:0][63:0] rf`): one wide vector, or an
  array of separately addressed elements. Proposed: an array.
- Division by zero: decided, an error event (`docs/notes-division-by-zero.md`).
  Out-of-range array index: still open; the same reasoning suggests an error event.
- Four-state operators (14) and level-sensitive lists (22).
- Statement-level interleaving between blocks: `sched` currently runs a chosen block to
  its end.
- A static check that flops do not clock each other in a cycle, which would bound the
  number of rounds in a step.
