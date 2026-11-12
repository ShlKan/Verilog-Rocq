# Notes: the width at which Verilog computes an expression

Why `src/Semantics/Expr/Width.v` is written the way it is, with the sources and the
simulator runs behind it.

## The rule

Verilog decides the width of a computation before computing anything.

1. Every expression has a width of its own, found from the declarations
   (`self_width`). The table is below.
2. For an assignment `x = e`, the computation width is the larger of the width of `x`
   and the width of `e` on its own.
3. Every operator in `e` that takes its width from the context runs at that width: its
   operands are extended to it first, and its result is cut to it.

Consequences:

- Extra bits for a carry or a product appear only when the left-hand side (or another
  operand) is wider. Verilog never adds a bit on its own.
- The cut happens at each operator, not once at the end. A carry lost in `a + b` is not
  available to a `>>` that follows.
- Computing at width `w` with wrap-around is the same as computing the full result and
  keeping the low `w` bits. So `bv_add` and `bv_mul` at the computation width are
  correct; their "overflow" is exactly the cut.

## The table

From the OVI Verilog HDL Language Reference Manual, section 4.4.2, table 4-14, "Bit
lengths resulting from expressions". `L(i)` is the width of `i`.

| Expression | Width | Comment in the manual |
|---|---|---|
| unsized constant | same as integer (usually 32) | |
| sized constant | as given | |
| `i op j`, op one of `+ - * / % & \| ^ ^~` | `max(L(i), L(j))` | |
| `+i`, `-i` | `L(i)` | |
| `~i` | `L(i)` | |
| `i op j`, op one of `=== !== == != && \|\| > >= < <=` | 1 | all operands are self-determined |
| `op i`, op one of `& ~& \| ~\| ^ ~^` | 1 | all operands are self-determined |
| `i >> j`, `i << j` | `L(i)` | `j` is self-determined |
| `i ? j : k` | `max(L(j), L(k))` | `i` is self-determined |
| `{i, .., j}` | `L(i) + .. + L(j)` | all operands are self-determined |
| `{i {j, .., k}}` | `i * (L(j) + .. + L(k))` | all operands are self-determined |

Multiplication is in the `max` row. It is not `L(i) + L(j)`.

"Self-determined" means the operand is sized on its own, ignoring the surrounding
context. For those operands a new computation width is found from the operand itself.

## What the manual says about carries

Section 4.4.1, for 16-bit `a` and `b`:

> During the evaluation of an expression, interim results take the size of the largest
> operand (in the case of an assignment, this also includes the left-hand side).

> If a and b are 16-bit registers, then the result of (a+b) is 16 bits wide—unless the
> result is assigned to a register wider than 16 bits. If answer is a 17-bit register,
> then (answer = a + b) yields a full 17-bit result. But in the expression (a + b >> 1),
> the sum of (a + b) produces an interim result that is only 16 bits wide. Therefore,
> the assignment of (a + b >> 1) to a 16-bit register loses the carry bit before the
> evaluation performs the one-bit right shift.

Its fix is to add the integer zero, `(a + b + 0) >> 1`, which makes the widest operand
32 bits.

## Simulator checks

Verilator 5.028, with 8-bit `a = 200` and `b = 100`.

Multiplication (true product 20000):

| Expression | Result | Reason |
|---|---|---|
| `$bits(a * b)` | 8 | the wider operand, not the sum of the widths |
| `c8 = a * b` | 32 | computed at 8 bits; 20000 mod 256 |
| `c16 = a * b` | 20000 | the 16-bit left-hand side widens the operands first |
| `c16 = {a * b}` | 32 | inside `{}` the product is sized on its own |
| `(a * b) > 8'd100` | 0 | compared at 8 bits: 32 > 100 is false |

Addition then shift (true sum 300):

| Statement | Result | Reason |
|---|---|---|
| `c8 = (a + b) >> 1` | 22 | sum at 8 bits is 44, carry lost, then shifted |
| `c9 = (a + b) >> 1` | 150 | the 9-bit left-hand side keeps the carry |
| `c8 = (a + b + 0) >> 1` | 150 | the literal `0` is 32 bits |

The left-hand side reaches through a shift. Verilator 5.028 and Icarus Verilog 13.0
agree on every line, with 16-bit `a = 40000` and `b = 30000` (true sum 70000):

| Statement | Result | Carry |
|---|---|---|
| `r16 = a + b` | 4464 | lost |
| `r17 = a + b` | 70000 | kept |
| `r16 = (a + b) >> 1` | 2232 | lost before the shift |
| `r17 = (a + b) >> 1` | 35000 | kept |
| `r16 = (a + b + 0) >> 1` | 35000 | kept, by the 32-bit zero |

The manual's passage in 4.4.1 discusses the first three rows only. Its sentence "the sum
of (a + b) produces an interim result that is only 16 bits wide" is about the third row,
an assignment to a 16-bit register, and does not hold for the fourth.

### Multiplication, thirty cases

Verilator 5.028 and Icarus Verilog 13.0 give identical output on all thirty. Operands:
4-bit `n = 13`, 8-bit `a = 200`, `b = 100`, `c = 50`; `rN` is an `N`-bit register.
True values: `a*b` = 20000, `n*a` = 2600, `a*b*c` = 1000000. "Width" is the computation
width the rule predicts; every result equals the true value cut to that width at each
operator.

| # | Expression | Result | Width | Note |
|---|---|---|---|---|
| 01 | `$bits(a*b)` | 8 | | max, not 16 |
| 02 | `$bits(n*a)` | 8 | | max of 4 and 8, not 12 |
| 03 | `$bits(a*b*c)` | 8 | | does not grow with each `*` |
| 04 | `r8 = a*b` | 32 | 8 | 20000 mod 2^8 |
| 05 | `r12 = a*b` | 3616 | 12 | 20000 mod 2^12 |
| 06 | `r16 = a*b` | 20000 | 16 | full product |
| 07 | `r32 = a*b` | 20000 | 32 | |
| 08 | `r8 = n*a` | 40 | 8 | 2600 mod 2^8 |
| 09 | `r16 = n*a` | 2600 | 16 | |
| 10 | `r16 = a*b*c` | 16960 | 16 | 1000000 mod 2^16 |
| 11 | `r24 = a*b*c` | 1000000 | 24 | |
| 12 | `r16 = a*b+c` | 20050 | 16 | |
| 13 | `r8 = a*b+c` | 82 | 8 | 20050 mod 2^8 |
| 14 | `r16 = (a*b)>>4` | 1250 | 16 | 20000 >> 4 |
| 15 | `r8 = (a*b)>>4` | 2 | 8 | product cut to 32 first, then shifted |
| 16 | `r8 = (a*b)>>8` | 0 | 8 | the high half is not reachable this way |
| 17 | `r16 = {a*b}` | 32 | 8 inside | concatenation cuts the context off |
| 18 | `r16 = {8'd0,a}*b` | 20000 | 16 | a widened operand widens the product |
| 19 | `r8 = ({8'd0,a}*b)>>8` | 78 | 16 | the way to get the high half |
| 20 | `(a*b) > 8'd100` | 0 | 8 | 32 > 100 |
| 21 | `(a*b) > 16'd100` | 1 | 16 | the other side of the comparison widens it |
| 22 | `(a*b) > 100` | 1 | 32 | unsized literal is 32 bits |
| 23 | `(a*b) == 8'd32` | 1 | 8 | |
| 24 | `r16 = a*2` | 400 | 32 | unsized literal |
| 25 | `r8 = (a*2)>>1` | 200 | 32 | 400 >> 1, kept by the 32-bit literal |
| 26 | `r8 = (a*8'd2)>>1` | 72 | 8 | 400 mod 2^8 = 144, then >> 1 |
| 27 | `r16 = n[0] ? a*b : c` | 20000 | 16 | the context passes into the branches |
| 28 | `r16 = a << (n*8'd1)` | 0 | 16; amount at 8 | shift amount is sized on its own |
| 29 | `r16 = (a*b)/c` | 400 | 16 | 20000 / 50 |
| 30 | `r8 = (a*b)/c` | 0 | 8 | 32 / 50 |

## Sources, and how far each was checked

- **OVI Verilog HDL Language Reference Manual**, sections 4.4.1 and 4.4.2. The table and
  the quotations above were read from the PDF text.
  <https://cin.ufpe.br/~apaf/if674/verilog%20LangRefereceManual.PDF>
- **Verilator runs** above: run on this machine.
- **IEEE 1800, section 11.6, table 11-21**, "Bit lengths resulting from self-determined
  expressions": the current form of the same table. Not read directly; its existence
  and its use for shifts and `?:` are confirmed by a committee member's forum post.
  <https://verificationacademy.com/forums/t/expression-bit-length-and-associativity/51613>
- **A source that disagrees.** One tutorial blog gives `i * j` the width
  `L(i) + L(j)`. That contradicts the manual's table and the `$bits(a * b) = 8` run, so
  it is taken to be wrong.
  <https://verilogtutorial.blogspot.com/2012/09/expression-bit-length.html>

## Not covered yet

- Signed operands: extension is by sign, and the signedness of an expression has its own
  propagation rules.
- Fill literals `'0`, `'1`, which take the computation width.
- Contexts other than assignment: port connections, function arguments, `case` items.
