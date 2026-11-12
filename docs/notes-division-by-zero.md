# Notes: division by zero

Decision (2026-11-12): `a / 0` and `a % 0` are an error event, `throw "division by
zero"`, raised by `denote_expr` before the operator is applied. The operators
themselves (`sem_binop` in `src/Semantics/Expr/Ops.v`) are unsigned division and
remainder on bit-vectors and are never applied to a zero divisor.

## Why there is something to decide

The Verilog standard says the result of `/` or `%` with a zero divisor is `x`,
unknown. Our values are two-state bit-vectors, which have no `x`, so the standard's
answer cannot be represented. Something else has to be chosen.

Tools do not agree either, since each has to pick a two-state answer somewhere:

| Tool | `8'd200 / 8'd0` | `8'd200 % 8'd0` |
|---|---|---|
| Icarus Verilog 13.0 (four-state) | `xxxxxxxx` | `xxxxxxxx` |
| Verilator 5.028 (two-state) | `0` | `0` |
| Synthesis tools | whatever the divider circuit happens to produce; not specified | |

So any fixed value would agree with some tools and disagree with others, and no value
is "the" semantics.

## Why an error event

- Nothing is invented. A fixed value would make `a / 0` look like a successful
  computation, and a proof about a design could then rely on it.
- It fits the rule that nothing is dropped silently: a design whose inputs can reach a
  zero divisor has a reachable `throw` in its tree, and the completeness check can
  report it.
- A rewrite proved equivalent to the original must have the same error on the same
  paths, so an optimisation cannot quietly change what happens on `/ 0`.
- A design that guards its divisions (`if (b != 0) q = a / b;`) has no reachable
  error, which is also what a careful designer intends.

## Cost

The error is raised in `denote_expr`, not in `sem_binop`, because `sem_binop` is a pure
function on bit-vectors and an error is an event. So `/` and `%` are the one place
where a binary operator's denotation can end in a `throw` with a value-dependent
condition; every other operator is total.

## Alternatives, if the decision is revisited

- `0`, as Verilator. Matches one widely used two-state simulator.
- All ones, which is what some divider implementations produce for `/`, with the
  dividend for `%`.
- A separate "unknown" value, which would be the start of a four-state model and is out
  of scope.
