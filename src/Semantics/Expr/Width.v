(** * The width of an expression

    Verilog fixes the width at which an expression is computed before computing
    anything. [self_width e] is the width [e] has on its own, found from the
    declarations without evaluating anything. It follows the table "Bit lengths
    resulting from expressions" of the Verilog reference manual row by row.

    An assignment [x = e] is then computed at the larger of the width of [x] and
    [self_width e], and every operator in [e] runs at that width. So in [c = a + b]
    with 8-bit [a], [b] and 9-bit [c] the sum is taken at 9 bits and keeps its
    carry, while with an 8-bit [c] it is taken at 8 bits and loses it.

    Sources and simulator checks are in [docs/notes-expression-width.md].

    An expression that is not supported yet has width 0 here; its evaluation is an
    error anyway. *)

From Stdlib Require Import NArith.BinNat Lists.List.
From RiscVITree Require Import data.
Require Import Lib.HMap Lang.Syntax.
Require Import Semantics.Core.Events Semantics.Core.Value Semantics.Expr.Literal.

Import ListNotations.

Section Width.
  Context `{vid_ops} `{BitVec}.
  Context (S : sigs).

  Fixpoint self_width (e : @VExpr vid_t) : N :=
    match e with
    (* a literal: the width it states, 32 if it states none; ['0], ['1]: one bit *)
    | VExprPriLiteral p =>
        match sem_literal p with
        | Some v => vwidth v
        | None => 1
        end
    (* a variable: its declared width *)
    | VExprId x => width S ([x], [])
    | VExprUniOp op e1 =>
        match op with
        (* [+e], [-e], [~e]: the width of the operand *)
        | VUniPlus | VUniMinus | VUniNeg => self_width e1
        (* [!e] and the reductions: one bit *)
        | _ => 1
        end
    | VExprBinOp op e1 e2 =>
        match op with
        (* arithmetic and bitwise, [*] included: the wider operand. The full
           product or the carry is kept only when the target is wider. *)
        | VBinAdd | VBinSub | VBinMul | VBinDiv | VBinRem
        | VBinBAnd | VBinBOr | VBinBXor | VBinBXnor =>
            N.max (self_width e1) (self_width e2)
        (* shifts and power: the left operand *)
        | VBinShl | VBinShr | VBinSal | VBinSar | VBinPow => self_width e1
        (* comparisons and logical operators: one bit *)
        | _ => 1
        end
    (* [c ? a : b]: the wider branch *)
    | VExprCond _ e1 e2 => N.max (self_width e1) (self_width e2)
    | _ => 0
    end.

End Width.
