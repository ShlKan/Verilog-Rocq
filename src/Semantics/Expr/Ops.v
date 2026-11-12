(** * Operators

    The meaning of an operator, given the values of its operands. No events: an
    operator only computes. *)

From Stdlib Require Import ZArith.
From RiscVITree Require Import data.
Require Import Lang.Syntax Semantics.Core.Value.

Section Ops.
  Context `{BitVec}.

  (** A truth value as a one-bit value. *)
  Definition of_bool (c : bool) : value := mk (Z_to_bv 1 (if c then 1 else 0)).

  (** Whether the number of 1 bits among the low [n] bits of [b] is odd. *)
  Definition parity {n : N} (b : bv n) : bool :=
    N.recursion false (fun i acc => xorb acc (bv_test_bit b i)) n.

  (** Constructs 6 and 7: the unary operators. The result of [+], [-] and [~] has
      the width of the operand. [!] and the reduction operators give one bit. *)
  Definition sem_unop (op : VUniOp) (v : value) : value :=
    let n := vwidth v in
    let b := projT2 v in
    let zero := Z_to_bv n 0 in
    match op with
    (* [+e]: the operand itself *)
    | VUniPlus => v
    (* [-e]: zero minus the operand *)
    | VUniMinus => mk (bv_sub zero b)
    (* [~e]: every bit flipped *)
    | VUniNeg => mk (bv_not b)
    (* [!e]: 1 if the operand is zero *)
    | VUniNot => of_bool (bv_equal b zero)
    (* [&e]: 1 if every bit is 1 *)
    | VUniAnd => of_bool (bv_equal b (bv_not zero))
    (* [~&e]: 1 if some bit is 0 *)
    | VUniNand => of_bool (negb (bv_equal b (bv_not zero)))
    (* [|e]: 1 if some bit is 1 *)
    | VUniOr => of_bool (negb (bv_equal b zero))
    (* [~|e]: 1 if every bit is 0 *)
    | VUniNor => of_bool (bv_equal b zero)
    (* [^e]: 1 if the number of 1 bits is odd *)
    | VUniXor => of_bool (parity b)
    (* [~^e]: 1 if the number of 1 bits is even *)
    | VUniXnor => of_bool (negb (parity b))
    end.

  (** Whether a unary operator takes its width from the context ([+ - ~]) or
      sizes its operand on its own ([!] and the reductions). *)
  Definition unop_in_context (op : VUniOp) : bool :=
    match op with
    | VUniPlus | VUniMinus | VUniNeg => true
    | _ => false
    end.

  (** Constructs 8 and 9: the bitwise operators [& | ^ ~^] and the arithmetic
      operators [+ - * / %]. Both operands are given at the computation width,
      and so is the result: a carry or the high half of a product is kept only if
      that width has room for it. [None]: not supported yet. *)
  Definition sem_binop (op : VBinOp) {n : N} (a b : bv n) : option (bv n) :=
    match op with
    (* [a & b]: 1 where both bits are 1 *)
    | VBinBAnd => Some (bv_and a b)
    (* [a | b]: 1 where at least one bit is 1 *)
    | VBinBOr => Some (bv_or a b)
    (* [a ^ b]: 1 where the bits differ *)
    | VBinBXor => Some (bv_xor a b)
    (* [a ~^ b]: 1 where the bits are equal *)
    | VBinBXnor => Some (bv_not (bv_xor a b))
    (* [a + b]: the sum, cut to the computation width *)
    | VBinAdd => Some (bv_add a b)
    (* [a - b]: the difference, cut to the computation width *)
    | VBinSub => Some (bv_sub a b)
    (* [a * b]: the product, cut to the computation width *)
    | VBinMul => Some (bv_mul a b)
    (* [a / b], [a % b]: unsigned; [b = 0] is caught by [div_by_zero] before
       this is applied, see [docs/notes-division-by-zero.md] *)
    | VBinDiv => Some (bv_divu a b)
    | VBinRem => Some (bv_modu a b)
    | _ => None
    end.

  (** Construct 9a, the one run-time error of the operators: [/] and [%] with a
      zero divisor. Verilog gives [x], which a two-state model has no value for;
      [denote_expr] raises an error instead. *)
  Definition div_by_zero (op : VBinOp) {n : N} (b : bv n) : bool :=
    match op with
    | VBinDiv | VBinRem => bv_equal b (Z_to_bv n 0)
    | _ => false
    end.

End Ops.
