(** * Tests of [self_width]

    Each test is a row of the simulator tables in [docs/notes-expression-width.md]:
    the width of an expression on its own, as [$bits] reports it in Verilator and
    Icarus Verilog. They hold by computation. *)

From Stdlib Require Import NArith.BinNat ZArith Lists.List Strings.String.
From RiscVITree Require Import data.
Require Import Lib.HMap Lang.Syntax.
Require Import Semantics.Core.Events Semantics.Expr.Width.

Import ListNotations.
Local Open Scope string_scope.
Local Open Scope N_scope.

(** Identifiers are strings in the tests. *)
#[local] Instance vid_string : vid_t_c := {| vid_t := string |}.
#[local] Instance vid_string_ops : vid_ops := {| vid_eq_dec := string_dec |}.

Section WidthTest.
  Context `{BitVec}.

  (** [reg [3:0] n;  reg [7:0] a, b, c;  reg [15:0] r16;] *)
  Definition S : sigs := fun x =>
    if List.list_eq_dec string_dec x ["n"] then Some (Bits 4)
    else if List.list_eq_dec string_dec x ["a"] then Some (Bits 8)
    else if List.list_eq_dec string_dec x ["b"] then Some (Bits 8)
    else if List.list_eq_dec string_dec x ["c"] then Some (Bits 8)
    else if List.list_eq_dec string_dec x ["r16"] then Some (Bits 16)
    else None.

  (** Short names for building expressions. *)
  Definition var (x : string) : @VExpr string := VExprId x.
  Definition bin (op : VBinOp) (e1 e2 : @VExpr string) : @VExpr string := VExprBinOp op e1 e2.
  Definition un (op : VUniOp) (e : @VExpr string) : @VExpr string := VExprUniOp op e.
  (** [sz'd z] *)
  Definition dec (sz z : Z) : @VExpr string :=
    VExprPriLiteral (VPriLiteralNumber (VNumberIntegral (VIntegralDecimal (VDecimalNumberB (Some sz) z)))).
  (** [z], unsized *)
  Definition num (z : Z) : @VExpr string :=
    VExprPriLiteral (VPriLiteralNumber (VNumberIntegral (VIntegralDecimal (VDecimalNumberNB z)))).

  Local Notation a := (var "a").
  Local Notation b := (var "b").
  Local Notation c := (var "c").
  Local Notation n := (var "n").

  (** Variables and literals. *)
  Example w_var : self_width S a = 8. Proof. reflexivity. Qed.
  Example w_var4 : self_width S n = 4. Proof. reflexivity. Qed.
  Example w_sized : self_width S (dec 16 100) = 16. Proof. reflexivity. Qed.
  Example w_unsized : self_width S (num 100) = 32. Proof. reflexivity. Qed.
  Example w_undeclared : self_width S (var "nope") = 0. Proof. reflexivity. Qed.

  (** [$bits(a*b) = 8], [$bits(n*a) = 8], [$bits(a*b*c) = 8]: the wider operand,
      not the sum of the widths, and no growth with each [*]. *)
  Example w_mul : self_width S (bin VBinMul a b) = 8. Proof. reflexivity. Qed.
  Example w_mul_mixed : self_width S (bin VBinMul n a) = 8. Proof. reflexivity. Qed.
  Example w_mul3 : self_width S (bin VBinMul (bin VBinMul a b) c) = 8. Proof. reflexivity. Qed.

  (** The other arithmetic and bitwise operators follow the same row. *)
  Example w_add : self_width S (bin VBinAdd a b) = 8. Proof. reflexivity. Qed.
  Example w_and_mixed : self_width S (bin VBinBAnd n a) = 8. Proof. reflexivity. Qed.

  (** A literal is an operand like any other: [a * 2] is 32 bits, [a * 8'd2] is 8. *)
  Example w_mul_unsized : self_width S (bin VBinMul a (num 2)) = 32. Proof. reflexivity. Qed.
  Example w_mul_sized : self_width S (bin VBinMul a (dec 8 2)) = 8. Proof. reflexivity. Qed.

  (** A shift has the width of its left operand: [(a + b) >> 1] is 8 bits, whatever
      the width of the amount. *)
  Example w_shr : self_width S (bin VBinShr (bin VBinAdd a b) (num 1)) = 8. Proof. reflexivity. Qed.

  (** Comparisons, [!] and the reductions are one bit. *)
  Example w_gt : self_width S (bin VBinGt (bin VBinMul a b) (dec 8 100)) = 1. Proof. reflexivity. Qed.
  Example w_not : self_width S (un VUniNot a) = 1. Proof. reflexivity. Qed.
  Example w_redand : self_width S (un VUniAnd a) = 1. Proof. reflexivity. Qed.

  (** [~], unary [-] and [+] keep the width of the operand. *)
  Example w_neg : self_width S (un VUniNeg a) = 8. Proof. reflexivity. Qed.
  Example w_minus : self_width S (un VUniMinus n) = 4. Proof. reflexivity. Qed.

  (** [c ? a : b]: the wider branch; the condition does not count. *)
  Example w_cond : self_width S (VExprCond (var "r16") n a) = 8. Proof. reflexivity. Qed.

  (** The computation width of an assignment: the larger of the two sides.
      [r16 = a * b] is computed at 16 bits, [a = a * b] at 8, [n = a + b] at 8. *)
  Example w_assign_wide :
    N.max (width S (["r16"], [])) (self_width S (bin VBinMul a b)) = 16.
  Proof. reflexivity. Qed.
  Example w_assign_same :
    N.max (width S (["a"], [])) (self_width S (bin VBinMul a b)) = 8.
  Proof. reflexivity. Qed.
  Example w_assign_narrow :
    N.max (width S (["n"], [])) (self_width S (bin VBinAdd a b)) = 8.
  Proof. reflexivity. Qed.

End WidthTest.
