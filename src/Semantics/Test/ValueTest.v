(** * Value tests

    Computed with the stdpp bit-vectors of [RiscVITree.data.stdpp_impl] and
    compared with what Verilator 5.028 and Icarus Verilog 13.0 print for the same
    expressions; the numbers are from the tables in
    [docs/notes-expression-width.md]. Nothing is interpreted here: the operators
    are applied directly, and the expressions use literals only, so their trees
    are a plain [Ret]. *)

From Stdlib Require Import NArith.BinNat ZArith Lists.List Strings.String.
From ITree Require Import ITree Events.Exception.
From RiscVITree Require Import data data.stdpp_impl.
Require Import Lib.HMap Lang.Syntax.
Require Import Semantics.Core.Events Semantics.Core.Value.
Require Import Semantics.Expr.Ops Semantics.Expr.Width Semantics.Expr.Denote.
Require Import Semantics.Test.TestLib.

Import ListNotations.
Local Open Scope string_scope.
Local Open Scope Z_scope.

(** ** The operators on concrete bit-vectors *)

Definition z {n : N} (v : bv n) : Z := bv_to_Z v.
Definition zo {n : N} (o : option (bv n)) : option Z := option_map bv_to_Z o.
Definition zv (v : value) : Z := bv_to_Z (projT2 v).

(** [resize]: cut or zero-extend. *)
Example rs_cut : z (resize 8 (mk (Z_to_bv 9 300))) = 44.    Proof. vm_compute. reflexivity. Qed.
Example rs_ext : z (resize 16 (mk (Z_to_bv 8 200))) = 200.  Proof. vm_compute. reflexivity. Qed.
Example rs_same : z (resize 8 (mk (Z_to_bv 8 200))) = 200.  Proof. vm_compute. reflexivity. Qed.

(** [a * b] with 200 and 100 (true product 20000) at each width in which a
    simulator computed it: the low bits of the product. *)
Example mul8  : zo (sem_binop VBinMul (Z_to_bv 8 200) (Z_to_bv 8 100)) = Some 32.      Proof. vm_compute. reflexivity. Qed.
Example mul12 : zo (sem_binop VBinMul (Z_to_bv 12 200) (Z_to_bv 12 100)) = Some 3616.  Proof. vm_compute. reflexivity. Qed.
Example mul16 : zo (sem_binop VBinMul (Z_to_bv 16 200) (Z_to_bv 16 100)) = Some 20000. Proof. vm_compute. reflexivity. Qed.
Example mul32 : zo (sem_binop VBinMul (Z_to_bv 32 200) (Z_to_bv 32 100)) = Some 20000. Proof. vm_compute. reflexivity. Qed.

(** [a + b] with 200 and 100 (true sum 300): the carry survives at 9 bits. *)
Example add8 : zo (sem_binop VBinAdd (Z_to_bv 8 200) (Z_to_bv 8 100)) = Some 44.   Proof. vm_compute. reflexivity. Qed.
Example add9 : zo (sem_binop VBinAdd (Z_to_bv 9 200) (Z_to_bv 9 100)) = Some 300.  Proof. vm_compute. reflexivity. Qed.

(** [b - a] wraps. *)
Example sub8  : zo (sem_binop VBinSub (Z_to_bv 8 100) (Z_to_bv 8 200)) = Some 156.    Proof. vm_compute. reflexivity. Qed.
Example sub16 : zo (sem_binop VBinSub (Z_to_bv 16 100) (Z_to_bv 16 200)) = Some 65436. Proof. vm_compute. reflexivity. Qed.

(** Bitwise, 200 = 11001000 and 100 = 01100100. *)
Example band : zo (sem_binop VBinBAnd (Z_to_bv 8 200) (Z_to_bv 8 100)) = Some 64.   Proof. vm_compute. reflexivity. Qed.
Example bor  : zo (sem_binop VBinBOr (Z_to_bv 8 200) (Z_to_bv 8 100)) = Some 236.   Proof. vm_compute. reflexivity. Qed.
Example bxor : zo (sem_binop VBinBXor (Z_to_bv 8 200) (Z_to_bv 8 100)) = Some 172.  Proof. vm_compute. reflexivity. Qed.
Example bxnor : zo (sem_binop VBinBXnor (Z_to_bv 8 200) (Z_to_bv 8 100)) = Some 83. Proof. vm_compute. reflexivity. Qed.

(** [/] and [%], 200 / 7 = 28 remainder 4 in both simulators. *)
Example div8 : zo (sem_binop VBinDiv (Z_to_bv 8 200) (Z_to_bv 8 7)) = Some 28. Proof. vm_compute. reflexivity. Qed.
Example rem8 : zo (sem_binop VBinRem (Z_to_bv 8 200) (Z_to_bv 8 7)) = Some 4.  Proof. vm_compute. reflexivity. Qed.
Example dz_yes : div_by_zero VBinDiv (Z_to_bv 8 0) = true.  Proof. vm_compute. reflexivity. Qed.
Example dz_no  : div_by_zero VBinDiv (Z_to_bv 8 7) = false. Proof. vm_compute. reflexivity. Qed.
Example dz_add : div_by_zero VBinAdd (Z_to_bv 8 0) = false. Proof. vm_compute. reflexivity. Qed.

(** Not supported yet. *)
Example pow_none : zo (sem_binop VBinPow (Z_to_bv 8 2) (Z_to_bv 8 3)) = None. Proof. vm_compute. reflexivity. Qed.

(** Unary, on 200 = 11001000 (three 1 bits). *)
Example u_plus  : zv (sem_unop VUniPlus (mk (Z_to_bv 8 200))) = 200.  Proof. vm_compute. reflexivity. Qed.
Example u_minus : zv (sem_unop VUniMinus (mk (Z_to_bv 8 200))) = 56.  Proof. vm_compute. reflexivity. Qed.
Example u_neg8  : zv (sem_unop VUniNeg (mk (Z_to_bv 8 200))) = 55.    Proof. vm_compute. reflexivity. Qed.
Example u_neg16 : zv (sem_unop VUniNeg (mk (Z_to_bv 16 200))) = 65335. Proof. vm_compute. reflexivity. Qed.
Example u_not   : zv (sem_unop VUniNot (mk (Z_to_bv 8 200))) = 0.     Proof. vm_compute. reflexivity. Qed.
Example u_not0  : zv (sem_unop VUniNot (mk (Z_to_bv 8 0))) = 1.       Proof. vm_compute. reflexivity. Qed.
Example u_and   : zv (sem_unop VUniAnd (mk (Z_to_bv 8 200))) = 0.     Proof. vm_compute. reflexivity. Qed.
Example u_and1  : zv (sem_unop VUniAnd (mk (Z_to_bv 8 255))) = 1.     Proof. vm_compute. reflexivity. Qed.
Example u_nand  : zv (sem_unop VUniNand (mk (Z_to_bv 8 200))) = 1.    Proof. vm_compute. reflexivity. Qed.
Example u_or    : zv (sem_unop VUniOr (mk (Z_to_bv 8 200))) = 1.      Proof. vm_compute. reflexivity. Qed.
Example u_nor   : zv (sem_unop VUniNor (mk (Z_to_bv 8 0))) = 1.       Proof. vm_compute. reflexivity. Qed.
Example u_xor   : zv (sem_unop VUniXor (mk (Z_to_bv 8 200))) = 1.     Proof. vm_compute. reflexivity. Qed.
Example u_xnor  : zv (sem_unop VUniXnor (mk (Z_to_bv 8 200))) = 0.    Proof. vm_compute. reflexivity. Qed.
Example u_width : vwidth (sem_unop VUniXor (mk (Z_to_bv 8 200))) = 1%N. Proof. vm_compute. reflexivity. Qed.

(** ** Expressions with literals only

    Their trees have no events, so [observe] gives the value directly. [w] plays
    the part of the computation width an assignment would choose. *)

Definition S : sigs := sigs_of [].
Definition E := sigE S +' errE.

Definition eval (w : N) (e : @VExpr string) : option Z :=
  match observe (denote_expr (S:=S) (E:=E) w e) with
  | RetF v => Some (bv_to_Z v)
  | _ => None
  end.

(** [r8 = 8'd200 * 8'd100] is computed at 8 bits, [r16 = ...] at 16. *)
Example e_mul8  : eval 8  (bin VBinMul (dec 8 200) (dec 8 100)) = Some 32.    Proof. vm_compute. reflexivity. Qed.
Example e_mul16 : eval 16 (bin VBinMul (dec 8 200) (dec 8 100)) = Some 20000. Proof. vm_compute. reflexivity. Qed.

(** The cut happens at each operator, before the next one runs: at 8 bits
    [(200 + 100) + 100] is 44 + 100 = 144, at 9 bits it is 300 + 100 = 400. *)
Example e_add8  : eval 8 (bin VBinAdd (dec 8 200) (dec 8 100)) = Some 44.   Proof. vm_compute. reflexivity. Qed.
Example e_add9  : eval 9 (bin VBinAdd (dec 8 200) (dec 8 100)) = Some 300.  Proof. vm_compute. reflexivity. Qed.
Example e_add_add8 : eval 8 (bin VBinAdd (bin VBinAdd (dec 8 200) (dec 8 100)) (dec 8 100)) = Some 144. Proof. vm_compute. reflexivity. Qed.
Example e_add_add9 : eval 9 (bin VBinAdd (bin VBinAdd (dec 8 200) (dec 8 100)) (dec 8 100)) = Some 400. Proof. vm_compute. reflexivity. Qed.

(** [(200 * 100) / 50] is 400 at 16 bits and 0 at 8 (32 / 50), as both
    simulators printed; a zero divisor is an error, not a value. *)
Example e_div16 : eval 16 (bin VBinDiv (bin VBinMul (dec 8 200) (dec 8 100)) (dec 8 50)) = Some 400. Proof. vm_compute. reflexivity. Qed.
Example e_div8  : eval 8  (bin VBinDiv (bin VBinMul (dec 8 200) (dec 8 100)) (dec 8 50)) = Some 0.   Proof. vm_compute. reflexivity. Qed.
Example e_div0  : eval 8 (bin VBinDiv (dec 8 200) (dec 8 0)) = None. Proof. vm_compute. reflexivity. Qed.

(** A literal wider than [w] is cut; a narrower one is extended. *)
Example e_lit_cut : eval 8 (dec 16 300) = Some 44.   Proof. vm_compute. reflexivity. Qed.
Example e_lit_ext : eval 16 (dec 8 200) = Some 200.  Proof. vm_compute. reflexivity. Qed.
Example e_unsized : eval 32 (num 100) = Some 100.    Proof. vm_compute. reflexivity. Qed.

(** [~] runs at [w]; [!] and the reductions size their operand on its own. *)
Example e_neg16 : eval 16 (un VUniNeg (dec 8 200)) = Some 65335. Proof. vm_compute. reflexivity. Qed.
Example e_not16 : eval 16 (un VUniNot (dec 8 200)) = Some 0.     Proof. vm_compute. reflexivity. Qed.
Example e_xor16 : eval 16 (un VUniXor (dec 8 200)) = Some 1.     Proof. vm_compute. reflexivity. Qed.

(** The computation width of an assignment, from both sides: [r16 = 8'd200 * 8'd100]
    is computed at 16 bits and gives the full product, [r8 = ...] at 8 bits. *)
Definition S2 : sigs := sigs_of [("r8", Bits 8); ("r16", Bits 16)].
Example e_assign16 :
  let e := bin VBinMul (dec 8 200) (dec 8 100) in
  eval (N.max (width S2 (["r16"], [])) (self_width S2 e)) e = Some 20000.
Proof. vm_compute. reflexivity. Qed.
Example e_assign8 :
  let e := bin VBinMul (dec 8 200) (dec 8 100) in
  eval (N.max (width S2 (["r8"], [])) (self_width S2 e)) e = Some 32.
Proof. vm_compute. reflexivity. Qed.
