(** * Tree tests

    A statement with variables denotes to a tree with [Get] and [SetB] events in
    it. Each test writes that tree out and proves the denotation equal to it,
    event for event ([≅]): which events, in what order, and at what width each
    value is computed. Nothing is interpreted. *)

From Stdlib Require Import NArith.BinNat ZArith Lists.List Strings.String.
From ITree Require Import ITree ITreeFacts Events.Exception.
From RiscVITree Require Import data.
Require Import Lib.HMap Lang.Syntax.
Require Import Semantics.Core.Events Semantics.Core.Value.
Require Import Semantics.Expr.Ops Semantics.Expr.Denote Semantics.Stmt.Denote Semantics.Stmt.Block.
Require Import Semantics.Test.TestLib.

Import ListNotations ITreeNotations.
Local Open Scope itree_scope.
Local Open Scope string_scope.

Section TreeTest.
  Context `{BitVec}.

  (** [reg [7:0] a, b;  reg [15:0] r16;] *)
  Definition S : sigs := sigs_of [("a", Bits 8); ("b", Bits 8); ("r16", Bits 16)].
  Definition E := sigE S +' errE.

  Local Notation get x := (trigger (Get (S:=S) ([x], []))).
  Local Notation setb x v := (trigger (SetB (S:=S) ([x], []) v)).
  Local Notation setnb x v := (trigger (SetNB (S:=S) ([x], []) v)).
  Local Notation run s := (denote_stmt (S:=S) (E:=E) s).

  (** [a = 8'h01;]: one write, no read. The literal is brought to the computation
      width (8) and then to the width of [a] (8). *)
  Example t_const :
    run (set_b "a" (hex 8 1)) ≅ setb "a" (resize 8 (mk (resize 8 (mk (Z_to_bv 8 1))))).
  Proof. tree_eq. Qed.

  (** [b = a;]: read then write. *)
  Example t_copy :
    run (set_b "b" (var "a")) ≅ (va <- get "a";; setb "b" (resize 8 (mk (resize 8 (mk va))))).
  Proof. tree_eq. Qed.

  (** [r16 = a & b;]: both operands are read at 8 bits and extended to 16 before
      the [&], which runs at 16. *)
  Example t_and16 :
    run (set_b "r16" (bin VBinBAnd (var "a") (var "b")))
    ≅ (va <- get "a";; vb <- get "b";;
       setb "r16" (resize 16 (mk (bv_and (resize 16 (mk va)) (resize 16 (mk vb)))))).
  Proof. tree_eq. Qed.

  (** [begin a = 8'h01; b <= a; end]: the statements in order; the second is a
      pending write. *)
  Example t_block :
    run (block [set_b "a" (hex 8 1); set_nb "b" (var "a")])
    ≅ (setb "a" (resize 8 (mk (resize 8 (mk (Z_to_bv 8 1)))));;
       va <- get "a";;
       setnb "b" (resize 8 (mk (resize 8 (mk va))))).
  Proof. tree_eq. Qed.

  (** Errors: the tree ends at the error, after whatever was read before it. *)
  Example t_undeclared_read :
    run (set_b "a" (var "zz")) ≅ throw "undeclared variable".
  Proof. tree_eq. Qed.

  Example t_undeclared_write :
    run (set_b "zz" (var "a")) ≅ (va <- get "a";; throw "assignment to an undeclared variable").
  Proof. tree_eq. Qed.

  Example t_unsupported :
    run (set_b "a" (bin VBinPow (var "a") (var "b")))
    ≅ (va <- get "a";; vb <- get "b";; throw "binary operator not supported").
  Proof. tree_eq. Qed.

  (** [a = a / b;]: the error depends on the value read for [b], so the tree
      branches on it after the reads. *)
  Example t_div :
    run (set_b "a" (bin VBinDiv (var "a") (var "b")))
    ≅ (va <- get "a";; vb <- get "b";;
       if div_by_zero VBinDiv (resize 8 (mk vb)) then throw "division by zero"
       else setb "a" (resize 8 (mk (bv_divu (resize 8 (mk va)) (resize 8 (mk vb)))))).
  Proof.
    tree_eq.
    destruct (bv_equal _ _); tree_eq.
  Qed.

End TreeTest.
