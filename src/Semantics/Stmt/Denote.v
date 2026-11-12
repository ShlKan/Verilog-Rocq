(** * Statements: from the AST to a tree

    [denote_stmt s] is the tree that runs the statement [s]. Each case evaluates
    the expressions it needs with [denote_expr] and hands over to the definition of
    its construct; a construct that is not written yet is an error. *)

From Stdlib Require Import NArith.BinNat Lists.List Strings.String.
From ITree Require Import ITree Events.Exception.
From RiscVITree Require Import data.
Require Import Lib.HMap Lang.Syntax.
Require Import Semantics.Core.Events Semantics.Core.Value.
Require Import Semantics.Expr.Width Semantics.Expr.Denote.
Require Import Semantics.Stmt.Assign Semantics.Stmt.Block.

Import ListNotations ITreeNotations.
Local Open Scope itree_scope.
Local Open Scope string_scope.

Section Denote.
  Context `{vid_ops} `{BitVec}.
  Context {S : sigs} {E : Type -> Type} `{sigE S -< E} `{errE -< E}.

  Fixpoint denote_stmt (s : @VStatementItem vid_t) : itree E unit :=
    match s with
    (* the right-hand side is computed at the larger of the width of [x] and its
       own width, then cut to the width of [x] by the assignment *)
    | VStatementItemBlockingAssignNormal (VExprId x) e =>
        let w := N.max (width S ([x], [])) (self_width S e) in
        v <- denote_expr (S:=S) w e;; sem_assign_b (S:=S) [x] (mk v)
    | VStatementItemNonblockingAssign (VExprId x) e =>
        let w := N.max (width S ([x], [])) (self_width S e) in
        v <- denote_expr (S:=S) w e;; sem_assign_nb (S:=S) [x] (mk v)
    | VStatementSeqBlock ss => sem_seq (map denote_stmt ss)
    | _ => throw "statement not supported"
    end.

End Denote.
