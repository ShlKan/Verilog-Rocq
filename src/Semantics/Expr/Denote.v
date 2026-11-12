(** * Expressions: from the AST to a tree

    [denote_expr e] is the tree that evaluates the expression [e] to a value. Each
    case hands over to the definition of its construct; a construct that is not
    written yet is an error, never a default value. *)

From Stdlib Require Import NArith.BinNat Lists.List Strings.String.
From ITree Require Import ITree Events.Exception.
From RiscVITree Require Import data.
Require Import Lib.HMap Lang.Syntax.
Require Import Semantics.Core.Events Semantics.Core.Value.
Require Import Semantics.Expr.Literal Semantics.Expr.Var Semantics.Expr.Ops.
Require Import Semantics.Expr.Width.

Import ListNotations ITreeNotations.
Local Open Scope itree_scope.
Local Open Scope string_scope.

Section Denote.
  Context `{vid_ops} `{BitVec}.
  Context {S : sigs} {E : Type -> Type} `{sigE S -< E} `{errE -< E}.

  (** [w] is the computation width, fixed by the caller before anything is
      evaluated (see [Width.v]). The result has that width. *)
  Fixpoint denote_expr (w : N) (e : @VExpr vid_t) : itree E (bv w) :=
    match e with
    (* a literal, extended or cut to [w] *)
    | VExprPriLiteral p =>
        match sem_literal p with
        | Some v => Ret (resize w v)
        | None => throw "literal not supported"
        end
    (* a variable, read at its declared width, then extended or cut to [w] *)
    | VExprId x =>
        v <- sem_var (S:=S) [x];;
        Ret (resize w v)
    (* [+ - ~] compute at [w]; [!] and the reductions size their operand on its
       own and give one bit, which is then extended to [w] *)
    | VExprUniOp op e1 =>
        let n := if unop_in_context op then w else self_width S e1 in
        a <- denote_expr n e1;;
        Ret (resize w (sem_unop op (mk a)))
    (* both operands at [w], and the operator at [w] *)
    | VExprBinOp op e1 e2 =>
        a <- denote_expr w e1;;
        b <- denote_expr w e2;;
        if div_by_zero op b then throw "division by zero" else
        match sem_binop op a b with
        | Some r => Ret r
        | None => throw "binary operator not supported"
        end
    | _ => throw "expression not supported"
    end.

End Denote.
