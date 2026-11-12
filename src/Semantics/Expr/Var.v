(** * Construct 2: reading a variable

    [x] as an expression. A declared variable is read with one [Get] event, and the
    bits it answers are packed with the variable's width. An undeclared variable is
    an error ([throw]): nothing is read silently.

    Only plain variables; an array element [m[i]] is a later construct. *)

From Stdlib Require Import Lists.List Strings.String.
From ITree Require Import ITree Events.Exception.
From RiscVITree Require Import data.
Require Import Lib.HMap Semantics.Core.Events Semantics.Core.Value.

Import ListNotations ITreeNotations.
Local Open Scope itree_scope.
Local Open Scope string_scope.

Section Var.
  Context `{vid_ops} `{BitVec}.
  Context {S : sigs} {E : Type -> Type} `{sigE S -< E} `{errE -< E}.

  Definition sem_var (x : vname) : itree E value :=
    if declared S (x, []) then
      v <- trigger (Get (S:=S) (x, []));;
      Ret (mk v)
    else
      throw "undeclared variable".

End Var.
