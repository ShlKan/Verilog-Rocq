(** * Constructs 3 and 4: assignments

    [x = e] (blocking) and [x <= e] (nonblocking). In both, the value of [e],
    already evaluated, is brought to the declared width of [x] and written with one
    event. Assigning to an undeclared variable is an error.

    - [x = e] is [SetB]: the new value is visible to the reads that follow.
    - [x <= e] is [SetNB]: the write is pending, reads keep seeing the old value,
      and it takes effect at the next [Commit].

    Only a plain variable as target; [m[i] = e] and [x[7:4] = e] are later
    constructs. *)

From Stdlib Require Import Lists.List Strings.String.
From ITree Require Import ITree Events.Exception.
From RiscVITree Require Import data.
Require Import Lib.HMap Semantics.Core.Events Semantics.Core.Value.

Import ListNotations.
Local Open Scope string_scope.

Section Assign.
  Context `{vid_ops} `{BitVec}.
  Context {S : sigs} {E : Type -> Type} `{sigE S -< E} `{errE -< E}.

  (** Blocking assignment [x = e], with [v] the value of [e]: [x] changes at once,
      so a read of [x] after it sees [v]. *)
  Definition sem_assign_b (x : vname) (v : value) : itree E unit :=
    if declared S (x, []) then
      trigger (SetB (S:=S) (x, []) (resize (width S (x, [])) v))
    else
      throw "assignment to an undeclared variable".

  (** Nonblocking assignment [x <= e], with [v] the value of [e]: [v] is recorded
      now, and [x] changes only at the next [Commit]; until then a read of [x]
      still sees its old value. *)
  Definition sem_assign_nb (x : vname) (v : value) : itree E unit :=
    if declared S (x, []) then
      trigger (SetNB (S:=S) (x, []) (resize (width S (x, [])) v))
    else
      throw "assignment to an undeclared variable".

End Assign.
