(** * Scheduling the blocks of a module within a step

    A module is a list of blocks, each an ITree. This file composes them:
    - [sched bs] runs every block of [bs] once, in an order asked for with [Choose];
    - [round ls] runs the levels [ls] in order, the blocks of one level in a chosen
      order, then [Commit]s;
    - [rounds ls] repeats [round] until a [Commit] changes nothing.

    Levels come from levelization: a block is in a later level than every block
    whose blocking writes it reads, so that order is forced and not a choice. The
    blocks within one level are the ones Verilog leaves unordered.

    A chosen block runs to its end before the next choice. Reading the inputs and
    writing the outputs around [rounds] is the step wrapper's job, not this file's. *)

From Stdlib Require Import Lists.List.
#[local] Set Warnings "-stdlib-vector".
From Stdlib Require Vectors.Fin.
#[local] Set Warnings "+stdlib-vector".
(* Not imported: stdpp's notations and [ITreeNotations] disagree on the
   associativity of level 61. [base.lookup n l] is [l !! n]. *)
From stdpp Require base list.
From ITree Require Import ITree.
Require Import Lib.HMap Semantics.Core.Events.

Import ListNotations ITreeNotations.
Local Open Scope itree_scope.

Set Implicit Arguments.

Section Sched.
  Context `{vid_ops}.
  Context {E : Type -> Type} `{chooseE -< E} `{stepE -< E}.

  (** A loop over the blocks still to run: choose one, run it, continue with the
      others. A single remaining block needs no choice. The [None] branch is
      unreachable, the answer to [Choose n] being below [n]. *)
  Definition sched (bs : list (itree E unit)) : itree E unit :=
    ITree.iter (fun bs : list (itree E unit) =>
      match bs with
      | [] => Ret (inr tt)
      | [b] => b;; Ret (inr tt)
      | _ =>
          i <- trigger (Choose (length bs));;
          let n := proj1_sig (Fin.to_nat i) in
          match base.lookup n bs with
          | Some b => b;; Ret (inl (base.delete n bs))
          | None => Ret (inr tt)
          end
      end) bs.

  Fixpoint sched_levels (ls : list (list (itree E unit))) : itree E unit :=
    match ls with
    | [] => Ret tt
    | l :: ls' => sched l;; sched_levels ls'
    end.

  (** One round: every block once, then the nonblocking updates. The result is
      [Commit]'s answer, whether anything changed. *)
  Definition round (ls : list (list (itree E unit))) : itree E bool :=
    sched_levels ls;; trigger Commit.

  (** Rounds until stable. A design whose flops clock each other in a cycle never
      becomes stable, and this tree is then infinite. *)
  Definition rounds (ls : list (list (itree E unit))) : itree E unit :=
    ITree.iter (fun _ : unit =>
                  changed <- round ls;;
                  Ret (if changed : bool then inl tt else inr tt)) tt.

End Sched.
