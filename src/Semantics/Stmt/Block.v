(** * Construct 5: sequential block

    [begin s1; s2; ... end]. The statements run one after the other, each seeing
    the blocking writes of those before it. An empty block does nothing.

    The statements are given already denoted, as trees. *)

From Stdlib Require Import Lists.List.
From ITree Require Import ITree.

Import ListNotations ITreeNotations.
Local Open Scope itree_scope.

Section Block.
  Context {E : Type -> Type}.

  Fixpoint sem_seq (ts : list (itree E unit)) : itree E unit :=
    match ts with
    | [] => Ret tt
    | t :: ts' => t;; sem_seq ts'
    end.

End Block.
