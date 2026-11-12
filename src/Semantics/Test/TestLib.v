(** * Shared setup for the tests

    String identifiers, short names for building syntax trees by hand, a
    declaration table built from a list, and the lemmas and tactic the tree tests
    use. *)

From Stdlib Require Import NArith.BinNat ZArith Lists.List Strings.String.
From ITree Require Import ITree ITreeFacts Events.Exception.
From RiscVITree Require Import data.
Require Import Lib.HMap Lang.Syntax.
Require Import Semantics.Core.Events.

Import ListNotations ITreeNotations.
Local Open Scope itree_scope.

(** Identifiers are strings in the tests. *)
#[export] Instance vid_string : vid_t_c := {| vid_t := string |}.
#[export] Instance vid_string_ops : vid_ops := {| vid_eq_dec := string_dec |}.

(** ** Syntax *)

Definition var (x : string) : @VExpr string := VExprId x.
Definition bin (op : VBinOp) (e1 e2 : @VExpr string) : @VExpr string := VExprBinOp op e1 e2.
Definition un (op : VUniOp) (e : @VExpr string) : @VExpr string := VExprUniOp op e.

Definition lit (i : VIntegralNumber) : @VExpr string :=
  VExprPriLiteral (VPriLiteralNumber (VNumberIntegral i)).
(** [sz'd z] *)
Definition dec (sz z : Z) : @VExpr string := lit (VIntegralDecimal (VDecimalNumberB (Some sz) z)).
(** [z], no size and no base *)
Definition num (z : Z) : @VExpr string := lit (VIntegralDecimal (VDecimalNumberNB z)).
(** [sz'h z] *)
Definition hex (sz z : Z) : @VExpr string := lit (VIntegralHex (Some sz) z).

(** [x = e;], [x <= e;], [begin ... end] *)
Definition set_b (x : string) (e : @VExpr string) : @VStatementItem string :=
  VStatementItemBlockingAssignNormal (VExprId x) e.
Definition set_nb (x : string) (e : @VExpr string) : @VStatementItem string :=
  VStatementItemNonblockingAssign (VExprId x) e.
Definition block (ss : list (@VStatementItem string)) : @VStatementItem string :=
  VStatementSeqBlock ss.

(** ** Declarations *)

(** The table declaring exactly the listed module-level variables. *)
Definition sigs_of (l : list (string * vtype)) : sigs := fun x =>
  match x with
  | [y] =>
      match find (fun p => if string_dec (fst p) y then true else false) l with
      | Some p => Some (snd p)
      | None => None
      end
  | _ => None
  end.

(** ** Trees *)

Section Trees.
  Context {E : Type -> Type}.

  Lemma bind_ret_tt (t : itree E unit) : (t;; Ret tt) ≅ t.
  Proof.
    rewrite <- (bind_ret_r t) at 2.
    eapply eqit_bind; [reflexivity|]. intros []. reflexivity.
  Qed.

  (** Nothing runs after an error. *)
  Lemma bind_throw `{exceptE string -< E} {A B} (msg : string) (k : A -> itree E B) :
    (x <- throw msg;; k x) ≅ throw msg.
  Proof. unfold throw. rewrite bind_vis. apply eqit_Vis. intros []. Qed.
End Trees.

(** Prove that two trees are the same, event for event: unfold the definitions,
    flatten the sequencing, and step over one event at a time. *)
Ltac tree_eq :=
  cbn;
  repeat first
    [ reflexivity
    | rewrite bind_ret_l
    | rewrite bind_bind
    | rewrite bind_throw
    | rewrite bind_ret_tt
    | (eapply eqit_bind; [reflexivity | intros ?]) ];
  cbn.
