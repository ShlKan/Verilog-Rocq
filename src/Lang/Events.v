(** * Events of the ITree semantics of Verilog

    This file fixes the event signature of the new, ITree-based semantics. It is
    independent of [Semantics.v] (the imported LFP semantics over [hmap]) and of the
    syntax; the denotation of the syntax into these events comes in a later file.

    Design:
    - Inside a clock step, the behaviour of a module is a sequence of individual
      accesses to named, typed locations ([sigE]). Each access names exactly one
      location, so two accesses to different locations are independent and may be
      reordered; that independence ([indep_sig]) is what an optimisation proof
      relies on.
    - The module boundary is a set of typed ports ([portE]); direction is in the
      event, so a module cannot drive its own inputs.
    - Clock edges are detected by a handler that remembers previous values
      ([Fired]); nonblocking assignments are pending until [Commit], which applies
      all of them at once at the end of the step.
    - Nothing is dropped silently: an unsupported or ill-formed construct is an
      [Err] event with no continuation.

    Values are bit-vectors [bv n] from the [BitVec] class of [RiscVITree.data], so a
    design and the RISC-V specification share one value type. Identifiers stay
    abstract ([vid_t], as in the rest of [Lang]); real programs instantiate them with
    [string], the case study with its enum. *)

From Stdlib Require Import NArith.BinNat Lists.List Strings.String.
From ITree Require Import Basics.Basics Core.Subevent Indexed.Sum.
From stdpp Require Import base.
From RiscVITree Require Import data.
Require Import Lib.HMap.

Set Implicit Arguments.

Section Events.
  Context `{vid_ops} `{BitVec}.

  (** ** Signatures

      The type of a declared variable: a bit-vector, or an unpacked array dimension
      [lo..hi] of elements of a type. [reg [7:0] m [0:3][0:3]] has type
      [Array 0 3 (Array 0 3 (Bits 8))]. Packed dimensions are part of the
      bit-vector width. *)
  Inductive vtype :=
  | Bits (n : N)
  | Array (lo hi : N) (t : vtype).

  (** A variable name: a path of identifiers. A module-level variable is a
      singleton path [[cnt]]; a variable declared in a named block, a generate
      block or a function is qualified by its scopes, [[blk; t]]. Scopes are
      flattened into the one table of the module this way; the module hierarchy
      (instances) is not in any signature, it is in the composition of handlers. *)
  Definition vname : Type := list vid_t.

  (** The signature of a module: its declaration table, name to type. It holds no
      values; the store that interprets [sigE] does. It is computed from the
      declarations of a module, never written by hand. *)
  Definition sigs : Type := vname -> option vtype.

  (** A location: a variable plus array indices, one per unpacked dimension.
      [([cnt], [])], [([rf], [5])], [([m], [1; 2])]. Each array element is its own
      location, so accesses to different elements are independent. *)
  Definition nloc : Type := vname * list N.

  #[export] Instance nloc_eq_dec : EqDecision nloc.
  Proof.
    intros [x xs] [y ys].
    destruct (List.list_eq_dec vid_eq_dec x y) as [-> | NE].
    - destruct (List.list_eq_dec N.eq_dec xs ys) as [-> | NE]; [left; reflexivity | right].
      intros EQ; apply NE; injection EQ; auto.
    - right. intros EQ; apply NE; injection EQ; auto.
  Defined.

  (** Follow the indices into a type: the width of the element they select, if every
      index is in range and exactly one index is given per dimension. *)
  Fixpoint sel (t : vtype) (is : list N) : option N :=
    match t, is with
    | Bits n, [] => Some n
    | Array lo hi t', i :: is' => if (lo <=? i) && (i <=? hi) then sel t' is' else None
    | _, _ => None
    end%N.

  (** Whether a location is declared, and its width. Undeclared locations have
      width 0; the completeness check keeps them out of a module's events. *)
  Definition declared (S : sigs) (l : nloc) : bool :=
    match S (fst l) with
    | Some t => match sel t (snd l) with Some _ => true | None => false end
    | None => false
    end.

  Definition width (S : sigs) (l : nloc) : N :=
    match S (fst l) with
    | Some t => match sel t (snd l) with Some n => n | None => 0 end
    | None => 0
    end.

  (** ** Access to signals inside a step *)
  Variant sigE (S : sigs) : Type -> Type :=
  | Get (x : nloc) : sigE S (bv (width S x))                  (** read the current value *)
  | SetB (x : nloc) (v : bv (width S x)) : sigE S unit        (** blocking [=]: visible now *)
  | SetNB (x : nloc) (v : bv (width S x)) : sigE S unit.      (** nonblocking [<=]: pending until [Commit] *)

  (** Independence of two accesses: they commute whenever they do not both touch
      the same location with at least one of them writing the current value. A
      pending nonblocking write is invisible to reads and to blocking writes. *)
  Definition indep_sig {S : sigs} {X Y} (e1 : sigE S X) (e2 : sigE S Y) : Prop :=
    match e1, e2 with
    | Get _ _, Get _ _ => True
    | Get _ x, SetB _ y _ | SetB _ x _, Get _ y | SetB _ x _, SetB _ y _ => x <> y
    | Get _ _, SetNB _ _ _ | SetNB _ _ _, Get _ _ => True
    | SetB _ _ _, SetNB _ _ _ | SetNB _ _ _, SetB _ _ _ => True
    | SetNB _ x _, SetNB _ y _ => x <> y
    end.

  (** ** Ports: the module boundary

      An interface is two signatures, the input ports and the output ports. *)
  Record iface := {
    in_sigs : sigs;
    out_sigs : sigs;
  }.

  Variant portE (I : iface) : Type -> Type :=
  | In (p : nloc) : portE I (bv (width (in_sigs I) p))                 (** this step's value of an input *)
  | Out (p : nloc) (v : bv (width (out_sigs I) p)) : portE I unit.     (** drive an output *)

  (** Two port accesses are independent unless both drive the same output. *)
  Definition indep_port {I : iface} {X Y} (e1 : portE I X) (e2 : portE I Y) : Prop :=
    match e1, e2 with
    | Out _ p _, Out _ q _ => p <> q
    | _, _ => True
    end.

  (** ** Edges and the step boundary

      [Fired (Pos x)] asks whether [x] rose since the previous step; the handler
      keeps the previous values, so edge detection is not part of the Verilog state.
      [Commit] ends the step: every pending [SetNB] takes effect at once. *)
  Variant edge := Pos (x : nloc) | Neg (x : nloc).

  Variant stepE : Type -> Type :=
  | Fired (e : edge) : stepE bool
  | Commit : stepE unit.

  (** ** Errors: no continuation, never silent *)
  Variant errE : Type -> Type :=
  | Err (msg : string) : errE void.

  (** ** The event signature of a module

      Module items (blocks, continuous assignments) are denoted over [sigE], [stepE]
      and [errE] only: inside the module, ports are ordinary locations. The step
      wrapper around the items reads every input with [In] into the store first and
      emits every output with [Out] after [Commit]. *)
  Definition moduleE (S : sigs) (I : iface) : Type -> Type :=
    sigE S +' stepE +' portE I +' errE.

End Events.

(* The signature is not inferable from a location, only from the expected event
   type; it is implicit so that one writes [Get x] under [trigger]. The two [_]
   are the [vid_t_c] and [BitVec] instances. *)
Arguments Get {_ _ S} x.
Arguments SetB {_ _ S} x v.
Arguments SetNB {_ _ S} x v.
Arguments In {_ _ I} p.
Arguments Out {_ _ I} p v.

