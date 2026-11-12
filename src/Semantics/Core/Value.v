(** * Values of expressions

    The width of a Verilog expression depends on the expression, not on the Rocq type
    of its AST: [a + b] is as wide as the wider operand. So an expression evaluates
    to a bit-vector packed with its width. The events are typed by a fixed width
    ([Get x : sigE S (bv (width S x))]); [mk] and [resize] convert between the two. *)

From Stdlib Require Import NArith.BinNat.
From RiscVITree Require Import data.

Section Value.
  Context `{BitVec}.

  Definition value : Type := { n : N & bv n }.

  Definition mk {n : N} (v : bv n) : value := existT _ n v.

  Definition vwidth (v : value) : N := projT1 v.

  (** Bring a value to width [m], as an unsigned assignment does: the low [m] bits
      if it is too wide, zero-extension if it is too narrow. *)
  Definition resize (m : N) (v : value) : bv m :=
    if (m <=? vwidth v)%N
    then bv_extract 0 m (projT2 v)
    else zero_extend m (projT2 v).

End Value.
