(** * Construct 1: number literals

    [8'hFF], [4'b1010], [12], ['d7]. A literal evaluates to a value with no event.

    - A sized literal has the width it states; an unsized one is 32 bits wide.
    - The AST keeps a binary or octal literal as the decimal number with the same
      digits ([4'b1010] is [VIntegralBinary (Some 4) 1010]); [binaryZtoZ] and
      [octalZtoZ] from [Lib.SZ] read the digits back. Hex and decimal literals
      hold their numeric value directly.

    Not done here: ['0] and ['1] take their width from the context, which a literal
    alone does not know, and the signedness of unsized decimals comes with
    signedness. *)

From Stdlib Require Import ZArith.
From RiscVITree Require Import data.
Require Import Lib.SZ Lang.Syntax Semantics.Core.Value.

Section Literal.
  Context `{BitVec}.

  Definition lit_width (osz : option Z) : N :=
    match osz with
    | Some sz => Z.to_N sz
    | None => 32
    end.

  (** The value of a number literal: a bit-vector of the literal's width holding
      its number. One case per way of writing a number.

      Example: [4'b1010] is [VIntegralBinary (Some 4) 1010]. Its width is
      [lit_width (Some 4) = 4]; [binaryZtoZ 4 1010] reads the four digits 1,0,1,0
      as the number ten; the result is [mk (Z_to_bv 4 10)], the 4-bit value ten.

      The two decimal forms: [VDecimalNumberNB] ("no base") is a plain number
      such as [12]; [VDecimalNumberB] ("base") is one written with the decimal
      base ['d], such as [8'd200] or ['d200]. *)
  Definition sem_number (i : VIntegralNumber) : value :=
    match i with
    | VIntegralBinary osz d =>
        let n := lit_width osz in mk (Z_to_bv n (binaryZtoZ (N.to_nat n) d))
    | VIntegralOctal osz d =>
        let n := lit_width osz in mk (Z_to_bv n (octalZtoZ (N.to_nat n) d))
    | VIntegralHex osz z => mk (Z_to_bv (lit_width osz) z)
    | VIntegralDecimal (VDecimalNumberNB z) => mk (Z_to_bv 32 z)
    | VIntegralDecimal (VDecimalNumberB osz z) => mk (Z_to_bv (lit_width osz) z)
    end.

  (** [None]: not supported yet. *)
  Definition sem_literal (p : VPriLiteral) : option value :=
    match p with
    | VPriLiteralNumber (VNumberIntegral i) => Some (sem_number i)
    | VPriLiteralUU _ => None
    end.

End Literal.
