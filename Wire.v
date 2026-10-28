(** * Wire bytes

    The field kinds the definitions are built from, each with an encoder, a decoder, and the lemmas
    every message proof leans on: an encoding is as wide as its field says, and decoding what was
    encoded gives the value back and leaves the following bytes alone.

    A field of n bytes holds a number below 256^n, written most significant byte first. The bound
    is not in the type - a field is an N - so it is stated where it is needed: each generated
    record carries a bound predicate of its own, and its round trip theorem asks for it. *)

From Stdlib Require Import List.
From Stdlib Require Import NArith.
From Stdlib Require Import Lia.
From Stdlib Require Import Strings.Byte.

Import ListNotations.

(** The byte a value below 256 names *)
Definition byted (value : N) : byte :=
  match Byte.of_N value with
  | Some b => b
  | None => Byte.x00
  end.

Lemma byted_to_N : forall value, (value < 256)%N -> Byte.to_N (byted value) = value.
Proof.
  intros value bound. unfold byted.
  destruct (Byte.of_N value) as [b |] eqn:found.
  - apply Byte.to_of_N in found. exact found.
  - exfalso. apply Byte.of_N_None_iff in found. lia.
Qed.

(** An unsigned field of the given width, most significant byte first *)
Fixpoint encode_uint (width : nat) (value : N) : list byte :=
  match width with
  | O => []
  | S rest =>
      byted (value / 256 ^ N.of_nat rest)%N
        :: encode_uint rest (value mod 256 ^ N.of_nat rest)%N
  end.

Fixpoint decode_uint (width : nat) (bytes : list byte) : option (N * list byte) :=
  match width with
  | O => Some (0%N, bytes)
  | S rest =>
      match bytes with
      | [] => None
      | b :: tail =>
          match decode_uint rest tail with
          | Some (value, after) => Some ((Byte.to_N b * 256 ^ N.of_nat rest + value)%N, after)
          | None => None
          end
      end
  end.

Lemma encode_uint_length :
  forall width value, Datatypes.length (encode_uint width value) = width.
Proof.
  induction width as [| rest IH]; intros value; simpl; [reflexivity | now rewrite IH].
Qed.

Lemma power_positive : forall width, (0 < 256 ^ N.of_nat width)%N.
Proof.
  intros width.
  assert (nonzero : (256 ^ N.of_nat width <> 0)%N) by (apply N.pow_nonzero; lia).
  lia.
Qed.

(** Decoding what was encoded gives the value back and leaves the bytes after it alone *)
Theorem decode_encode_uint :
  forall width value after,
    (value < 256 ^ N.of_nat width)%N ->
    decode_uint width (encode_uint width value ++ after) = Some (value, after).
Proof.
  induction width as [| rest IH]; intros value after bound; simpl.
  - replace value with 0%N by (simpl in bound; lia). reflexivity.
  - assert (positive : (0 < 256 ^ N.of_nat rest)%N) by apply power_positive.
    assert (high : (value / 256 ^ N.of_nat rest < 256)%N).
    { apply N.Div0.div_lt_upper_bound.
      rewrite N.mul_comm, <- N.pow_succ_r'.
      replace (N.succ (N.of_nat rest)) with (N.of_nat (S rest)) by lia. exact bound. }
    rewrite IH by (apply N.mod_lt; lia).
    rewrite byted_to_N by exact high.
    rewrite N.mul_comm, <- N.div_mod by lia.
    reflexivity.
Qed.

(** * Byte runs

    A field of bytes the definition keeps as they are - a text, a reserved run, anything whose
    value is not a number - is a list of bytes of the width its field states. The encoder pads or
    truncates to that width, so an encoding is as wide as the field says whatever it holds, and the
    round trip asks only that the field holds the bytes it says it does. *)

Definition encode_bytes (width : nat) (value : list byte) : list byte :=
  firstn width (value ++ repeat x00 width).

Fixpoint decode_bytes (width : nat) (bytes : list byte) : option (list byte * list byte) :=
  match width with
  | O => Some ([], bytes)
  | S rest =>
      match bytes with
      | [] => None
      | b :: tail =>
          match decode_bytes rest tail with
          | Some (value, after) => Some (b :: value, after)
          | None => None
          end
      end
  end.

Lemma encode_bytes_length :
  forall width value, Datatypes.length (encode_bytes width value) = width.
Proof.
  intros width value. unfold encode_bytes.
  rewrite firstn_length_le; [reflexivity |].
  rewrite length_app, repeat_length. lia.
Qed.

Lemma encode_bytes_exact :
  forall width value, Datatypes.length value = width -> encode_bytes width value = value.
Proof.
  intros width value held. unfold encode_bytes.
  rewrite <- held, firstn_app, firstn_all, PeanoNat.Nat.sub_diag. simpl.
  apply app_nil_r.
Qed.

Lemma decode_bytes_run :
  forall value after,
    decode_bytes (Datatypes.length value) (value ++ after) = Some (value, after).
Proof.
  induction value as [| b tail IH]; intros after; simpl; [reflexivity | now rewrite IH].
Qed.

(** Decoding the bytes that were encoded gives them back, when the field holds its width *)
Theorem decode_encode_bytes :
  forall width value after,
    Datatypes.length value = width ->
    decode_bytes width (encode_bytes width value ++ after) = Some (value, after).
Proof.
  intros width value after held.
  rewrite encode_bytes_exact by exact held.
  rewrite <- held.
  apply decode_bytes_run.
Qed.