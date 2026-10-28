From Stdlib Require Import List.
From Stdlib Require Import NArith.
From Stdlib Require Import Lia.
From Stdlib Require Import Strings.Byte.
From Omi Require Import Wire.

Import ListNotations.

(** * Chicago Board Options Exchange Market Data Feed

    Generated from the binary model. Every record is a run of fields, and carries the two
    theorems the model's rules call for: an encoding is as wide as its fields say, and
    decoding what was encoded gives the record back and leaves the bytes after it alone.

    A field is a number of its width, a run of bytes kept as they are, or a record nested
    in it. A number's width bounds it, which the record's own bound predicate states, and
    the round trip asks for that predicate - a field is an N, so the bound is not in the
    type. Text and reserved runs are kept byte for byte, so what is decoded encodes back
    unchanged.

    Each record is a module of its own, so two messages may both have a price and a
    consumer may read either.

    What this definition does not state, and the model does:
      - a run counted by a field
      - a length prefix framing what follows
  *)

Module C1OptionsMarketDataFeedV142.

  Module PacketHeader.

    Record t := {
      version : N;
      packet_length : N;
      sending_time : N;
      message_count : N;
      first_msg_seq_num : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (version record < 256 ^ N.of_nat 1)%N /\
      (packet_length record < 256 ^ N.of_nat 2)%N /\
      (sending_time record < 256 ^ N.of_nat 8)%N /\
      (message_count record < 256 ^ N.of_nat 1)%N /\
      (first_msg_seq_num record < 256 ^ N.of_nat 4)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 1 (version record) ++
      encode_uint 2 (packet_length record) ++
      encode_uint 8 (sending_time record) ++
      encode_uint 1 (message_count record) ++
      encode_uint 4 (first_msg_seq_num record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 1 bytes with
      | None => None
      | Some (version_value, bytes) =>
          match decode_uint 2 bytes with
          | None => None
          | Some (packet_length_value, bytes) =>
              match decode_uint 8 bytes with
              | None => None
              | Some (sending_time_value, bytes) =>
                  match decode_uint 1 bytes with
                  | None => None
                  | Some (message_count_value, bytes) =>
                      match decode_uint 4 bytes with
                      | None => None
                      | Some (first_msg_seq_num_value, bytes) =>
                          Some ({| version := version_value; packet_length := packet_length_value; sending_time := sending_time_value; message_count := message_count_value; first_msg_seq_num := first_msg_seq_num_value |}, bytes)
                      end
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 16.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_uint_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 [bound_1 [bound_2 [bound_3 bound_4]]]].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_uint by exact bound_0.
      rewrite decode_encode_uint by exact bound_1.
      rewrite decode_encode_uint by exact bound_2.
      rewrite decode_encode_uint by exact bound_3.
      rewrite decode_encode_uint by exact bound_4.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec]. Defined.

  End PacketHeader.

  Module MessageHeader.

    Record t := {
      message_length : N;
      template_id : N;
      message_type : list byte;
      msg_seq_num : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (message_length record < 256 ^ N.of_nat 2)%N /\
      (template_id record < 256 ^ N.of_nat 1)%N /\
      Datatypes.length (message_type record) = 1 /\
      (msg_seq_num record < 256 ^ N.of_nat 4)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 2 (message_length record) ++
      encode_uint 1 (template_id record) ++
      encode_bytes 1 (message_type record) ++
      encode_uint 4 (msg_seq_num record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 2 bytes with
      | None => None
      | Some (message_length_value, bytes) =>
          match decode_uint 1 bytes with
          | None => None
          | Some (template_id_value, bytes) =>
              match decode_bytes 1 bytes with
              | None => None
              | Some (message_type_value, bytes) =>
                  match decode_uint 4 bytes with
                  | None => None
                  | Some (msg_seq_num_value, bytes) =>
                      Some ({| message_length := message_length_value; template_id := template_id_value; message_type := message_type_value; msg_seq_num := msg_seq_num_value |}, bytes)
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 8.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_uint_length, !encode_bytes_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 [bound_1 [bound_2 bound_3]]].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_uint by exact bound_0.
      rewrite decode_encode_uint by exact bound_1.
      rewrite decode_encode_bytes by exact bound_2.
      rewrite decode_encode_uint by exact bound_3.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End MessageHeader.

  Module StrikePrice.

    Record t := {
      strike_price_exponent : N;
      strike_price_mantissa : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (strike_price_exponent record < 256 ^ N.of_nat 1)%N /\
      (strike_price_mantissa record < 256 ^ N.of_nat 4)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 1 (strike_price_exponent record) ++
      encode_uint 4 (strike_price_mantissa record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 1 bytes with
      | None => None
      | Some (strike_price_exponent_value, bytes) =>
          match decode_uint 4 bytes with
          | None => None
          | Some (strike_price_mantissa_value, bytes) =>
              Some ({| strike_price_exponent := strike_price_exponent_value; strike_price_mantissa := strike_price_mantissa_value |}, bytes)
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 5.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_uint_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 bound_1].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_uint by exact bound_0.
      rewrite decode_encode_uint by exact bound_1.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec]. Defined.

  End StrikePrice.

  Module MinimumStrikePriceFraction.

    Record t := {
      minimum_strike_price_fraction_exponent : N;
      minimum_strike_price_fraction_mantissa : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (minimum_strike_price_fraction_exponent record < 256 ^ N.of_nat 1)%N /\
      (minimum_strike_price_fraction_mantissa record < 256 ^ N.of_nat 4)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 1 (minimum_strike_price_fraction_exponent record) ++
      encode_uint 4 (minimum_strike_price_fraction_mantissa record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 1 bytes with
      | None => None
      | Some (minimum_strike_price_fraction_exponent_value, bytes) =>
          match decode_uint 4 bytes with
          | None => None
          | Some (minimum_strike_price_fraction_mantissa_value, bytes) =>
              Some ({| minimum_strike_price_fraction_exponent := minimum_strike_price_fraction_exponent_value; minimum_strike_price_fraction_mantissa := minimum_strike_price_fraction_mantissa_value |}, bytes)
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 5.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_uint_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 bound_1].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_uint by exact bound_0.
      rewrite decode_encode_uint by exact bound_1.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec]. Defined.

  End MinimumStrikePriceFraction.

  Module MaxStrikePrice.

    Record t := {
      max_strike_price_exponent : N;
      max_strike_price_mantissa : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (max_strike_price_exponent record < 256 ^ N.of_nat 1)%N /\
      (max_strike_price_mantissa record < 256 ^ N.of_nat 4)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 1 (max_strike_price_exponent record) ++
      encode_uint 4 (max_strike_price_mantissa record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 1 bytes with
      | None => None
      | Some (max_strike_price_exponent_value, bytes) =>
          match decode_uint 4 bytes with
          | None => None
          | Some (max_strike_price_mantissa_value, bytes) =>
              Some ({| max_strike_price_exponent := max_strike_price_exponent_value; max_strike_price_mantissa := max_strike_price_mantissa_value |}, bytes)
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 5.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_uint_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 bound_1].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_uint by exact bound_0.
      rewrite decode_encode_uint by exact bound_1.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec]. Defined.

  End MaxStrikePrice.

  Module PremiumBreakPoint.

    Record t := {
      premium_break_point_exponent : N;
      premium_break_point_mantissa : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (premium_break_point_exponent record < 256 ^ N.of_nat 1)%N /\
      (premium_break_point_mantissa record < 256 ^ N.of_nat 4)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 1 (premium_break_point_exponent record) ++
      encode_uint 4 (premium_break_point_mantissa record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 1 bytes with
      | None => None
      | Some (premium_break_point_exponent_value, bytes) =>
          match decode_uint 4 bytes with
          | None => None
          | Some (premium_break_point_mantissa_value, bytes) =>
              Some ({| premium_break_point_exponent := premium_break_point_exponent_value; premium_break_point_mantissa := premium_break_point_mantissa_value |}, bytes)
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 5.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_uint_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 bound_1].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_uint by exact bound_0.
      rewrite decode_encode_uint by exact bound_1.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec]. Defined.

  End PremiumBreakPoint.

  Module MinimumAbovePremiumFraction.

    Record t := {
      minimum_above_premium_fraction_exponent : N;
      minimum_above_premium_fraction_mantissa : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (minimum_above_premium_fraction_exponent record < 256 ^ N.of_nat 1)%N /\
      (minimum_above_premium_fraction_mantissa record < 256 ^ N.of_nat 4)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 1 (minimum_above_premium_fraction_exponent record) ++
      encode_uint 4 (minimum_above_premium_fraction_mantissa record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 1 bytes with
      | None => None
      | Some (minimum_above_premium_fraction_exponent_value, bytes) =>
          match decode_uint 4 bytes with
          | None => None
          | Some (minimum_above_premium_fraction_mantissa_value, bytes) =>
              Some ({| minimum_above_premium_fraction_exponent := minimum_above_premium_fraction_exponent_value; minimum_above_premium_fraction_mantissa := minimum_above_premium_fraction_mantissa_value |}, bytes)
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 5.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_uint_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 bound_1].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_uint by exact bound_0.
      rewrite decode_encode_uint by exact bound_1.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec]. Defined.

  End MinimumAbovePremiumFraction.

  Module MinimumBelowPremiumFraction.

    Record t := {
      minimum_below_premium_fraction_exponent : N;
      minimum_below_premium_fraction_mantissa : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (minimum_below_premium_fraction_exponent record < 256 ^ N.of_nat 1)%N /\
      (minimum_below_premium_fraction_mantissa record < 256 ^ N.of_nat 4)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 1 (minimum_below_premium_fraction_exponent record) ++
      encode_uint 4 (minimum_below_premium_fraction_mantissa record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 1 bytes with
      | None => None
      | Some (minimum_below_premium_fraction_exponent_value, bytes) =>
          match decode_uint 4 bytes with
          | None => None
          | Some (minimum_below_premium_fraction_mantissa_value, bytes) =>
              Some ({| minimum_below_premium_fraction_exponent := minimum_below_premium_fraction_exponent_value; minimum_below_premium_fraction_mantissa := minimum_below_premium_fraction_mantissa_value |}, bytes)
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 5.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_uint_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 bound_1].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_uint by exact bound_0.
      rewrite decode_encode_uint by exact bound_1.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec]. Defined.

  End MinimumBelowPremiumFraction.

  Module MdEntryPx.

    Record t := {
      md_entry_px_exponent : N;
      md_entry_px_mantissa : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (md_entry_px_exponent record < 256 ^ N.of_nat 1)%N /\
      (md_entry_px_mantissa record < 256 ^ N.of_nat 4)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 1 (md_entry_px_exponent record) ++
      encode_uint 4 (md_entry_px_mantissa record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 1 bytes with
      | None => None
      | Some (md_entry_px_exponent_value, bytes) =>
          match decode_uint 4 bytes with
          | None => None
          | Some (md_entry_px_mantissa_value, bytes) =>
              Some ({| md_entry_px_exponent := md_entry_px_exponent_value; md_entry_px_mantissa := md_entry_px_mantissa_value |}, bytes)
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 5.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_uint_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 bound_1].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_uint by exact bound_0.
      rewrite decode_encode_uint by exact bound_1.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec]. Defined.

  End MdEntryPx.

  Module PrevClosePx.

    Record t := {
      prev_close_px_exponent : N;
      prev_close_px_mantissa : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (prev_close_px_exponent record < 256 ^ N.of_nat 1)%N /\
      (prev_close_px_mantissa record < 256 ^ N.of_nat 4)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 1 (prev_close_px_exponent record) ++
      encode_uint 4 (prev_close_px_mantissa record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 1 bytes with
      | None => None
      | Some (prev_close_px_exponent_value, bytes) =>
          match decode_uint 4 bytes with
          | None => None
          | Some (prev_close_px_mantissa_value, bytes) =>
              Some ({| prev_close_px_exponent := prev_close_px_exponent_value; prev_close_px_mantissa := prev_close_px_mantissa_value |}, bytes)
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 5.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_uint_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 bound_1].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_uint by exact bound_0.
      rewrite decode_encode_uint by exact bound_1.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec]. Defined.

  End PrevClosePx.

  Module MdEntryPx2.

    Record t := {
      md_entry_px_exponent : N;
      md_entry_px_mantissa : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (md_entry_px_exponent record < 256 ^ N.of_nat 1)%N /\
      (md_entry_px_mantissa record < 256 ^ N.of_nat 4)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 1 (md_entry_px_exponent record) ++
      encode_uint 4 (md_entry_px_mantissa record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 1 bytes with
      | None => None
      | Some (md_entry_px_exponent_value, bytes) =>
          match decode_uint 4 bytes with
          | None => None
          | Some (md_entry_px_mantissa_value, bytes) =>
              Some ({| md_entry_px_exponent := md_entry_px_exponent_value; md_entry_px_mantissa := md_entry_px_mantissa_value |}, bytes)
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 5.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_uint_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 bound_1].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_uint by exact bound_0.
      rewrite decode_encode_uint by exact bound_1.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec]. Defined.

  End MdEntryPx2.

  Module MdEntryPx3.

    Record t := {
      md_entry_px_exponent : N;
      md_entry_px_mantissa : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (md_entry_px_exponent record < 256 ^ N.of_nat 1)%N /\
      (md_entry_px_mantissa record < 256 ^ N.of_nat 4)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 1 (md_entry_px_exponent record) ++
      encode_uint 4 (md_entry_px_mantissa record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 1 bytes with
      | None => None
      | Some (md_entry_px_exponent_value, bytes) =>
          match decode_uint 4 bytes with
          | None => None
          | Some (md_entry_px_mantissa_value, bytes) =>
              Some ({| md_entry_px_exponent := md_entry_px_exponent_value; md_entry_px_mantissa := md_entry_px_mantissa_value |}, bytes)
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 5.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_uint_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 bound_1].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_uint by exact bound_0.
      rewrite decode_encode_uint by exact bound_1.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec]. Defined.

  End MdEntryPx3.

  Module PrevClosePx2.

    Record t := {
      prev_close_px_exponent : N;
      prev_close_px_mantissa : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (prev_close_px_exponent record < 256 ^ N.of_nat 1)%N /\
      (prev_close_px_mantissa record < 256 ^ N.of_nat 4)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 1 (prev_close_px_exponent record) ++
      encode_uint 4 (prev_close_px_mantissa record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 1 bytes with
      | None => None
      | Some (prev_close_px_exponent_value, bytes) =>
          match decode_uint 4 bytes with
          | None => None
          | Some (prev_close_px_mantissa_value, bytes) =>
              Some ({| prev_close_px_exponent := prev_close_px_exponent_value; prev_close_px_mantissa := prev_close_px_mantissa_value |}, bytes)
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 5.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_uint_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 bound_1].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_uint by exact bound_0.
      rewrite decode_encode_uint by exact bound_1.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec]. Defined.

  End PrevClosePx2.

  Module MdEntryPx4.

    Record t := {
      md_entry_px_exponent : N;
      md_entry_px_mantissa : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (md_entry_px_exponent record < 256 ^ N.of_nat 1)%N /\
      (md_entry_px_mantissa record < 256 ^ N.of_nat 4)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 1 (md_entry_px_exponent record) ++
      encode_uint 4 (md_entry_px_mantissa record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 1 bytes with
      | None => None
      | Some (md_entry_px_exponent_value, bytes) =>
          match decode_uint 4 bytes with
          | None => None
          | Some (md_entry_px_mantissa_value, bytes) =>
              Some ({| md_entry_px_exponent := md_entry_px_exponent_value; md_entry_px_mantissa := md_entry_px_mantissa_value |}, bytes)
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 5.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_uint_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 bound_1].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_uint by exact bound_0.
      rewrite decode_encode_uint by exact bound_1.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec]. Defined.

  End MdEntryPx4.

  Module MdEntryPx5.

    Record t := {
      md_entry_px_exponent : N;
      md_entry_px_mantissa : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (md_entry_px_exponent record < 256 ^ N.of_nat 1)%N /\
      (md_entry_px_mantissa record < 256 ^ N.of_nat 4)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 1 (md_entry_px_exponent record) ++
      encode_uint 4 (md_entry_px_mantissa record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 1 bytes with
      | None => None
      | Some (md_entry_px_exponent_value, bytes) =>
          match decode_uint 4 bytes with
          | None => None
          | Some (md_entry_px_mantissa_value, bytes) =>
              Some ({| md_entry_px_exponent := md_entry_px_exponent_value; md_entry_px_mantissa := md_entry_px_mantissa_value |}, bytes)
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 5.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_uint_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 bound_1].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_uint by exact bound_0.
      rewrite decode_encode_uint by exact bound_1.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec]. Defined.

  End MdEntryPx5.

  Module Eop.

    Record t := {
      eop_exponent : N;
      eop_mantissa : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (eop_exponent record < 256 ^ N.of_nat 1)%N /\
      (eop_mantissa record < 256 ^ N.of_nat 4)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 1 (eop_exponent record) ++
      encode_uint 4 (eop_mantissa record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 1 bytes with
      | None => None
      | Some (eop_exponent_value, bytes) =>
          match decode_uint 4 bytes with
          | None => None
          | Some (eop_mantissa_value, bytes) =>
              Some ({| eop_exponent := eop_exponent_value; eop_mantissa := eop_mantissa_value |}, bytes)
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 5.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_uint_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 bound_1].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_uint by exact bound_0.
      rewrite decode_encode_uint by exact bound_1.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec]. Defined.

  End Eop.

  Module ExpectedOpeningPriceAndSizeMessage.

    (** The EOP message contains expected opening price and size information for a security. *)
    Record t := {
      class_key : N;
      security_id : N;
      eop : Eop.t;
      eos : N;
      eop_type : N;
      legal_market : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (class_key record < 256 ^ N.of_nat 4)%N /\
      (security_id record < 256 ^ N.of_nat 4)%N /\
      Eop.bounded (eop record) /\
      (eos record < 256 ^ N.of_nat 4)%N /\
      (eop_type record < 256 ^ N.of_nat 1)%N /\
      (legal_market record < 256 ^ N.of_nat 1)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 4 (class_key record) ++
      encode_uint 4 (security_id record) ++
      Eop.encode (eop record) ++
      encode_uint 4 (eos record) ++
      encode_uint 1 (eop_type record) ++
      encode_uint 1 (legal_market record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 4 bytes with
      | None => None
      | Some (class_key_value, bytes) =>
          match decode_uint 4 bytes with
          | None => None
          | Some (security_id_value, bytes) =>
              match Eop.decode bytes with
              | None => None
              | Some (eop_value, bytes) =>
                  match decode_uint 4 bytes with
                  | None => None
                  | Some (eos_value, bytes) =>
                      match decode_uint 1 bytes with
                      | None => None
                      | Some (eop_type_value, bytes) =>
                          match decode_uint 1 bytes with
                          | None => None
                          | Some (legal_market_value, bytes) =>
                              Some ({| class_key := class_key_value; security_id := security_id_value; eop := eop_value; eos := eos_value; eop_type := eop_type_value; legal_market := legal_market_value |}, bytes)
                          end
                      end
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 19.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_uint_length, !Eop.encode_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 [bound_1 [bound_2 [bound_3 [bound_4 bound_5]]]]].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_uint by exact bound_0.
      rewrite decode_encode_uint by exact bound_1.
      rewrite Eop.decode_encode by exact bound_2.
      rewrite decode_encode_uint by exact bound_3.
      rewrite decode_encode_uint by exact bound_4.
      rewrite decode_encode_uint by exact bound_5.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply Eop.eq_dec]. Defined.

  End ExpectedOpeningPriceAndSizeMessage.

  Module MdEntryPx6.

    Record t := {
      md_entry_px_exponent : N;
      md_entry_px_mantissa : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (md_entry_px_exponent record < 256 ^ N.of_nat 1)%N /\
      (md_entry_px_mantissa record < 256 ^ N.of_nat 4)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 1 (md_entry_px_exponent record) ++
      encode_uint 4 (md_entry_px_mantissa record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 1 bytes with
      | None => None
      | Some (md_entry_px_exponent_value, bytes) =>
          match decode_uint 4 bytes with
          | None => None
          | Some (md_entry_px_mantissa_value, bytes) =>
              Some ({| md_entry_px_exponent := md_entry_px_exponent_value; md_entry_px_mantissa := md_entry_px_mantissa_value |}, bytes)
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 5.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_uint_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 bound_1].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_uint by exact bound_0.
      rewrite decode_encode_uint by exact bound_1.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec]. Defined.

  End MdEntryPx6.

  Module MdEntryPx7.

    Record t := {
      md_entry_px_exponent : N;
      md_entry_px_mantissa : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (md_entry_px_exponent record < 256 ^ N.of_nat 1)%N /\
      (md_entry_px_mantissa record < 256 ^ N.of_nat 4)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 1 (md_entry_px_exponent record) ++
      encode_uint 4 (md_entry_px_mantissa record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 1 bytes with
      | None => None
      | Some (md_entry_px_exponent_value, bytes) =>
          match decode_uint 4 bytes with
          | None => None
          | Some (md_entry_px_mantissa_value, bytes) =>
              Some ({| md_entry_px_exponent := md_entry_px_exponent_value; md_entry_px_mantissa := md_entry_px_mantissa_value |}, bytes)
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 5.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_uint_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 bound_1].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_uint by exact bound_0.
      rewrite decode_encode_uint by exact bound_1.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec]. Defined.

  End MdEntryPx7.

  Module NetChgPrevDay.

    Record t := {
      net_chg_prev_day_exponent : N;
      net_chg_prev_day_mantissa : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (net_chg_prev_day_exponent record < 256 ^ N.of_nat 1)%N /\
      (net_chg_prev_day_mantissa record < 256 ^ N.of_nat 4)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 1 (net_chg_prev_day_exponent record) ++
      encode_uint 4 (net_chg_prev_day_mantissa record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 1 bytes with
      | None => None
      | Some (net_chg_prev_day_exponent_value, bytes) =>
          match decode_uint 4 bytes with
          | None => None
          | Some (net_chg_prev_day_mantissa_value, bytes) =>
              Some ({| net_chg_prev_day_exponent := net_chg_prev_day_exponent_value; net_chg_prev_day_mantissa := net_chg_prev_day_mantissa_value |}, bytes)
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 5.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_uint_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 bound_1].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_uint by exact bound_0.
      rewrite decode_encode_uint by exact bound_1.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec]. Defined.

  End NetChgPrevDay.

  Module UnderlyingPx.

    Record t := {
      underlying_px_exponent : N;
      underlying_px_mantissa : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (underlying_px_exponent record < 256 ^ N.of_nat 1)%N /\
      (underlying_px_mantissa record < 256 ^ N.of_nat 4)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 1 (underlying_px_exponent record) ++
      encode_uint 4 (underlying_px_mantissa record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 1 bytes with
      | None => None
      | Some (underlying_px_exponent_value, bytes) =>
          match decode_uint 4 bytes with
          | None => None
          | Some (underlying_px_mantissa_value, bytes) =>
              Some ({| underlying_px_exponent := underlying_px_exponent_value; underlying_px_mantissa := underlying_px_mantissa_value |}, bytes)
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 5.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_uint_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 bound_1].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_uint by exact bound_0.
      rewrite decode_encode_uint by exact bound_1.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec]. Defined.

  End UnderlyingPx.

  Module MdEntryPx8.

    Record t := {
      md_entry_px_exponent : N;
      md_entry_px_mantissa : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (md_entry_px_exponent record < 256 ^ N.of_nat 1)%N /\
      (md_entry_px_mantissa record < 256 ^ N.of_nat 4)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 1 (md_entry_px_exponent record) ++
      encode_uint 4 (md_entry_px_mantissa record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 1 bytes with
      | None => None
      | Some (md_entry_px_exponent_value, bytes) =>
          match decode_uint 4 bytes with
          | None => None
          | Some (md_entry_px_mantissa_value, bytes) =>
              Some ({| md_entry_px_exponent := md_entry_px_exponent_value; md_entry_px_mantissa := md_entry_px_mantissa_value |}, bytes)
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 5.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_uint_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 bound_1].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_uint by exact bound_0.
      rewrite decode_encode_uint by exact bound_1.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec]. Defined.

  End MdEntryPx8.

  Module MarketDataControlMessage.

    (** Market Data Control messages mark the start and end of the end of session Summary and the end of session Settlement data transmissions. *)
    Record t := {
      md_control_type : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (md_control_type record < 256 ^ N.of_nat 1)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 1 (md_control_type record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 1 bytes with
      | None => None
      | Some (md_control_type_value, bytes) =>
          Some ({| md_control_type := md_control_type_value |}, bytes)
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 1.
    Proof.
      intros record. unfold encode.
      rewrite !encode_uint_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      unfold decode, encode.
      rewrite decode_encode_uint by exact bound.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec]. Defined.

  End MarketDataControlMessage.

End C1OptionsMarketDataFeedV142.
