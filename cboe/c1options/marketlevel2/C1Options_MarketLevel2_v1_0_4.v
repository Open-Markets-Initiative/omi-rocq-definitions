From Stdlib Require Import List.
From Stdlib Require Import NArith.
From Stdlib Require Import Lia.
From Stdlib Require Import Strings.Byte.
From Omi Require Import Wire.

Import ListNotations.

(** * Chicago Board Options Exchange Market Level 2 Feed

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

Module C1OptionsMarketLevel2V104.

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

  Module SecurityStatusMessage.

    (** Security Status messages contain the SecurityTradingStatus for a product *)
    Record t := {
      class_key : N;
      security_id : N;
      rpt_seq : N;
      security_trading_status : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (class_key record < 256 ^ N.of_nat 4)%N /\
      (security_id record < 256 ^ N.of_nat 4)%N /\
      (rpt_seq record < 256 ^ N.of_nat 4)%N /\
      (security_trading_status record < 256 ^ N.of_nat 1)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 4 (class_key record) ++
      encode_uint 4 (security_id record) ++
      encode_uint 4 (rpt_seq record) ++
      encode_uint 1 (security_trading_status record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 4 bytes with
      | None => None
      | Some (class_key_value, bytes) =>
          match decode_uint 4 bytes with
          | None => None
          | Some (security_id_value, bytes) =>
              match decode_uint 4 bytes with
              | None => None
              | Some (rpt_seq_value, bytes) =>
                  match decode_uint 1 bytes with
                  | None => None
                  | Some (security_trading_status_value, bytes) =>
                      Some ({| class_key := class_key_value; security_id := security_id_value; rpt_seq := rpt_seq_value; security_trading_status := security_trading_status_value |}, bytes)
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 13.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_uint_length. reflexivity.
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
      rewrite decode_encode_uint by exact bound_2.
      rewrite decode_encode_uint by exact bound_3.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec]. Defined.

  End SecurityStatusMessage.

End C1OptionsMarketLevel2V104.
