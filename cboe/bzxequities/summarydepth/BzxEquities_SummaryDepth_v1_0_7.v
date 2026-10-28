From Stdlib Require Import List.
From Stdlib Require Import NArith.
From Stdlib Require Import Lia.
From Stdlib Require Import Strings.Byte.
From Omi Require Import Wire.

Import ListNotations.

(** * Chicago Board Options Exchange Summary Depth

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
      - the dispatch that chooses a message by its type
      - a run filling what frames it
      - a field read in bits
      - a run counted by a field
  *)

Module BzxEquitiesSummaryDepthV107.

  Module PacketHeader.

    Record t := {
      length_ : N;
      message_count : N;
      unit_ : N;
      sequence : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (length_ record < 256 ^ N.of_nat 2)%N /\
      (message_count record < 256 ^ N.of_nat 1)%N /\
      (unit_ record < 256 ^ N.of_nat 1)%N /\
      (sequence record < 256 ^ N.of_nat 4)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 2 (length_ record) ++
      encode_uint 1 (message_count record) ++
      encode_uint 1 (unit_ record) ++
      encode_uint 4 (sequence record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 2 bytes with
      | None => None
      | Some (length__value, bytes) =>
          match decode_uint 1 bytes with
          | None => None
          | Some (message_count_value, bytes) =>
              match decode_uint 1 bytes with
              | None => None
              | Some (unit__value, bytes) =>
                  match decode_uint 4 bytes with
                  | None => None
                  | Some (sequence_value, bytes) =>
                      Some ({| length_ := length__value; message_count := message_count_value; unit_ := unit__value; sequence := sequence_value |}, bytes)
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 8.
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

  End PacketHeader.

  Module MessageHeader.

    Record t := {
      message_length : N;
      message_type : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (message_length record < 256 ^ N.of_nat 1)%N /\
      (message_type record < 256 ^ N.of_nat 1)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 1 (message_length record) ++
      encode_uint 1 (message_type record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 1 bytes with
      | None => None
      | Some (message_length_value, bytes) =>
          match decode_uint 1 bytes with
          | None => None
          | Some (message_type_value, bytes) =>
              Some ({| message_length := message_length_value; message_type := message_type_value |}, bytes)
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 2.
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

  End MessageHeader.

  Module ClearQuoteMessage.

    (** The Clear Quote message instructs feed recipients to clear all quotes and ADAP information for the specified symbol. This message does not affect the executed volume of the symbol. *)
    Record t := {
      last_update_timestamp : N;
      symbol : list byte;
      reserved_1 : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (last_update_timestamp record < 256 ^ N.of_nat 8)%N /\
      Datatypes.length (symbol record) = 8 /\
      Datatypes.length (reserved_1 record) = 1.

    Definition encode (record : t) : list byte :=
      encode_uint 8 (last_update_timestamp record) ++
      encode_bytes 8 (symbol record) ++
      encode_bytes 1 (reserved_1 record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 8 bytes with
      | None => None
      | Some (last_update_timestamp_value, bytes) =>
          match decode_bytes 8 bytes with
          | None => None
          | Some (symbol_value, bytes) =>
              match decode_bytes 1 bytes with
              | None => None
              | Some (reserved_1_value, bytes) =>
                  Some ({| last_update_timestamp := last_update_timestamp_value; symbol := symbol_value; reserved_1 := reserved_1_value |}, bytes)
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 17.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_uint_length, !encode_bytes_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 [bound_1 bound_2]].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_uint by exact bound_0.
      rewrite decode_encode_bytes by exact bound_1.
      rewrite decode_encode_bytes by exact bound_2.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End ClearQuoteMessage.

  Module CboeMarketStatusMessage.

    (** The Cboe Market Status message is disseminated to reflect a change in the status of the market. *)
    Record t := {
      timestamp : N;
      reserved_1 : list byte;
      market_status : list byte;
      session_indicator : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (timestamp record < 256 ^ N.of_nat 8)%N /\
      Datatypes.length (reserved_1 record) = 1 /\
      Datatypes.length (market_status record) = 1 /\
      Datatypes.length (session_indicator record) = 1.

    Definition encode (record : t) : list byte :=
      encode_uint 8 (timestamp record) ++
      encode_bytes 1 (reserved_1 record) ++
      encode_bytes 1 (market_status record) ++
      encode_bytes 1 (session_indicator record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 8 bytes with
      | None => None
      | Some (timestamp_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (reserved_1_value, bytes) =>
              match decode_bytes 1 bytes with
              | None => None
              | Some (market_status_value, bytes) =>
                  match decode_bytes 1 bytes with
                  | None => None
                  | Some (session_indicator_value, bytes) =>
                      Some ({| timestamp := timestamp_value; reserved_1 := reserved_1_value; market_status := market_status_value; session_indicator := session_indicator_value |}, bytes)
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 11.
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
      rewrite decode_encode_bytes by exact bound_1.
      rewrite decode_encode_bytes by exact bound_2.
      rewrite decode_encode_bytes by exact bound_3.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End CboeMarketStatusMessage.

  Module ShortUpdateAdapBlock.

    (** Short Update ADAP Block *)
    Record t := {
      reserved_1 : list byte;
      side : list byte;
      price_short : N;
      quantity_short : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (reserved_1 record) = 1 /\
      Datatypes.length (side record) = 1 /\
      (price_short record < 256 ^ N.of_nat 4)%N /\
      (quantity_short record < 256 ^ N.of_nat 4)%N.

    Definition encode (record : t) : list byte :=
      encode_bytes 1 (reserved_1 record) ++
      encode_bytes 1 (side record) ++
      encode_uint 4 (price_short record) ++
      encode_uint 4 (quantity_short record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 1 bytes with
      | None => None
      | Some (reserved_1_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (side_value, bytes) =>
              match decode_uint 4 bytes with
              | None => None
              | Some (price_short_value, bytes) =>
                  match decode_uint 4 bytes with
                  | None => None
                  | Some (quantity_short_value, bytes) =>
                      Some ({| reserved_1 := reserved_1_value; side := side_value; price_short := price_short_value; quantity_short := quantity_short_value |}, bytes)
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 10.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_bytes_length, !encode_uint_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 [bound_1 [bound_2 bound_3]]].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_bytes by exact bound_0.
      rewrite decode_encode_bytes by exact bound_1.
      rewrite decode_encode_uint by exact bound_2.
      rewrite decode_encode_uint by exact bound_3.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End ShortUpdateAdapBlock.

  Module LongUpdateAdapBlock.

    (** Long Update ADAP Block *)
    Record t := {
      reserved_1 : list byte;
      side : list byte;
      price_long : N;
      quantity_long : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (reserved_1 record) = 1 /\
      Datatypes.length (side record) = 1 /\
      (price_long record < 256 ^ N.of_nat 8)%N /\
      (quantity_long record < 256 ^ N.of_nat 8)%N.

    Definition encode (record : t) : list byte :=
      encode_bytes 1 (reserved_1 record) ++
      encode_bytes 1 (side record) ++
      encode_uint 8 (price_long record) ++
      encode_uint 8 (quantity_long record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 1 bytes with
      | None => None
      | Some (reserved_1_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (side_value, bytes) =>
              match decode_uint 8 bytes with
              | None => None
              | Some (price_long_value, bytes) =>
                  match decode_uint 8 bytes with
                  | None => None
                  | Some (quantity_long_value, bytes) =>
                      Some ({| reserved_1 := reserved_1_value; side := side_value; price_long := price_long_value; quantity_long := quantity_long_value |}, bytes)
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 18.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_bytes_length, !encode_uint_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 [bound_1 [bound_2 bound_3]]].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_bytes by exact bound_0.
      rewrite decode_encode_bytes by exact bound_1.
      rewrite decode_encode_uint by exact bound_2.
      rewrite decode_encode_uint by exact bound_3.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End LongUpdateAdapBlock.

  Module RpiMessage.

    (** The Retail Price Improvement (RPI) message is a retail liquidity indicator that includes symbol and side, but not price and size. *)
    Record t := {
      timestamp : N;
      symbol : list byte;
      reserved_1 : list byte;
      retail_price_improvement : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (timestamp record < 256 ^ N.of_nat 8)%N /\
      Datatypes.length (symbol record) = 8 /\
      Datatypes.length (reserved_1 record) = 1 /\
      Datatypes.length (retail_price_improvement record) = 1.

    Definition encode (record : t) : list byte :=
      encode_uint 8 (timestamp record) ++
      encode_bytes 8 (symbol record) ++
      encode_bytes 1 (reserved_1 record) ++
      encode_bytes 1 (retail_price_improvement record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 8 bytes with
      | None => None
      | Some (timestamp_value, bytes) =>
          match decode_bytes 8 bytes with
          | None => None
          | Some (symbol_value, bytes) =>
              match decode_bytes 1 bytes with
              | None => None
              | Some (reserved_1_value, bytes) =>
                  match decode_bytes 1 bytes with
                  | None => None
                  | Some (retail_price_improvement_value, bytes) =>
                      Some ({| timestamp := timestamp_value; symbol := symbol_value; reserved_1 := reserved_1_value; retail_price_improvement := retail_price_improvement_value |}, bytes)
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 18.
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
      rewrite decode_encode_bytes by exact bound_1.
      rewrite decode_encode_bytes by exact bound_2.
      rewrite decode_encode_bytes by exact bound_3.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End RpiMessage.

  Module TradingStatusMessage.

    (** The Trading Status message is used to indicate the current trading status of a security on the Cboe exchange. *)
    Record t := {
      timestamp : N;
      symbol : list byte;
      reserved_1 : list byte;
      halt_status : list byte;
      reg_sho_action : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (timestamp record < 256 ^ N.of_nat 8)%N /\
      Datatypes.length (symbol record) = 8 /\
      Datatypes.length (reserved_1 record) = 1 /\
      Datatypes.length (halt_status record) = 1 /\
      Datatypes.length (reg_sho_action record) = 1.

    Definition encode (record : t) : list byte :=
      encode_uint 8 (timestamp record) ++
      encode_bytes 8 (symbol record) ++
      encode_bytes 1 (reserved_1 record) ++
      encode_bytes 1 (halt_status record) ++
      encode_bytes 1 (reg_sho_action record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 8 bytes with
      | None => None
      | Some (timestamp_value, bytes) =>
          match decode_bytes 8 bytes with
          | None => None
          | Some (symbol_value, bytes) =>
              match decode_bytes 1 bytes with
              | None => None
              | Some (reserved_1_value, bytes) =>
                  match decode_bytes 1 bytes with
                  | None => None
                  | Some (halt_status_value, bytes) =>
                      match decode_bytes 1 bytes with
                      | None => None
                      | Some (reg_sho_action_value, bytes) =>
                          Some ({| timestamp := timestamp_value; symbol := symbol_value; reserved_1 := reserved_1_value; halt_status := halt_status_value; reg_sho_action := reg_sho_action_value |}, bytes)
                      end
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 19.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_uint_length, !encode_bytes_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 [bound_1 [bound_2 [bound_3 bound_4]]]].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_uint by exact bound_0.
      rewrite decode_encode_bytes by exact bound_1.
      rewrite decode_encode_bytes by exact bound_2.
      rewrite decode_encode_bytes by exact bound_3.
      rewrite decode_encode_bytes by exact bound_4.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End TradingStatusMessage.

End BzxEquitiesSummaryDepthV107.
