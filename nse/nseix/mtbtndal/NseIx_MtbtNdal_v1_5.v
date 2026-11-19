From Stdlib Require Import List.
From Stdlib Require Import NArith.
From Stdlib Require Import Lia.
From Stdlib Require Import Strings.Byte.
From Omi Require Import Wire.

Import ListNotations.

(** * National Stock Exchange of India Ltd Multicast Tick By Tick Data Feed

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
      - a length prefix framing what follows
      - a Composite rule

    License: MIT No Attribution
  *)

Module NseIxMtbtNdalV15.

  Module StreamHeader.

    (** STREAM_HEADER *)
    Record t := {
      message_length : N;
      stream_id : N;
      sequence_number : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (message_length record < 256 ^ N.of_nat 2)%N /\
      (stream_id record < 256 ^ N.of_nat 2)%N /\
      (sequence_number record < 256 ^ N.of_nat 4)%N.

    Definition encode (record : t) : list byte :=
      encode_uint_le 2 (message_length record) ++
      encode_uint_le 2 (stream_id record) ++
      encode_uint_le 4 (sequence_number record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint_le 2 bytes with
      | None => None
      | Some (message_length_value, bytes) =>
          match decode_uint_le 2 bytes with
          | None => None
          | Some (stream_id_value, bytes) =>
              match decode_uint_le 4 bytes with
              | None => None
              | Some (sequence_number_value, bytes) =>
                  Some ({| message_length := message_length_value; stream_id := stream_id_value; sequence_number := sequence_number_value |}, bytes)
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 8.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_uint_le_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 [bound_1 bound_2]].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_uint_le by exact bound_0.
      rewrite decode_encode_uint_le by exact bound_1.
      rewrite decode_encode_uint_le by exact bound_2.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec]. Defined.

  End StreamHeader.

  Module ContractInformationMessage.

    (** Beginning of day contract master information, sent before the market opens on Stream Id no. 99, for contracts valid in the NSE IX market. *)
    Record t := {
      timestamp : N;
      contract_stream_id : N;
      token_number : N;
      instrument : list byte;
      symbol : list byte;
      expiry_date : N;
      strike_price : N;
      option_type : list byte;
      low_price_range : N;
      high_price_range : N;
      daily_contract_indicator : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (timestamp record < 256 ^ N.of_nat 8)%N /\
      (contract_stream_id record < 256 ^ N.of_nat 2)%N /\
      (token_number record < 256 ^ N.of_nat 4)%N /\
      Datatypes.length (instrument record) = 6 /\
      Datatypes.length (symbol record) = 10 /\
      (expiry_date record < 256 ^ N.of_nat 4)%N /\
      (strike_price record < 256 ^ N.of_nat 4)%N /\
      Datatypes.length (option_type record) = 2 /\
      (low_price_range record < 256 ^ N.of_nat 4)%N /\
      (high_price_range record < 256 ^ N.of_nat 4)%N /\
      Datatypes.length (daily_contract_indicator record) = 1.

    Definition encode (record : t) : list byte :=
      encode_uint_le 8 (timestamp record) ++
      encode_uint_le 2 (contract_stream_id record) ++
      encode_uint_le 4 (token_number record) ++
      encode_bytes 6 (instrument record) ++
      encode_bytes 10 (symbol record) ++
      encode_uint_le 4 (expiry_date record) ++
      encode_uint_le 4 (strike_price record) ++
      encode_bytes 2 (option_type record) ++
      encode_uint_le 4 (low_price_range record) ++
      encode_uint_le 4 (high_price_range record) ++
      encode_bytes 1 (daily_contract_indicator record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint_le 8 bytes with
      | None => None
      | Some (timestamp_value, bytes) =>
          match decode_uint_le 2 bytes with
          | None => None
          | Some (contract_stream_id_value, bytes) =>
              match decode_uint_le 4 bytes with
              | None => None
              | Some (token_number_value, bytes) =>
                  match decode_bytes 6 bytes with
                  | None => None
                  | Some (instrument_value, bytes) =>
                      match decode_bytes 10 bytes with
                      | None => None
                      | Some (symbol_value, bytes) =>
                          match decode_uint_le 4 bytes with
                          | None => None
                          | Some (expiry_date_value, bytes) =>
                              match decode_uint_le 4 bytes with
                              | None => None
                              | Some (strike_price_value, bytes) =>
                                  match decode_bytes 2 bytes with
                                  | None => None
                                  | Some (option_type_value, bytes) =>
                                      match decode_uint_le 4 bytes with
                                      | None => None
                                      | Some (low_price_range_value, bytes) =>
                                          match decode_uint_le 4 bytes with
                                          | None => None
                                          | Some (high_price_range_value, bytes) =>
                                              match decode_bytes 1 bytes with
                                              | None => None
                                              | Some (daily_contract_indicator_value, bytes) =>
                                                  Some ({| timestamp := timestamp_value; contract_stream_id := contract_stream_id_value; token_number := token_number_value; instrument := instrument_value; symbol := symbol_value; expiry_date := expiry_date_value; strike_price := strike_price_value; option_type := option_type_value; low_price_range := low_price_range_value; high_price_range := high_price_range_value; daily_contract_indicator := daily_contract_indicator_value |}, bytes)
                                              end
                                          end
                                      end
                                  end
                              end
                          end
                      end
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 49.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_uint_le_length, !encode_bytes_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 [bound_1 [bound_2 [bound_3 [bound_4 [bound_5 [bound_6 [bound_7 [bound_8 [bound_9 bound_10]]]]]]]]]].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_uint_le by exact bound_0.
      rewrite decode_encode_uint_le by exact bound_1.
      rewrite decode_encode_uint_le by exact bound_2.
      rewrite decode_encode_bytes by exact bound_3.
      rewrite decode_encode_bytes by exact bound_4.
      rewrite decode_encode_uint_le by exact bound_5.
      rewrite decode_encode_uint_le by exact bound_6.
      rewrite decode_encode_bytes by exact bound_7.
      rewrite decode_encode_uint_le by exact bound_8.
      rewrite decode_encode_uint_le by exact bound_9.
      rewrite decode_encode_bytes by exact bound_10.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End ContractInformationMessage.

  Module SpreadContractInformationMessage.

    (** Information about the spread contracts valid in the NSE IX market, sent on Stream Id no. 99. *)
    Record t := {
      timestamp : N;
      contract_stream_id : N;
      token_1 : N;
      token_2 : N;
      day_low_price_diff_range : N;
      day_high_price_diff_range : N;
      operating_range_low_price_diff_range : N;
      operating_range_high_price_diff_range : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (timestamp record < 256 ^ N.of_nat 8)%N /\
      (contract_stream_id record < 256 ^ N.of_nat 2)%N /\
      (token_1 record < 256 ^ N.of_nat 4)%N /\
      (token_2 record < 256 ^ N.of_nat 4)%N /\
      (day_low_price_diff_range record < 256 ^ N.of_nat 4)%N /\
      (day_high_price_diff_range record < 256 ^ N.of_nat 4)%N /\
      (operating_range_low_price_diff_range record < 256 ^ N.of_nat 4)%N /\
      (operating_range_high_price_diff_range record < 256 ^ N.of_nat 4)%N.

    Definition encode (record : t) : list byte :=
      encode_uint_le 8 (timestamp record) ++
      encode_uint_le 2 (contract_stream_id record) ++
      encode_uint_le 4 (token_1 record) ++
      encode_uint_le 4 (token_2 record) ++
      encode_uint_le 4 (day_low_price_diff_range record) ++
      encode_uint_le 4 (day_high_price_diff_range record) ++
      encode_uint_le 4 (operating_range_low_price_diff_range record) ++
      encode_uint_le 4 (operating_range_high_price_diff_range record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint_le 8 bytes with
      | None => None
      | Some (timestamp_value, bytes) =>
          match decode_uint_le 2 bytes with
          | None => None
          | Some (contract_stream_id_value, bytes) =>
              match decode_uint_le 4 bytes with
              | None => None
              | Some (token_1_value, bytes) =>
                  match decode_uint_le 4 bytes with
                  | None => None
                  | Some (token_2_value, bytes) =>
                      match decode_uint_le 4 bytes with
                      | None => None
                      | Some (day_low_price_diff_range_value, bytes) =>
                          match decode_uint_le 4 bytes with
                          | None => None
                          | Some (day_high_price_diff_range_value, bytes) =>
                              match decode_uint_le 4 bytes with
                              | None => None
                              | Some (operating_range_low_price_diff_range_value, bytes) =>
                                  match decode_uint_le 4 bytes with
                                  | None => None
                                  | Some (operating_range_high_price_diff_range_value, bytes) =>
                                      Some ({| timestamp := timestamp_value; contract_stream_id := contract_stream_id_value; token_1 := token_1_value; token_2 := token_2_value; day_low_price_diff_range := day_low_price_diff_range_value; day_high_price_diff_range := day_high_price_diff_range_value; operating_range_low_price_diff_range := operating_range_low_price_diff_range_value; operating_range_high_price_diff_range := operating_range_high_price_diff_range_value |}, bytes)
                                  end
                              end
                          end
                      end
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 34.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_uint_le_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 [bound_1 [bound_2 [bound_3 [bound_4 [bound_5 [bound_6 bound_7]]]]]]].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_uint_le by exact bound_0.
      rewrite decode_encode_uint_le by exact bound_1.
      rewrite decode_encode_uint_le by exact bound_2.
      rewrite decode_encode_uint_le by exact bound_3.
      rewrite decode_encode_uint_le by exact bound_4.
      rewrite decode_encode_uint_le by exact bound_5.
      rewrite decode_encode_uint_le by exact bound_6.
      rewrite decode_encode_uint_le by exact bound_7.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec]. Defined.

  End SpreadContractInformationMessage.

  Module MarketStatusMessage.

    (** Sent whenever the status of the market is changed to pre-open, pre-open end, open, closed, pre-close or pre-close end, for both T and T+1 sessions. *)
    Record t := {
      timestamp : N;
      instrument : list byte;
      status : N;
      session_indicator : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (timestamp record < 256 ^ N.of_nat 8)%N /\
      Datatypes.length (instrument record) = 6 /\
      (status record < 256 ^ N.of_nat 2)%N /\
      (session_indicator record < 256 ^ N.of_nat 2)%N.

    Definition encode (record : t) : list byte :=
      encode_uint_le 8 (timestamp record) ++
      encode_bytes 6 (instrument record) ++
      encode_uint_le 2 (status record) ++
      encode_uint_le 2 (session_indicator record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint_le 8 bytes with
      | None => None
      | Some (timestamp_value, bytes) =>
          match decode_bytes 6 bytes with
          | None => None
          | Some (instrument_value, bytes) =>
              match decode_uint_le 2 bytes with
              | None => None
              | Some (status_value, bytes) =>
                  match decode_uint_le 2 bytes with
                  | None => None
                  | Some (session_indicator_value, bytes) =>
                      Some ({| timestamp := timestamp_value; instrument := instrument_value; status := status_value; session_indicator := session_indicator_value |}, bytes)
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 18.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_uint_le_length, !encode_bytes_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 [bound_1 [bound_2 bound_3]]].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_uint_le by exact bound_0.
      rewrite decode_encode_bytes by exact bound_1.
      rewrite decode_encode_uint_le by exact bound_2.
      rewrite decode_encode_uint_le by exact bound_3.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End MarketStatusMessage.

  Module IndicativePriceAndQuantityMessage.

    (** Indicative equilibrium price and quantity, sent for contracts with pre-open and pre-close sessions, only between the pre-open or pre-close and the pre-open end or pre-close end statuses, when the indicative price and quantity are determined or updated during order collection. *)
    Record t := {
      timestamp : N;
      token : N;
      identifier : list byte;
      indicative_price : N;
      indicative_quantity : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (timestamp record < 256 ^ N.of_nat 8)%N /\
      (token record < 256 ^ N.of_nat 4)%N /\
      Datatypes.length (identifier record) = 1 /\
      (indicative_price record < 256 ^ N.of_nat 4)%N /\
      (indicative_quantity record < 256 ^ N.of_nat 4)%N.

    Definition encode (record : t) : list byte :=
      encode_uint_le 8 (timestamp record) ++
      encode_uint_le 4 (token record) ++
      encode_bytes 1 (identifier record) ++
      encode_uint_le 4 (indicative_price record) ++
      encode_uint_le 4 (indicative_quantity record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint_le 8 bytes with
      | None => None
      | Some (timestamp_value, bytes) =>
          match decode_uint_le 4 bytes with
          | None => None
          | Some (token_value, bytes) =>
              match decode_bytes 1 bytes with
              | None => None
              | Some (identifier_value, bytes) =>
                  match decode_uint_le 4 bytes with
                  | None => None
                  | Some (indicative_price_value, bytes) =>
                      match decode_uint_le 4 bytes with
                      | None => None
                      | Some (indicative_quantity_value, bytes) =>
                          Some ({| timestamp := timestamp_value; token := token_value; identifier := identifier_value; indicative_price := indicative_price_value; indicative_quantity := indicative_quantity_value |}, bytes)
                      end
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 21.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_uint_le_length, !encode_bytes_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 [bound_1 [bound_2 [bound_3 bound_4]]]].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_uint_le by exact bound_0.
      rewrite decode_encode_uint_le by exact bound_1.
      rewrite decode_encode_bytes by exact bound_2.
      rewrite decode_encode_uint_le by exact bound_3.
      rewrite decode_encode_uint_le by exact bound_4.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End IndicativePriceAndQuantityMessage.

  Module OpenInterestMessage.

    (** Open interest of the contracts traded, sent during trading hours on Stream Id no. 99. *)
    Record t := {
      timestamp : N;
      token : N;
      open_interest : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (timestamp record < 256 ^ N.of_nat 8)%N /\
      (token record < 256 ^ N.of_nat 4)%N /\
      (open_interest record < 256 ^ N.of_nat 4)%N.

    Definition encode (record : t) : list byte :=
      encode_uint_le 8 (timestamp record) ++
      encode_uint_le 4 (token record) ++
      encode_uint_le 4 (open_interest record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint_le 8 bytes with
      | None => None
      | Some (timestamp_value, bytes) =>
          match decode_uint_le 4 bytes with
          | None => None
          | Some (token_value, bytes) =>
              match decode_uint_le 4 bytes with
              | None => None
              | Some (open_interest_value, bytes) =>
                  Some ({| timestamp := timestamp_value; token := token_value; open_interest := open_interest_value |}, bytes)
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 16.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_uint_le_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 [bound_1 bound_2]].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_uint_le by exact bound_0.
      rewrite decode_encode_uint_le by exact bound_1.
      rewrite decode_encode_uint_le by exact bound_2.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec]. Defined.

  End OpenInterestMessage.

  Module HeartbeatMessage.

    (** Sent when there is no data available for a few seconds. The sequence number field in the Stream Header will have the value 0 (zero) for this message. *)
    Record t := {
      last_sequence_no : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (last_sequence_no record < 256 ^ N.of_nat 4)%N.

    Definition encode (record : t) : list byte :=
      encode_uint_le 4 (last_sequence_no record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint_le 4 bytes with
      | None => None
      | Some (last_sequence_no_value, bytes) =>
          Some ({| last_sequence_no := last_sequence_no_value |}, bytes)
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 4.
    Proof.
      intros record. unfold encode.
      rewrite !encode_uint_le_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      unfold decode, encode.
      rewrite decode_encode_uint_le by exact bound.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec]. Defined.

  End HeartbeatMessage.

End NseIxMtbtNdalV15.
