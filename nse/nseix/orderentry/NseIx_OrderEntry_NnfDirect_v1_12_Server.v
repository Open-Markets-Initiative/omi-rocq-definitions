From Stdlib Require Import List.
From Stdlib Require Import NArith.
From Stdlib Require Import Lia.
From Stdlib Require Import Strings.Byte.
From Omi Require Import Wire.

Import ListNotations.

(** * National Stock Exchange of India Ltd Order Entry

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
      - a run filling what frames it
      - a Integrity rule
      - the dispatch that chooses a message by its type
      - a Composite rule
      - a field read in bits
      - a length prefix framing what follows
      - a run of a stated number of entries

    License: MIT No Attribution
  *)

Module NseIxOrderEntryV112Server.

  Module PacketHeader.

    (** Packet Length and Sequence number, the first six bytes of the direct interface's twenty two byte packet header; its last sixteen open each packet body branch *)
    Record t := {
      packet_length : N;
      packet_sequence_number : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (packet_length record < 256 ^ N.of_nat 2)%N /\
      (packet_sequence_number record < 256 ^ N.of_nat 4)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 2 (packet_length record) ++
      encode_uint 4 (packet_sequence_number record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 2 bytes with
      | None => None
      | Some (packet_length_value, bytes) =>
          match decode_uint 4 bytes with
          | None => None
          | Some (packet_sequence_number_value, bytes) =>
              Some ({| packet_length := packet_length_value; packet_sequence_number := packet_sequence_number_value |}, bytes)
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 6.
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

  End PacketHeader.

  Module MessageHeader.

    (** MESSAGE_HEADER *)
    Record t := {
      transaction_code : N;
      log_time : N;
      alpha_char : list byte;
      trader_id : N;
      error_code : N;
      header_timestamp : list byte;
      time_stamp_1 : list byte;
      time_stamp_2 : list byte;
      message_length : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (transaction_code record < 256 ^ N.of_nat 2)%N /\
      (log_time record < 256 ^ N.of_nat 4)%N /\
      Datatypes.length (alpha_char record) = 2 /\
      (trader_id record < 256 ^ N.of_nat 4)%N /\
      (error_code record < 256 ^ N.of_nat 2)%N /\
      Datatypes.length (header_timestamp record) = 8 /\
      Datatypes.length (time_stamp_1 record) = 8 /\
      Datatypes.length (time_stamp_2 record) = 8 /\
      (message_length record < 256 ^ N.of_nat 2)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 2 (transaction_code record) ++
      encode_uint 4 (log_time record) ++
      encode_bytes 2 (alpha_char record) ++
      encode_uint 4 (trader_id record) ++
      encode_uint 2 (error_code record) ++
      encode_bytes 8 (header_timestamp record) ++
      encode_bytes 8 (time_stamp_1 record) ++
      encode_bytes 8 (time_stamp_2 record) ++
      encode_uint 2 (message_length record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 2 bytes with
      | None => None
      | Some (transaction_code_value, bytes) =>
          match decode_uint 4 bytes with
          | None => None
          | Some (log_time_value, bytes) =>
              match decode_bytes 2 bytes with
              | None => None
              | Some (alpha_char_value, bytes) =>
                  match decode_uint 4 bytes with
                  | None => None
                  | Some (trader_id_value, bytes) =>
                      match decode_uint 2 bytes with
                      | None => None
                      | Some (error_code_value, bytes) =>
                          match decode_bytes 8 bytes with
                          | None => None
                          | Some (header_timestamp_value, bytes) =>
                              match decode_bytes 8 bytes with
                              | None => None
                              | Some (time_stamp_1_value, bytes) =>
                                  match decode_bytes 8 bytes with
                                  | None => None
                                  | Some (time_stamp_2_value, bytes) =>
                                      match decode_uint 2 bytes with
                                      | None => None
                                      | Some (message_length_value, bytes) =>
                                          Some ({| transaction_code := transaction_code_value; log_time := log_time_value; alpha_char := alpha_char_value; trader_id := trader_id_value; error_code := error_code_value; header_timestamp := header_timestamp_value; time_stamp_1 := time_stamp_1_value; time_stamp_2 := time_stamp_2_value; message_length := message_length_value |}, bytes)
                                      end
                                  end
                              end
                          end
                      end
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 40.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_uint_length, !encode_bytes_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 [bound_1 [bound_2 [bound_3 [bound_4 [bound_5 [bound_6 [bound_7 bound_8]]]]]]]].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_uint by exact bound_0.
      rewrite decode_encode_uint by exact bound_1.
      rewrite decode_encode_bytes by exact bound_2.
      rewrite decode_encode_uint by exact bound_3.
      rewrite decode_encode_uint by exact bound_4.
      rewrite decode_encode_bytes by exact bound_5.
      rewrite decode_encode_bytes by exact bound_6.
      rewrite decode_encode_bytes by exact bound_7.
      rewrite decode_encode_uint by exact bound_8.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End MessageHeader.

  Module ErrorResponseBody.

    (** Error Response Body *)
    Record t := {
      key : list byte;
      error_message : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (key record) = 14 /\
      Datatypes.length (error_message record) = 128.

    Definition encode (record : t) : list byte :=
      encode_bytes 14 (key record) ++
      encode_bytes 128 (error_message record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 14 bytes with
      | None => None
      | Some (key_value, bytes) =>
          match decode_bytes 128 bytes with
          | None => None
          | Some (error_message_value, bytes) =>
              Some ({| key := key_value; error_message := error_message_value |}, bytes)
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 142.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_bytes_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 bound_1].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_bytes by exact bound_0.
      rewrite decode_encode_bytes by exact bound_1.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End ErrorResponseBody.

  Module SignOffRequestOutMessage.

    (** Details of the user's last log off, sent when the user logs on again *)
    Record t := {
      user_id : N;
      reserved_145 : list byte;
      reserved_1 : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (user_id record < 256 ^ N.of_nat 4)%N /\
      Datatypes.length (reserved_145 record) = 145 /\
      Datatypes.length (reserved_1 record) = 1.

    Definition encode (record : t) : list byte :=
      encode_uint 4 (user_id record) ++
      encode_bytes 145 (reserved_145 record) ++
      encode_bytes 1 (reserved_1 record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 4 bytes with
      | None => None
      | Some (user_id_value, bytes) =>
          match decode_bytes 145 bytes with
          | None => None
          | Some (reserved_145_value, bytes) =>
              match decode_bytes 1 bytes with
              | None => None
              | Some (reserved_1_value, bytes) =>
                  Some ({| user_id := user_id_value; reserved_145 := reserved_145_value; reserved_1 := reserved_1_value |}, bytes)
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 150.
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

  End SignOffRequestOutMessage.

  Module StMarketStatus.

    (** ST_MARKET_STATUS *)
    Record t := {
      normal : N;
      oddlot : N;
      spot : N;
      auction : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (normal record < 256 ^ N.of_nat 2)%N /\
      (oddlot record < 256 ^ N.of_nat 2)%N /\
      (spot record < 256 ^ N.of_nat 2)%N /\
      (auction record < 256 ^ N.of_nat 2)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 2 (normal record) ++
      encode_uint 2 (oddlot record) ++
      encode_uint 2 (spot record) ++
      encode_uint 2 (auction record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 2 bytes with
      | None => None
      | Some (normal_value, bytes) =>
          match decode_uint 2 bytes with
          | None => None
          | Some (oddlot_value, bytes) =>
              match decode_uint 2 bytes with
              | None => None
              | Some (spot_value, bytes) =>
                  match decode_uint 2 bytes with
                  | None => None
                  | Some (auction_value, bytes) =>
                      Some ({| normal := normal_value; oddlot := oddlot_value; spot := spot_value; auction := auction_value |}, bytes)
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

  End StMarketStatus.

  Module StExMarketStatus.

    (** ST_EX_MARKET_STATUS *)
    Record t := {
      normal : N;
      oddlot : N;
      spot : N;
      auction : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (normal record < 256 ^ N.of_nat 2)%N /\
      (oddlot record < 256 ^ N.of_nat 2)%N /\
      (spot record < 256 ^ N.of_nat 2)%N /\
      (auction record < 256 ^ N.of_nat 2)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 2 (normal record) ++
      encode_uint 2 (oddlot record) ++
      encode_uint 2 (spot record) ++
      encode_uint 2 (auction record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 2 bytes with
      | None => None
      | Some (normal_value, bytes) =>
          match decode_uint 2 bytes with
          | None => None
          | Some (oddlot_value, bytes) =>
              match decode_uint 2 bytes with
              | None => None
              | Some (spot_value, bytes) =>
                  match decode_uint 2 bytes with
                  | None => None
                  | Some (auction_value, bytes) =>
                      Some ({| normal := normal_value; oddlot := oddlot_value; spot := spot_value; auction := auction_value |}, bytes)
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

  End StExMarketStatus.

  Module StPlMarketStatus.

    (** ST_PL_MARKET_STATUS *)
    Record t := {
      normal : N;
      oddlot : N;
      spot : N;
      auction : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (normal record < 256 ^ N.of_nat 2)%N /\
      (oddlot record < 256 ^ N.of_nat 2)%N /\
      (spot record < 256 ^ N.of_nat 2)%N /\
      (auction record < 256 ^ N.of_nat 2)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 2 (normal record) ++
      encode_uint 2 (oddlot record) ++
      encode_uint 2 (spot record) ++
      encode_uint 2 (auction record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 2 bytes with
      | None => None
      | Some (normal_value, bytes) =>
          match decode_uint 2 bytes with
          | None => None
          | Some (oddlot_value, bytes) =>
              match decode_uint 2 bytes with
              | None => None
              | Some (spot_value, bytes) =>
                  match decode_uint 2 bytes with
                  | None => None
                  | Some (auction_value, bytes) =>
                      Some ({| normal := normal_value; oddlot := oddlot_value; spot := spot_value; auction := auction_value |}, bytes)
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

  End StPlMarketStatus.

  Module UpdateLocalDatabaseHeaderMessage.

    (** Opens the local database download *)
    Record t := {
      reserved_2 : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (reserved_2 record) = 2.

    Definition encode (record : t) : list byte :=
      encode_bytes 2 (reserved_2 record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 2 bytes with
      | None => None
      | Some (reserved_2_value, bytes) =>
          Some ({| reserved_2 := reserved_2_value |}, bytes)
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 2.
    Proof.
      intros record. unfold encode.
      rewrite !encode_bytes_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      unfold decode, encode.
      rewrite decode_encode_bytes by exact bound.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End UpdateLocalDatabaseHeaderMessage.

  Module UpdateLocalDatabaseTrailerMessage.

    (** Closes the local database download *)
    Record t := {
      reserved_2 : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (reserved_2 record) = 2.

    Definition encode (record : t) : list byte :=
      encode_bytes 2 (reserved_2 record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 2 bytes with
      | None => None
      | Some (reserved_2_value, bytes) =>
          Some ({| reserved_2 := reserved_2_value |}, bytes)
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 2.
    Proof.
      intros record. unfold encode.
      rewrite !encode_bytes_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      unfold decode, encode.
      rewrite decode_encode_bytes by exact bound.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End UpdateLocalDatabaseTrailerMessage.

  Module InnerHeader.

    (** INNER_MESSAGE_HEADER *)
    Record t := {
      inner_trader_id : N;
      inner_log_time : N;
      inner_alpha_char : list byte;
      inner_transaction_code : N;
      inner_error_code : N;
      inner_timestamp : list byte;
      inner_time_stamp_1 : list byte;
      inner_time_stamp_2 : list byte;
      inner_message_length : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (inner_trader_id record < 256 ^ N.of_nat 4)%N /\
      (inner_log_time record < 256 ^ N.of_nat 4)%N /\
      Datatypes.length (inner_alpha_char record) = 2 /\
      (inner_transaction_code record < 256 ^ N.of_nat 2)%N /\
      (inner_error_code record < 256 ^ N.of_nat 2)%N /\
      Datatypes.length (inner_timestamp record) = 8 /\
      Datatypes.length (inner_time_stamp_1 record) = 8 /\
      Datatypes.length (inner_time_stamp_2 record) = 8 /\
      (inner_message_length record < 256 ^ N.of_nat 2)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 4 (inner_trader_id record) ++
      encode_uint 4 (inner_log_time record) ++
      encode_bytes 2 (inner_alpha_char record) ++
      encode_uint 2 (inner_transaction_code record) ++
      encode_uint 2 (inner_error_code record) ++
      encode_bytes 8 (inner_timestamp record) ++
      encode_bytes 8 (inner_time_stamp_1 record) ++
      encode_bytes 8 (inner_time_stamp_2 record) ++
      encode_uint 2 (inner_message_length record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 4 bytes with
      | None => None
      | Some (inner_trader_id_value, bytes) =>
          match decode_uint 4 bytes with
          | None => None
          | Some (inner_log_time_value, bytes) =>
              match decode_bytes 2 bytes with
              | None => None
              | Some (inner_alpha_char_value, bytes) =>
                  match decode_uint 2 bytes with
                  | None => None
                  | Some (inner_transaction_code_value, bytes) =>
                      match decode_uint 2 bytes with
                      | None => None
                      | Some (inner_error_code_value, bytes) =>
                          match decode_bytes 8 bytes with
                          | None => None
                          | Some (inner_timestamp_value, bytes) =>
                              match decode_bytes 8 bytes with
                              | None => None
                              | Some (inner_time_stamp_1_value, bytes) =>
                                  match decode_bytes 8 bytes with
                                  | None => None
                                  | Some (inner_time_stamp_2_value, bytes) =>
                                      match decode_uint 2 bytes with
                                      | None => None
                                      | Some (inner_message_length_value, bytes) =>
                                          Some ({| inner_trader_id := inner_trader_id_value; inner_log_time := inner_log_time_value; inner_alpha_char := inner_alpha_char_value; inner_transaction_code := inner_transaction_code_value; inner_error_code := inner_error_code_value; inner_timestamp := inner_timestamp_value; inner_time_stamp_1 := inner_time_stamp_1_value; inner_time_stamp_2 := inner_time_stamp_2_value; inner_message_length := inner_message_length_value |}, bytes)
                                      end
                                  end
                              end
                          end
                      end
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 40.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_uint_length, !encode_bytes_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 [bound_1 [bound_2 [bound_3 [bound_4 [bound_5 [bound_6 [bound_7 bound_8]]]]]]]].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_uint by exact bound_0.
      rewrite decode_encode_uint by exact bound_1.
      rewrite decode_encode_bytes by exact bound_2.
      rewrite decode_encode_uint by exact bound_3.
      rewrite decode_encode_uint by exact bound_4.
      rewrite decode_encode_bytes by exact bound_5.
      rewrite decode_encode_bytes by exact bound_6.
      rewrite decode_encode_bytes by exact bound_7.
      rewrite decode_encode_uint by exact bound_8.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End InnerHeader.

  Module ContractDesc.

    (** CONTRACT_DESC *)
    Record t := {
      instrument_name : list byte;
      symbol : list byte;
      expiry_date : N;
      strike_price : N;
      option_type : list byte;
      ca_level : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (instrument_name record) = 6 /\
      Datatypes.length (symbol record) = 10 /\
      (expiry_date record < 256 ^ N.of_nat 4)%N /\
      (strike_price record < 256 ^ N.of_nat 4)%N /\
      Datatypes.length (option_type record) = 2 /\
      (ca_level record < 256 ^ N.of_nat 2)%N.

    Definition encode (record : t) : list byte :=
      encode_bytes 6 (instrument_name record) ++
      encode_bytes 10 (symbol record) ++
      encode_uint 4 (expiry_date record) ++
      encode_uint 4 (strike_price record) ++
      encode_bytes 2 (option_type record) ++
      encode_uint 2 (ca_level record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 6 bytes with
      | None => None
      | Some (instrument_name_value, bytes) =>
          match decode_bytes 10 bytes with
          | None => None
          | Some (symbol_value, bytes) =>
              match decode_uint 4 bytes with
              | None => None
              | Some (expiry_date_value, bytes) =>
                  match decode_uint 4 bytes with
                  | None => None
                  | Some (strike_price_value, bytes) =>
                      match decode_bytes 2 bytes with
                      | None => None
                      | Some (option_type_value, bytes) =>
                          match decode_uint 2 bytes with
                          | None => None
                          | Some (ca_level_value, bytes) =>
                              Some ({| instrument_name := instrument_name_value; symbol := symbol_value; expiry_date := expiry_date_value; strike_price := strike_price_value; option_type := option_type_value; ca_level := ca_level_value |}, bytes)
                          end
                      end
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 28.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_bytes_length, !encode_uint_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 [bound_1 [bound_2 [bound_3 [bound_4 bound_5]]]]].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_bytes by exact bound_0.
      rewrite decode_encode_bytes by exact bound_1.
      rewrite decode_encode_uint by exact bound_2.
      rewrite decode_encode_uint by exact bound_3.
      rewrite decode_encode_bytes by exact bound_4.
      rewrite decode_encode_uint by exact bound_5.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End ContractDesc.

  Module TradeInquiryBody.

    (** Trade Inquiry Body *)
    Record t := {
      token_no : N;
      contract_desc : ContractDesc.t;
      fill_number : N;
      fill_quantity : N;
      fill_price : N;
      mkt_type : list byte;
      buy_open_close : list byte;
      new_volume : N;
      buy_broker_id : list byte;
      sell_broker_id : list byte;
      trader_id : N;
      requested_by : list byte;
      sell_open_close : list byte;
      buy_account_number : list byte;
      sell_account_number : list byte;
      buy_participant : list byte;
      sell_participant : list byte;
      reserved_2 : list byte;
      buy_giveup_flag : list byte;
      sell_giveup_flag : list byte;
      reserved_80 : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (token_no record < 256 ^ N.of_nat 4)%N /\
      ContractDesc.bounded (contract_desc record) /\
      (fill_number record < 256 ^ N.of_nat 4)%N /\
      (fill_quantity record < 256 ^ N.of_nat 4)%N /\
      (fill_price record < 256 ^ N.of_nat 4)%N /\
      Datatypes.length (mkt_type record) = 1 /\
      Datatypes.length (buy_open_close record) = 1 /\
      (new_volume record < 256 ^ N.of_nat 4)%N /\
      Datatypes.length (buy_broker_id record) = 5 /\
      Datatypes.length (sell_broker_id record) = 5 /\
      (trader_id record < 256 ^ N.of_nat 4)%N /\
      Datatypes.length (requested_by record) = 1 /\
      Datatypes.length (sell_open_close record) = 1 /\
      Datatypes.length (buy_account_number record) = 10 /\
      Datatypes.length (sell_account_number record) = 10 /\
      Datatypes.length (buy_participant record) = 12 /\
      Datatypes.length (sell_participant record) = 12 /\
      Datatypes.length (reserved_2 record) = 2 /\
      Datatypes.length (buy_giveup_flag record) = 1 /\
      Datatypes.length (sell_giveup_flag record) = 1 /\
      Datatypes.length (reserved_80 record) = 80.

    Definition encode (record : t) : list byte :=
      encode_uint 4 (token_no record) ++
      ContractDesc.encode (contract_desc record) ++
      encode_uint 4 (fill_number record) ++
      encode_uint 4 (fill_quantity record) ++
      encode_uint 4 (fill_price record) ++
      encode_bytes 1 (mkt_type record) ++
      encode_bytes 1 (buy_open_close record) ++
      encode_uint 4 (new_volume record) ++
      encode_bytes 5 (buy_broker_id record) ++
      encode_bytes 5 (sell_broker_id record) ++
      encode_uint 4 (trader_id record) ++
      encode_bytes 1 (requested_by record) ++
      encode_bytes 1 (sell_open_close record) ++
      encode_bytes 10 (buy_account_number record) ++
      encode_bytes 10 (sell_account_number record) ++
      encode_bytes 12 (buy_participant record) ++
      encode_bytes 12 (sell_participant record) ++
      encode_bytes 2 (reserved_2 record) ++
      encode_bytes 1 (buy_giveup_flag record) ++
      encode_bytes 1 (sell_giveup_flag record) ++
      encode_bytes 80 (reserved_80 record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 4 bytes with
      | None => None
      | Some (token_no_value, bytes) =>
          match ContractDesc.decode bytes with
          | None => None
          | Some (contract_desc_value, bytes) =>
              match decode_uint 4 bytes with
              | None => None
              | Some (fill_number_value, bytes) =>
                  match decode_uint 4 bytes with
                  | None => None
                  | Some (fill_quantity_value, bytes) =>
                      match decode_uint 4 bytes with
                      | None => None
                      | Some (fill_price_value, bytes) =>
                          match decode_bytes 1 bytes with
                          | None => None
                          | Some (mkt_type_value, bytes) =>
                              match decode_bytes 1 bytes with
                              | None => None
                              | Some (buy_open_close_value, bytes) =>
                                  match decode_uint 4 bytes with
                                  | None => None
                                  | Some (new_volume_value, bytes) =>
                                      match decode_bytes 5 bytes with
                                      | None => None
                                      | Some (buy_broker_id_value, bytes) =>
                                          match decode_bytes 5 bytes with
                                          | None => None
                                          | Some (sell_broker_id_value, bytes) =>
                                              match decode_uint 4 bytes with
                                              | None => None
                                              | Some (trader_id_value, bytes) =>
                                                  match decode_bytes 1 bytes with
                                                  | None => None
                                                  | Some (requested_by_value, bytes) =>
                                                      match decode_bytes 1 bytes with
                                                      | None => None
                                                      | Some (sell_open_close_value, bytes) =>
                                                          match decode_bytes 10 bytes with
                                                          | None => None
                                                          | Some (buy_account_number_value, bytes) =>
                                                              match decode_bytes 10 bytes with
                                                              | None => None
                                                              | Some (sell_account_number_value, bytes) =>
                                                                  match decode_bytes 12 bytes with
                                                                  | None => None
                                                                  | Some (buy_participant_value, bytes) =>
                                                                      match decode_bytes 12 bytes with
                                                                      | None => None
                                                                      | Some (sell_participant_value, bytes) =>
                                                                          match decode_bytes 2 bytes with
                                                                          | None => None
                                                                          | Some (reserved_2_value, bytes) =>
                                                                              match decode_bytes 1 bytes with
                                                                              | None => None
                                                                              | Some (buy_giveup_flag_value, bytes) =>
                                                                                  match decode_bytes 1 bytes with
                                                                                  | None => None
                                                                                  | Some (sell_giveup_flag_value, bytes) =>
                                                                                      match decode_bytes 80 bytes with
                                                                                      | None => None
                                                                                      | Some (reserved_80_value, bytes) =>
                                                                                          Some ({| token_no := token_no_value; contract_desc := contract_desc_value; fill_number := fill_number_value; fill_quantity := fill_quantity_value; fill_price := fill_price_value; mkt_type := mkt_type_value; buy_open_close := buy_open_close_value; new_volume := new_volume_value; buy_broker_id := buy_broker_id_value; sell_broker_id := sell_broker_id_value; trader_id := trader_id_value; requested_by := requested_by_value; sell_open_close := sell_open_close_value; buy_account_number := buy_account_number_value; sell_account_number := sell_account_number_value; buy_participant := buy_participant_value; sell_participant := sell_participant_value; reserved_2 := reserved_2_value; buy_giveup_flag := buy_giveup_flag_value; sell_giveup_flag := sell_giveup_flag_value; reserved_80 := reserved_80_value |}, bytes)
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

    Theorem encode_length : forall record, Datatypes.length (encode record) = 194.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_uint_length, !ContractDesc.encode_length, !encode_bytes_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 [bound_1 [bound_2 [bound_3 [bound_4 [bound_5 [bound_6 [bound_7 [bound_8 [bound_9 [bound_10 [bound_11 [bound_12 [bound_13 [bound_14 [bound_15 [bound_16 [bound_17 [bound_18 [bound_19 bound_20]]]]]]]]]]]]]]]]]]]].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_uint by exact bound_0.
      rewrite ContractDesc.decode_encode by exact bound_1.
      rewrite decode_encode_uint by exact bound_2.
      rewrite decode_encode_uint by exact bound_3.
      rewrite decode_encode_uint by exact bound_4.
      rewrite decode_encode_bytes by exact bound_5.
      rewrite decode_encode_bytes by exact bound_6.
      rewrite decode_encode_uint by exact bound_7.
      rewrite decode_encode_bytes by exact bound_8.
      rewrite decode_encode_bytes by exact bound_9.
      rewrite decode_encode_uint by exact bound_10.
      rewrite decode_encode_bytes by exact bound_11.
      rewrite decode_encode_bytes by exact bound_12.
      rewrite decode_encode_bytes by exact bound_13.
      rewrite decode_encode_bytes by exact bound_14.
      rewrite decode_encode_bytes by exact bound_15.
      rewrite decode_encode_bytes by exact bound_16.
      rewrite decode_encode_bytes by exact bound_17.
      rewrite decode_encode_bytes by exact bound_18.
      rewrite decode_encode_bytes by exact bound_19.
      rewrite decode_encode_bytes by exact bound_20.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec) | apply ContractDesc.eq_dec]. Defined.

  End TradeInquiryBody.

  Module TradeInquiryResponseMessage.

    (** Trade cancellation response, trade error, trade modification rejection and the negotiated large trade rejections and cancellation confirmation, carried in the shared trade structure. Transaction Code in the header names the response *)
    Record t := {
      trade_inquiry_body : TradeInquiryBody.t;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      TradeInquiryBody.bounded (trade_inquiry_body record).

    Definition encode (record : t) : list byte :=
      TradeInquiryBody.encode (trade_inquiry_body record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match TradeInquiryBody.decode bytes with
      | None => None
      | Some (trade_inquiry_body_value, bytes) =>
          Some ({| trade_inquiry_body := trade_inquiry_body_value |}, bytes)
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 194.
    Proof.
      intros record. unfold encode.
      rewrite !TradeInquiryBody.encode_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      unfold decode, encode.
      rewrite TradeInquiryBody.decode_encode by exact bound.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply TradeInquiryBody.eq_dec]. Defined.

  End TradeInquiryResponseMessage.

  Module ControlMessageToTraderMessage.

    (** Interactive message sent to the trader from Nse Ix Control *)
    Record t := {
      trader_id : N;
      action_code : list byte;
      reserved_1 : list byte;
      broad_cast_message_length : N;
      broad_cast_message : list byte;
      second_reserved_1 : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (trader_id record < 256 ^ N.of_nat 4)%N /\
      Datatypes.length (action_code record) = 3 /\
      Datatypes.length (reserved_1 record) = 1 /\
      (broad_cast_message_length record < 256 ^ N.of_nat 2)%N /\
      Datatypes.length (broad_cast_message record) = 239 /\
      Datatypes.length (second_reserved_1 record) = 1.

    Definition encode (record : t) : list byte :=
      encode_uint 4 (trader_id record) ++
      encode_bytes 3 (action_code record) ++
      encode_bytes 1 (reserved_1 record) ++
      encode_uint 2 (broad_cast_message_length record) ++
      encode_bytes 239 (broad_cast_message record) ++
      encode_bytes 1 (second_reserved_1 record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 4 bytes with
      | None => None
      | Some (trader_id_value, bytes) =>
          match decode_bytes 3 bytes with
          | None => None
          | Some (action_code_value, bytes) =>
              match decode_bytes 1 bytes with
              | None => None
              | Some (reserved_1_value, bytes) =>
                  match decode_uint 2 bytes with
                  | None => None
                  | Some (broad_cast_message_length_value, bytes) =>
                      match decode_bytes 239 bytes with
                      | None => None
                      | Some (broad_cast_message_value, bytes) =>
                          match decode_bytes 1 bytes with
                          | None => None
                          | Some (second_reserved_1_value, bytes) =>
                              Some ({| trader_id := trader_id_value; action_code := action_code_value; reserved_1 := reserved_1_value; broad_cast_message_length := broad_cast_message_length_value; broad_cast_message := broad_cast_message_value; second_reserved_1 := second_reserved_1_value |}, bytes)
                          end
                      end
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 250.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_uint_length, !encode_bytes_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 [bound_1 [bound_2 [bound_3 [bound_4 bound_5]]]]].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_uint by exact bound_0.
      rewrite decode_encode_bytes by exact bound_1.
      rewrite decode_encode_bytes by exact bound_2.
      rewrite decode_encode_uint by exact bound_3.
      rewrite decode_encode_bytes by exact bound_4.
      rewrite decode_encode_bytes by exact bound_5.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End ControlMessageToTraderMessage.

  Module ReportHeaderBody.

    (** Report Header Body *)
    Record t := {
      org_scope : list byte;
      report_date : N;
      user_type : N;
      broker_id : list byte;
      firm_name : list byte;
      trader_number : N;
      trader_name : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (org_scope record) = 1 /\
      (report_date record < 256 ^ N.of_nat 4)%N /\
      (user_type record < 256 ^ N.of_nat 2)%N /\
      Datatypes.length (broker_id record) = 5 /\
      Datatypes.length (firm_name record) = 25 /\
      (trader_number record < 256 ^ N.of_nat 4)%N /\
      Datatypes.length (trader_name record) = 26.

    Definition encode (record : t) : list byte :=
      encode_bytes 1 (org_scope record) ++
      encode_uint 4 (report_date record) ++
      encode_uint 2 (user_type record) ++
      encode_bytes 5 (broker_id record) ++
      encode_bytes 25 (firm_name record) ++
      encode_uint 4 (trader_number record) ++
      encode_bytes 26 (trader_name record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 1 bytes with
      | None => None
      | Some (org_scope_value, bytes) =>
          match decode_uint 4 bytes with
          | None => None
          | Some (report_date_value, bytes) =>
              match decode_uint 2 bytes with
              | None => None
              | Some (user_type_value, bytes) =>
                  match decode_bytes 5 bytes with
                  | None => None
                  | Some (broker_id_value, bytes) =>
                      match decode_bytes 25 bytes with
                      | None => None
                      | Some (firm_name_value, bytes) =>
                          match decode_uint 4 bytes with
                          | None => None
                          | Some (trader_number_value, bytes) =>
                              match decode_bytes 26 bytes with
                              | None => None
                              | Some (trader_name_value, bytes) =>
                                  Some ({| org_scope := org_scope_value; report_date := report_date_value; user_type := user_type_value; broker_id := broker_id_value; firm_name := firm_name_value; trader_number := trader_number_value; trader_name := trader_name_value |}, bytes)
                              end
                          end
                      end
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 67.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_bytes_length, !encode_uint_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 [bound_1 [bound_2 [bound_3 [bound_4 [bound_5 bound_6]]]]]].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_bytes by exact bound_0.
      rewrite decode_encode_uint by exact bound_1.
      rewrite decode_encode_uint by exact bound_2.
      rewrite decode_encode_bytes by exact bound_3.
      rewrite decode_encode_bytes by exact bound_4.
      rewrite decode_encode_uint by exact bound_5.
      rewrite decode_encode_bytes by exact bound_6.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End ReportHeaderBody.

  Module ReportTrailerBody.

    (** Report Trailer Body *)
    Record t := {
      number_of_packets : N;
      reserved_1 : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (number_of_packets record < 256 ^ N.of_nat 4)%N /\
      Datatypes.length (reserved_1 record) = 1.

    Definition encode (record : t) : list byte :=
      encode_uint 4 (number_of_packets record) ++
      encode_bytes 1 (reserved_1 record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 4 bytes with
      | None => None
      | Some (number_of_packets_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (reserved_1_value, bytes) =>
              Some ({| number_of_packets := number_of_packets_value; reserved_1 := reserved_1_value |}, bytes)
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 5.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_uint_length, !encode_bytes_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 bound_1].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_uint by exact bound_0.
      rewrite decode_encode_bytes by exact bound_1.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End ReportTrailerBody.

  Module SpreadReportHeaderBody.

    (** Spread Report Header Body *)
    Record t := {
      org_scope : list byte;
      report_date : N;
      user_type : N;
      broker_number : list byte;
      broker_name : list byte;
      trader_number : N;
      trader_name : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (org_scope record) = 1 /\
      (report_date record < 256 ^ N.of_nat 4)%N /\
      (user_type record < 256 ^ N.of_nat 2)%N /\
      Datatypes.length (broker_number record) = 5 /\
      Datatypes.length (broker_name record) = 25 /\
      (trader_number record < 256 ^ N.of_nat 4)%N /\
      Datatypes.length (trader_name record) = 26.

    Definition encode (record : t) : list byte :=
      encode_bytes 1 (org_scope record) ++
      encode_uint 4 (report_date record) ++
      encode_uint 2 (user_type record) ++
      encode_bytes 5 (broker_number record) ++
      encode_bytes 25 (broker_name record) ++
      encode_uint 4 (trader_number record) ++
      encode_bytes 26 (trader_name record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 1 bytes with
      | None => None
      | Some (org_scope_value, bytes) =>
          match decode_uint 4 bytes with
          | None => None
          | Some (report_date_value, bytes) =>
              match decode_uint 2 bytes with
              | None => None
              | Some (user_type_value, bytes) =>
                  match decode_bytes 5 bytes with
                  | None => None
                  | Some (broker_number_value, bytes) =>
                      match decode_bytes 25 bytes with
                      | None => None
                      | Some (broker_name_value, bytes) =>
                          match decode_uint 4 bytes with
                          | None => None
                          | Some (trader_number_value, bytes) =>
                              match decode_bytes 26 bytes with
                              | None => None
                              | Some (trader_name_value, bytes) =>
                                  Some ({| org_scope := org_scope_value; report_date := report_date_value; user_type := user_type_value; broker_number := broker_number_value; broker_name := broker_name_value; trader_number := trader_number_value; trader_name := trader_name_value |}, bytes)
                              end
                          end
                      end
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 67.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_bytes_length, !encode_uint_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 [bound_1 [bound_2 [bound_3 [bound_4 [bound_5 bound_6]]]]]].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_bytes by exact bound_0.
      rewrite decode_encode_uint by exact bound_1.
      rewrite decode_encode_uint by exact bound_2.
      rewrite decode_encode_bytes by exact bound_3.
      rewrite decode_encode_bytes by exact bound_4.
      rewrite decode_encode_uint by exact bound_5.
      rewrite decode_encode_bytes by exact bound_6.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End SpreadReportHeaderBody.

  Module GatewayRouterResponseMessage.

    (** Returns the allocated gateway server and the keys used to encrypt the session *)
    Record t := {
      box_id : N;
      broker_id : list byte;
      filler : list byte;
      ip_address : list byte;
      port : N;
      session_key : list byte;
      cryptographic_key : list byte;
      cryptographic_iv : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (box_id record < 256 ^ N.of_nat 2)%N /\
      Datatypes.length (broker_id record) = 5 /\
      Datatypes.length (filler record) = 1 /\
      Datatypes.length (ip_address record) = 16 /\
      (port record < 256 ^ N.of_nat 4)%N /\
      Datatypes.length (session_key record) = 8 /\
      Datatypes.length (cryptographic_key record) = 32 /\
      Datatypes.length (cryptographic_iv record) = 16.

    Definition encode (record : t) : list byte :=
      encode_uint 2 (box_id record) ++
      encode_bytes 5 (broker_id record) ++
      encode_bytes 1 (filler record) ++
      encode_bytes 16 (ip_address record) ++
      encode_uint 4 (port record) ++
      encode_bytes 8 (session_key record) ++
      encode_bytes 32 (cryptographic_key record) ++
      encode_bytes 16 (cryptographic_iv record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 2 bytes with
      | None => None
      | Some (box_id_value, bytes) =>
          match decode_bytes 5 bytes with
          | None => None
          | Some (broker_id_value, bytes) =>
              match decode_bytes 1 bytes with
              | None => None
              | Some (filler_value, bytes) =>
                  match decode_bytes 16 bytes with
                  | None => None
                  | Some (ip_address_value, bytes) =>
                      match decode_uint 4 bytes with
                      | None => None
                      | Some (port_value, bytes) =>
                          match decode_bytes 8 bytes with
                          | None => None
                          | Some (session_key_value, bytes) =>
                              match decode_bytes 32 bytes with
                              | None => None
                              | Some (cryptographic_key_value, bytes) =>
                                  match decode_bytes 16 bytes with
                                  | None => None
                                  | Some (cryptographic_iv_value, bytes) =>
                                      Some ({| box_id := box_id_value; broker_id := broker_id_value; filler := filler_value; ip_address := ip_address_value; port := port_value; session_key := session_key_value; cryptographic_key := cryptographic_key_value; cryptographic_iv := cryptographic_iv_value |}, bytes)
                                  end
                              end
                          end
                      end
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 84.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_uint_length, !encode_bytes_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 [bound_1 [bound_2 [bound_3 [bound_4 [bound_5 [bound_6 bound_7]]]]]]].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_uint by exact bound_0.
      rewrite decode_encode_bytes by exact bound_1.
      rewrite decode_encode_bytes by exact bound_2.
      rewrite decode_encode_bytes by exact bound_3.
      rewrite decode_encode_uint by exact bound_4.
      rewrite decode_encode_bytes by exact bound_5.
      rewrite decode_encode_bytes by exact bound_6.
      rewrite decode_encode_bytes by exact bound_7.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End GatewayRouterResponseMessage.

  Module BoxSignOnRequestOutMessage.

    (** Confirms the box sign on *)
    Record t := {
      box_id : N;
      reserved_10 : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (box_id record < 256 ^ N.of_nat 2)%N /\
      Datatypes.length (reserved_10 record) = 10.

    Definition encode (record : t) : list byte :=
      encode_uint 2 (box_id record) ++
      encode_bytes 10 (reserved_10 record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 2 bytes with
      | None => None
      | Some (box_id_value, bytes) =>
          match decode_bytes 10 bytes with
          | None => None
          | Some (reserved_10_value, bytes) =>
              Some ({| box_id := box_id_value; reserved_10 := reserved_10_value |}, bytes)
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 12.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_uint_length, !encode_bytes_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 bound_1].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_uint by exact bound_0.
      rewrite decode_encode_bytes by exact bound_1.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End BoxSignOnRequestOutMessage.

  Module BoxSignOffMessage.

    (** Signs the box off the gateway server when the exchange terminates the connection *)
    Record t := {
      box_id : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (box_id record < 256 ^ N.of_nat 2)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 2 (box_id record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 2 bytes with
      | None => None
      | Some (box_id_value, bytes) =>
          Some ({| box_id := box_id_value |}, bytes)
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 2.
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

  End BoxSignOffMessage.

  Module ContingencyBroadcastMessage.

    (** Signals the start or end of an outage on one or all matching engine streams *)
    Record t := {
      stream_number : N;
      status : N;
      reserved_200 : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (stream_number record < 256 ^ N.of_nat 2)%N /\
      (status record < 256 ^ N.of_nat 2)%N /\
      Datatypes.length (reserved_200 record) = 200.

    Definition encode (record : t) : list byte :=
      encode_uint 2 (stream_number record) ++
      encode_uint 2 (status record) ++
      encode_bytes 200 (reserved_200 record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 2 bytes with
      | None => None
      | Some (stream_number_value, bytes) =>
          match decode_uint 2 bytes with
          | None => None
          | Some (status_value, bytes) =>
              match decode_bytes 200 bytes with
              | None => None
              | Some (reserved_200_value, bytes) =>
                  Some ({| stream_number := stream_number_value; status := status_value; reserved_200 := reserved_200_value |}, bytes)
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 204.
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
      rewrite decode_encode_uint by exact bound_1.
      rewrite decode_encode_bytes by exact bound_2.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End ContingencyBroadcastMessage.

  Module ResetUserPasswordResponseMessage.

    (** Answers the password reset request, Error Code in the header saying whether it succeeded *)
    Record t := {
      user_id : N;
      reserved_14 : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (user_id record < 256 ^ N.of_nat 4)%N /\
      Datatypes.length (reserved_14 record) = 14.

    Definition encode (record : t) : list byte :=
      encode_uint 4 (user_id record) ++
      encode_bytes 14 (reserved_14 record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 4 bytes with
      | None => None
      | Some (user_id_value, bytes) =>
          match decode_bytes 14 bytes with
          | None => None
          | Some (reserved_14_value, bytes) =>
              Some ({| user_id := user_id_value; reserved_14 := reserved_14_value |}, bytes)
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
      destruct bound as [bound_0 bound_1].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_uint by exact bound_0.
      rewrite decode_encode_bytes by exact bound_1.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End ResetUserPasswordResponseMessage.

  Module CollateralUserStatusChangeResponseMessage.

    (** Answers the cancel on logout status change *)
    Record t := {
      user_id : N;
      col_user_bit : list byte;
      reserved_1 : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (user_id record < 256 ^ N.of_nat 4)%N /\
      Datatypes.length (col_user_bit record) = 1 /\
      Datatypes.length (reserved_1 record) = 1.

    Definition encode (record : t) : list byte :=
      encode_uint 4 (user_id record) ++
      encode_bytes 1 (col_user_bit record) ++
      encode_bytes 1 (reserved_1 record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 4 bytes with
      | None => None
      | Some (user_id_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (col_user_bit_value, bytes) =>
              match decode_bytes 1 bytes with
              | None => None
              | Some (reserved_1_value, bytes) =>
                  Some ({| user_id := user_id_value; col_user_bit := col_user_bit_value; reserved_1 := reserved_1_value |}, bytes)
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 6.
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

  End CollateralUserStatusChangeResponseMessage.

  Module UserTradeModifyCancelStatusChangeResponseMessage.

    (** Answers the trade modification or cancellation status change *)
    Record t := {
      user_id : N;
      trd_mod_cxl_bit : list byte;
      reserved_1 : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (user_id record < 256 ^ N.of_nat 4)%N /\
      Datatypes.length (trd_mod_cxl_bit record) = 1 /\
      Datatypes.length (reserved_1 record) = 1.

    Definition encode (record : t) : list byte :=
      encode_uint 4 (user_id record) ++
      encode_bytes 1 (trd_mod_cxl_bit record) ++
      encode_bytes 1 (reserved_1 record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 4 bytes with
      | None => None
      | Some (user_id_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (trd_mod_cxl_bit_value, bytes) =>
              match decode_bytes 1 bytes with
              | None => None
              | Some (reserved_1_value, bytes) =>
                  Some ({| user_id := user_id_value; trd_mod_cxl_bit := trd_mod_cxl_bit_value; reserved_1 := reserved_1_value |}, bytes)
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 6.
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

  End UserTradeModifyCancelStatusChangeResponseMessage.

  Module UserAddressUnlockConfirmMessage.

    (** Acknowledges that the unlock request reached the trading system *)
    Record t := {
      user_id : N;
      reserved_36 : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (user_id record < 256 ^ N.of_nat 4)%N /\
      Datatypes.length (reserved_36 record) = 36.

    Definition encode (record : t) : list byte :=
      encode_uint 4 (user_id record) ++
      encode_bytes 36 (reserved_36 record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 4 bytes with
      | None => None
      | Some (user_id_value, bytes) =>
          match decode_bytes 36 bytes with
          | None => None
          | Some (reserved_36_value, bytes) =>
              Some ({| user_id := user_id_value; reserved_36 := reserved_36_value |}, bytes)
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 40.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_uint_length, !encode_bytes_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 bound_1].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_uint by exact bound_0.
      rewrite decode_encode_bytes by exact bound_1.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End UserAddressUnlockConfirmMessage.

  Module UserAddressUnlockApproveMessage.

    (** Approves or rejects the unlock of a user. Transaction Code in the header names which *)
    Record t := {
      user_id : N;
      reserved_36 : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (user_id record < 256 ^ N.of_nat 4)%N /\
      Datatypes.length (reserved_36 record) = 36.

    Definition encode (record : t) : list byte :=
      encode_uint 4 (user_id record) ++
      encode_bytes 36 (reserved_36 record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 4 bytes with
      | None => None
      | Some (user_id_value, bytes) =>
          match decode_bytes 36 bytes with
          | None => None
          | Some (reserved_36_value, bytes) =>
              Some ({| user_id := user_id_value; reserved_36 := reserved_36_value |}, bytes)
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 40.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_uint_length, !encode_bytes_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 bound_1].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_uint by exact bound_0.
      rewrite decode_encode_bytes by exact bound_1.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End UserAddressUnlockApproveMessage.

  Module NltOrderMessageToTraderMessage.

    (** Tells the counter member's corporate manager of a negotiated large trade order placed against it *)
    Record t := {
      message_buffer : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (message_buffer record) = 276.

    Definition encode (record : t) : list byte :=
      encode_bytes 276 (message_buffer record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 276 bytes with
      | None => None
      | Some (message_buffer_value, bytes) =>
          Some ({| message_buffer := message_buffer_value |}, bytes)
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 276.
    Proof.
      intros record. unfold encode.
      rewrite !encode_bytes_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      unfold decode, encode.
      rewrite decode_encode_bytes by exact bound.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End NltOrderMessageToTraderMessage.

End NseIxOrderEntryV112Server.
