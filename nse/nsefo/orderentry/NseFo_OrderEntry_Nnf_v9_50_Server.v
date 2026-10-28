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
      - a Composite rule
      - a field read in bits
      - the dispatch that chooses a message by its type
      - a length prefix framing what follows
      - a run counted by a field
  *)

Module NseFoOrderEntryV950Server.

  Module MessageHeader.

    (** MESSAGE_HEADER *)
    Record t := {
      transaction_code : N;
      log_time : N;
      alpha_char : list byte;
      trader_id : N;
      error_code : N;
      header_timestamp : N;
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
      (header_timestamp record < 256 ^ N.of_nat 8)%N /\
      Datatypes.length (time_stamp_1 record) = 8 /\
      Datatypes.length (time_stamp_2 record) = 8 /\
      (message_length record < 256 ^ N.of_nat 2)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 2 (transaction_code record) ++
      encode_uint 4 (log_time record) ++
      encode_bytes 2 (alpha_char record) ++
      encode_uint 4 (trader_id record) ++
      encode_uint 2 (error_code record) ++
      encode_uint 8 (header_timestamp record) ++
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
                          match decode_uint 8 bytes with
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
      rewrite decode_encode_uint by exact bound_5.
      rewrite decode_encode_bytes by exact bound_6.
      rewrite decode_encode_bytes by exact bound_7.
      rewrite decode_encode_uint by exact bound_8.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End MessageHeader.

  Module SignOffRequestOutMessage.

    (** Breaks the virtual circuit between the host and the front end *)
    Record t := {
      user_id : N;
      reserved_145 : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (user_id record < 256 ^ N.of_nat 4)%N /\
      Datatypes.length (reserved_145 record) = 145.

    Definition encode (record : t) : list byte :=
      encode_uint 4 (user_id record) ++
      encode_bytes 145 (reserved_145 record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 4 bytes with
      | None => None
      | Some (user_id_value, bytes) =>
          match decode_bytes 145 bytes with
          | None => None
          | Some (reserved_145_value, bytes) =>
              Some ({| user_id := user_id_value; reserved_145 := reserved_145_value |}, bytes)
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 149.
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

  End SignOffRequestOutMessage.

  Module StMarketStatus.

    (** ST_MARKET_STATUS *)
    Record t := {
      market_status_normal : N;
      market_status_oddlot : N;
      market_status_spot : N;
      market_status_auction : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (market_status_normal record < 256 ^ N.of_nat 2)%N /\
      (market_status_oddlot record < 256 ^ N.of_nat 2)%N /\
      (market_status_spot record < 256 ^ N.of_nat 2)%N /\
      (market_status_auction record < 256 ^ N.of_nat 2)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 2 (market_status_normal record) ++
      encode_uint 2 (market_status_oddlot record) ++
      encode_uint 2 (market_status_spot record) ++
      encode_uint 2 (market_status_auction record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 2 bytes with
      | None => None
      | Some (market_status_normal_value, bytes) =>
          match decode_uint 2 bytes with
          | None => None
          | Some (market_status_oddlot_value, bytes) =>
              match decode_uint 2 bytes with
              | None => None
              | Some (market_status_spot_value, bytes) =>
                  match decode_uint 2 bytes with
                  | None => None
                  | Some (market_status_auction_value, bytes) =>
                      Some ({| market_status_normal := market_status_normal_value; market_status_oddlot := market_status_oddlot_value; market_status_spot := market_status_spot_value; market_status_auction := market_status_auction_value |}, bytes)
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
      ex_market_status_normal : N;
      ex_market_status_oddlot : N;
      ex_market_status_spot : N;
      ex_market_status_auction : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (ex_market_status_normal record < 256 ^ N.of_nat 2)%N /\
      (ex_market_status_oddlot record < 256 ^ N.of_nat 2)%N /\
      (ex_market_status_spot record < 256 ^ N.of_nat 2)%N /\
      (ex_market_status_auction record < 256 ^ N.of_nat 2)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 2 (ex_market_status_normal record) ++
      encode_uint 2 (ex_market_status_oddlot record) ++
      encode_uint 2 (ex_market_status_spot record) ++
      encode_uint 2 (ex_market_status_auction record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 2 bytes with
      | None => None
      | Some (ex_market_status_normal_value, bytes) =>
          match decode_uint 2 bytes with
          | None => None
          | Some (ex_market_status_oddlot_value, bytes) =>
              match decode_uint 2 bytes with
              | None => None
              | Some (ex_market_status_spot_value, bytes) =>
                  match decode_uint 2 bytes with
                  | None => None
                  | Some (ex_market_status_auction_value, bytes) =>
                      Some ({| ex_market_status_normal := ex_market_status_normal_value; ex_market_status_oddlot := ex_market_status_oddlot_value; ex_market_status_spot := ex_market_status_spot_value; ex_market_status_auction := ex_market_status_auction_value |}, bytes)
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
      pl_market_status_normal : N;
      pl_market_status_oddlot : N;
      pl_market_status_spot : N;
      pl_market_status_auction : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (pl_market_status_normal record < 256 ^ N.of_nat 2)%N /\
      (pl_market_status_oddlot record < 256 ^ N.of_nat 2)%N /\
      (pl_market_status_spot record < 256 ^ N.of_nat 2)%N /\
      (pl_market_status_auction record < 256 ^ N.of_nat 2)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 2 (pl_market_status_normal record) ++
      encode_uint 2 (pl_market_status_oddlot record) ++
      encode_uint 2 (pl_market_status_spot record) ++
      encode_uint 2 (pl_market_status_auction record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 2 bytes with
      | None => None
      | Some (pl_market_status_normal_value, bytes) =>
          match decode_uint 2 bytes with
          | None => None
          | Some (pl_market_status_oddlot_value, bytes) =>
              match decode_uint 2 bytes with
              | None => None
              | Some (pl_market_status_spot_value, bytes) =>
                  match decode_uint 2 bytes with
                  | None => None
                  | Some (pl_market_status_auction_value, bytes) =>
                      Some ({| pl_market_status_normal := pl_market_status_normal_value; pl_market_status_oddlot := pl_market_status_oddlot_value; pl_market_status_spot := pl_market_status_spot_value; pl_market_status_auction := pl_market_status_auction_value |}, bytes)
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

  Module ExistingEncryptionTail.

    (** Initialisation vector used by the existing encryption *)
    Record t := {
      cryptographic_iv : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (cryptographic_iv record) = 16.

    Definition encode (record : t) : list byte :=
      encode_bytes 16 (cryptographic_iv record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 16 bytes with
      | None => None
      | Some (cryptographic_iv_value, bytes) =>
          Some ({| cryptographic_iv := cryptographic_iv_value |}, bytes)
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 16.
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

  End ExistingEncryptionTail.

  Module NewEncryptionTail.

    (** Initialisation vectors used by the new authenticated encryption *)
    Record t := {
      static_cryptographic_iv : list byte;
      dynamic_cryptographic_iv : N;
      cryptographic_additional_key : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (static_cryptographic_iv record) = 8 /\
      (dynamic_cryptographic_iv record < 256 ^ N.of_nat 8)%N /\
      Datatypes.length (cryptographic_additional_key record) = 12.

    Definition encode (record : t) : list byte :=
      encode_bytes 8 (static_cryptographic_iv record) ++
      encode_uint 8 (dynamic_cryptographic_iv record) ++
      encode_bytes 12 (cryptographic_additional_key record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 8 bytes with
      | None => None
      | Some (static_cryptographic_iv_value, bytes) =>
          match decode_uint 8 bytes with
          | None => None
          | Some (dynamic_cryptographic_iv_value, bytes) =>
              match decode_bytes 12 bytes with
              | None => None
              | Some (cryptographic_additional_key_value, bytes) =>
                  Some ({| static_cryptographic_iv := static_cryptographic_iv_value; dynamic_cryptographic_iv := dynamic_cryptographic_iv_value; cryptographic_additional_key := cryptographic_additional_key_value |}, bytes)
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
      destruct bound as [bound_0 [bound_1 bound_2]].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_bytes by exact bound_0.
      rewrite decode_encode_uint by exact bound_1.
      rewrite decode_encode_bytes by exact bound_2.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End NewEncryptionTail.

  Module UpdateLocalDatabaseHeaderMessage.

    (** Opens the local database download *)
    Record t := {
      reserved_2 : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (reserved_2 record < 256 ^ N.of_nat 2)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 2 (reserved_2 record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 2 bytes with
      | None => None
      | Some (reserved_2_value, bytes) =>
          Some ({| reserved_2 := reserved_2_value |}, bytes)
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

  End UpdateLocalDatabaseHeaderMessage.

  Module UpdateLocalDatabaseTrailerMessage.

    (** Closes the local database download *)
    Record t := {
      reserved_2 : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (reserved_2 record < 256 ^ N.of_nat 2)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 2 (reserved_2 record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 2 bytes with
      | None => None
      | Some (reserved_2_value, bytes) =>
          Some ({| reserved_2 := reserved_2_value |}, bytes)
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

  End UpdateLocalDatabaseTrailerMessage.

  Module InnerHeader.

    (** INNER_MESSAGE_HEADER *)
    Record t := {
      inner_trader_id : N;
      inner_log_time : N;
      inner_alpha_char : list byte;
      inner_transaction_code : N;
      inner_error_code : N;
      inner_timestamp : N;
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
      (inner_timestamp record < 256 ^ N.of_nat 8)%N /\
      Datatypes.length (inner_time_stamp_1 record) = 8 /\
      Datatypes.length (inner_time_stamp_2 record) = 8 /\
      (inner_message_length record < 256 ^ N.of_nat 2)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 4 (inner_trader_id record) ++
      encode_uint 4 (inner_log_time record) ++
      encode_bytes 2 (inner_alpha_char record) ++
      encode_uint 2 (inner_transaction_code record) ++
      encode_uint 2 (inner_error_code record) ++
      encode_uint 8 (inner_timestamp record) ++
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
                          match decode_uint 8 bytes with
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
      rewrite decode_encode_uint by exact bound_5.
      rewrite decode_encode_bytes by exact bound_6.
      rewrite decode_encode_bytes by exact bound_7.
      rewrite decode_encode_uint by exact bound_8.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End InnerHeader.

  Module InnerHeader2.

    (** INNER_MESSAGE_HEADER *)
    Record t := {
      inner_trader_id : N;
      inner_log_time : N;
      inner_alpha_char : list byte;
      inner_transaction_code : N;
      inner_error_code : N;
      inner_timestamp : N;
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
      (inner_timestamp record < 256 ^ N.of_nat 8)%N /\
      Datatypes.length (inner_time_stamp_1 record) = 8 /\
      Datatypes.length (inner_time_stamp_2 record) = 8 /\
      (inner_message_length record < 256 ^ N.of_nat 2)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 4 (inner_trader_id record) ++
      encode_uint 4 (inner_log_time record) ++
      encode_bytes 2 (inner_alpha_char record) ++
      encode_uint 2 (inner_transaction_code record) ++
      encode_uint 2 (inner_error_code record) ++
      encode_uint 8 (inner_timestamp record) ++
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
                          match decode_uint 8 bytes with
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
      rewrite decode_encode_uint by exact bound_5.
      rewrite decode_encode_bytes by exact bound_6.
      rewrite decode_encode_bytes by exact bound_7.
      rewrite decode_encode_uint by exact bound_8.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End InnerHeader2.

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

  Module ControlMessageToTraderMessage.

    (** Interactive message sent to the trader from Nse Control *)
    Record t := {
      trader_id : N;
      action_code : list byte;
      reserved_1 : N;
      broad_cast_message_length : N;
      broad_cast_message : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (trader_id record < 256 ^ N.of_nat 4)%N /\
      Datatypes.length (action_code record) = 3 /\
      (reserved_1 record < 256 ^ N.of_nat 1)%N /\
      (broad_cast_message_length record < 256 ^ N.of_nat 2)%N /\
      Datatypes.length (broad_cast_message record) = 239.

    Definition encode (record : t) : list byte :=
      encode_uint 4 (trader_id record) ++
      encode_bytes 3 (action_code record) ++
      encode_uint 1 (reserved_1 record) ++
      encode_uint 2 (broad_cast_message_length record) ++
      encode_bytes 239 (broad_cast_message record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 4 bytes with
      | None => None
      | Some (trader_id_value, bytes) =>
          match decode_bytes 3 bytes with
          | None => None
          | Some (action_code_value, bytes) =>
              match decode_uint 1 bytes with
              | None => None
              | Some (reserved_1_value, bytes) =>
                  match decode_uint 2 bytes with
                  | None => None
                  | Some (broad_cast_message_length_value, bytes) =>
                      match decode_bytes 239 bytes with
                      | None => None
                      | Some (broad_cast_message_value, bytes) =>
                          Some ({| trader_id := trader_id_value; action_code := action_code_value; reserved_1 := reserved_1_value; broad_cast_message_length := broad_cast_message_length_value; broad_cast_message := broad_cast_message_value |}, bytes)
                      end
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 249.
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
      rewrite decode_encode_uint by exact bound_2.
      rewrite decode_encode_uint by exact bound_3.
      rewrite decode_encode_bytes by exact bound_4.
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

  Module ContractDesc2.

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

  End ContractDesc2.

  Module ReportTrailerBody.

    (** Report Trailer Body *)
    Record t := {
      number_of_packets : N;
      reserved_1 : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (number_of_packets record < 256 ^ N.of_nat 4)%N /\
      (reserved_1 record < 256 ^ N.of_nat 1)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 4 (number_of_packets record) ++
      encode_uint 1 (reserved_1 record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 4 bytes with
      | None => None
      | Some (number_of_packets_value, bytes) =>
          match decode_uint 1 bytes with
          | None => None
          | Some (reserved_1_value, bytes) =>
              Some ({| number_of_packets := number_of_packets_value; reserved_1 := reserved_1_value |}, bytes)
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

  End ReportTrailerBody.

  Module ContractDesc3.

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

  End ContractDesc3.

  Module MktIndex.

    (** MKT_INDEX *)
    Record t := {
      market_opening_index : N;
      market_high_index : N;
      market_low_index : N;
      market_closing_index : N;
      market_start_index : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (market_opening_index record < 256 ^ N.of_nat 2)%N /\
      (market_high_index record < 256 ^ N.of_nat 2)%N /\
      (market_low_index record < 256 ^ N.of_nat 2)%N /\
      (market_closing_index record < 256 ^ N.of_nat 2)%N /\
      (market_start_index record < 256 ^ N.of_nat 2)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 2 (market_opening_index record) ++
      encode_uint 2 (market_high_index record) ++
      encode_uint 2 (market_low_index record) ++
      encode_uint 2 (market_closing_index record) ++
      encode_uint 2 (market_start_index record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 2 bytes with
      | None => None
      | Some (market_opening_index_value, bytes) =>
          match decode_uint 2 bytes with
          | None => None
          | Some (market_high_index_value, bytes) =>
              match decode_uint 2 bytes with
              | None => None
              | Some (market_low_index_value, bytes) =>
                  match decode_uint 2 bytes with
                  | None => None
                  | Some (market_closing_index_value, bytes) =>
                      match decode_uint 2 bytes with
                      | None => None
                      | Some (market_start_index_value, bytes) =>
                          Some ({| market_opening_index := market_opening_index_value; market_high_index := market_high_index_value; market_low_index := market_low_index_value; market_closing_index := market_closing_index_value; market_start_index := market_start_index_value |}, bytes)
                      end
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 10.
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

  End MktIndex.

  Module MarketIndexReportMessage.

    (** Bhavcopy market index report *)
    Record t := {
      message_type : list byte;
      index_name : list byte;
      mkt_index : MktIndex.t;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (message_type record) = 1 /\
      Datatypes.length (index_name record) = 15 /\
      MktIndex.bounded (mkt_index record).

    Definition encode (record : t) : list byte :=
      encode_bytes 1 (message_type record) ++
      encode_bytes 15 (index_name record) ++
      MktIndex.encode (mkt_index record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 1 bytes with
      | None => None
      | Some (message_type_value, bytes) =>
          match decode_bytes 15 bytes with
          | None => None
          | Some (index_name_value, bytes) =>
              match MktIndex.decode bytes with
              | None => None
              | Some (mkt_index_value, bytes) =>
                  Some ({| message_type := message_type_value; index_name := index_name_value; mkt_index := mkt_index_value |}, bytes)
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 26.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_bytes_length, !MktIndex.encode_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 [bound_1 bound_2]].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_bytes by exact bound_0.
      rewrite decode_encode_bytes by exact bound_1.
      rewrite MktIndex.decode_encode by exact bound_2.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec) | apply MktIndex.eq_dec]. Defined.

  End MarketIndexReportMessage.

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

  Module ReportTrailerBody2.

    (** Report Trailer Body *)
    Record t := {
      number_of_packets : N;
      reserved_1 : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (number_of_packets record < 256 ^ N.of_nat 4)%N /\
      (reserved_1 record < 256 ^ N.of_nat 1)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 4 (number_of_packets record) ++
      encode_uint 1 (reserved_1 record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 4 bytes with
      | None => None
      | Some (number_of_packets_value, bytes) =>
          match decode_uint 1 bytes with
          | None => None
          | Some (reserved_1_value, bytes) =>
              Some ({| number_of_packets := number_of_packets_value; reserved_1 := reserved_1_value |}, bytes)
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

  End ReportTrailerBody2.

  Module IndexDetails.

    (** INDEX_DETAILS *)
    Record t := {
      token : N;
      name : list byte;
      open : N;
      high : N;
      low : N;
      last : N;
      close : N;
      prev_close : N;
      life_high : N;
      life_low : N;
      filler_4 : N;
      filler_2 : N;
      filler_3 : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (token record < 256 ^ N.of_nat 4)%N /\
      Datatypes.length (name record) = 50 /\
      (open record < 256 ^ N.of_nat 4)%N /\
      (high record < 256 ^ N.of_nat 4)%N /\
      (low record < 256 ^ N.of_nat 4)%N /\
      (last record < 256 ^ N.of_nat 4)%N /\
      (close record < 256 ^ N.of_nat 4)%N /\
      (prev_close record < 256 ^ N.of_nat 4)%N /\
      (life_high record < 256 ^ N.of_nat 4)%N /\
      (life_low record < 256 ^ N.of_nat 4)%N /\
      (filler_4 record < 256 ^ N.of_nat 4)%N /\
      (filler_2 record < 256 ^ N.of_nat 4)%N /\
      (filler_3 record < 256 ^ N.of_nat 4)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 4 (token record) ++
      encode_bytes 50 (name record) ++
      encode_uint 4 (open record) ++
      encode_uint 4 (high record) ++
      encode_uint 4 (low record) ++
      encode_uint 4 (last record) ++
      encode_uint 4 (close record) ++
      encode_uint 4 (prev_close record) ++
      encode_uint 4 (life_high record) ++
      encode_uint 4 (life_low record) ++
      encode_uint 4 (filler_4 record) ++
      encode_uint 4 (filler_2 record) ++
      encode_uint 4 (filler_3 record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 4 bytes with
      | None => None
      | Some (token_value, bytes) =>
          match decode_bytes 50 bytes with
          | None => None
          | Some (name_value, bytes) =>
              match decode_uint 4 bytes with
              | None => None
              | Some (open_value, bytes) =>
                  match decode_uint 4 bytes with
                  | None => None
                  | Some (high_value, bytes) =>
                      match decode_uint 4 bytes with
                      | None => None
                      | Some (low_value, bytes) =>
                          match decode_uint 4 bytes with
                          | None => None
                          | Some (last_value, bytes) =>
                              match decode_uint 4 bytes with
                              | None => None
                              | Some (close_value, bytes) =>
                                  match decode_uint 4 bytes with
                                  | None => None
                                  | Some (prev_close_value, bytes) =>
                                      match decode_uint 4 bytes with
                                      | None => None
                                      | Some (life_high_value, bytes) =>
                                          match decode_uint 4 bytes with
                                          | None => None
                                          | Some (life_low_value, bytes) =>
                                              match decode_uint 4 bytes with
                                              | None => None
                                              | Some (filler_4_value, bytes) =>
                                                  match decode_uint 4 bytes with
                                                  | None => None
                                                  | Some (filler_2_value, bytes) =>
                                                      match decode_uint 4 bytes with
                                                      | None => None
                                                      | Some (filler_3_value, bytes) =>
                                                          Some ({| token := token_value; name := name_value; open := open_value; high := high_value; low := low_value; last := last_value; close := close_value; prev_close := prev_close_value; life_high := life_high_value; life_low := life_low_value; filler_4 := filler_4_value; filler_2 := filler_2_value; filler_3 := filler_3_value |}, bytes)
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

    Theorem encode_length : forall record, Datatypes.length (encode record) = 98.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_uint_length, !encode_bytes_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 [bound_1 [bound_2 [bound_3 [bound_4 [bound_5 [bound_6 [bound_7 [bound_8 [bound_9 [bound_10 [bound_11 bound_12]]]]]]]]]]]].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_uint by exact bound_0.
      rewrite decode_encode_bytes by exact bound_1.
      rewrite decode_encode_uint by exact bound_2.
      rewrite decode_encode_uint by exact bound_3.
      rewrite decode_encode_uint by exact bound_4.
      rewrite decode_encode_uint by exact bound_5.
      rewrite decode_encode_uint by exact bound_6.
      rewrite decode_encode_uint by exact bound_7.
      rewrite decode_encode_uint by exact bound_8.
      rewrite decode_encode_uint by exact bound_9.
      rewrite decode_encode_uint by exact bound_10.
      rewrite decode_encode_uint by exact bound_11.
      rewrite decode_encode_uint by exact bound_12.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End IndexDetails.

  Module GlobalIndicesMessage.

    (** Carries the values of a global index *)
    Record t := {
      index_details : IndexDetails.t;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      IndexDetails.bounded (index_details record).

    Definition encode (record : t) : list byte :=
      IndexDetails.encode (index_details record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match IndexDetails.decode bytes with
      | None => None
      | Some (index_details_value, bytes) =>
          Some ({| index_details := index_details_value |}, bytes)
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 98.
    Proof.
      intros record. unfold encode.
      rewrite !IndexDetails.encode_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      unfold decode, encode.
      rewrite IndexDetails.decode_encode by exact bound.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply IndexDetails.eq_dec]. Defined.

  End GlobalIndicesMessage.

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

  Module CollateralUserStatusChangeResponseMessage.

    (** Confirms the collateral status change *)
    Record t := {
      user_id : N;
      col_user_bit : list byte;
      reserved_1 : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (user_id record < 256 ^ N.of_nat 4)%N /\
      Datatypes.length (col_user_bit record) = 1 /\
      (reserved_1 record < 256 ^ N.of_nat 1)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 4 (user_id record) ++
      encode_bytes 1 (col_user_bit record) ++
      encode_uint 1 (reserved_1 record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 4 bytes with
      | None => None
      | Some (user_id_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (col_user_bit_value, bytes) =>
              match decode_uint 1 bytes with
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
      rewrite decode_encode_uint by exact bound_2.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End CollateralUserStatusChangeResponseMessage.

  Module UserTradeModifyCancelStatusChangeResponseMessage.

    (** Confirms the trade modify and cancel permission change *)
    Record t := {
      user_id : N;
      trd_mod_cxl_bit : list byte;
      reserved_1 : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (user_id record < 256 ^ N.of_nat 4)%N /\
      Datatypes.length (trd_mod_cxl_bit record) = 1 /\
      (reserved_1 record < 256 ^ N.of_nat 1)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 4 (user_id record) ++
      encode_bytes 1 (trd_mod_cxl_bit record) ++
      encode_uint 1 (reserved_1 record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 4 bytes with
      | None => None
      | Some (user_id_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (trd_mod_cxl_bit_value, bytes) =>
              match decode_uint 1 bytes with
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
      rewrite decode_encode_uint by exact bound_2.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End UserTradeModifyCancelStatusChangeResponseMessage.

  Module UserAddressUnlockConfirmMessage.

    (** Confirms that the unlock request was received *)
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

    (** Approves the unlock of a user address *)
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

  Module ContractDesc4.

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

  End ContractDesc4.

  Module ContractDesc5.

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

  End ContractDesc5.

  Module ContractDesc6.

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

  End ContractDesc6.

End NseFoOrderEntryV950Server.
