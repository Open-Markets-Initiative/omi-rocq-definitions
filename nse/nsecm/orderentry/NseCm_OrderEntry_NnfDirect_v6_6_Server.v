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
      - a run counted by a field
      - a Composite rule
      - the dispatch that chooses a message by its type
      - a field read in bits
      - a length prefix framing what follows
  *)

Module NseCmOrderEntryV66Server.

  Module PacketHeader.

    (** Direct interface twenty two byte packet header *)
    Record t := {
      packet_length : N;
      packet_sequence_number : N;
      checksum : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (packet_length record < 256 ^ N.of_nat 2)%N /\
      (packet_sequence_number record < 256 ^ N.of_nat 4)%N /\
      Datatypes.length (checksum record) = 16.

    Definition encode (record : t) : list byte :=
      encode_uint 2 (packet_length record) ++
      encode_uint 4 (packet_sequence_number record) ++
      encode_bytes 16 (checksum record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 2 bytes with
      | None => None
      | Some (packet_length_value, bytes) =>
          match decode_uint 4 bytes with
          | None => None
          | Some (packet_sequence_number_value, bytes) =>
              match decode_bytes 16 bytes with
              | None => None
              | Some (checksum_value, bytes) =>
                  Some ({| packet_length := packet_length_value; packet_sequence_number := packet_sequence_number_value; checksum := checksum_value |}, bytes)
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 22.
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

  End PacketHeader.

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

  Module CancelOnLogoutStatusResponseMessage.

    (** Sent as COL_USER_STATUS_CHANGE _OUT *)
    Record t := {
      user_id : N;
      colo_user_bit : list byte;
      reserved_1 : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (user_id record < 256 ^ N.of_nat 4)%N /\
      Datatypes.length (colo_user_bit record) = 1 /\
      (reserved_1 record < 256 ^ N.of_nat 1)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 4 (user_id record) ++
      encode_bytes 1 (colo_user_bit record) ++
      encode_uint 1 (reserved_1 record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 4 bytes with
      | None => None
      | Some (user_id_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (colo_user_bit_value, bytes) =>
              match decode_uint 1 bytes with
              | None => None
              | Some (reserved_1_value, bytes) =>
                  Some ({| user_id := user_id_value; colo_user_bit := colo_user_bit_value; reserved_1 := reserved_1_value |}, bytes)
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

  End CancelOnLogoutStatusResponseMessage.

  Module SecInfo.

    (** SEC_INFO *)
    Record t := {
      symbol : list byte;
      series : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (symbol record) = 10 /\
      Datatypes.length (series record) = 2.

    Definition encode (record : t) : list byte :=
      encode_bytes 10 (symbol record) ++
      encode_bytes 2 (series record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 10 bytes with
      | None => None
      | Some (symbol_value, bytes) =>
          match decode_bytes 2 bytes with
          | None => None
          | Some (series_value, bytes) =>
              Some ({| symbol := symbol_value; series := series_value |}, bytes)
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 12.
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

  End SecInfo.

  Module ErrorResponseMessage.

    (** Sent as ERROR_RESPONSE_OUT *)
    Record t := {
      sec_info : SecInfo.t;
      error_message : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      SecInfo.bounded (sec_info record) /\
      Datatypes.length (error_message record) = 128.

    Definition encode (record : t) : list byte :=
      SecInfo.encode (sec_info record) ++
      encode_bytes 128 (error_message record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match SecInfo.decode bytes with
      | None => None
      | Some (sec_info_value, bytes) =>
          match decode_bytes 128 bytes with
          | None => None
          | Some (error_message_value, bytes) =>
              Some ({| sec_info := sec_info_value; error_message := error_message_value |}, bytes)
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 140.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !SecInfo.encode_length, !encode_bytes_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 bound_1].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite SecInfo.decode_encode by exact bound_0.
      rewrite decode_encode_bytes by exact bound_1.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec) | apply SecInfo.eq_dec]. Defined.

  End ErrorResponseMessage.

  Module SecureBoxRegistrationRequestMessage.

    (** Sent as SECURE_BOX_REGISTRATION_REQUE *)
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

  End SecureBoxRegistrationRequestMessage.

  Module BoxSignOnResponseMessage.

    (** Sent as BOX_SIGN_ON_REQUEST_OUT *)
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

  End BoxSignOnResponseMessage.

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

  Module ControlMessageToTraderMessage.

    (** Sent as CTRL_MSG_TO_TRADER *)
    Record t := {
      trader_id : N;
      action_code : list byte;
      reserved_1 : N;
      msg_length : N;
      msg : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (trader_id record < 256 ^ N.of_nat 4)%N /\
      Datatypes.length (action_code record) = 3 /\
      (reserved_1 record < 256 ^ N.of_nat 1)%N /\
      (msg_length record < 256 ^ N.of_nat 2)%N /\
      Datatypes.length (msg record) = 240.

    Definition encode (record : t) : list byte :=
      encode_uint 4 (trader_id record) ++
      encode_bytes 3 (action_code record) ++
      encode_uint 1 (reserved_1 record) ++
      encode_uint 2 (msg_length record) ++
      encode_bytes 240 (msg record).

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
                  | Some (msg_length_value, bytes) =>
                      match decode_bytes 240 bytes with
                      | None => None
                      | Some (msg_value, bytes) =>
                          Some ({| trader_id := trader_id_value; action_code := action_code_value; reserved_1 := reserved_1_value; msg_length := msg_length_value; msg := msg_value |}, bytes)
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

  Module SecInfo2.

    (** SEC_INFO *)
    Record t := {
      symbol : list byte;
      series : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (symbol record) = 10 /\
      Datatypes.length (series record) = 2.

    Definition encode (record : t) : list byte :=
      encode_bytes 10 (symbol record) ++
      encode_bytes 2 (series record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 10 bytes with
      | None => None
      | Some (symbol_value, bytes) =>
          match decode_bytes 2 bytes with
          | None => None
          | Some (series_value, bytes) =>
              Some ({| symbol := symbol_value; series := series_value |}, bytes)
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 12.
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

  End SecInfo2.

  Module SecInfo3.

    (** SEC_INFO *)
    Record t := {
      symbol : list byte;
      series : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (symbol record) = 10 /\
      Datatypes.length (series record) = 2.

    Definition encode (record : t) : list byte :=
      encode_bytes 10 (symbol record) ++
      encode_bytes 2 (series record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 10 bytes with
      | None => None
      | Some (symbol_value, bytes) =>
          match decode_bytes 2 bytes with
          | None => None
          | Some (series_value, bytes) =>
              Some ({| symbol := symbol_value; series := series_value |}, bytes)
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 12.
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

  End SecInfo3.

  Module SecInfo4.

    (** SEC_INFO *)
    Record t := {
      symbol : list byte;
      series : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (symbol record) = 10 /\
      Datatypes.length (series record) = 2.

    Definition encode (record : t) : list byte :=
      encode_bytes 10 (symbol record) ++
      encode_bytes 2 (series record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 10 bytes with
      | None => None
      | Some (symbol_value, bytes) =>
          match decode_bytes 2 bytes with
          | None => None
          | Some (series_value, bytes) =>
              Some ({| symbol := symbol_value; series := series_value |}, bytes)
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 12.
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

  End SecInfo4.

  Module PasswordResetOutMessage.

    (** Sent as RESET_PASSWORD_OUT *)
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

  End PasswordResetOutMessage.

  Module SecInfo5.

    (** SEC_INFO *)
    Record t := {
      symbol : list byte;
      series : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (symbol record) = 10 /\
      Datatypes.length (series record) = 2.

    Definition encode (record : t) : list byte :=
      encode_bytes 10 (symbol record) ++
      encode_bytes 2 (series record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 10 bytes with
      | None => None
      | Some (symbol_value, bytes) =>
          match decode_bytes 2 bytes with
          | None => None
          | Some (series_value, bytes) =>
              Some ({| symbol := symbol_value; series := series_value |}, bytes)
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 12.
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

  End SecInfo5.

  Module SecInfo6.

    (** SEC_INFO *)
    Record t := {
      symbol : list byte;
      series : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (symbol record) = 10 /\
      Datatypes.length (series record) = 2.

    Definition encode (record : t) : list byte :=
      encode_bytes 10 (symbol record) ++
      encode_bytes 2 (series record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 10 bytes with
      | None => None
      | Some (symbol_value, bytes) =>
          match decode_bytes 2 bytes with
          | None => None
          | Some (series_value, bytes) =>
              Some ({| symbol := symbol_value; series := series_value |}, bytes)
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 12.
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

  End SecInfo6.

  Module TradeInquiryOutMessage.

    (** Sent as TRADE_ERROR, TRADE_CANCEL_OUT *)
    Record t := {
      sec_info : SecInfo6.t;
      fill_number : N;
      fill_qty : N;
      fill_price : N;
      market_type : N;
      new_volume : N;
      reserved_24 : list byte;
      buy_broker_id : list byte;
      sell_broker_id : list byte;
      trader_id : N;
      requested_by : N;
      buy_account_number : list byte;
      sell_account_number : list byte;
      buy_pan : list byte;
      sell_pan : list byte;
      reserved_60 : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      SecInfo6.bounded (sec_info record) /\
      (fill_number record < 256 ^ N.of_nat 4)%N /\
      (fill_qty record < 256 ^ N.of_nat 4)%N /\
      (fill_price record < 256 ^ N.of_nat 4)%N /\
      (market_type record < 256 ^ N.of_nat 2)%N /\
      (new_volume record < 256 ^ N.of_nat 4)%N /\
      Datatypes.length (reserved_24 record) = 24 /\
      Datatypes.length (buy_broker_id record) = 5 /\
      Datatypes.length (sell_broker_id record) = 5 /\
      (trader_id record < 256 ^ N.of_nat 4)%N /\
      (requested_by record < 256 ^ N.of_nat 2)%N /\
      Datatypes.length (buy_account_number record) = 10 /\
      Datatypes.length (sell_account_number record) = 10 /\
      Datatypes.length (buy_pan record) = 10 /\
      Datatypes.length (sell_pan record) = 10 /\
      Datatypes.length (reserved_60 record) = 60.

    Definition encode (record : t) : list byte :=
      SecInfo6.encode (sec_info record) ++
      encode_uint 4 (fill_number record) ++
      encode_uint 4 (fill_qty record) ++
      encode_uint 4 (fill_price record) ++
      encode_uint 2 (market_type record) ++
      encode_uint 4 (new_volume record) ++
      encode_bytes 24 (reserved_24 record) ++
      encode_bytes 5 (buy_broker_id record) ++
      encode_bytes 5 (sell_broker_id record) ++
      encode_uint 4 (trader_id record) ++
      encode_uint 2 (requested_by record) ++
      encode_bytes 10 (buy_account_number record) ++
      encode_bytes 10 (sell_account_number record) ++
      encode_bytes 10 (buy_pan record) ++
      encode_bytes 10 (sell_pan record) ++
      encode_bytes 60 (reserved_60 record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match SecInfo6.decode bytes with
      | None => None
      | Some (sec_info_value, bytes) =>
          match decode_uint 4 bytes with
          | None => None
          | Some (fill_number_value, bytes) =>
              match decode_uint 4 bytes with
              | None => None
              | Some (fill_qty_value, bytes) =>
                  match decode_uint 4 bytes with
                  | None => None
                  | Some (fill_price_value, bytes) =>
                      match decode_uint 2 bytes with
                      | None => None
                      | Some (market_type_value, bytes) =>
                          match decode_uint 4 bytes with
                          | None => None
                          | Some (new_volume_value, bytes) =>
                              match decode_bytes 24 bytes with
                              | None => None
                              | Some (reserved_24_value, bytes) =>
                                  match decode_bytes 5 bytes with
                                  | None => None
                                  | Some (buy_broker_id_value, bytes) =>
                                      match decode_bytes 5 bytes with
                                      | None => None
                                      | Some (sell_broker_id_value, bytes) =>
                                          match decode_uint 4 bytes with
                                          | None => None
                                          | Some (trader_id_value, bytes) =>
                                              match decode_uint 2 bytes with
                                              | None => None
                                              | Some (requested_by_value, bytes) =>
                                                  match decode_bytes 10 bytes with
                                                  | None => None
                                                  | Some (buy_account_number_value, bytes) =>
                                                      match decode_bytes 10 bytes with
                                                      | None => None
                                                      | Some (sell_account_number_value, bytes) =>
                                                          match decode_bytes 10 bytes with
                                                          | None => None
                                                          | Some (buy_pan_value, bytes) =>
                                                              match decode_bytes 10 bytes with
                                                              | None => None
                                                              | Some (sell_pan_value, bytes) =>
                                                                  match decode_bytes 60 bytes with
                                                                  | None => None
                                                                  | Some (reserved_60_value, bytes) =>
                                                                      Some ({| sec_info := sec_info_value; fill_number := fill_number_value; fill_qty := fill_qty_value; fill_price := fill_price_value; market_type := market_type_value; new_volume := new_volume_value; reserved_24 := reserved_24_value; buy_broker_id := buy_broker_id_value; sell_broker_id := sell_broker_id_value; trader_id := trader_id_value; requested_by := requested_by_value; buy_account_number := buy_account_number_value; sell_account_number := sell_account_number_value; buy_pan := buy_pan_value; sell_pan := sell_pan_value; reserved_60 := reserved_60_value |}, bytes)
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

    Theorem encode_length : forall record, Datatypes.length (encode record) = 170.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !SecInfo6.encode_length, !encode_uint_length, !encode_bytes_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 [bound_1 [bound_2 [bound_3 [bound_4 [bound_5 [bound_6 [bound_7 [bound_8 [bound_9 [bound_10 [bound_11 [bound_12 [bound_13 [bound_14 bound_15]]]]]]]]]]]]]]].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite SecInfo6.decode_encode by exact bound_0.
      rewrite decode_encode_uint by exact bound_1.
      rewrite decode_encode_uint by exact bound_2.
      rewrite decode_encode_uint by exact bound_3.
      rewrite decode_encode_uint by exact bound_4.
      rewrite decode_encode_uint by exact bound_5.
      rewrite decode_encode_bytes by exact bound_6.
      rewrite decode_encode_bytes by exact bound_7.
      rewrite decode_encode_bytes by exact bound_8.
      rewrite decode_encode_uint by exact bound_9.
      rewrite decode_encode_uint by exact bound_10.
      rewrite decode_encode_bytes by exact bound_11.
      rewrite decode_encode_bytes by exact bound_12.
      rewrite decode_encode_bytes by exact bound_13.
      rewrite decode_encode_bytes by exact bound_14.
      rewrite decode_encode_bytes by exact bound_15.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec) | apply SecInfo6.eq_dec]. Defined.

  End TradeInquiryOutMessage.

  Module UpdateLocalDatabaseHeaderMessage.

    (** Sent as UPDATE_LOCALDB_HEADER *)
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

    (** Sent as UPDATE_LOCALDB_TRAILER *)
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

  Module UserUnlockApprovalRejectionMessage.

    (** Sent as USER_ADDR_UNLOCK_APPROVE_OUT, USER_ADDR_UNLOCK_REJECT_OUT *)
    Record t := {
      user_id : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (user_id record < 256 ^ N.of_nat 4)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 4 (user_id record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 4 bytes with
      | None => None
      | Some (user_id_value, bytes) =>
          Some ({| user_id := user_id_value |}, bytes)
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 4.
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

  End UserUnlockApprovalRejectionMessage.

  Module UserUnlockRequestedResponseMessage.

    (** Sent as USER_ADDR_UNLOCK_OUT *)
    Record t := {
      user_id : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (user_id record < 256 ^ N.of_nat 4)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 4 (user_id record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 4 bytes with
      | None => None
      | Some (user_id_value, bytes) =>
          Some ({| user_id := user_id_value |}, bytes)
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 4.
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

  End UserUnlockRequestedResponseMessage.

  Module TradeModificationCancellationStatusResponseMessage.

    (** Sent as TRD_MOD_CXL_STATUS_CHANGE _OUT *)
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

  End TradeModificationCancellationStatusResponseMessage.

  Module InnerHeader.

    (** Forty byte header prefacing each downloaded record *)
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

End NseCmOrderEntryV66Server.
