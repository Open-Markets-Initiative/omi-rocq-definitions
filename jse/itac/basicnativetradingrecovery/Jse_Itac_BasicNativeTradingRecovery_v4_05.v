From Stdlib Require Import List.
From Stdlib Require Import NArith.
From Stdlib Require Import Lia.
From Stdlib Require Import Strings.Byte.
From Omi Require Import Wire.

Import ListNotations.

(** * JSE Limited Basic Native Trading Recovery

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
      - a field read in bits
  *)

Module JseItacBasicNativeTradingRecoveryV405.

  Module MessageHeader.

    (** Jse Native Trading Gateway Message Header *)
    Record t := {
      start_of_message : N;
      message_length : N;
      message_type : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (start_of_message record < 256 ^ N.of_nat 1)%N /\
      (message_length record < 256 ^ N.of_nat 2)%N /\
      Datatypes.length (message_type record) = 1.

    Definition encode (record : t) : list byte :=
      encode_uint 1 (start_of_message record) ++
      encode_uint 2 (message_length record) ++
      encode_bytes 1 (message_type record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 1 bytes with
      | None => None
      | Some (start_of_message_value, bytes) =>
          match decode_uint 2 bytes with
          | None => None
          | Some (message_length_value, bytes) =>
              match decode_bytes 1 bytes with
              | None => None
              | Some (message_type_value, bytes) =>
                  Some ({| start_of_message := start_of_message_value; message_length := message_length_value; message_type := message_type_value |}, bytes)
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 4.
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

  End MessageHeader.

  Module LogonMessage.

    (** Allows the client to login to the server. *)
    Record t := {
      comp_id : list byte;
      password : list byte;
      new_password : list byte;
      protocol_version : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (comp_id record) = 6 /\
      Datatypes.length (password record) = 25 /\
      Datatypes.length (new_password record) = 25 /\
      (protocol_version record < 256 ^ N.of_nat 4)%N.

    Definition encode (record : t) : list byte :=
      encode_bytes 6 (comp_id record) ++
      encode_bytes 25 (password record) ++
      encode_bytes 25 (new_password record) ++
      encode_uint 4 (protocol_version record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 6 bytes with
      | None => None
      | Some (comp_id_value, bytes) =>
          match decode_bytes 25 bytes with
          | None => None
          | Some (password_value, bytes) =>
              match decode_bytes 25 bytes with
              | None => None
              | Some (new_password_value, bytes) =>
                  match decode_uint 4 bytes with
                  | None => None
                  | Some (protocol_version_value, bytes) =>
                      Some ({| comp_id := comp_id_value; password := password_value; new_password := new_password_value; protocol_version := protocol_version_value |}, bytes)
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 60.
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
      rewrite decode_encode_bytes by exact bound_2.
      rewrite decode_encode_uint by exact bound_3.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End LogonMessage.

  Module LogonResponseMessage.

    (** Used by the server to accept or reject a login request. *)
    Record t := {
      reject_code : N;
      password_expiry : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (reject_code record < 256 ^ N.of_nat 4)%N /\
      (password_expiry record < 256 ^ N.of_nat 4)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 4 (reject_code record) ++
      encode_uint 4 (password_expiry record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 4 bytes with
      | None => None
      | Some (reject_code_value, bytes) =>
          match decode_uint 4 bytes with
          | None => None
          | Some (password_expiry_value, bytes) =>
              Some ({| reject_code := reject_code_value; password_expiry := password_expiry_value |}, bytes)
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
      destruct bound as [bound_0 bound_1].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_uint by exact bound_0.
      rewrite decode_encode_uint by exact bound_1.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec]. Defined.

  End LogonResponseMessage.

  Module LogoutMessage.

    (** Used by the client or server to terminate a session. *)
    Record t := {
      reason : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (reason record) = 20.

    Definition encode (record : t) : list byte :=
      encode_bytes 20 (reason record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 20 bytes with
      | None => None
      | Some (reason_value, bytes) =>
          Some ({| reason := reason_value |}, bytes)
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 20.
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

  End LogoutMessage.

  Module RejectMessage.

    (** Used by the server to reject a message that does not comply with the specifications. *)
    Record t := {
      reject_code : N;
      reject_reason : list byte;
      message_type : list byte;
      client_order_id : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (reject_code record < 256 ^ N.of_nat 4)%N /\
      Datatypes.length (reject_reason record) = 30 /\
      Datatypes.length (message_type record) = 1 /\
      Datatypes.length (client_order_id record) = 20.

    Definition encode (record : t) : list byte :=
      encode_uint 4 (reject_code record) ++
      encode_bytes 30 (reject_reason record) ++
      encode_bytes 1 (message_type record) ++
      encode_bytes 20 (client_order_id record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 4 bytes with
      | None => None
      | Some (reject_code_value, bytes) =>
          match decode_bytes 30 bytes with
          | None => None
          | Some (reject_reason_value, bytes) =>
              match decode_bytes 1 bytes with
              | None => None
              | Some (message_type_value, bytes) =>
                  match decode_bytes 20 bytes with
                  | None => None
                  | Some (client_order_id_value, bytes) =>
                      Some ({| reject_code := reject_code_value; reject_reason := reject_reason_value; message_type := message_type_value; client_order_id := client_order_id_value |}, bytes)
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 55.
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

  End RejectMessage.

  Module MissedMessageRequestMessage.

    (** Used by the client to recover missed messages through the Recovery Channel. *)
    Record t := {
      partition_id : N;
      sequence_number : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (partition_id record < 256 ^ N.of_nat 1)%N /\
      (sequence_number record < 256 ^ N.of_nat 4)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 1 (partition_id record) ++
      encode_uint 4 (sequence_number record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 1 bytes with
      | None => None
      | Some (partition_id_value, bytes) =>
          match decode_uint 4 bytes with
          | None => None
          | Some (sequence_number_value, bytes) =>
              Some ({| partition_id := partition_id_value; sequence_number := sequence_number_value |}, bytes)
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

  End MissedMessageRequestMessage.

  Module MissedMessageRequestAckMessage.

    (** Used by the server to accept or reject a request for missed messages. *)
    Record t := {
      missed_message_status : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (missed_message_status record < 256 ^ N.of_nat 1)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 1 (missed_message_status record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 1 bytes with
      | None => None
      | Some (missed_message_status_value, bytes) =>
          Some ({| missed_message_status := missed_message_status_value |}, bytes)
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

  End MissedMessageRequestAckMessage.

  Module TransmissionCompleteMessage.

    (** Used by the server to indicate that the transmission of missed messages is complete. *)
    Record t := {
      transmission_status : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (transmission_status record < 256 ^ N.of_nat 1)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 1 (transmission_status record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 1 bytes with
      | None => None
      | Some (transmission_status_value, bytes) =>
          Some ({| transmission_status := transmission_status_value |}, bytes)
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

  End TransmissionCompleteMessage.

  Module SystemStatusMessage.

    (** Disseminated in the recovery channel to indicate the status of a partition. *)
    Record t := {
      partition_id : N;
      system_status : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (partition_id record < 256 ^ N.of_nat 1)%N /\
      (system_status record < 256 ^ N.of_nat 1)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 1 (partition_id record) ++
      encode_uint 1 (system_status record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 1 bytes with
      | None => None
      | Some (partition_id_value, bytes) =>
          match decode_uint 1 bytes with
          | None => None
          | Some (system_status_value, bytes) =>
              Some ({| partition_id := partition_id_value; system_status := system_status_value |}, bytes)
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

  End SystemStatusMessage.

  Module NewsMessage.

    (** Carries a market operations announcement. *)
    Record t := {
      partition_id : N;
      sequence_number : N;
      orig_time : list byte;
      urgency : list byte;
      headline : list byte;
      text : list byte;
      instruments : list byte;
      underlyings : list byte;
      firm_list : list byte;
      user_list : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (partition_id record < 256 ^ N.of_nat 1)%N /\
      (sequence_number record < 256 ^ N.of_nat 4)%N /\
      Datatypes.length (orig_time record) = 24 /\
      Datatypes.length (urgency record) = 1 /\
      Datatypes.length (headline record) = 100 /\
      Datatypes.length (text record) = 750 /\
      Datatypes.length (instruments record) = 100 /\
      Datatypes.length (underlyings record) = 100 /\
      Datatypes.length (firm_list record) = 54 /\
      Datatypes.length (user_list record) = 54.

    Definition encode (record : t) : list byte :=
      encode_uint 1 (partition_id record) ++
      encode_uint 4 (sequence_number record) ++
      encode_bytes 24 (orig_time record) ++
      encode_bytes 1 (urgency record) ++
      encode_bytes 100 (headline record) ++
      encode_bytes 750 (text record) ++
      encode_bytes 100 (instruments record) ++
      encode_bytes 100 (underlyings record) ++
      encode_bytes 54 (firm_list record) ++
      encode_bytes 54 (user_list record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 1 bytes with
      | None => None
      | Some (partition_id_value, bytes) =>
          match decode_uint 4 bytes with
          | None => None
          | Some (sequence_number_value, bytes) =>
              match decode_bytes 24 bytes with
              | None => None
              | Some (orig_time_value, bytes) =>
                  match decode_bytes 1 bytes with
                  | None => None
                  | Some (urgency_value, bytes) =>
                      match decode_bytes 100 bytes with
                      | None => None
                      | Some (headline_value, bytes) =>
                          match decode_bytes 750 bytes with
                          | None => None
                          | Some (text_value, bytes) =>
                              match decode_bytes 100 bytes with
                              | None => None
                              | Some (instruments_value, bytes) =>
                                  match decode_bytes 100 bytes with
                                  | None => None
                                  | Some (underlyings_value, bytes) =>
                                      match decode_bytes 54 bytes with
                                      | None => None
                                      | Some (firm_list_value, bytes) =>
                                          match decode_bytes 54 bytes with
                                          | None => None
                                          | Some (user_list_value, bytes) =>
                                              Some ({| partition_id := partition_id_value; sequence_number := sequence_number_value; orig_time := orig_time_value; urgency := urgency_value; headline := headline_value; text := text_value; instruments := instruments_value; underlyings := underlyings_value; firm_list := firm_list_value; user_list := user_list_value |}, bytes)
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

    Theorem encode_length : forall record, Datatypes.length (encode record) = 1188.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_uint_length, !encode_bytes_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 [bound_1 [bound_2 [bound_3 [bound_4 [bound_5 [bound_6 [bound_7 [bound_8 bound_9]]]]]]]]].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_uint by exact bound_0.
      rewrite decode_encode_uint by exact bound_1.
      rewrite decode_encode_bytes by exact bound_2.
      rewrite decode_encode_bytes by exact bound_3.
      rewrite decode_encode_bytes by exact bound_4.
      rewrite decode_encode_bytes by exact bound_5.
      rewrite decode_encode_bytes by exact bound_6.
      rewrite decode_encode_bytes by exact bound_7.
      rewrite decode_encode_bytes by exact bound_8.
      rewrite decode_encode_bytes by exact bound_9.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End NewsMessage.

End JseItacBasicNativeTradingRecoveryV405.
