From Stdlib Require Import List.
From Stdlib Require Import NArith.
From Stdlib Require Import Lia.
From Stdlib Require Import Strings.Byte.
From Omi Require Import Wire.

Import ListNotations.

(** * Chicago Board Options Exchange Gap Request Proxy

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
      - a Reassemble rule
      - a run filling what frames it
  *)

Module NeoEquitiesGapRequestProxyV1013.

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

  Module LoginMessage.

    (** The first message the Member process sends to the GRP after connection to the GRP is established. Failure to login before sending any other message type will result in the connection being dropped by the GRP. *)
    Record t := {
      session_sub_id : list byte;
      username : list byte;
      filler : list byte;
      password : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (session_sub_id record) = 4 /\
      Datatypes.length (username record) = 4 /\
      Datatypes.length (filler record) = 2 /\
      Datatypes.length (password record) = 10.

    Definition encode (record : t) : list byte :=
      encode_bytes 4 (session_sub_id record) ++
      encode_bytes 4 (username record) ++
      encode_bytes 2 (filler record) ++
      encode_bytes 10 (password record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 4 bytes with
      | None => None
      | Some (session_sub_id_value, bytes) =>
          match decode_bytes 4 bytes with
          | None => None
          | Some (username_value, bytes) =>
              match decode_bytes 2 bytes with
              | None => None
              | Some (filler_value, bytes) =>
                  match decode_bytes 10 bytes with
                  | None => None
                  | Some (password_value, bytes) =>
                      Some ({| session_sub_id := session_sub_id_value; username := username_value; filler := filler_value; password := password_value |}, bytes)
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 20.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_bytes_length. reflexivity.
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
      rewrite decode_encode_bytes by exact bound_3.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End LoginMessage.

  Module LoginResponseMessage.

    (** Sent by the GRP to the Member process in response to a Login message. The Status field reflects an accepted login or the reason the session was not accepted. If login fails, the connection will be dropped after the Login Response message is sent. *)
    Record t := {
      login_response_status : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (login_response_status record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 1 (login_response_status record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 1 bytes with
      | None => None
      | Some (login_response_status_value, bytes) =>
          Some ({| login_response_status := login_response_status_value |}, bytes)
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 1.
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

  End LoginResponseMessage.

  Module GapRequestMessage.

    (** Used by a Member's process to request retransmission of a sequenced message (or messages) by one of Cboe Canada's gap servers. *)
    Record t := {
      gap_unit : N;
      gap_sequence : N;
      count : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (gap_unit record < 256 ^ N.of_nat 1)%N /\
      (gap_sequence record < 256 ^ N.of_nat 4)%N /\
      (count record < 256 ^ N.of_nat 2)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 1 (gap_unit record) ++
      encode_uint 4 (gap_sequence record) ++
      encode_uint 2 (count record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 1 bytes with
      | None => None
      | Some (gap_unit_value, bytes) =>
          match decode_uint 4 bytes with
          | None => None
          | Some (gap_sequence_value, bytes) =>
              match decode_uint 2 bytes with
              | None => None
              | Some (count_value, bytes) =>
                  Some ({| gap_unit := gap_unit_value; gap_sequence := gap_sequence_value; count := count_value |}, bytes)
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 7.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_uint_length. reflexivity.
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
      rewrite decode_encode_uint by exact bound_2.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec]. Defined.

  End GapRequestMessage.

  Module GapResponseMessage.

    (** Sent by the GRP in response to a Gap Request message. The Unit and Sequence fields will match the values supplied in the Gap Request message. A Gap Response message, with a Status of Accepted or reason for failure, will be sent for each Gap Request message received by the GRP. *)
    Record t := {
      gap_unit : N;
      gap_sequence : N;
      count : N;
      gap_response_status : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (gap_unit record < 256 ^ N.of_nat 1)%N /\
      (gap_sequence record < 256 ^ N.of_nat 4)%N /\
      (count record < 256 ^ N.of_nat 2)%N /\
      Datatypes.length (gap_response_status record) = 1.

    Definition encode (record : t) : list byte :=
      encode_uint 1 (gap_unit record) ++
      encode_uint 4 (gap_sequence record) ++
      encode_uint 2 (count record) ++
      encode_bytes 1 (gap_response_status record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 1 bytes with
      | None => None
      | Some (gap_unit_value, bytes) =>
          match decode_uint 4 bytes with
          | None => None
          | Some (gap_sequence_value, bytes) =>
              match decode_uint 2 bytes with
              | None => None
              | Some (count_value, bytes) =>
                  match decode_bytes 1 bytes with
                  | None => None
                  | Some (gap_response_status_value, bytes) =>
                      Some ({| gap_unit := gap_unit_value; gap_sequence := gap_sequence_value; count := count_value; gap_response_status := gap_response_status_value |}, bytes)
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
      rewrite decode_encode_uint by exact bound_2.
      rewrite decode_encode_bytes by exact bound_3.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End GapResponseMessage.

End NeoEquitiesGapRequestProxyV1013.
