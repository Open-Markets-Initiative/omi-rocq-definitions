From Stdlib Require Import List.
From Stdlib Require Import NArith.
From Stdlib Require Import Lia.
From Stdlib Require Import Strings.Byte.
From Omi Require Import Wire.

Import ListNotations.

(** * Miami International Holdings Express Interface

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
      - a length prefix framing what follows
      - a field read in bits
      - a run counted by a field
  *)

Module OnyxFuturesExpressInterfaceV10C.

  Module SesmPacketHeader.

    (** SesM packet header *)
    Record t := {
      sesm_packet_length : N;
      sesm_packet_type : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (sesm_packet_length record < 256 ^ N.of_nat 2)%N /\
      Datatypes.length (sesm_packet_type record) = 1.

    Definition encode (record : t) : list byte :=
      encode_uint 2 (sesm_packet_length record) ++
      encode_bytes 1 (sesm_packet_type record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 2 bytes with
      | None => None
      | Some (sesm_packet_length_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (sesm_packet_type_value, bytes) =>
              Some ({| sesm_packet_length := sesm_packet_length_value; sesm_packet_type := sesm_packet_type_value |}, bytes)
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 3.
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

  End SesmPacketHeader.

  Module NewOrderResponseMessage.

    (** An acknowledgement for a New Order Request accepted by MIAX Futures Onyx *)
    Record t := {
      matching_engine : N;
      mp_id : list byte;
      client_order_id : list byte;
      instrument_id_binary_u_4 : N;
      order_id : N;
      status : list byte;
      reserved_10 : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (matching_engine record < 256 ^ N.of_nat 8)%N /\
      Datatypes.length (mp_id record) = 5 /\
      Datatypes.length (client_order_id record) = 20 /\
      (instrument_id_binary_u_4 record < 256 ^ N.of_nat 4)%N /\
      (order_id record < 256 ^ N.of_nat 8)%N /\
      Datatypes.length (status record) = 1 /\
      Datatypes.length (reserved_10 record) = 10.

    Definition encode (record : t) : list byte :=
      encode_uint 8 (matching_engine record) ++
      encode_bytes 5 (mp_id record) ++
      encode_bytes 20 (client_order_id record) ++
      encode_uint 4 (instrument_id_binary_u_4 record) ++
      encode_uint 8 (order_id record) ++
      encode_bytes 1 (status record) ++
      encode_bytes 10 (reserved_10 record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 8 bytes with
      | None => None
      | Some (matching_engine_value, bytes) =>
          match decode_bytes 5 bytes with
          | None => None
          | Some (mp_id_value, bytes) =>
              match decode_bytes 20 bytes with
              | None => None
              | Some (client_order_id_value, bytes) =>
                  match decode_uint 4 bytes with
                  | None => None
                  | Some (instrument_id_binary_u_4_value, bytes) =>
                      match decode_uint 8 bytes with
                      | None => None
                      | Some (order_id_value, bytes) =>
                          match decode_bytes 1 bytes with
                          | None => None
                          | Some (status_value, bytes) =>
                              match decode_bytes 10 bytes with
                              | None => None
                              | Some (reserved_10_value, bytes) =>
                                  Some ({| matching_engine := matching_engine_value; mp_id := mp_id_value; client_order_id := client_order_id_value; instrument_id_binary_u_4 := instrument_id_binary_u_4_value; order_id := order_id_value; status := status_value; reserved_10 := reserved_10_value |}, bytes)
                              end
                          end
                      end
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 56.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_uint_length, !encode_bytes_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 [bound_1 [bound_2 [bound_3 [bound_4 [bound_5 bound_6]]]]]].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_uint by exact bound_0.
      rewrite decode_encode_bytes by exact bound_1.
      rewrite decode_encode_bytes by exact bound_2.
      rewrite decode_encode_uint by exact bound_3.
      rewrite decode_encode_uint by exact bound_4.
      rewrite decode_encode_bytes by exact bound_5.
      rewrite decode_encode_bytes by exact bound_6.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End NewOrderResponseMessage.

  Module ModifyOrderResponse.

    (** Acknowledgement for a Modify Order Request accepted by MIAX Futures Onyx *)
    Record t := {
      matching_engine_time : N;
      mp_id : list byte;
      client_order_id : list byte;
      original_client_order_id : list byte;
      instrument_id_binary_u_4 : N;
      order_id : N;
      leaves_qty : N;
      status : list byte;
      reserved_10 : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (matching_engine_time record < 256 ^ N.of_nat 8)%N /\
      Datatypes.length (mp_id record) = 5 /\
      Datatypes.length (client_order_id record) = 20 /\
      Datatypes.length (original_client_order_id record) = 20 /\
      (instrument_id_binary_u_4 record < 256 ^ N.of_nat 4)%N /\
      (order_id record < 256 ^ N.of_nat 8)%N /\
      (leaves_qty record < 256 ^ N.of_nat 4)%N /\
      Datatypes.length (status record) = 1 /\
      Datatypes.length (reserved_10 record) = 10.

    Definition encode (record : t) : list byte :=
      encode_uint 8 (matching_engine_time record) ++
      encode_bytes 5 (mp_id record) ++
      encode_bytes 20 (client_order_id record) ++
      encode_bytes 20 (original_client_order_id record) ++
      encode_uint 4 (instrument_id_binary_u_4 record) ++
      encode_uint 8 (order_id record) ++
      encode_uint 4 (leaves_qty record) ++
      encode_bytes 1 (status record) ++
      encode_bytes 10 (reserved_10 record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 8 bytes with
      | None => None
      | Some (matching_engine_time_value, bytes) =>
          match decode_bytes 5 bytes with
          | None => None
          | Some (mp_id_value, bytes) =>
              match decode_bytes 20 bytes with
              | None => None
              | Some (client_order_id_value, bytes) =>
                  match decode_bytes 20 bytes with
                  | None => None
                  | Some (original_client_order_id_value, bytes) =>
                      match decode_uint 4 bytes with
                      | None => None
                      | Some (instrument_id_binary_u_4_value, bytes) =>
                          match decode_uint 8 bytes with
                          | None => None
                          | Some (order_id_value, bytes) =>
                              match decode_uint 4 bytes with
                              | None => None
                              | Some (leaves_qty_value, bytes) =>
                                  match decode_bytes 1 bytes with
                                  | None => None
                                  | Some (status_value, bytes) =>
                                      match decode_bytes 10 bytes with
                                      | None => None
                                      | Some (reserved_10_value, bytes) =>
                                          Some ({| matching_engine_time := matching_engine_time_value; mp_id := mp_id_value; client_order_id := client_order_id_value; original_client_order_id := original_client_order_id_value; instrument_id_binary_u_4 := instrument_id_binary_u_4_value; order_id := order_id_value; leaves_qty := leaves_qty_value; status := status_value; reserved_10 := reserved_10_value |}, bytes)
                                      end
                                  end
                              end
                          end
                      end
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 80.
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
      rewrite decode_encode_bytes by exact bound_1.
      rewrite decode_encode_bytes by exact bound_2.
      rewrite decode_encode_bytes by exact bound_3.
      rewrite decode_encode_uint by exact bound_4.
      rewrite decode_encode_uint by exact bound_5.
      rewrite decode_encode_uint by exact bound_6.
      rewrite decode_encode_bytes by exact bound_7.
      rewrite decode_encode_bytes by exact bound_8.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End ModifyOrderResponse.

  Module CancelOrderResponse.

    (** provides response to an Order Cancel Request *)
    Record t := {
      matching_engine_time : N;
      mp_id : list byte;
      client_order_id : list byte;
      original_client_order : list byte;
      instrument_id_binary_u_4 : N;
      order_id : N;
      status : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (matching_engine_time record < 256 ^ N.of_nat 8)%N /\
      Datatypes.length (mp_id record) = 5 /\
      Datatypes.length (client_order_id record) = 20 /\
      Datatypes.length (original_client_order record) = 20 /\
      (instrument_id_binary_u_4 record < 256 ^ N.of_nat 4)%N /\
      (order_id record < 256 ^ N.of_nat 8)%N /\
      Datatypes.length (status record) = 1.

    Definition encode (record : t) : list byte :=
      encode_uint 8 (matching_engine_time record) ++
      encode_bytes 5 (mp_id record) ++
      encode_bytes 20 (client_order_id record) ++
      encode_bytes 20 (original_client_order record) ++
      encode_uint 4 (instrument_id_binary_u_4 record) ++
      encode_uint 8 (order_id record) ++
      encode_bytes 1 (status record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 8 bytes with
      | None => None
      | Some (matching_engine_time_value, bytes) =>
          match decode_bytes 5 bytes with
          | None => None
          | Some (mp_id_value, bytes) =>
              match decode_bytes 20 bytes with
              | None => None
              | Some (client_order_id_value, bytes) =>
                  match decode_bytes 20 bytes with
                  | None => None
                  | Some (original_client_order_value, bytes) =>
                      match decode_uint 4 bytes with
                      | None => None
                      | Some (instrument_id_binary_u_4_value, bytes) =>
                          match decode_uint 8 bytes with
                          | None => None
                          | Some (order_id_value, bytes) =>
                              match decode_bytes 1 bytes with
                              | None => None
                              | Some (status_value, bytes) =>
                                  Some ({| matching_engine_time := matching_engine_time_value; mp_id := mp_id_value; client_order_id := client_order_id_value; original_client_order := original_client_order_value; instrument_id_binary_u_4 := instrument_id_binary_u_4_value; order_id := order_id_value; status := status_value |}, bytes)
                              end
                          end
                      end
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 66.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_uint_length, !encode_bytes_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 [bound_1 [bound_2 [bound_3 [bound_4 [bound_5 bound_6]]]]]].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_uint by exact bound_0.
      rewrite decode_encode_bytes by exact bound_1.
      rewrite decode_encode_bytes by exact bound_2.
      rewrite decode_encode_bytes by exact bound_3.
      rewrite decode_encode_uint by exact bound_4.
      rewrite decode_encode_uint by exact bound_5.
      rewrite decode_encode_bytes by exact bound_6.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End CancelOrderResponse.

  Module MassCancelResponse.

    (** used to inform the Firm about the status of their previous Mass Cancel Request *)
    Record t := {
      matching_engine_time : N;
      mp_id : list byte;
      client_order_id : list byte;
      status : list byte;
      reserved_10 : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (matching_engine_time record < 256 ^ N.of_nat 8)%N /\
      Datatypes.length (mp_id record) = 5 /\
      Datatypes.length (client_order_id record) = 20 /\
      Datatypes.length (status record) = 1 /\
      Datatypes.length (reserved_10 record) = 10.

    Definition encode (record : t) : list byte :=
      encode_uint 8 (matching_engine_time record) ++
      encode_bytes 5 (mp_id record) ++
      encode_bytes 20 (client_order_id record) ++
      encode_bytes 1 (status record) ++
      encode_bytes 10 (reserved_10 record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 8 bytes with
      | None => None
      | Some (matching_engine_time_value, bytes) =>
          match decode_bytes 5 bytes with
          | None => None
          | Some (mp_id_value, bytes) =>
              match decode_bytes 20 bytes with
              | None => None
              | Some (client_order_id_value, bytes) =>
                  match decode_bytes 1 bytes with
                  | None => None
                  | Some (status_value, bytes) =>
                      match decode_bytes 10 bytes with
                      | None => None
                      | Some (reserved_10_value, bytes) =>
                          Some ({| matching_engine_time := matching_engine_time_value; mp_id := mp_id_value; client_order_id := client_order_id_value; status := status_value; reserved_10 := reserved_10_value |}, bytes)
                      end
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 44.
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

  End MassCancelResponse.

  Module StrategyCreationResponseMessage.

    (** response to the Strategy Creation Request *)
    Record t := {
      matching_engine_time : N;
      mp_id : list byte;
      client_order_id : list byte;
      instrument_id_string_20 : list byte;
      status : list byte;
      reserved_16 : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (matching_engine_time record < 256 ^ N.of_nat 8)%N /\
      Datatypes.length (mp_id record) = 5 /\
      Datatypes.length (client_order_id record) = 20 /\
      Datatypes.length (instrument_id_string_20 record) = 20 /\
      Datatypes.length (status record) = 1 /\
      Datatypes.length (reserved_16 record) = 16.

    Definition encode (record : t) : list byte :=
      encode_uint 8 (matching_engine_time record) ++
      encode_bytes 5 (mp_id record) ++
      encode_bytes 20 (client_order_id record) ++
      encode_bytes 20 (instrument_id_string_20 record) ++
      encode_bytes 1 (status record) ++
      encode_bytes 16 (reserved_16 record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 8 bytes with
      | None => None
      | Some (matching_engine_time_value, bytes) =>
          match decode_bytes 5 bytes with
          | None => None
          | Some (mp_id_value, bytes) =>
              match decode_bytes 20 bytes with
              | None => None
              | Some (client_order_id_value, bytes) =>
                  match decode_bytes 20 bytes with
                  | None => None
                  | Some (instrument_id_string_20_value, bytes) =>
                      match decode_bytes 1 bytes with
                      | None => None
                      | Some (status_value, bytes) =>
                          match decode_bytes 16 bytes with
                          | None => None
                          | Some (reserved_16_value, bytes) =>
                              Some ({| matching_engine_time := matching_engine_time_value; mp_id := mp_id_value; client_order_id := client_order_id_value; instrument_id_string_20 := instrument_id_string_20_value; status := status_value; reserved_16 := reserved_16_value |}, bytes)
                          end
                      end
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 70.
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
      rewrite decode_encode_bytes by exact bound_3.
      rewrite decode_encode_bytes by exact bound_4.
      rewrite decode_encode_bytes by exact bound_5.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End StrategyCreationResponseMessage.

  Module SystemStateNotificationMessage.

    (** published whenever system state events take place *)
    Record t := {
      matching_engine_time : N;
      version : list byte;
      session_id : N;
      system_status : list byte;
      reserved_8 : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (matching_engine_time record < 256 ^ N.of_nat 8)%N /\
      Datatypes.length (version record) = 8 /\
      (session_id record < 256 ^ N.of_nat 1)%N /\
      Datatypes.length (system_status record) = 1 /\
      (reserved_8 record < 256 ^ N.of_nat 8)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 8 (matching_engine_time record) ++
      encode_bytes 8 (version record) ++
      encode_uint 1 (session_id record) ++
      encode_bytes 1 (system_status record) ++
      encode_uint 8 (reserved_8 record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 8 bytes with
      | None => None
      | Some (matching_engine_time_value, bytes) =>
          match decode_bytes 8 bytes with
          | None => None
          | Some (version_value, bytes) =>
              match decode_uint 1 bytes with
              | None => None
              | Some (session_id_value, bytes) =>
                  match decode_bytes 1 bytes with
                  | None => None
                  | Some (system_status_value, bytes) =>
                      match decode_uint 8 bytes with
                      | None => None
                      | Some (reserved_8_value, bytes) =>
                          Some ({| matching_engine_time := matching_engine_time_value; version := version_value; session_id := session_id_value; system_status := system_status_value; reserved_8 := reserved_8_value |}, bytes)
                      end
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 26.
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
      rewrite decode_encode_bytes by exact bound_3.
      rewrite decode_encode_uint by exact bound_4.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End SystemStateNotificationMessage.

  Module CancelReduceSizeOrderNotification.

    (** used when Cancel Order Request is accepted by MIAX Futures Onyx or when unsolicited order cancels or order size reductions are to be notified to firms *)
    Record t := {
      matching_engine_time : N;
      mp_id : list byte;
      operator_id : list byte;
      operator_location : list byte;
      client_order_id : list byte;
      instrument_id_binary_u_4 : N;
      order_id : N;
      client_send_time : N;
      leaves_qty : N;
      cancel_reason : list byte;
      last_price : N;
      last_size : N;
      reserved_8 : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (matching_engine_time record < 256 ^ N.of_nat 8)%N /\
      Datatypes.length (mp_id record) = 5 /\
      Datatypes.length (operator_id record) = 18 /\
      Datatypes.length (operator_location record) = 6 /\
      Datatypes.length (client_order_id record) = 20 /\
      (instrument_id_binary_u_4 record < 256 ^ N.of_nat 4)%N /\
      (order_id record < 256 ^ N.of_nat 8)%N /\
      (client_send_time record < 256 ^ N.of_nat 8)%N /\
      (leaves_qty record < 256 ^ N.of_nat 4)%N /\
      Datatypes.length (cancel_reason record) = 1 /\
      (last_price record < 256 ^ N.of_nat 8)%N /\
      (last_size record < 256 ^ N.of_nat 4)%N /\
      (reserved_8 record < 256 ^ N.of_nat 8)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 8 (matching_engine_time record) ++
      encode_bytes 5 (mp_id record) ++
      encode_bytes 18 (operator_id record) ++
      encode_bytes 6 (operator_location record) ++
      encode_bytes 20 (client_order_id record) ++
      encode_uint 4 (instrument_id_binary_u_4 record) ++
      encode_uint 8 (order_id record) ++
      encode_uint 8 (client_send_time record) ++
      encode_uint 4 (leaves_qty record) ++
      encode_bytes 1 (cancel_reason record) ++
      encode_uint 8 (last_price record) ++
      encode_uint 4 (last_size record) ++
      encode_uint 8 (reserved_8 record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 8 bytes with
      | None => None
      | Some (matching_engine_time_value, bytes) =>
          match decode_bytes 5 bytes with
          | None => None
          | Some (mp_id_value, bytes) =>
              match decode_bytes 18 bytes with
              | None => None
              | Some (operator_id_value, bytes) =>
                  match decode_bytes 6 bytes with
                  | None => None
                  | Some (operator_location_value, bytes) =>
                      match decode_bytes 20 bytes with
                      | None => None
                      | Some (client_order_id_value, bytes) =>
                          match decode_uint 4 bytes with
                          | None => None
                          | Some (instrument_id_binary_u_4_value, bytes) =>
                              match decode_uint 8 bytes with
                              | None => None
                              | Some (order_id_value, bytes) =>
                                  match decode_uint 8 bytes with
                                  | None => None
                                  | Some (client_send_time_value, bytes) =>
                                      match decode_uint 4 bytes with
                                      | None => None
                                      | Some (leaves_qty_value, bytes) =>
                                          match decode_bytes 1 bytes with
                                          | None => None
                                          | Some (cancel_reason_value, bytes) =>
                                              match decode_uint 8 bytes with
                                              | None => None
                                              | Some (last_price_value, bytes) =>
                                                  match decode_uint 4 bytes with
                                                  | None => None
                                                  | Some (last_size_value, bytes) =>
                                                      match decode_uint 8 bytes with
                                                      | None => None
                                                      | Some (reserved_8_value, bytes) =>
                                                          Some ({| matching_engine_time := matching_engine_time_value; mp_id := mp_id_value; operator_id := operator_id_value; operator_location := operator_location_value; client_order_id := client_order_id_value; instrument_id_binary_u_4 := instrument_id_binary_u_4_value; order_id := order_id_value; client_send_time := client_send_time_value; leaves_qty := leaves_qty_value; cancel_reason := cancel_reason_value; last_price := last_price_value; last_size := last_size_value; reserved_8 := reserved_8_value |}, bytes)
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

    Theorem encode_length : forall record, Datatypes.length (encode record) = 102.
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
      rewrite decode_encode_bytes by exact bound_2.
      rewrite decode_encode_bytes by exact bound_3.
      rewrite decode_encode_bytes by exact bound_4.
      rewrite decode_encode_uint by exact bound_5.
      rewrite decode_encode_uint by exact bound_6.
      rewrite decode_encode_uint by exact bound_7.
      rewrite decode_encode_uint by exact bound_8.
      rewrite decode_encode_bytes by exact bound_9.
      rewrite decode_encode_uint by exact bound_10.
      rewrite decode_encode_uint by exact bound_11.
      rewrite decode_encode_uint by exact bound_12.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End CancelReduceSizeOrderNotification.

  Module OrderStatusUpdateNotification.

    (** used to notify the firms about order status updates *)
    Record t := {
      matching_engine_time : N;
      instrument_id_binary_u_4 : N;
      order_id : N;
      update_status : list byte;
      reserved_32 : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (matching_engine_time record < 256 ^ N.of_nat 8)%N /\
      (instrument_id_binary_u_4 record < 256 ^ N.of_nat 4)%N /\
      (order_id record < 256 ^ N.of_nat 8)%N /\
      Datatypes.length (update_status record) = 1 /\
      Datatypes.length (reserved_32 record) = 32.

    Definition encode (record : t) : list byte :=
      encode_uint 8 (matching_engine_time record) ++
      encode_uint 4 (instrument_id_binary_u_4 record) ++
      encode_uint 8 (order_id record) ++
      encode_bytes 1 (update_status record) ++
      encode_bytes 32 (reserved_32 record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 8 bytes with
      | None => None
      | Some (matching_engine_time_value, bytes) =>
          match decode_uint 4 bytes with
          | None => None
          | Some (instrument_id_binary_u_4_value, bytes) =>
              match decode_uint 8 bytes with
              | None => None
              | Some (order_id_value, bytes) =>
                  match decode_bytes 1 bytes with
                  | None => None
                  | Some (update_status_value, bytes) =>
                      match decode_bytes 32 bytes with
                      | None => None
                      | Some (reserved_32_value, bytes) =>
                          Some ({| matching_engine_time := matching_engine_time_value; instrument_id_binary_u_4 := instrument_id_binary_u_4_value; order_id := order_id_value; update_status := update_status_value; reserved_32 := reserved_32_value |}, bytes)
                      end
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 53.
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
      rewrite decode_encode_uint by exact bound_1.
      rewrite decode_encode_uint by exact bound_2.
      rewrite decode_encode_bytes by exact bound_3.
      rewrite decode_encode_bytes by exact bound_4.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End OrderStatusUpdateNotification.

  Module NewOrderResponseMessage2.

    (** An acknowledgement for a New Order Request accepted by MIAX Futures Onyx *)
    Record t := {
      matching_engine : N;
      mp_id : list byte;
      client_order_id : list byte;
      instrument_id_binary_u_4 : N;
      order_id : N;
      status : list byte;
      reserved_10 : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (matching_engine record < 256 ^ N.of_nat 8)%N /\
      Datatypes.length (mp_id record) = 5 /\
      Datatypes.length (client_order_id record) = 20 /\
      (instrument_id_binary_u_4 record < 256 ^ N.of_nat 4)%N /\
      (order_id record < 256 ^ N.of_nat 8)%N /\
      Datatypes.length (status record) = 1 /\
      Datatypes.length (reserved_10 record) = 10.

    Definition encode (record : t) : list byte :=
      encode_uint 8 (matching_engine record) ++
      encode_bytes 5 (mp_id record) ++
      encode_bytes 20 (client_order_id record) ++
      encode_uint 4 (instrument_id_binary_u_4 record) ++
      encode_uint 8 (order_id record) ++
      encode_bytes 1 (status record) ++
      encode_bytes 10 (reserved_10 record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 8 bytes with
      | None => None
      | Some (matching_engine_value, bytes) =>
          match decode_bytes 5 bytes with
          | None => None
          | Some (mp_id_value, bytes) =>
              match decode_bytes 20 bytes with
              | None => None
              | Some (client_order_id_value, bytes) =>
                  match decode_uint 4 bytes with
                  | None => None
                  | Some (instrument_id_binary_u_4_value, bytes) =>
                      match decode_uint 8 bytes with
                      | None => None
                      | Some (order_id_value, bytes) =>
                          match decode_bytes 1 bytes with
                          | None => None
                          | Some (status_value, bytes) =>
                              match decode_bytes 10 bytes with
                              | None => None
                              | Some (reserved_10_value, bytes) =>
                                  Some ({| matching_engine := matching_engine_value; mp_id := mp_id_value; client_order_id := client_order_id_value; instrument_id_binary_u_4 := instrument_id_binary_u_4_value; order_id := order_id_value; status := status_value; reserved_10 := reserved_10_value |}, bytes)
                              end
                          end
                      end
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 56.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_uint_length, !encode_bytes_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 [bound_1 [bound_2 [bound_3 [bound_4 [bound_5 bound_6]]]]]].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_uint by exact bound_0.
      rewrite decode_encode_bytes by exact bound_1.
      rewrite decode_encode_bytes by exact bound_2.
      rewrite decode_encode_uint by exact bound_3.
      rewrite decode_encode_uint by exact bound_4.
      rewrite decode_encode_bytes by exact bound_5.
      rewrite decode_encode_bytes by exact bound_6.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End NewOrderResponseMessage2.

  Module ModifyOrderResponse2.

    (** Acknowledgement for a Modify Order Request accepted by MIAX Futures Onyx *)
    Record t := {
      matching_engine_time : N;
      mp_id : list byte;
      client_order_id : list byte;
      original_client_order_id : list byte;
      instrument_id_binary_u_4 : N;
      order_id : N;
      leaves_qty : N;
      status : list byte;
      reserved_10 : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (matching_engine_time record < 256 ^ N.of_nat 8)%N /\
      Datatypes.length (mp_id record) = 5 /\
      Datatypes.length (client_order_id record) = 20 /\
      Datatypes.length (original_client_order_id record) = 20 /\
      (instrument_id_binary_u_4 record < 256 ^ N.of_nat 4)%N /\
      (order_id record < 256 ^ N.of_nat 8)%N /\
      (leaves_qty record < 256 ^ N.of_nat 4)%N /\
      Datatypes.length (status record) = 1 /\
      Datatypes.length (reserved_10 record) = 10.

    Definition encode (record : t) : list byte :=
      encode_uint 8 (matching_engine_time record) ++
      encode_bytes 5 (mp_id record) ++
      encode_bytes 20 (client_order_id record) ++
      encode_bytes 20 (original_client_order_id record) ++
      encode_uint 4 (instrument_id_binary_u_4 record) ++
      encode_uint 8 (order_id record) ++
      encode_uint 4 (leaves_qty record) ++
      encode_bytes 1 (status record) ++
      encode_bytes 10 (reserved_10 record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 8 bytes with
      | None => None
      | Some (matching_engine_time_value, bytes) =>
          match decode_bytes 5 bytes with
          | None => None
          | Some (mp_id_value, bytes) =>
              match decode_bytes 20 bytes with
              | None => None
              | Some (client_order_id_value, bytes) =>
                  match decode_bytes 20 bytes with
                  | None => None
                  | Some (original_client_order_id_value, bytes) =>
                      match decode_uint 4 bytes with
                      | None => None
                      | Some (instrument_id_binary_u_4_value, bytes) =>
                          match decode_uint 8 bytes with
                          | None => None
                          | Some (order_id_value, bytes) =>
                              match decode_uint 4 bytes with
                              | None => None
                              | Some (leaves_qty_value, bytes) =>
                                  match decode_bytes 1 bytes with
                                  | None => None
                                  | Some (status_value, bytes) =>
                                      match decode_bytes 10 bytes with
                                      | None => None
                                      | Some (reserved_10_value, bytes) =>
                                          Some ({| matching_engine_time := matching_engine_time_value; mp_id := mp_id_value; client_order_id := client_order_id_value; original_client_order_id := original_client_order_id_value; instrument_id_binary_u_4 := instrument_id_binary_u_4_value; order_id := order_id_value; leaves_qty := leaves_qty_value; status := status_value; reserved_10 := reserved_10_value |}, bytes)
                                      end
                                  end
                              end
                          end
                      end
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 80.
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
      rewrite decode_encode_bytes by exact bound_1.
      rewrite decode_encode_bytes by exact bound_2.
      rewrite decode_encode_bytes by exact bound_3.
      rewrite decode_encode_uint by exact bound_4.
      rewrite decode_encode_uint by exact bound_5.
      rewrite decode_encode_uint by exact bound_6.
      rewrite decode_encode_bytes by exact bound_7.
      rewrite decode_encode_bytes by exact bound_8.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End ModifyOrderResponse2.

  Module CancelOrderRequestMessage.

    (** a cancel request for a resting order *)
    Record t := {
      client_send_time : N;
      mp_id : list byte;
      operator_id : list byte;
      operator_location : list byte;
      order_id : N;
      client_order_id : list byte;
      original_client_order_id : list byte;
      instrument_id_binary_u_4 : N;
      reserved_10 : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (client_send_time record < 256 ^ N.of_nat 8)%N /\
      Datatypes.length (mp_id record) = 5 /\
      Datatypes.length (operator_id record) = 18 /\
      Datatypes.length (operator_location record) = 6 /\
      (order_id record < 256 ^ N.of_nat 8)%N /\
      Datatypes.length (client_order_id record) = 20 /\
      Datatypes.length (original_client_order_id record) = 20 /\
      (instrument_id_binary_u_4 record < 256 ^ N.of_nat 4)%N /\
      Datatypes.length (reserved_10 record) = 10.

    Definition encode (record : t) : list byte :=
      encode_uint 8 (client_send_time record) ++
      encode_bytes 5 (mp_id record) ++
      encode_bytes 18 (operator_id record) ++
      encode_bytes 6 (operator_location record) ++
      encode_uint 8 (order_id record) ++
      encode_bytes 20 (client_order_id record) ++
      encode_bytes 20 (original_client_order_id record) ++
      encode_uint 4 (instrument_id_binary_u_4 record) ++
      encode_bytes 10 (reserved_10 record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 8 bytes with
      | None => None
      | Some (client_send_time_value, bytes) =>
          match decode_bytes 5 bytes with
          | None => None
          | Some (mp_id_value, bytes) =>
              match decode_bytes 18 bytes with
              | None => None
              | Some (operator_id_value, bytes) =>
                  match decode_bytes 6 bytes with
                  | None => None
                  | Some (operator_location_value, bytes) =>
                      match decode_uint 8 bytes with
                      | None => None
                      | Some (order_id_value, bytes) =>
                          match decode_bytes 20 bytes with
                          | None => None
                          | Some (client_order_id_value, bytes) =>
                              match decode_bytes 20 bytes with
                              | None => None
                              | Some (original_client_order_id_value, bytes) =>
                                  match decode_uint 4 bytes with
                                  | None => None
                                  | Some (instrument_id_binary_u_4_value, bytes) =>
                                      match decode_bytes 10 bytes with
                                      | None => None
                                      | Some (reserved_10_value, bytes) =>
                                          Some ({| client_send_time := client_send_time_value; mp_id := mp_id_value; operator_id := operator_id_value; operator_location := operator_location_value; order_id := order_id_value; client_order_id := client_order_id_value; original_client_order_id := original_client_order_id_value; instrument_id_binary_u_4 := instrument_id_binary_u_4_value; reserved_10 := reserved_10_value |}, bytes)
                                      end
                                  end
                              end
                          end
                      end
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 99.
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
      rewrite decode_encode_bytes by exact bound_1.
      rewrite decode_encode_bytes by exact bound_2.
      rewrite decode_encode_bytes by exact bound_3.
      rewrite decode_encode_uint by exact bound_4.
      rewrite decode_encode_bytes by exact bound_5.
      rewrite decode_encode_bytes by exact bound_6.
      rewrite decode_encode_uint by exact bound_7.
      rewrite decode_encode_bytes by exact bound_8.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End CancelOrderRequestMessage.

  Module CancelOrderResponse2.

    (** provides response to an Order Cancel Request *)
    Record t := {
      matching_engine_time : N;
      mp_id : list byte;
      client_order_id : list byte;
      original_client_order : list byte;
      instrument_id_binary_u_4 : N;
      order_id : N;
      status : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (matching_engine_time record < 256 ^ N.of_nat 8)%N /\
      Datatypes.length (mp_id record) = 5 /\
      Datatypes.length (client_order_id record) = 20 /\
      Datatypes.length (original_client_order record) = 20 /\
      (instrument_id_binary_u_4 record < 256 ^ N.of_nat 4)%N /\
      (order_id record < 256 ^ N.of_nat 8)%N /\
      Datatypes.length (status record) = 1.

    Definition encode (record : t) : list byte :=
      encode_uint 8 (matching_engine_time record) ++
      encode_bytes 5 (mp_id record) ++
      encode_bytes 20 (client_order_id record) ++
      encode_bytes 20 (original_client_order record) ++
      encode_uint 4 (instrument_id_binary_u_4 record) ++
      encode_uint 8 (order_id record) ++
      encode_bytes 1 (status record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 8 bytes with
      | None => None
      | Some (matching_engine_time_value, bytes) =>
          match decode_bytes 5 bytes with
          | None => None
          | Some (mp_id_value, bytes) =>
              match decode_bytes 20 bytes with
              | None => None
              | Some (client_order_id_value, bytes) =>
                  match decode_bytes 20 bytes with
                  | None => None
                  | Some (original_client_order_value, bytes) =>
                      match decode_uint 4 bytes with
                      | None => None
                      | Some (instrument_id_binary_u_4_value, bytes) =>
                          match decode_uint 8 bytes with
                          | None => None
                          | Some (order_id_value, bytes) =>
                              match decode_bytes 1 bytes with
                              | None => None
                              | Some (status_value, bytes) =>
                                  Some ({| matching_engine_time := matching_engine_time_value; mp_id := mp_id_value; client_order_id := client_order_id_value; original_client_order := original_client_order_value; instrument_id_binary_u_4 := instrument_id_binary_u_4_value; order_id := order_id_value; status := status_value |}, bytes)
                              end
                          end
                      end
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 66.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_uint_length, !encode_bytes_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 [bound_1 [bound_2 [bound_3 [bound_4 [bound_5 bound_6]]]]]].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_uint by exact bound_0.
      rewrite decode_encode_bytes by exact bound_1.
      rewrite decode_encode_bytes by exact bound_2.
      rewrite decode_encode_bytes by exact bound_3.
      rewrite decode_encode_uint by exact bound_4.
      rewrite decode_encode_uint by exact bound_5.
      rewrite decode_encode_bytes by exact bound_6.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End CancelOrderResponse2.

  Module MassCancelRequest.

    (** request the cancellation of all orders based on the requested scope and the provided criteria *)
    Record t := {
      client_send_time : N;
      mp_id : list byte;
      operator_id : list byte;
      operator_location : list byte;
      reserved_10 : list byte;
      client_order_id : list byte;
      scope : list byte;
      action : list byte;
      product_group_code : list byte;
      product_type : list byte;
      purge_group : list byte;
      reserved_9 : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (client_send_time record < 256 ^ N.of_nat 8)%N /\
      Datatypes.length (mp_id record) = 5 /\
      Datatypes.length (operator_id record) = 18 /\
      Datatypes.length (operator_location record) = 6 /\
      Datatypes.length (reserved_10 record) = 10 /\
      Datatypes.length (client_order_id record) = 20 /\
      Datatypes.length (scope record) = 1 /\
      Datatypes.length (action record) = 1 /\
      Datatypes.length (product_group_code record) = 6 /\
      Datatypes.length (product_type record) = 1 /\
      Datatypes.length (purge_group record) = 1 /\
      Datatypes.length (reserved_9 record) = 9.

    Definition encode (record : t) : list byte :=
      encode_uint 8 (client_send_time record) ++
      encode_bytes 5 (mp_id record) ++
      encode_bytes 18 (operator_id record) ++
      encode_bytes 6 (operator_location record) ++
      encode_bytes 10 (reserved_10 record) ++
      encode_bytes 20 (client_order_id record) ++
      encode_bytes 1 (scope record) ++
      encode_bytes 1 (action record) ++
      encode_bytes 6 (product_group_code record) ++
      encode_bytes 1 (product_type record) ++
      encode_bytes 1 (purge_group record) ++
      encode_bytes 9 (reserved_9 record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 8 bytes with
      | None => None
      | Some (client_send_time_value, bytes) =>
          match decode_bytes 5 bytes with
          | None => None
          | Some (mp_id_value, bytes) =>
              match decode_bytes 18 bytes with
              | None => None
              | Some (operator_id_value, bytes) =>
                  match decode_bytes 6 bytes with
                  | None => None
                  | Some (operator_location_value, bytes) =>
                      match decode_bytes 10 bytes with
                      | None => None
                      | Some (reserved_10_value, bytes) =>
                          match decode_bytes 20 bytes with
                          | None => None
                          | Some (client_order_id_value, bytes) =>
                              match decode_bytes 1 bytes with
                              | None => None
                              | Some (scope_value, bytes) =>
                                  match decode_bytes 1 bytes with
                                  | None => None
                                  | Some (action_value, bytes) =>
                                      match decode_bytes 6 bytes with
                                      | None => None
                                      | Some (product_group_code_value, bytes) =>
                                          match decode_bytes 1 bytes with
                                          | None => None
                                          | Some (product_type_value, bytes) =>
                                              match decode_bytes 1 bytes with
                                              | None => None
                                              | Some (purge_group_value, bytes) =>
                                                  match decode_bytes 9 bytes with
                                                  | None => None
                                                  | Some (reserved_9_value, bytes) =>
                                                      Some ({| client_send_time := client_send_time_value; mp_id := mp_id_value; operator_id := operator_id_value; operator_location := operator_location_value; reserved_10 := reserved_10_value; client_order_id := client_order_id_value; scope := scope_value; action := action_value; product_group_code := product_group_code_value; product_type := product_type_value; purge_group := purge_group_value; reserved_9 := reserved_9_value |}, bytes)
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

    Theorem encode_length : forall record, Datatypes.length (encode record) = 86.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_uint_length, !encode_bytes_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 [bound_1 [bound_2 [bound_3 [bound_4 [bound_5 [bound_6 [bound_7 [bound_8 [bound_9 [bound_10 bound_11]]]]]]]]]]].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_uint by exact bound_0.
      rewrite decode_encode_bytes by exact bound_1.
      rewrite decode_encode_bytes by exact bound_2.
      rewrite decode_encode_bytes by exact bound_3.
      rewrite decode_encode_bytes by exact bound_4.
      rewrite decode_encode_bytes by exact bound_5.
      rewrite decode_encode_bytes by exact bound_6.
      rewrite decode_encode_bytes by exact bound_7.
      rewrite decode_encode_bytes by exact bound_8.
      rewrite decode_encode_bytes by exact bound_9.
      rewrite decode_encode_bytes by exact bound_10.
      rewrite decode_encode_bytes by exact bound_11.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End MassCancelRequest.

  Module MassCancelResponse2.

    (** used to inform the Firm about the status of their previous Mass Cancel Request *)
    Record t := {
      matching_engine_time : N;
      mp_id : list byte;
      client_order_id : list byte;
      status : list byte;
      reserved_10 : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (matching_engine_time record < 256 ^ N.of_nat 8)%N /\
      Datatypes.length (mp_id record) = 5 /\
      Datatypes.length (client_order_id record) = 20 /\
      Datatypes.length (status record) = 1 /\
      Datatypes.length (reserved_10 record) = 10.

    Definition encode (record : t) : list byte :=
      encode_uint 8 (matching_engine_time record) ++
      encode_bytes 5 (mp_id record) ++
      encode_bytes 20 (client_order_id record) ++
      encode_bytes 1 (status record) ++
      encode_bytes 10 (reserved_10 record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 8 bytes with
      | None => None
      | Some (matching_engine_time_value, bytes) =>
          match decode_bytes 5 bytes with
          | None => None
          | Some (mp_id_value, bytes) =>
              match decode_bytes 20 bytes with
              | None => None
              | Some (client_order_id_value, bytes) =>
                  match decode_bytes 1 bytes with
                  | None => None
                  | Some (status_value, bytes) =>
                      match decode_bytes 10 bytes with
                      | None => None
                      | Some (reserved_10_value, bytes) =>
                          Some ({| matching_engine_time := matching_engine_time_value; mp_id := mp_id_value; client_order_id := client_order_id_value; status := status_value; reserved_10 := reserved_10_value |}, bytes)
                      end
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 44.
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

  End MassCancelResponse2.

  Module StrategyCreationResponseMessage2.

    (** response to the Strategy Creation Request *)
    Record t := {
      matching_engine_time : N;
      mp_id : list byte;
      client_order_id : list byte;
      instrument_id_string_20 : list byte;
      status : list byte;
      reserved_16 : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (matching_engine_time record < 256 ^ N.of_nat 8)%N /\
      Datatypes.length (mp_id record) = 5 /\
      Datatypes.length (client_order_id record) = 20 /\
      Datatypes.length (instrument_id_string_20 record) = 20 /\
      Datatypes.length (status record) = 1 /\
      Datatypes.length (reserved_16 record) = 16.

    Definition encode (record : t) : list byte :=
      encode_uint 8 (matching_engine_time record) ++
      encode_bytes 5 (mp_id record) ++
      encode_bytes 20 (client_order_id record) ++
      encode_bytes 20 (instrument_id_string_20 record) ++
      encode_bytes 1 (status record) ++
      encode_bytes 16 (reserved_16 record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 8 bytes with
      | None => None
      | Some (matching_engine_time_value, bytes) =>
          match decode_bytes 5 bytes with
          | None => None
          | Some (mp_id_value, bytes) =>
              match decode_bytes 20 bytes with
              | None => None
              | Some (client_order_id_value, bytes) =>
                  match decode_bytes 20 bytes with
                  | None => None
                  | Some (instrument_id_string_20_value, bytes) =>
                      match decode_bytes 1 bytes with
                      | None => None
                      | Some (status_value, bytes) =>
                          match decode_bytes 16 bytes with
                          | None => None
                          | Some (reserved_16_value, bytes) =>
                              Some ({| matching_engine_time := matching_engine_time_value; mp_id := mp_id_value; client_order_id := client_order_id_value; instrument_id_string_20 := instrument_id_string_20_value; status := status_value; reserved_16 := reserved_16_value |}, bytes)
                          end
                      end
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 70.
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
      rewrite decode_encode_bytes by exact bound_3.
      rewrite decode_encode_bytes by exact bound_4.
      rewrite decode_encode_bytes by exact bound_5.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End StrategyCreationResponseMessage2.

  Module LoginRequest.

    (** The SesM client must send a Login request packet immediately upon establishing a new TCP/IP socket connection to the server *)
    Record t := {
      sesm_version : list byte;
      username : list byte;
      computer_id : list byte;
      application_protocol : list byte;
      requested_session : N;
      requested_sequence_number : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (sesm_version record) = 5 /\
      Datatypes.length (username record) = 5 /\
      Datatypes.length (computer_id record) = 8 /\
      Datatypes.length (application_protocol record) = 8 /\
      (requested_session record < 256 ^ N.of_nat 1)%N /\
      (requested_sequence_number record < 256 ^ N.of_nat 8)%N.

    Definition encode (record : t) : list byte :=
      encode_bytes 5 (sesm_version record) ++
      encode_bytes 5 (username record) ++
      encode_bytes 8 (computer_id record) ++
      encode_bytes 8 (application_protocol record) ++
      encode_uint 1 (requested_session record) ++
      encode_uint 8 (requested_sequence_number record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 5 bytes with
      | None => None
      | Some (sesm_version_value, bytes) =>
          match decode_bytes 5 bytes with
          | None => None
          | Some (username_value, bytes) =>
              match decode_bytes 8 bytes with
              | None => None
              | Some (computer_id_value, bytes) =>
                  match decode_bytes 8 bytes with
                  | None => None
                  | Some (application_protocol_value, bytes) =>
                      match decode_uint 1 bytes with
                      | None => None
                      | Some (requested_session_value, bytes) =>
                          match decode_uint 8 bytes with
                          | None => None
                          | Some (requested_sequence_number_value, bytes) =>
                              Some ({| sesm_version := sesm_version_value; username := username_value; computer_id := computer_id_value; application_protocol := application_protocol_value; requested_session := requested_session_value; requested_sequence_number := requested_sequence_number_value |}, bytes)
                          end
                      end
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 35.
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
      rewrite decode_encode_bytes by exact bound_2.
      rewrite decode_encode_bytes by exact bound_3.
      rewrite decode_encode_uint by exact bound_4.
      rewrite decode_encode_uint by exact bound_5.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End LoginRequest.

  Module LoginResponse.

    (** The SesM server sends a Login response packet in response a Login request packet from the client *)
    Record t := {
      login_status : list byte;
      session_id : N;
      highest_sequence_number : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (login_status record) = 1 /\
      (session_id record < 256 ^ N.of_nat 1)%N /\
      (highest_sequence_number record < 256 ^ N.of_nat 8)%N.

    Definition encode (record : t) : list byte :=
      encode_bytes 1 (login_status record) ++
      encode_uint 1 (session_id record) ++
      encode_uint 8 (highest_sequence_number record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 1 bytes with
      | None => None
      | Some (login_status_value, bytes) =>
          match decode_uint 1 bytes with
          | None => None
          | Some (session_id_value, bytes) =>
              match decode_uint 8 bytes with
              | None => None
              | Some (highest_sequence_number_value, bytes) =>
                  Some ({| login_status := login_status_value; session_id := session_id_value; highest_sequence_number := highest_sequence_number_value |}, bytes)
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
      destruct bound as [bound_0 [bound_1 bound_2]].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_bytes by exact bound_0.
      rewrite decode_encode_uint by exact bound_1.
      rewrite decode_encode_uint by exact bound_2.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End LoginResponse.

  Module RetransmissionRequest.

    (** The SesM server sends a Login response packet in response a Login request packet from the client *)
    Record t := {
      start_sequence_number : N;
      end_sequence_number : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (start_sequence_number record < 256 ^ N.of_nat 8)%N /\
      (end_sequence_number record < 256 ^ N.of_nat 8)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 8 (start_sequence_number record) ++
      encode_uint 8 (end_sequence_number record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 8 bytes with
      | None => None
      | Some (start_sequence_number_value, bytes) =>
          match decode_uint 8 bytes with
          | None => None
          | Some (end_sequence_number_value, bytes) =>
              Some ({| start_sequence_number := start_sequence_number_value; end_sequence_number := end_sequence_number_value |}, bytes)
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
      destruct bound as [bound_0 bound_1].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_uint by exact bound_0.
      rewrite decode_encode_uint by exact bound_1.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec]. Defined.

  End RetransmissionRequest.

End OnyxFuturesExpressInterfaceV10C.
