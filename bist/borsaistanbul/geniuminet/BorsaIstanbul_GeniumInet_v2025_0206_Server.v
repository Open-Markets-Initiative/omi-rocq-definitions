From Stdlib Require Import List.
From Stdlib Require Import NArith.
From Stdlib Require Import Lia.
From Stdlib Require Import Strings.Byte.
From Omi Require Import Wire.

Import ListNotations.

(** * Borsa İstanbul A.Ş. Genium Inet

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
  *)

Module BorsaIstanbulGeniumInetV20250206Server.

  Module ServerPacketHeader.

    (** Packet header of a packet sent by the server *)
    Record t := {
      packet_length : N;
      server_packet_type : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (packet_length record < 256 ^ N.of_nat 2)%N /\
      Datatypes.length (server_packet_type record) = 1.

    Definition encode (record : t) : list byte :=
      encode_uint 2 (packet_length record) ++
      encode_bytes 1 (server_packet_type record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 2 bytes with
      | None => None
      | Some (packet_length_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (server_packet_type_value, bytes) =>
              Some ({| packet_length := packet_length_value; server_packet_type := server_packet_type_value |}, bytes)
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

  End ServerPacketHeader.

  Module LoginAcceptedPacket.

    (** The SoupBinTCP server sends a Login Accepted Packet in response to receiving a valid Login Request from the client *)
    Record t := {
      accepted_session : list byte;
      accepted_sequence_number : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (accepted_session record) = 10 /\
      Datatypes.length (accepted_sequence_number record) = 20.

    Definition encode (record : t) : list byte :=
      encode_bytes 10 (accepted_session record) ++
      encode_bytes 20 (accepted_sequence_number record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 10 bytes with
      | None => None
      | Some (accepted_session_value, bytes) =>
          match decode_bytes 20 bytes with
          | None => None
          | Some (accepted_sequence_number_value, bytes) =>
              Some ({| accepted_session := accepted_session_value; accepted_sequence_number := accepted_sequence_number_value |}, bytes)
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 30.
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

  End LoginAcceptedPacket.

  Module LoginRejectedPacket.

    (** The SoupBinTCP server sends this packet in response to an invalid Login Request Packet from the client *)
    Record t := {
      reject_reason_code : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (reject_reason_code record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 1 (reject_reason_code record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 1 bytes with
      | None => None
      | Some (reject_reason_code_value, bytes) =>
          Some ({| reject_reason_code := reject_reason_code_value |}, bytes)
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

  End LoginRejectedPacket.

  Module OrderAccepted.

    (** Acknowledges the receipt and acceptance of a valid Enter Order message. The data fields from the Enter Order message are echoed back, though accepted values may differ from entered values for some fields. Accepted messages are guaranteed to come before any Executed or Canceled messages for an order. *)
    Record t := {
      nanoseconds : N;
      order_token : list byte;
      order_book_id : N;
      side : list byte;
      order_id : N;
      quantity : N;
      price : N;
      time_in_force : N;
      open_close : N;
      client_account : list byte;
      order_state : N;
      customer_info : list byte;
      exchange_info_alpha_32 : list byte;
      pre_trade_quantity : N;
      display_quantity : N;
      client_category : N;
      off_hours : N;
      smp_level : N;
      smp_method : N;
      smp_id : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (nanoseconds record < 256 ^ N.of_nat 8)%N /\
      Datatypes.length (order_token record) = 14 /\
      (order_book_id record < 256 ^ N.of_nat 4)%N /\
      Datatypes.length (side record) = 1 /\
      (order_id record < 256 ^ N.of_nat 8)%N /\
      (quantity record < 256 ^ N.of_nat 8)%N /\
      (price record < 256 ^ N.of_nat 4)%N /\
      (time_in_force record < 256 ^ N.of_nat 1)%N /\
      (open_close record < 256 ^ N.of_nat 1)%N /\
      Datatypes.length (client_account record) = 16 /\
      (order_state record < 256 ^ N.of_nat 1)%N /\
      Datatypes.length (customer_info record) = 15 /\
      Datatypes.length (exchange_info_alpha_32 record) = 32 /\
      (pre_trade_quantity record < 256 ^ N.of_nat 8)%N /\
      (display_quantity record < 256 ^ N.of_nat 8)%N /\
      (client_category record < 256 ^ N.of_nat 1)%N /\
      (off_hours record < 256 ^ N.of_nat 1)%N /\
      (smp_level record < 256 ^ N.of_nat 1)%N /\
      (smp_method record < 256 ^ N.of_nat 1)%N /\
      Datatypes.length (smp_id record) = 3.

    Definition encode (record : t) : list byte :=
      encode_uint 8 (nanoseconds record) ++
      encode_bytes 14 (order_token record) ++
      encode_uint 4 (order_book_id record) ++
      encode_bytes 1 (side record) ++
      encode_uint 8 (order_id record) ++
      encode_uint 8 (quantity record) ++
      encode_uint 4 (price record) ++
      encode_uint 1 (time_in_force record) ++
      encode_uint 1 (open_close record) ++
      encode_bytes 16 (client_account record) ++
      encode_uint 1 (order_state record) ++
      encode_bytes 15 (customer_info record) ++
      encode_bytes 32 (exchange_info_alpha_32 record) ++
      encode_uint 8 (pre_trade_quantity record) ++
      encode_uint 8 (display_quantity record) ++
      encode_uint 1 (client_category record) ++
      encode_uint 1 (off_hours record) ++
      encode_uint 1 (smp_level record) ++
      encode_uint 1 (smp_method record) ++
      encode_bytes 3 (smp_id record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 8 bytes with
      | None => None
      | Some (nanoseconds_value, bytes) =>
          match decode_bytes 14 bytes with
          | None => None
          | Some (order_token_value, bytes) =>
              match decode_uint 4 bytes with
              | None => None
              | Some (order_book_id_value, bytes) =>
                  match decode_bytes 1 bytes with
                  | None => None
                  | Some (side_value, bytes) =>
                      match decode_uint 8 bytes with
                      | None => None
                      | Some (order_id_value, bytes) =>
                          match decode_uint 8 bytes with
                          | None => None
                          | Some (quantity_value, bytes) =>
                              match decode_uint 4 bytes with
                              | None => None
                              | Some (price_value, bytes) =>
                                  match decode_uint 1 bytes with
                                  | None => None
                                  | Some (time_in_force_value, bytes) =>
                                      match decode_uint 1 bytes with
                                      | None => None
                                      | Some (open_close_value, bytes) =>
                                          match decode_bytes 16 bytes with
                                          | None => None
                                          | Some (client_account_value, bytes) =>
                                              match decode_uint 1 bytes with
                                              | None => None
                                              | Some (order_state_value, bytes) =>
                                                  match decode_bytes 15 bytes with
                                                  | None => None
                                                  | Some (customer_info_value, bytes) =>
                                                      match decode_bytes 32 bytes with
                                                      | None => None
                                                      | Some (exchange_info_alpha_32_value, bytes) =>
                                                          match decode_uint 8 bytes with
                                                          | None => None
                                                          | Some (pre_trade_quantity_value, bytes) =>
                                                              match decode_uint 8 bytes with
                                                              | None => None
                                                              | Some (display_quantity_value, bytes) =>
                                                                  match decode_uint 1 bytes with
                                                                  | None => None
                                                                  | Some (client_category_value, bytes) =>
                                                                      match decode_uint 1 bytes with
                                                                      | None => None
                                                                      | Some (off_hours_value, bytes) =>
                                                                          match decode_uint 1 bytes with
                                                                          | None => None
                                                                          | Some (smp_level_value, bytes) =>
                                                                              match decode_uint 1 bytes with
                                                                              | None => None
                                                                              | Some (smp_method_value, bytes) =>
                                                                                  match decode_bytes 3 bytes with
                                                                                  | None => None
                                                                                  | Some (smp_id_value, bytes) =>
                                                                                      Some ({| nanoseconds := nanoseconds_value; order_token := order_token_value; order_book_id := order_book_id_value; side := side_value; order_id := order_id_value; quantity := quantity_value; price := price_value; time_in_force := time_in_force_value; open_close := open_close_value; client_account := client_account_value; order_state := order_state_value; customer_info := customer_info_value; exchange_info_alpha_32 := exchange_info_alpha_32_value; pre_trade_quantity := pre_trade_quantity_value; display_quantity := display_quantity_value; client_category := client_category_value; off_hours := off_hours_value; smp_level := smp_level_value; smp_method := smp_method_value; smp_id := smp_id_value |}, bytes)
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

    Theorem encode_length : forall record, Datatypes.length (encode record) = 136.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_uint_length, !encode_bytes_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 [bound_1 [bound_2 [bound_3 [bound_4 [bound_5 [bound_6 [bound_7 [bound_8 [bound_9 [bound_10 [bound_11 [bound_12 [bound_13 [bound_14 [bound_15 [bound_16 [bound_17 [bound_18 bound_19]]]]]]]]]]]]]]]]]]].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_uint by exact bound_0.
      rewrite decode_encode_bytes by exact bound_1.
      rewrite decode_encode_uint by exact bound_2.
      rewrite decode_encode_bytes by exact bound_3.
      rewrite decode_encode_uint by exact bound_4.
      rewrite decode_encode_uint by exact bound_5.
      rewrite decode_encode_uint by exact bound_6.
      rewrite decode_encode_uint by exact bound_7.
      rewrite decode_encode_uint by exact bound_8.
      rewrite decode_encode_bytes by exact bound_9.
      rewrite decode_encode_uint by exact bound_10.
      rewrite decode_encode_bytes by exact bound_11.
      rewrite decode_encode_bytes by exact bound_12.
      rewrite decode_encode_uint by exact bound_13.
      rewrite decode_encode_uint by exact bound_14.
      rewrite decode_encode_uint by exact bound_15.
      rewrite decode_encode_uint by exact bound_16.
      rewrite decode_encode_uint by exact bound_17.
      rewrite decode_encode_uint by exact bound_18.
      rewrite decode_encode_bytes by exact bound_19.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End OrderAccepted.

  Module OrderRejected.

    (** Used to reject Enter Order messages, Cancel Order messages, and Replace Order messages. *)
    Record t := {
      nanoseconds : N;
      order_token : list byte;
      reject_code : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (nanoseconds record < 256 ^ N.of_nat 8)%N /\
      Datatypes.length (order_token record) = 14 /\
      (reject_code record < 256 ^ N.of_nat 4)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 8 (nanoseconds record) ++
      encode_bytes 14 (order_token record) ++
      encode_uint 4 (reject_code record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 8 bytes with
      | None => None
      | Some (nanoseconds_value, bytes) =>
          match decode_bytes 14 bytes with
          | None => None
          | Some (order_token_value, bytes) =>
              match decode_uint 4 bytes with
              | None => None
              | Some (reject_code_value, bytes) =>
                  Some ({| nanoseconds := nanoseconds_value; order_token := order_token_value; reject_code := reject_code_value |}, bytes)
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

  End OrderRejected.

  Module OrderReplaced.

    (** Acknowledges the receipt and acceptance of a valid Replace Order message. The data fields from the Replace Order message are echoed back, though accepted values may differ from entered values for some fields. Uses the Order State field to denote that a replace was accepted and then automatically canceled when the Order State is Not on book. *)
    Record t := {
      nanoseconds : N;
      replacement_order_token : list byte;
      previous_order_token : list byte;
      order_book_id : N;
      side : list byte;
      order_id : N;
      quantity : N;
      price : N;
      time_in_force : N;
      replace_open_close : N;
      client_account : list byte;
      order_state : N;
      customer_info : list byte;
      exchange_info_alpha_32 : list byte;
      pre_trade_quantity : N;
      display_quantity : N;
      client_category : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (nanoseconds record < 256 ^ N.of_nat 8)%N /\
      Datatypes.length (replacement_order_token record) = 14 /\
      Datatypes.length (previous_order_token record) = 14 /\
      (order_book_id record < 256 ^ N.of_nat 4)%N /\
      Datatypes.length (side record) = 1 /\
      (order_id record < 256 ^ N.of_nat 8)%N /\
      (quantity record < 256 ^ N.of_nat 8)%N /\
      (price record < 256 ^ N.of_nat 4)%N /\
      (time_in_force record < 256 ^ N.of_nat 1)%N /\
      (replace_open_close record < 256 ^ N.of_nat 1)%N /\
      Datatypes.length (client_account record) = 16 /\
      (order_state record < 256 ^ N.of_nat 1)%N /\
      Datatypes.length (customer_info record) = 15 /\
      Datatypes.length (exchange_info_alpha_32 record) = 32 /\
      (pre_trade_quantity record < 256 ^ N.of_nat 8)%N /\
      (display_quantity record < 256 ^ N.of_nat 8)%N /\
      (client_category record < 256 ^ N.of_nat 1)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 8 (nanoseconds record) ++
      encode_bytes 14 (replacement_order_token record) ++
      encode_bytes 14 (previous_order_token record) ++
      encode_uint 4 (order_book_id record) ++
      encode_bytes 1 (side record) ++
      encode_uint 8 (order_id record) ++
      encode_uint 8 (quantity record) ++
      encode_uint 4 (price record) ++
      encode_uint 1 (time_in_force record) ++
      encode_uint 1 (replace_open_close record) ++
      encode_bytes 16 (client_account record) ++
      encode_uint 1 (order_state record) ++
      encode_bytes 15 (customer_info record) ++
      encode_bytes 32 (exchange_info_alpha_32 record) ++
      encode_uint 8 (pre_trade_quantity record) ++
      encode_uint 8 (display_quantity record) ++
      encode_uint 1 (client_category record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 8 bytes with
      | None => None
      | Some (nanoseconds_value, bytes) =>
          match decode_bytes 14 bytes with
          | None => None
          | Some (replacement_order_token_value, bytes) =>
              match decode_bytes 14 bytes with
              | None => None
              | Some (previous_order_token_value, bytes) =>
                  match decode_uint 4 bytes with
                  | None => None
                  | Some (order_book_id_value, bytes) =>
                      match decode_bytes 1 bytes with
                      | None => None
                      | Some (side_value, bytes) =>
                          match decode_uint 8 bytes with
                          | None => None
                          | Some (order_id_value, bytes) =>
                              match decode_uint 8 bytes with
                              | None => None
                              | Some (quantity_value, bytes) =>
                                  match decode_uint 4 bytes with
                                  | None => None
                                  | Some (price_value, bytes) =>
                                      match decode_uint 1 bytes with
                                      | None => None
                                      | Some (time_in_force_value, bytes) =>
                                          match decode_uint 1 bytes with
                                          | None => None
                                          | Some (replace_open_close_value, bytes) =>
                                              match decode_bytes 16 bytes with
                                              | None => None
                                              | Some (client_account_value, bytes) =>
                                                  match decode_uint 1 bytes with
                                                  | None => None
                                                  | Some (order_state_value, bytes) =>
                                                      match decode_bytes 15 bytes with
                                                      | None => None
                                                      | Some (customer_info_value, bytes) =>
                                                          match decode_bytes 32 bytes with
                                                          | None => None
                                                          | Some (exchange_info_alpha_32_value, bytes) =>
                                                              match decode_uint 8 bytes with
                                                              | None => None
                                                              | Some (pre_trade_quantity_value, bytes) =>
                                                                  match decode_uint 8 bytes with
                                                                  | None => None
                                                                  | Some (display_quantity_value, bytes) =>
                                                                      match decode_uint 1 bytes with
                                                                      | None => None
                                                                      | Some (client_category_value, bytes) =>
                                                                          Some ({| nanoseconds := nanoseconds_value; replacement_order_token := replacement_order_token_value; previous_order_token := previous_order_token_value; order_book_id := order_book_id_value; side := side_value; order_id := order_id_value; quantity := quantity_value; price := price_value; time_in_force := time_in_force_value; replace_open_close := replace_open_close_value; client_account := client_account_value; order_state := order_state_value; customer_info := customer_info_value; exchange_info_alpha_32 := exchange_info_alpha_32_value; pre_trade_quantity := pre_trade_quantity_value; display_quantity := display_quantity_value; client_category := client_category_value |}, bytes)
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

    Theorem encode_length : forall record, Datatypes.length (encode record) = 144.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_uint_length, !encode_bytes_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 [bound_1 [bound_2 [bound_3 [bound_4 [bound_5 [bound_6 [bound_7 [bound_8 [bound_9 [bound_10 [bound_11 [bound_12 [bound_13 [bound_14 [bound_15 bound_16]]]]]]]]]]]]]]]].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_uint by exact bound_0.
      rewrite decode_encode_bytes by exact bound_1.
      rewrite decode_encode_bytes by exact bound_2.
      rewrite decode_encode_uint by exact bound_3.
      rewrite decode_encode_bytes by exact bound_4.
      rewrite decode_encode_uint by exact bound_5.
      rewrite decode_encode_uint by exact bound_6.
      rewrite decode_encode_uint by exact bound_7.
      rewrite decode_encode_uint by exact bound_8.
      rewrite decode_encode_uint by exact bound_9.
      rewrite decode_encode_bytes by exact bound_10.
      rewrite decode_encode_uint by exact bound_11.
      rewrite decode_encode_bytes by exact bound_12.
      rewrite decode_encode_bytes by exact bound_13.
      rewrite decode_encode_uint by exact bound_14.
      rewrite decode_encode_uint by exact bound_15.
      rewrite decode_encode_uint by exact bound_16.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End OrderReplaced.

  Module OrderCanceled.

    (** Informs that an order has been canceled. This could be acknowledging a Cancel Order message, or the result of system cancellation. Order Canceled messages are sent when orders are suspended due to connection loss; more than one Order Canceled message may be received for the same order. *)
    Record t := {
      nanoseconds : N;
      order_token : list byte;
      order_book_id : N;
      side : list byte;
      order_id : N;
      reason : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (nanoseconds record < 256 ^ N.of_nat 8)%N /\
      Datatypes.length (order_token record) = 14 /\
      (order_book_id record < 256 ^ N.of_nat 4)%N /\
      Datatypes.length (side record) = 1 /\
      (order_id record < 256 ^ N.of_nat 8)%N /\
      (reason record < 256 ^ N.of_nat 1)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 8 (nanoseconds record) ++
      encode_bytes 14 (order_token record) ++
      encode_uint 4 (order_book_id record) ++
      encode_bytes 1 (side record) ++
      encode_uint 8 (order_id record) ++
      encode_uint 1 (reason record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 8 bytes with
      | None => None
      | Some (nanoseconds_value, bytes) =>
          match decode_bytes 14 bytes with
          | None => None
          | Some (order_token_value, bytes) =>
              match decode_uint 4 bytes with
              | None => None
              | Some (order_book_id_value, bytes) =>
                  match decode_bytes 1 bytes with
                  | None => None
                  | Some (side_value, bytes) =>
                      match decode_uint 8 bytes with
                      | None => None
                      | Some (order_id_value, bytes) =>
                          match decode_uint 1 bytes with
                          | None => None
                          | Some (reason_value, bytes) =>
                              Some ({| nanoseconds := nanoseconds_value; order_token := order_token_value; order_book_id := order_book_id_value; side := side_value; order_id := order_id_value; reason := reason_value |}, bytes)
                          end
                      end
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 36.
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
      rewrite decode_encode_uint by exact bound_2.
      rewrite decode_encode_bytes by exact bound_3.
      rewrite decode_encode_uint by exact bound_4.
      rewrite decode_encode_uint by exact bound_5.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End OrderCanceled.

  Module OrderExecuted.

    (** Returned when a partial or full fill occurs. In case of a combination order fill, one Order Executed message will be received per leg. *)
    Record t := {
      nanoseconds : N;
      order_token : list byte;
      order_book_id : N;
      traded_quantity : N;
      trade_price : N;
      match_id : list byte;
      client_category : N;
      reserved_numeric_unsigned_16 : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (nanoseconds record < 256 ^ N.of_nat 8)%N /\
      Datatypes.length (order_token record) = 14 /\
      (order_book_id record < 256 ^ N.of_nat 4)%N /\
      (traded_quantity record < 256 ^ N.of_nat 8)%N /\
      (trade_price record < 256 ^ N.of_nat 4)%N /\
      Datatypes.length (match_id record) = 12 /\
      (client_category record < 256 ^ N.of_nat 1)%N /\
      Datatypes.length (reserved_numeric_unsigned_16 record) = 16.

    Definition encode (record : t) : list byte :=
      encode_uint 8 (nanoseconds record) ++
      encode_bytes 14 (order_token record) ++
      encode_uint 4 (order_book_id record) ++
      encode_uint 8 (traded_quantity record) ++
      encode_uint 4 (trade_price record) ++
      encode_bytes 12 (match_id record) ++
      encode_uint 1 (client_category record) ++
      encode_bytes 16 (reserved_numeric_unsigned_16 record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 8 bytes with
      | None => None
      | Some (nanoseconds_value, bytes) =>
          match decode_bytes 14 bytes with
          | None => None
          | Some (order_token_value, bytes) =>
              match decode_uint 4 bytes with
              | None => None
              | Some (order_book_id_value, bytes) =>
                  match decode_uint 8 bytes with
                  | None => None
                  | Some (traded_quantity_value, bytes) =>
                      match decode_uint 4 bytes with
                      | None => None
                      | Some (trade_price_value, bytes) =>
                          match decode_bytes 12 bytes with
                          | None => None
                          | Some (match_id_value, bytes) =>
                              match decode_uint 1 bytes with
                              | None => None
                              | Some (client_category_value, bytes) =>
                                  match decode_bytes 16 bytes with
                                  | None => None
                                  | Some (reserved_numeric_unsigned_16_value, bytes) =>
                                      Some ({| nanoseconds := nanoseconds_value; order_token := order_token_value; order_book_id := order_book_id_value; traded_quantity := traded_quantity_value; trade_price := trade_price_value; match_id := match_id_value; client_category := client_category_value; reserved_numeric_unsigned_16 := reserved_numeric_unsigned_16_value |}, bytes)
                                  end
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
      rewrite decode_encode_uint by exact bound_2.
      rewrite decode_encode_uint by exact bound_3.
      rewrite decode_encode_uint by exact bound_4.
      rewrite decode_encode_bytes by exact bound_5.
      rewrite decode_encode_uint by exact bound_6.
      rewrite decode_encode_bytes by exact bound_7.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End OrderExecuted.

  Module MassQuoteAcknowledgement.

    (** A positive response to a Mass Quote message. Every quote in a mass quote message must be responded to with an individual message (Mass Quote Acknowledgement or Mass Quote Rejection). If the individual quote in mass quote is accepted, the system sends two Mass Quote Acknowledgement messages, for bid and offer side. *)
    Record t := {
      nanoseconds : N;
      order_token : list byte;
      order_book_id : N;
      quantity : N;
      traded_quantity : N;
      price : N;
      quote_side : list byte;
      quote_status : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (nanoseconds record < 256 ^ N.of_nat 8)%N /\
      Datatypes.length (order_token record) = 14 /\
      (order_book_id record < 256 ^ N.of_nat 4)%N /\
      (quantity record < 256 ^ N.of_nat 8)%N /\
      (traded_quantity record < 256 ^ N.of_nat 8)%N /\
      (price record < 256 ^ N.of_nat 4)%N /\
      Datatypes.length (quote_side record) = 1 /\
      (quote_status record < 256 ^ N.of_nat 4)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 8 (nanoseconds record) ++
      encode_bytes 14 (order_token record) ++
      encode_uint 4 (order_book_id record) ++
      encode_uint 8 (quantity record) ++
      encode_uint 8 (traded_quantity record) ++
      encode_uint 4 (price record) ++
      encode_bytes 1 (quote_side record) ++
      encode_uint 4 (quote_status record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 8 bytes with
      | None => None
      | Some (nanoseconds_value, bytes) =>
          match decode_bytes 14 bytes with
          | None => None
          | Some (order_token_value, bytes) =>
              match decode_uint 4 bytes with
              | None => None
              | Some (order_book_id_value, bytes) =>
                  match decode_uint 8 bytes with
                  | None => None
                  | Some (quantity_value, bytes) =>
                      match decode_uint 8 bytes with
                      | None => None
                      | Some (traded_quantity_value, bytes) =>
                          match decode_uint 4 bytes with
                          | None => None
                          | Some (price_value, bytes) =>
                              match decode_bytes 1 bytes with
                              | None => None
                              | Some (quote_side_value, bytes) =>
                                  match decode_uint 4 bytes with
                                  | None => None
                                  | Some (quote_status_value, bytes) =>
                                      Some ({| nanoseconds := nanoseconds_value; order_token := order_token_value; order_book_id := order_book_id_value; quantity := quantity_value; traded_quantity := traded_quantity_value; price := price_value; quote_side := quote_side_value; quote_status := quote_status_value |}, bytes)
                                  end
                              end
                          end
                      end
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 51.
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
      rewrite decode_encode_uint by exact bound_2.
      rewrite decode_encode_uint by exact bound_3.
      rewrite decode_encode_uint by exact bound_4.
      rewrite decode_encode_uint by exact bound_5.
      rewrite decode_encode_bytes by exact bound_6.
      rewrite decode_encode_uint by exact bound_7.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End MassQuoteAcknowledgement.

  Module MassQuoteRejection.

    (** A negative response to a Mass Quote message. If an individual quote in the mass quote is rejected, a single Mass Quote Rejection is sent for that quote with the Order Book Id populated. If all quotes in the mass quote message are rejected, only one Mass Quote Rejection is sent for the whole request, without an Order Book Id. *)
    Record t := {
      nanoseconds : N;
      order_token : list byte;
      order_book_id : N;
      reject_code : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (nanoseconds record < 256 ^ N.of_nat 8)%N /\
      Datatypes.length (order_token record) = 14 /\
      (order_book_id record < 256 ^ N.of_nat 4)%N /\
      (reject_code record < 256 ^ N.of_nat 4)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 8 (nanoseconds record) ++
      encode_bytes 14 (order_token record) ++
      encode_uint 4 (order_book_id record) ++
      encode_uint 4 (reject_code record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 8 bytes with
      | None => None
      | Some (nanoseconds_value, bytes) =>
          match decode_bytes 14 bytes with
          | None => None
          | Some (order_token_value, bytes) =>
              match decode_uint 4 bytes with
              | None => None
              | Some (order_book_id_value, bytes) =>
                  match decode_uint 4 bytes with
                  | None => None
                  | Some (reject_code_value, bytes) =>
                      Some ({| nanoseconds := nanoseconds_value; order_token := order_token_value; order_book_id := order_book_id_value; reject_code := reject_code_value |}, bytes)
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 30.
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
      rewrite decode_encode_uint by exact bound_2.
      rewrite decode_encode_uint by exact bound_3.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End MassQuoteRejection.

End BorsaIstanbulGeniumInetV20250206Server.
