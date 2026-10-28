From Stdlib Require Import List.
From Stdlib Require Import NArith.
From Stdlib Require Import Lia.
From Stdlib Require Import Strings.Byte.
From Omi Require Import Wire.

Import ListNotations.

(** * Japan Exchange Group Genium Inet

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

Module OseDerivativesGeniumInetV50Server.

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

    (** Acknowledges the receipt and acceptance of a valid Enter Order Message *)
    Record t := {
      timestamp_nanoseconds : N;
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
      exchange_info : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (timestamp_nanoseconds record < 256 ^ N.of_nat 8)%N /\
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
      Datatypes.length (exchange_info record) = 32.

    Definition encode (record : t) : list byte :=
      encode_uint 8 (timestamp_nanoseconds record) ++
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
      encode_bytes 32 (exchange_info record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 8 bytes with
      | None => None
      | Some (timestamp_nanoseconds_value, bytes) =>
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
                                                      | Some (exchange_info_value, bytes) =>
                                                          Some ({| timestamp_nanoseconds := timestamp_nanoseconds_value; order_token := order_token_value; order_book_id := order_book_id_value; side := side_value; order_id := order_id_value; quantity := quantity_value; price := price_value; time_in_force := time_in_force_value; open_close := open_close_value; client_account := client_account_value; order_state := order_state_value; customer_info := customer_info_value; exchange_info := exchange_info_value |}, bytes)
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

    Theorem encode_length : forall record, Datatypes.length (encode record) = 113.
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
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End OrderAccepted.

  Module MassCancelAccepted.

    (** System notification indicating acceptance of a mass cancel request. *)
    Record t := {
      timestamp_nanoseconds : N;
      order_token : list byte;
      status : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (timestamp_nanoseconds record < 256 ^ N.of_nat 8)%N /\
      Datatypes.length (order_token record) = 14 /\
      (status record < 256 ^ N.of_nat 4)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 8 (timestamp_nanoseconds record) ++
      encode_bytes 14 (order_token record) ++
      encode_uint 4 (status record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 8 bytes with
      | None => None
      | Some (timestamp_nanoseconds_value, bytes) =>
          match decode_bytes 14 bytes with
          | None => None
          | Some (order_token_value, bytes) =>
              match decode_uint 4 bytes with
              | None => None
              | Some (status_value, bytes) =>
                  Some ({| timestamp_nanoseconds := timestamp_nanoseconds_value; order_token := order_token_value; status := status_value |}, bytes)
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

  End MassCancelAccepted.

  Module OrderRejected.

    (** System notification indicating that an order has been rejected. *)
    Record t := {
      timestamp_nanoseconds : N;
      order_token : list byte;
      reject_code : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (timestamp_nanoseconds record < 256 ^ N.of_nat 8)%N /\
      Datatypes.length (order_token record) = 14 /\
      (reject_code record < 256 ^ N.of_nat 4)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 8 (timestamp_nanoseconds record) ++
      encode_bytes 14 (order_token record) ++
      encode_uint 4 (reject_code record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 8 bytes with
      | None => None
      | Some (timestamp_nanoseconds_value, bytes) =>
          match decode_bytes 14 bytes with
          | None => None
          | Some (order_token_value, bytes) =>
              match decode_uint 4 bytes with
              | None => None
              | Some (reject_code_value, bytes) =>
                  Some ({| timestamp_nanoseconds := timestamp_nanoseconds_value; order_token := order_token_value; reject_code := reject_code_value |}, bytes)
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

    (** System notification indicating that an order has been successfully replaced. *)
    Record t := {
      timestamp_nanoseconds : N;
      replacement_order_token : list byte;
      previous_order_token : list byte;
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
      exchange_info : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (timestamp_nanoseconds record < 256 ^ N.of_nat 8)%N /\
      Datatypes.length (replacement_order_token record) = 14 /\
      Datatypes.length (previous_order_token record) = 14 /\
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
      Datatypes.length (exchange_info record) = 32.

    Definition encode (record : t) : list byte :=
      encode_uint 8 (timestamp_nanoseconds record) ++
      encode_bytes 14 (replacement_order_token record) ++
      encode_bytes 14 (previous_order_token record) ++
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
      encode_bytes 32 (exchange_info record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 8 bytes with
      | None => None
      | Some (timestamp_nanoseconds_value, bytes) =>
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
                                                          | Some (exchange_info_value, bytes) =>
                                                              Some ({| timestamp_nanoseconds := timestamp_nanoseconds_value; replacement_order_token := replacement_order_token_value; previous_order_token := previous_order_token_value; order_book_id := order_book_id_value; side := side_value; order_id := order_id_value; quantity := quantity_value; price := price_value; time_in_force := time_in_force_value; open_close := open_close_value; client_account := client_account_value; order_state := order_state_value; customer_info := customer_info_value; exchange_info := exchange_info_value |}, bytes)
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

    Theorem encode_length : forall record, Datatypes.length (encode record) = 127.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_uint_length, !encode_bytes_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 [bound_1 [bound_2 [bound_3 [bound_4 [bound_5 [bound_6 [bound_7 [bound_8 [bound_9 [bound_10 [bound_11 [bound_12 bound_13]]]]]]]]]]]]].
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
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End OrderReplaced.

  Module OrderCanceled.

    (** System notification indicating that an order has been canceled. *)
    Record t := {
      timestamp_nanoseconds : N;
      order_token : list byte;
      order_book_id : N;
      side : list byte;
      order_id : N;
      cancel_reason : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (timestamp_nanoseconds record < 256 ^ N.of_nat 8)%N /\
      Datatypes.length (order_token record) = 14 /\
      (order_book_id record < 256 ^ N.of_nat 4)%N /\
      Datatypes.length (side record) = 1 /\
      (order_id record < 256 ^ N.of_nat 8)%N /\
      (cancel_reason record < 256 ^ N.of_nat 1)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 8 (timestamp_nanoseconds record) ++
      encode_bytes 14 (order_token record) ++
      encode_uint 4 (order_book_id record) ++
      encode_bytes 1 (side record) ++
      encode_uint 8 (order_id record) ++
      encode_uint 1 (cancel_reason record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 8 bytes with
      | None => None
      | Some (timestamp_nanoseconds_value, bytes) =>
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
                          | Some (cancel_reason_value, bytes) =>
                              Some ({| timestamp_nanoseconds := timestamp_nanoseconds_value; order_token := order_token_value; order_book_id := order_book_id_value; side := side_value; order_id := order_id_value; cancel_reason := cancel_reason_value |}, bytes)
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

    (** System notification indicating that an order (or order leg) has been executed. *)
    Record t := {
      timestamp_nanoseconds : N;
      order_token : list byte;
      order_book_id : N;
      traded_quantity : N;
      trade_price : N;
      match_id : N;
      combo_group_id : N;
      deal_source : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (timestamp_nanoseconds record < 256 ^ N.of_nat 8)%N /\
      Datatypes.length (order_token record) = 14 /\
      (order_book_id record < 256 ^ N.of_nat 4)%N /\
      (traded_quantity record < 256 ^ N.of_nat 8)%N /\
      (trade_price record < 256 ^ N.of_nat 4)%N /\
      (match_id record < 256 ^ N.of_nat 8)%N /\
      (combo_group_id record < 256 ^ N.of_nat 4)%N /\
      (deal_source record < 256 ^ N.of_nat 1)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 8 (timestamp_nanoseconds record) ++
      encode_bytes 14 (order_token record) ++
      encode_uint 4 (order_book_id record) ++
      encode_uint 8 (traded_quantity record) ++
      encode_uint 4 (trade_price record) ++
      encode_uint 8 (match_id record) ++
      encode_uint 4 (combo_group_id record) ++
      encode_uint 1 (deal_source record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 8 bytes with
      | None => None
      | Some (timestamp_nanoseconds_value, bytes) =>
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
                          match decode_uint 8 bytes with
                          | None => None
                          | Some (match_id_value, bytes) =>
                              match decode_uint 4 bytes with
                              | None => None
                              | Some (combo_group_id_value, bytes) =>
                                  match decode_uint 1 bytes with
                                  | None => None
                                  | Some (deal_source_value, bytes) =>
                                      Some ({| timestamp_nanoseconds := timestamp_nanoseconds_value; order_token := order_token_value; order_book_id := order_book_id_value; traded_quantity := traded_quantity_value; trade_price := trade_price_value; match_id := match_id_value; combo_group_id := combo_group_id_value; deal_source := deal_source_value |}, bytes)
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
      rewrite decode_encode_uint by exact bound_6.
      rewrite decode_encode_uint by exact bound_7.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End OrderExecuted.

End OseDerivativesGeniumInetV50Server.
