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
      - a run counted by a field
  *)

Module BorsaIstanbulGeniumInetV20250206Client.

  Module ClientPacketHeader.

    (** Packet header of a packet sent by the client *)
    Record t := {
      packet_length : N;
      client_packet_type : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (packet_length record < 256 ^ N.of_nat 2)%N /\
      Datatypes.length (client_packet_type record) = 1.

    Definition encode (record : t) : list byte :=
      encode_uint 2 (packet_length record) ++
      encode_bytes 1 (client_packet_type record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 2 bytes with
      | None => None
      | Some (packet_length_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (client_packet_type_value, bytes) =>
              Some ({| packet_length := packet_length_value; client_packet_type := client_packet_type_value |}, bytes)
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

  End ClientPacketHeader.

  Module LoginRequestPacket.

    (** The SoupBinTCP client must send a Login Request Packet immediately upon establishing a new TCP/IP socket connection to the server *)
    Record t := {
      username : list byte;
      password : list byte;
      requested_session : list byte;
      requested_sequence_number : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (username record) = 6 /\
      Datatypes.length (password record) = 10 /\
      Datatypes.length (requested_session record) = 10 /\
      Datatypes.length (requested_sequence_number record) = 20.

    Definition encode (record : t) : list byte :=
      encode_bytes 6 (username record) ++
      encode_bytes 10 (password record) ++
      encode_bytes 10 (requested_session record) ++
      encode_bytes 20 (requested_sequence_number record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 6 bytes with
      | None => None
      | Some (username_value, bytes) =>
          match decode_bytes 10 bytes with
          | None => None
          | Some (password_value, bytes) =>
              match decode_bytes 10 bytes with
              | None => None
              | Some (requested_session_value, bytes) =>
                  match decode_bytes 20 bytes with
                  | None => None
                  | Some (requested_sequence_number_value, bytes) =>
                      Some ({| username := username_value; password := password_value; requested_session := requested_session_value; requested_sequence_number := requested_sequence_number_value |}, bytes)
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 46.
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

  End LoginRequestPacket.

  Module EnterOrder.

    (** Enters a new order into the system. The response to a successful Enter Order is an Order Accepted message. If the order is rejected, the Order Rejected message will be returned. *)
    Record t := {
      order_token : list byte;
      order_book_id : N;
      side : list byte;
      quantity : N;
      price : N;
      time_in_force : N;
      open_close : N;
      client_account : list byte;
      customer_info : list byte;
      exchange_info_alpha_32 : list byte;
      display_quantity : N;
      client_category : N;
      off_hours : N;
      smp_level : N;
      smp_method : N;
      smp_id : list byte;
      reserved_numeric_unsigned_2 : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (order_token record) = 14 /\
      (order_book_id record < 256 ^ N.of_nat 4)%N /\
      Datatypes.length (side record) = 1 /\
      (quantity record < 256 ^ N.of_nat 8)%N /\
      (price record < 256 ^ N.of_nat 4)%N /\
      (time_in_force record < 256 ^ N.of_nat 1)%N /\
      (open_close record < 256 ^ N.of_nat 1)%N /\
      Datatypes.length (client_account record) = 16 /\
      Datatypes.length (customer_info record) = 15 /\
      Datatypes.length (exchange_info_alpha_32 record) = 32 /\
      (display_quantity record < 256 ^ N.of_nat 8)%N /\
      (client_category record < 256 ^ N.of_nat 1)%N /\
      (off_hours record < 256 ^ N.of_nat 1)%N /\
      (smp_level record < 256 ^ N.of_nat 1)%N /\
      (smp_method record < 256 ^ N.of_nat 1)%N /\
      Datatypes.length (smp_id record) = 3 /\
      (reserved_numeric_unsigned_2 record < 256 ^ N.of_nat 2)%N.

    Definition encode (record : t) : list byte :=
      encode_bytes 14 (order_token record) ++
      encode_uint 4 (order_book_id record) ++
      encode_bytes 1 (side record) ++
      encode_uint 8 (quantity record) ++
      encode_uint 4 (price record) ++
      encode_uint 1 (time_in_force record) ++
      encode_uint 1 (open_close record) ++
      encode_bytes 16 (client_account record) ++
      encode_bytes 15 (customer_info record) ++
      encode_bytes 32 (exchange_info_alpha_32 record) ++
      encode_uint 8 (display_quantity record) ++
      encode_uint 1 (client_category record) ++
      encode_uint 1 (off_hours record) ++
      encode_uint 1 (smp_level record) ++
      encode_uint 1 (smp_method record) ++
      encode_bytes 3 (smp_id record) ++
      encode_uint 2 (reserved_numeric_unsigned_2 record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
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
                                      match decode_bytes 15 bytes with
                                      | None => None
                                      | Some (customer_info_value, bytes) =>
                                          match decode_bytes 32 bytes with
                                          | None => None
                                          | Some (exchange_info_alpha_32_value, bytes) =>
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
                                                                      match decode_uint 2 bytes with
                                                                      | None => None
                                                                      | Some (reserved_numeric_unsigned_2_value, bytes) =>
                                                                          Some ({| order_token := order_token_value; order_book_id := order_book_id_value; side := side_value; quantity := quantity_value; price := price_value; time_in_force := time_in_force_value; open_close := open_close_value; client_account := client_account_value; customer_info := customer_info_value; exchange_info_alpha_32 := exchange_info_alpha_32_value; display_quantity := display_quantity_value; client_category := client_category_value; off_hours := off_hours_value; smp_level := smp_level_value; smp_method := smp_method_value; smp_id := smp_id_value; reserved_numeric_unsigned_2 := reserved_numeric_unsigned_2_value |}, bytes)
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

    Theorem encode_length : forall record, Datatypes.length (encode record) = 113.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_bytes_length, !encode_uint_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 [bound_1 [bound_2 [bound_3 [bound_4 [bound_5 [bound_6 [bound_7 [bound_8 [bound_9 [bound_10 [bound_11 [bound_12 [bound_13 [bound_14 [bound_15 bound_16]]]]]]]]]]]]]]]].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_bytes by exact bound_0.
      rewrite decode_encode_uint by exact bound_1.
      rewrite decode_encode_bytes by exact bound_2.
      rewrite decode_encode_uint by exact bound_3.
      rewrite decode_encode_uint by exact bound_4.
      rewrite decode_encode_uint by exact bound_5.
      rewrite decode_encode_uint by exact bound_6.
      rewrite decode_encode_bytes by exact bound_7.
      rewrite decode_encode_bytes by exact bound_8.
      rewrite decode_encode_bytes by exact bound_9.
      rewrite decode_encode_uint by exact bound_10.
      rewrite decode_encode_uint by exact bound_11.
      rewrite decode_encode_uint by exact bound_12.
      rewrite decode_encode_uint by exact bound_13.
      rewrite decode_encode_uint by exact bound_14.
      rewrite decode_encode_bytes by exact bound_15.
      rewrite decode_encode_uint by exact bound_16.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End EnterOrder.

  Module ReplaceOrder.

    (** Modifies an existing order entered via OUCH. The response is an Order Replaced message if the modification was successful, or an Order Rejected message if the replace failed. *)
    Record t := {
      existing_order_token : list byte;
      replacement_order_token : list byte;
      quantity : N;
      price : N;
      replace_open_close : N;
      client_account : list byte;
      customer_info : list byte;
      exchange_info_alpha_32 : list byte;
      display_quantity : N;
      client_category : N;
      reserved_numeric_unsigned_8 : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (existing_order_token record) = 14 /\
      Datatypes.length (replacement_order_token record) = 14 /\
      (quantity record < 256 ^ N.of_nat 8)%N /\
      (price record < 256 ^ N.of_nat 4)%N /\
      (replace_open_close record < 256 ^ N.of_nat 1)%N /\
      Datatypes.length (client_account record) = 16 /\
      Datatypes.length (customer_info record) = 15 /\
      Datatypes.length (exchange_info_alpha_32 record) = 32 /\
      (display_quantity record < 256 ^ N.of_nat 8)%N /\
      (client_category record < 256 ^ N.of_nat 1)%N /\
      (reserved_numeric_unsigned_8 record < 256 ^ N.of_nat 8)%N.

    Definition encode (record : t) : list byte :=
      encode_bytes 14 (existing_order_token record) ++
      encode_bytes 14 (replacement_order_token record) ++
      encode_uint 8 (quantity record) ++
      encode_uint 4 (price record) ++
      encode_uint 1 (replace_open_close record) ++
      encode_bytes 16 (client_account record) ++
      encode_bytes 15 (customer_info record) ++
      encode_bytes 32 (exchange_info_alpha_32 record) ++
      encode_uint 8 (display_quantity record) ++
      encode_uint 1 (client_category record) ++
      encode_uint 8 (reserved_numeric_unsigned_8 record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 14 bytes with
      | None => None
      | Some (existing_order_token_value, bytes) =>
          match decode_bytes 14 bytes with
          | None => None
          | Some (replacement_order_token_value, bytes) =>
              match decode_uint 8 bytes with
              | None => None
              | Some (quantity_value, bytes) =>
                  match decode_uint 4 bytes with
                  | None => None
                  | Some (price_value, bytes) =>
                      match decode_uint 1 bytes with
                      | None => None
                      | Some (replace_open_close_value, bytes) =>
                          match decode_bytes 16 bytes with
                          | None => None
                          | Some (client_account_value, bytes) =>
                              match decode_bytes 15 bytes with
                              | None => None
                              | Some (customer_info_value, bytes) =>
                                  match decode_bytes 32 bytes with
                                  | None => None
                                  | Some (exchange_info_alpha_32_value, bytes) =>
                                      match decode_uint 8 bytes with
                                      | None => None
                                      | Some (display_quantity_value, bytes) =>
                                          match decode_uint 1 bytes with
                                          | None => None
                                          | Some (client_category_value, bytes) =>
                                              match decode_uint 8 bytes with
                                              | None => None
                                              | Some (reserved_numeric_unsigned_8_value, bytes) =>
                                                  Some ({| existing_order_token := existing_order_token_value; replacement_order_token := replacement_order_token_value; quantity := quantity_value; price := price_value; replace_open_close := replace_open_close_value; client_account := client_account_value; customer_info := customer_info_value; exchange_info_alpha_32 := exchange_info_alpha_32_value; display_quantity := display_quantity_value; client_category := client_category_value; reserved_numeric_unsigned_8 := reserved_numeric_unsigned_8_value |}, bytes)
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

    Theorem encode_length : forall record, Datatypes.length (encode record) = 121.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_bytes_length, !encode_uint_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 [bound_1 [bound_2 [bound_3 [bound_4 [bound_5 [bound_6 [bound_7 [bound_8 [bound_9 bound_10]]]]]]]]]].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_bytes by exact bound_0.
      rewrite decode_encode_bytes by exact bound_1.
      rewrite decode_encode_uint by exact bound_2.
      rewrite decode_encode_uint by exact bound_3.
      rewrite decode_encode_uint by exact bound_4.
      rewrite decode_encode_bytes by exact bound_5.
      rewrite decode_encode_bytes by exact bound_6.
      rewrite decode_encode_bytes by exact bound_7.
      rewrite decode_encode_uint by exact bound_8.
      rewrite decode_encode_uint by exact bound_9.
      rewrite decode_encode_uint by exact bound_10.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End ReplaceOrder.

  Module CancelOrder.

    (** Cancels an existing order entered via OUCH. Partial cancels are not supported; use Replace Order to modify an existing order. The response to a successful Cancel Order is an Order Canceled message. Failed Cancel Order messages are rejected with the Order Rejected message. *)
    Record t := {
      order_token : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (order_token record) = 14.

    Definition encode (record : t) : list byte :=
      encode_bytes 14 (order_token record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 14 bytes with
      | None => None
      | Some (order_token_value, bytes) =>
          Some ({| order_token := order_token_value |}, bytes)
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 14.
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

  End CancelOrder.

  Module CancelByOrderId.

    (** Cancels any order in the book, regardless of which session it was inserted over, using the system-generated Order ID. The response to a successful Cancel by Order Id is an Order Canceled message. Failed requests are rejected with the Order Rejected message. *)
    Record t := {
      order_book_id : N;
      side : list byte;
      order_id : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (order_book_id record < 256 ^ N.of_nat 4)%N /\
      Datatypes.length (side record) = 1 /\
      (order_id record < 256 ^ N.of_nat 8)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 4 (order_book_id record) ++
      encode_bytes 1 (side record) ++
      encode_uint 8 (order_id record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 4 bytes with
      | None => None
      | Some (order_book_id_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (side_value, bytes) =>
              match decode_uint 8 bytes with
              | None => None
              | Some (order_id_value, bytes) =>
                  Some ({| order_book_id := order_book_id_value; side := side_value; order_id := order_id_value |}, bytes)
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 13.
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

  End CancelByOrderId.

End BorsaIstanbulGeniumInetV20250206Client.
