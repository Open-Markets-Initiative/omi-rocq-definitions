From Stdlib Require Import List.
From Stdlib Require Import NArith.
From Stdlib Require Import Lia.
From Stdlib Require Import Strings.Byte.
From Omi Require Import Wire.

Import ListNotations.

(** * National Association of Securities Dealers Automated Quotations (Nasdaq) Nordic Equity TotalView

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
      - the dispatch that chooses a message by its type
      - a run counted by a field
      - a field read in bits
  *)

Module NordicEquitiesTotalViewV3046.

  Module PacketHeader.

    (** Itch Mold Udp 64 Packet Header *)
    Record t := {
      session : list byte;
      sequence_number : N;
      message_count : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (session record) = 10 /\
      (sequence_number record < 256 ^ N.of_nat 8)%N /\
      (message_count record < 256 ^ N.of_nat 2)%N.

    Definition encode (record : t) : list byte :=
      encode_bytes 10 (session record) ++
      encode_uint 8 (sequence_number record) ++
      encode_uint 2 (message_count record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 10 bytes with
      | None => None
      | Some (session_value, bytes) =>
          match decode_uint 8 bytes with
          | None => None
          | Some (sequence_number_value, bytes) =>
              match decode_uint 2 bytes with
              | None => None
              | Some (message_count_value, bytes) =>
                  Some ({| session := session_value; sequence_number := sequence_number_value; message_count := message_count_value |}, bytes)
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 20.
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

  End PacketHeader.

  Module MessageHeader.

    (** Mold Udp 64 Message Header *)
    Record t := {
      message_length : N;
      message_type : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (message_length record < 256 ^ N.of_nat 2)%N /\
      Datatypes.length (message_type record) = 1.

    Definition encode (record : t) : list byte :=
      encode_uint 2 (message_length record) ++
      encode_bytes 1 (message_type record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 2 bytes with
      | None => None
      | Some (message_length_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (message_type_value, bytes) =>
              Some ({| message_length := message_length_value; message_type := message_type_value |}, bytes)
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

  End MessageHeader.

  Module SystemEventMessage.

    (** Signals a market or data feed handler event *)
    Record t := {
      timestamp : N;
      tracking_number : N;
      event_code : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (timestamp record < 256 ^ N.of_nat 8)%N /\
      (tracking_number record < 256 ^ N.of_nat 2)%N /\
      Datatypes.length (event_code record) = 1.

    Definition encode (record : t) : list byte :=
      encode_uint 8 (timestamp record) ++
      encode_uint 2 (tracking_number record) ++
      encode_bytes 1 (event_code record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 8 bytes with
      | None => None
      | Some (timestamp_value, bytes) =>
          match decode_uint 2 bytes with
          | None => None
          | Some (tracking_number_value, bytes) =>
              match decode_bytes 1 bytes with
              | None => None
              | Some (event_code_value, bytes) =>
                  Some ({| timestamp := timestamp_value; tracking_number := tracking_number_value; event_code := event_code_value |}, bytes)
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 11.
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

  End SystemEventMessage.

  Module OrderBookTradingActionMessage.

    (** Indicates the current trading status of a security *)
    Record t := {
      timestamp : N;
      tracking_number : N;
      order_book : N;
      symbol_state : list byte;
      extension : list byte;
      reason : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (timestamp record < 256 ^ N.of_nat 8)%N /\
      (tracking_number record < 256 ^ N.of_nat 2)%N /\
      (order_book record < 256 ^ N.of_nat 4)%N /\
      Datatypes.length (symbol_state record) = 1 /\
      Datatypes.length (extension record) = 1 /\
      Datatypes.length (reason record) = 4.

    Definition encode (record : t) : list byte :=
      encode_uint 8 (timestamp record) ++
      encode_uint 2 (tracking_number record) ++
      encode_uint 4 (order_book record) ++
      encode_bytes 1 (symbol_state record) ++
      encode_bytes 1 (extension record) ++
      encode_bytes 4 (reason record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 8 bytes with
      | None => None
      | Some (timestamp_value, bytes) =>
          match decode_uint 2 bytes with
          | None => None
          | Some (tracking_number_value, bytes) =>
              match decode_uint 4 bytes with
              | None => None
              | Some (order_book_value, bytes) =>
                  match decode_bytes 1 bytes with
                  | None => None
                  | Some (symbol_state_value, bytes) =>
                      match decode_bytes 1 bytes with
                      | None => None
                      | Some (extension_value, bytes) =>
                          match decode_bytes 4 bytes with
                          | None => None
                          | Some (reason_value, bytes) =>
                              Some ({| timestamp := timestamp_value; tracking_number := tracking_number_value; order_book := order_book_value; symbol_state := symbol_state_value; extension := extension_value; reason := reason_value |}, bytes)
                          end
                      end
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 20.
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
      rewrite decode_encode_uint by exact bound_1.
      rewrite decode_encode_uint by exact bound_2.
      rewrite decode_encode_bytes by exact bound_3.
      rewrite decode_encode_bytes by exact bound_4.
      rewrite decode_encode_bytes by exact bound_5.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End OrderBookTradingActionMessage.

  Module AddOrderMessage.

    (** An order added to the book without Mpid attribution *)
    Record t := {
      timestamp : N;
      tracking_number : N;
      order_reference_number : N;
      buy_sell_indicator : list byte;
      quantity : N;
      order_book : N;
      price : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (timestamp record < 256 ^ N.of_nat 8)%N /\
      (tracking_number record < 256 ^ N.of_nat 2)%N /\
      (order_reference_number record < 256 ^ N.of_nat 8)%N /\
      Datatypes.length (buy_sell_indicator record) = 1 /\
      (quantity record < 256 ^ N.of_nat 4)%N /\
      (order_book record < 256 ^ N.of_nat 4)%N /\
      (price record < 256 ^ N.of_nat 4)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 8 (timestamp record) ++
      encode_uint 2 (tracking_number record) ++
      encode_uint 8 (order_reference_number record) ++
      encode_bytes 1 (buy_sell_indicator record) ++
      encode_uint 4 (quantity record) ++
      encode_uint 4 (order_book record) ++
      encode_uint 4 (price record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 8 bytes with
      | None => None
      | Some (timestamp_value, bytes) =>
          match decode_uint 2 bytes with
          | None => None
          | Some (tracking_number_value, bytes) =>
              match decode_uint 8 bytes with
              | None => None
              | Some (order_reference_number_value, bytes) =>
                  match decode_bytes 1 bytes with
                  | None => None
                  | Some (buy_sell_indicator_value, bytes) =>
                      match decode_uint 4 bytes with
                      | None => None
                      | Some (quantity_value, bytes) =>
                          match decode_uint 4 bytes with
                          | None => None
                          | Some (order_book_value, bytes) =>
                              match decode_uint 4 bytes with
                              | None => None
                              | Some (price_value, bytes) =>
                                  Some ({| timestamp := timestamp_value; tracking_number := tracking_number_value; order_reference_number := order_reference_number_value; buy_sell_indicator := buy_sell_indicator_value; quantity := quantity_value; order_book := order_book_value; price := price_value |}, bytes)
                              end
                          end
                      end
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 31.
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
      rewrite decode_encode_uint by exact bound_1.
      rewrite decode_encode_uint by exact bound_2.
      rewrite decode_encode_bytes by exact bound_3.
      rewrite decode_encode_uint by exact bound_4.
      rewrite decode_encode_uint by exact bound_5.
      rewrite decode_encode_uint by exact bound_6.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End AddOrderMessage.

  Module AddOrderMpidAttributionMessage.

    (** An order added to the book with Mpid attribution *)
    Record t := {
      timestamp : N;
      tracking_number : N;
      order_reference_number : N;
      buy_sell_indicator : list byte;
      quantity : N;
      order_book : N;
      price : N;
      attribution : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (timestamp record < 256 ^ N.of_nat 8)%N /\
      (tracking_number record < 256 ^ N.of_nat 2)%N /\
      (order_reference_number record < 256 ^ N.of_nat 8)%N /\
      Datatypes.length (buy_sell_indicator record) = 1 /\
      (quantity record < 256 ^ N.of_nat 4)%N /\
      (order_book record < 256 ^ N.of_nat 4)%N /\
      (price record < 256 ^ N.of_nat 4)%N /\
      Datatypes.length (attribution record) = 4.

    Definition encode (record : t) : list byte :=
      encode_uint 8 (timestamp record) ++
      encode_uint 2 (tracking_number record) ++
      encode_uint 8 (order_reference_number record) ++
      encode_bytes 1 (buy_sell_indicator record) ++
      encode_uint 4 (quantity record) ++
      encode_uint 4 (order_book record) ++
      encode_uint 4 (price record) ++
      encode_bytes 4 (attribution record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 8 bytes with
      | None => None
      | Some (timestamp_value, bytes) =>
          match decode_uint 2 bytes with
          | None => None
          | Some (tracking_number_value, bytes) =>
              match decode_uint 8 bytes with
              | None => None
              | Some (order_reference_number_value, bytes) =>
                  match decode_bytes 1 bytes with
                  | None => None
                  | Some (buy_sell_indicator_value, bytes) =>
                      match decode_uint 4 bytes with
                      | None => None
                      | Some (quantity_value, bytes) =>
                          match decode_uint 4 bytes with
                          | None => None
                          | Some (order_book_value, bytes) =>
                              match decode_uint 4 bytes with
                              | None => None
                              | Some (price_value, bytes) =>
                                  match decode_bytes 4 bytes with
                                  | None => None
                                  | Some (attribution_value, bytes) =>
                                      Some ({| timestamp := timestamp_value; tracking_number := tracking_number_value; order_reference_number := order_reference_number_value; buy_sell_indicator := buy_sell_indicator_value; quantity := quantity_value; order_book := order_book_value; price := price_value; attribution := attribution_value |}, bytes)
                                  end
                              end
                          end
                      end
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 35.
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
      rewrite decode_encode_uint by exact bound_1.
      rewrite decode_encode_uint by exact bound_2.
      rewrite decode_encode_bytes by exact bound_3.
      rewrite decode_encode_uint by exact bound_4.
      rewrite decode_encode_uint by exact bound_5.
      rewrite decode_encode_uint by exact bound_6.
      rewrite decode_encode_bytes by exact bound_7.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End AddOrderMpidAttributionMessage.

  Module OrderExecutedMessage.

    (** Sent whenever an order on the book is executed in whole or in part *)
    Record t := {
      timestamp : N;
      tracking_number : N;
      order_reference_number : N;
      executed_quantity : N;
      match_number : N;
      mpid : list byte;
      mpid_counterparty : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (timestamp record < 256 ^ N.of_nat 8)%N /\
      (tracking_number record < 256 ^ N.of_nat 2)%N /\
      (order_reference_number record < 256 ^ N.of_nat 8)%N /\
      (executed_quantity record < 256 ^ N.of_nat 4)%N /\
      (match_number record < 256 ^ N.of_nat 4)%N /\
      Datatypes.length (mpid record) = 4 /\
      Datatypes.length (mpid_counterparty record) = 4.

    Definition encode (record : t) : list byte :=
      encode_uint 8 (timestamp record) ++
      encode_uint 2 (tracking_number record) ++
      encode_uint 8 (order_reference_number record) ++
      encode_uint 4 (executed_quantity record) ++
      encode_uint 4 (match_number record) ++
      encode_bytes 4 (mpid record) ++
      encode_bytes 4 (mpid_counterparty record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 8 bytes with
      | None => None
      | Some (timestamp_value, bytes) =>
          match decode_uint 2 bytes with
          | None => None
          | Some (tracking_number_value, bytes) =>
              match decode_uint 8 bytes with
              | None => None
              | Some (order_reference_number_value, bytes) =>
                  match decode_uint 4 bytes with
                  | None => None
                  | Some (executed_quantity_value, bytes) =>
                      match decode_uint 4 bytes with
                      | None => None
                      | Some (match_number_value, bytes) =>
                          match decode_bytes 4 bytes with
                          | None => None
                          | Some (mpid_value, bytes) =>
                              match decode_bytes 4 bytes with
                              | None => None
                              | Some (mpid_counterparty_value, bytes) =>
                                  Some ({| timestamp := timestamp_value; tracking_number := tracking_number_value; order_reference_number := order_reference_number_value; executed_quantity := executed_quantity_value; match_number := match_number_value; mpid := mpid_value; mpid_counterparty := mpid_counterparty_value |}, bytes)
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
      rewrite decode_encode_uint by exact bound_1.
      rewrite decode_encode_uint by exact bound_2.
      rewrite decode_encode_uint by exact bound_3.
      rewrite decode_encode_uint by exact bound_4.
      rewrite decode_encode_bytes by exact bound_5.
      rewrite decode_encode_bytes by exact bound_6.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End OrderExecutedMessage.

  Module OrderExecutedWithPriceMessage.

    (** An order executed at a price different to its display price *)
    Record t := {
      timestamp : N;
      tracking_number : N;
      order_reference_number : N;
      executed_quantity : N;
      match_number : N;
      printable : list byte;
      trade_price : N;
      mpid_owner : list byte;
      mpid_counterparty : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (timestamp record < 256 ^ N.of_nat 8)%N /\
      (tracking_number record < 256 ^ N.of_nat 2)%N /\
      (order_reference_number record < 256 ^ N.of_nat 8)%N /\
      (executed_quantity record < 256 ^ N.of_nat 4)%N /\
      (match_number record < 256 ^ N.of_nat 4)%N /\
      Datatypes.length (printable record) = 1 /\
      (trade_price record < 256 ^ N.of_nat 4)%N /\
      Datatypes.length (mpid_owner record) = 4 /\
      Datatypes.length (mpid_counterparty record) = 4.

    Definition encode (record : t) : list byte :=
      encode_uint 8 (timestamp record) ++
      encode_uint 2 (tracking_number record) ++
      encode_uint 8 (order_reference_number record) ++
      encode_uint 4 (executed_quantity record) ++
      encode_uint 4 (match_number record) ++
      encode_bytes 1 (printable record) ++
      encode_uint 4 (trade_price record) ++
      encode_bytes 4 (mpid_owner record) ++
      encode_bytes 4 (mpid_counterparty record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 8 bytes with
      | None => None
      | Some (timestamp_value, bytes) =>
          match decode_uint 2 bytes with
          | None => None
          | Some (tracking_number_value, bytes) =>
              match decode_uint 8 bytes with
              | None => None
              | Some (order_reference_number_value, bytes) =>
                  match decode_uint 4 bytes with
                  | None => None
                  | Some (executed_quantity_value, bytes) =>
                      match decode_uint 4 bytes with
                      | None => None
                      | Some (match_number_value, bytes) =>
                          match decode_bytes 1 bytes with
                          | None => None
                          | Some (printable_value, bytes) =>
                              match decode_uint 4 bytes with
                              | None => None
                              | Some (trade_price_value, bytes) =>
                                  match decode_bytes 4 bytes with
                                  | None => None
                                  | Some (mpid_owner_value, bytes) =>
                                      match decode_bytes 4 bytes with
                                      | None => None
                                      | Some (mpid_counterparty_value, bytes) =>
                                          Some ({| timestamp := timestamp_value; tracking_number := tracking_number_value; order_reference_number := order_reference_number_value; executed_quantity := executed_quantity_value; match_number := match_number_value; printable := printable_value; trade_price := trade_price_value; mpid_owner := mpid_owner_value; mpid_counterparty := mpid_counterparty_value |}, bytes)
                                      end
                                  end
                              end
                          end
                      end
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 39.
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
      rewrite decode_encode_uint by exact bound_2.
      rewrite decode_encode_uint by exact bound_3.
      rewrite decode_encode_uint by exact bound_4.
      rewrite decode_encode_bytes by exact bound_5.
      rewrite decode_encode_uint by exact bound_6.
      rewrite decode_encode_bytes by exact bound_7.
      rewrite decode_encode_bytes by exact bound_8.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End OrderExecutedWithPriceMessage.

  Module OrderCancelMessage.

    (** An order on the book modified by a partial cancellation *)
    Record t := {
      timestamp : N;
      tracking_number : N;
      order_reference_number : N;
      canceled_quantity : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (timestamp record < 256 ^ N.of_nat 8)%N /\
      (tracking_number record < 256 ^ N.of_nat 2)%N /\
      (order_reference_number record < 256 ^ N.of_nat 8)%N /\
      (canceled_quantity record < 256 ^ N.of_nat 4)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 8 (timestamp record) ++
      encode_uint 2 (tracking_number record) ++
      encode_uint 8 (order_reference_number record) ++
      encode_uint 4 (canceled_quantity record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 8 bytes with
      | None => None
      | Some (timestamp_value, bytes) =>
          match decode_uint 2 bytes with
          | None => None
          | Some (tracking_number_value, bytes) =>
              match decode_uint 8 bytes with
              | None => None
              | Some (order_reference_number_value, bytes) =>
                  match decode_uint 4 bytes with
                  | None => None
                  | Some (canceled_quantity_value, bytes) =>
                      Some ({| timestamp := timestamp_value; tracking_number := tracking_number_value; order_reference_number := order_reference_number_value; canceled_quantity := canceled_quantity_value |}, bytes)
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 22.
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

  End OrderCancelMessage.

  Module OrderDeleteMessage.

    (** An order on the book being cancelled in full *)
    Record t := {
      timestamp : N;
      tracking_number : N;
      order_reference_number : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (timestamp record < 256 ^ N.of_nat 8)%N /\
      (tracking_number record < 256 ^ N.of_nat 2)%N /\
      (order_reference_number record < 256 ^ N.of_nat 8)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 8 (timestamp record) ++
      encode_uint 2 (tracking_number record) ++
      encode_uint 8 (order_reference_number record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 8 bytes with
      | None => None
      | Some (timestamp_value, bytes) =>
          match decode_uint 2 bytes with
          | None => None
          | Some (tracking_number_value, bytes) =>
              match decode_uint 8 bytes with
              | None => None
              | Some (order_reference_number_value, bytes) =>
                  Some ({| timestamp := timestamp_value; tracking_number := tracking_number_value; order_reference_number := order_reference_number_value |}, bytes)
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 18.
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

  End OrderDeleteMessage.

  Module OrderBookFlushMessage.

    (** An order book is flushed and all orders removed *)
    Record t := {
      timestamp : N;
      tracking_number : N;
      order_book : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (timestamp record < 256 ^ N.of_nat 8)%N /\
      (tracking_number record < 256 ^ N.of_nat 2)%N /\
      (order_book record < 256 ^ N.of_nat 4)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 8 (timestamp record) ++
      encode_uint 2 (tracking_number record) ++
      encode_uint 4 (order_book record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 8 bytes with
      | None => None
      | Some (timestamp_value, bytes) =>
          match decode_uint 2 bytes with
          | None => None
          | Some (tracking_number_value, bytes) =>
              match decode_uint 4 bytes with
              | None => None
              | Some (order_book_value, bytes) =>
                  Some ({| timestamp := timestamp_value; tracking_number := tracking_number_value; order_book := order_book_value |}, bytes)
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 14.
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

  End OrderBookFlushMessage.

  Module OrderReplaceMessage.

    (** An order on the book has been cancel replaced *)
    Record t := {
      timestamp : N;
      tracking_number : N;
      original_order_reference_number : N;
      new_order_reference_number : N;
      quantity : N;
      price : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (timestamp record < 256 ^ N.of_nat 8)%N /\
      (tracking_number record < 256 ^ N.of_nat 2)%N /\
      (original_order_reference_number record < 256 ^ N.of_nat 8)%N /\
      (new_order_reference_number record < 256 ^ N.of_nat 8)%N /\
      (quantity record < 256 ^ N.of_nat 4)%N /\
      (price record < 256 ^ N.of_nat 4)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 8 (timestamp record) ++
      encode_uint 2 (tracking_number record) ++
      encode_uint 8 (original_order_reference_number record) ++
      encode_uint 8 (new_order_reference_number record) ++
      encode_uint 4 (quantity record) ++
      encode_uint 4 (price record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 8 bytes with
      | None => None
      | Some (timestamp_value, bytes) =>
          match decode_uint 2 bytes with
          | None => None
          | Some (tracking_number_value, bytes) =>
              match decode_uint 8 bytes with
              | None => None
              | Some (original_order_reference_number_value, bytes) =>
                  match decode_uint 8 bytes with
                  | None => None
                  | Some (new_order_reference_number_value, bytes) =>
                      match decode_uint 4 bytes with
                      | None => None
                      | Some (quantity_value, bytes) =>
                          match decode_uint 4 bytes with
                          | None => None
                          | Some (price_value, bytes) =>
                              Some ({| timestamp := timestamp_value; tracking_number := tracking_number_value; original_order_reference_number := original_order_reference_number_value; new_order_reference_number := new_order_reference_number_value; quantity := quantity_value; price := price_value |}, bytes)
                          end
                      end
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 34.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_uint_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 [bound_1 [bound_2 [bound_3 [bound_4 bound_5]]]]].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_uint by exact bound_0.
      rewrite decode_encode_uint by exact bound_1.
      rewrite decode_encode_uint by exact bound_2.
      rewrite decode_encode_uint by exact bound_3.
      rewrite decode_encode_uint by exact bound_4.
      rewrite decode_encode_uint by exact bound_5.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec]. Defined.

  End OrderReplaceMessage.

  Module TradeMessage.

    (** Execution details for a match involving non displayable order types *)
    Record t := {
      timestamp : N;
      tracking_number : N;
      order_reference_number : N;
      trade_type : list byte;
      quantity : N;
      order_book : N;
      match_number : N;
      trade_price : N;
      participant_id_buyer : list byte;
      participant_id_seller : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (timestamp record < 256 ^ N.of_nat 8)%N /\
      (tracking_number record < 256 ^ N.of_nat 2)%N /\
      (order_reference_number record < 256 ^ N.of_nat 8)%N /\
      Datatypes.length (trade_type record) = 1 /\
      (quantity record < 256 ^ N.of_nat 4)%N /\
      (order_book record < 256 ^ N.of_nat 4)%N /\
      (match_number record < 256 ^ N.of_nat 4)%N /\
      (trade_price record < 256 ^ N.of_nat 4)%N /\
      Datatypes.length (participant_id_buyer record) = 4 /\
      Datatypes.length (participant_id_seller record) = 4.

    Definition encode (record : t) : list byte :=
      encode_uint 8 (timestamp record) ++
      encode_uint 2 (tracking_number record) ++
      encode_uint 8 (order_reference_number record) ++
      encode_bytes 1 (trade_type record) ++
      encode_uint 4 (quantity record) ++
      encode_uint 4 (order_book record) ++
      encode_uint 4 (match_number record) ++
      encode_uint 4 (trade_price record) ++
      encode_bytes 4 (participant_id_buyer record) ++
      encode_bytes 4 (participant_id_seller record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 8 bytes with
      | None => None
      | Some (timestamp_value, bytes) =>
          match decode_uint 2 bytes with
          | None => None
          | Some (tracking_number_value, bytes) =>
              match decode_uint 8 bytes with
              | None => None
              | Some (order_reference_number_value, bytes) =>
                  match decode_bytes 1 bytes with
                  | None => None
                  | Some (trade_type_value, bytes) =>
                      match decode_uint 4 bytes with
                      | None => None
                      | Some (quantity_value, bytes) =>
                          match decode_uint 4 bytes with
                          | None => None
                          | Some (order_book_value, bytes) =>
                              match decode_uint 4 bytes with
                              | None => None
                              | Some (match_number_value, bytes) =>
                                  match decode_uint 4 bytes with
                                  | None => None
                                  | Some (trade_price_value, bytes) =>
                                      match decode_bytes 4 bytes with
                                      | None => None
                                      | Some (participant_id_buyer_value, bytes) =>
                                          match decode_bytes 4 bytes with
                                          | None => None
                                          | Some (participant_id_seller_value, bytes) =>
                                              Some ({| timestamp := timestamp_value; tracking_number := tracking_number_value; order_reference_number := order_reference_number_value; trade_type := trade_type_value; quantity := quantity_value; order_book := order_book_value; match_number := match_number_value; trade_price := trade_price_value; participant_id_buyer := participant_id_buyer_value; participant_id_seller := participant_id_seller_value |}, bytes)
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

    Theorem encode_length : forall record, Datatypes.length (encode record) = 43.
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
      rewrite decode_encode_uint by exact bound_2.
      rewrite decode_encode_bytes by exact bound_3.
      rewrite decode_encode_uint by exact bound_4.
      rewrite decode_encode_uint by exact bound_5.
      rewrite decode_encode_uint by exact bound_6.
      rewrite decode_encode_uint by exact bound_7.
      rewrite decode_encode_bytes by exact bound_8.
      rewrite decode_encode_bytes by exact bound_9.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End TradeMessage.

  Module CrossTradeMessage.

    (** The cross process has completed for a specific security *)
    Record t := {
      timestamp : N;
      tracking_number : N;
      quantity : N;
      order_book : N;
      cross_price : N;
      match_number : N;
      cross_type : list byte;
      number_of_trades : N;
      avd_quantity : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (timestamp record < 256 ^ N.of_nat 8)%N /\
      (tracking_number record < 256 ^ N.of_nat 2)%N /\
      (quantity record < 256 ^ N.of_nat 4)%N /\
      (order_book record < 256 ^ N.of_nat 4)%N /\
      (cross_price record < 256 ^ N.of_nat 4)%N /\
      (match_number record < 256 ^ N.of_nat 4)%N /\
      Datatypes.length (cross_type record) = 1 /\
      (number_of_trades record < 256 ^ N.of_nat 4)%N /\
      (avd_quantity record < 256 ^ N.of_nat 4)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 8 (timestamp record) ++
      encode_uint 2 (tracking_number record) ++
      encode_uint 4 (quantity record) ++
      encode_uint 4 (order_book record) ++
      encode_uint 4 (cross_price record) ++
      encode_uint 4 (match_number record) ++
      encode_bytes 1 (cross_type record) ++
      encode_uint 4 (number_of_trades record) ++
      encode_uint 4 (avd_quantity record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 8 bytes with
      | None => None
      | Some (timestamp_value, bytes) =>
          match decode_uint 2 bytes with
          | None => None
          | Some (tracking_number_value, bytes) =>
              match decode_uint 4 bytes with
              | None => None
              | Some (quantity_value, bytes) =>
                  match decode_uint 4 bytes with
                  | None => None
                  | Some (order_book_value, bytes) =>
                      match decode_uint 4 bytes with
                      | None => None
                      | Some (cross_price_value, bytes) =>
                          match decode_uint 4 bytes with
                          | None => None
                          | Some (match_number_value, bytes) =>
                              match decode_bytes 1 bytes with
                              | None => None
                              | Some (cross_type_value, bytes) =>
                                  match decode_uint 4 bytes with
                                  | None => None
                                  | Some (number_of_trades_value, bytes) =>
                                      match decode_uint 4 bytes with
                                      | None => None
                                      | Some (avd_quantity_value, bytes) =>
                                          Some ({| timestamp := timestamp_value; tracking_number := tracking_number_value; quantity := quantity_value; order_book := order_book_value; cross_price := cross_price_value; match_number := match_number_value; cross_type := cross_type_value; number_of_trades := number_of_trades_value; avd_quantity := avd_quantity_value |}, bytes)
                                      end
                                  end
                              end
                          end
                      end
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 35.
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
      rewrite decode_encode_uint by exact bound_2.
      rewrite decode_encode_uint by exact bound_3.
      rewrite decode_encode_uint by exact bound_4.
      rewrite decode_encode_uint by exact bound_5.
      rewrite decode_encode_bytes by exact bound_6.
      rewrite decode_encode_uint by exact bound_7.
      rewrite decode_encode_uint by exact bound_8.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End CrossTradeMessage.

  Module BrokenTradeMessage.

    (** An execution has been broken and cannot be reinstated *)
    Record t := {
      timestamp : N;
      tracking_number : N;
      match_number : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (timestamp record < 256 ^ N.of_nat 8)%N /\
      (tracking_number record < 256 ^ N.of_nat 2)%N /\
      (match_number record < 256 ^ N.of_nat 4)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 8 (timestamp record) ++
      encode_uint 2 (tracking_number record) ++
      encode_uint 4 (match_number record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 8 bytes with
      | None => None
      | Some (timestamp_value, bytes) =>
          match decode_uint 2 bytes with
          | None => None
          | Some (tracking_number_value, bytes) =>
              match decode_uint 4 bytes with
              | None => None
              | Some (match_number_value, bytes) =>
                  Some ({| timestamp := timestamp_value; tracking_number := tracking_number_value; match_number := match_number_value |}, bytes)
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 14.
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

  End BrokenTradeMessage.

  Module NoiiMessage.

    (** Net order imbalance indicator disseminated during a cross auction *)
    Record t := {
      timestamp : N;
      tracking_number : N;
      paired_quantity : N;
      imbalance_quantity : N;
      imbalance_direction : list byte;
      order_book : N;
      equilibrium_price : N;
      cross_type : list byte;
      best_bid_price : N;
      best_bid_quantity : N;
      best_ask_price : N;
      best_ask_quantity : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (timestamp record < 256 ^ N.of_nat 8)%N /\
      (tracking_number record < 256 ^ N.of_nat 2)%N /\
      (paired_quantity record < 256 ^ N.of_nat 8)%N /\
      (imbalance_quantity record < 256 ^ N.of_nat 8)%N /\
      Datatypes.length (imbalance_direction record) = 1 /\
      (order_book record < 256 ^ N.of_nat 4)%N /\
      (equilibrium_price record < 256 ^ N.of_nat 4)%N /\
      Datatypes.length (cross_type record) = 1 /\
      (best_bid_price record < 256 ^ N.of_nat 4)%N /\
      (best_bid_quantity record < 256 ^ N.of_nat 8)%N /\
      (best_ask_price record < 256 ^ N.of_nat 4)%N /\
      (best_ask_quantity record < 256 ^ N.of_nat 8)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 8 (timestamp record) ++
      encode_uint 2 (tracking_number record) ++
      encode_uint 8 (paired_quantity record) ++
      encode_uint 8 (imbalance_quantity record) ++
      encode_bytes 1 (imbalance_direction record) ++
      encode_uint 4 (order_book record) ++
      encode_uint 4 (equilibrium_price record) ++
      encode_bytes 1 (cross_type record) ++
      encode_uint 4 (best_bid_price record) ++
      encode_uint 8 (best_bid_quantity record) ++
      encode_uint 4 (best_ask_price record) ++
      encode_uint 8 (best_ask_quantity record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 8 bytes with
      | None => None
      | Some (timestamp_value, bytes) =>
          match decode_uint 2 bytes with
          | None => None
          | Some (tracking_number_value, bytes) =>
              match decode_uint 8 bytes with
              | None => None
              | Some (paired_quantity_value, bytes) =>
                  match decode_uint 8 bytes with
                  | None => None
                  | Some (imbalance_quantity_value, bytes) =>
                      match decode_bytes 1 bytes with
                      | None => None
                      | Some (imbalance_direction_value, bytes) =>
                          match decode_uint 4 bytes with
                          | None => None
                          | Some (order_book_value, bytes) =>
                              match decode_uint 4 bytes with
                              | None => None
                              | Some (equilibrium_price_value, bytes) =>
                                  match decode_bytes 1 bytes with
                                  | None => None
                                  | Some (cross_type_value, bytes) =>
                                      match decode_uint 4 bytes with
                                      | None => None
                                      | Some (best_bid_price_value, bytes) =>
                                          match decode_uint 8 bytes with
                                          | None => None
                                          | Some (best_bid_quantity_value, bytes) =>
                                              match decode_uint 4 bytes with
                                              | None => None
                                              | Some (best_ask_price_value, bytes) =>
                                                  match decode_uint 8 bytes with
                                                  | None => None
                                                  | Some (best_ask_quantity_value, bytes) =>
                                                      Some ({| timestamp := timestamp_value; tracking_number := tracking_number_value; paired_quantity := paired_quantity_value; imbalance_quantity := imbalance_quantity_value; imbalance_direction := imbalance_direction_value; order_book := order_book_value; equilibrium_price := equilibrium_price_value; cross_type := cross_type_value; best_bid_price := best_bid_price_value; best_bid_quantity := best_bid_quantity_value; best_ask_price := best_ask_price_value; best_ask_quantity := best_ask_quantity_value |}, bytes)
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

    Theorem encode_length : forall record, Datatypes.length (encode record) = 60.
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
      rewrite decode_encode_uint by exact bound_1.
      rewrite decode_encode_uint by exact bound_2.
      rewrite decode_encode_uint by exact bound_3.
      rewrite decode_encode_bytes by exact bound_4.
      rewrite decode_encode_uint by exact bound_5.
      rewrite decode_encode_uint by exact bound_6.
      rewrite decode_encode_bytes by exact bound_7.
      rewrite decode_encode_uint by exact bound_8.
      rewrite decode_encode_uint by exact bound_9.
      rewrite decode_encode_uint by exact bound_10.
      rewrite decode_encode_uint by exact bound_11.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End NoiiMessage.

  Module MoiiMessage.

    (** Auction on demand order imbalance indicator *)
    Record t := {
      timestamp : N;
      tracking_number : N;
      paired_quantity : N;
      order_book : N;
      equilibrium_price : N;
      cross_type : list byte;
      cross_level : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (timestamp record < 256 ^ N.of_nat 8)%N /\
      (tracking_number record < 256 ^ N.of_nat 2)%N /\
      (paired_quantity record < 256 ^ N.of_nat 8)%N /\
      (order_book record < 256 ^ N.of_nat 4)%N /\
      (equilibrium_price record < 256 ^ N.of_nat 4)%N /\
      Datatypes.length (cross_type record) = 1 /\
      Datatypes.length (cross_level record) = 1.

    Definition encode (record : t) : list byte :=
      encode_uint 8 (timestamp record) ++
      encode_uint 2 (tracking_number record) ++
      encode_uint 8 (paired_quantity record) ++
      encode_uint 4 (order_book record) ++
      encode_uint 4 (equilibrium_price record) ++
      encode_bytes 1 (cross_type record) ++
      encode_bytes 1 (cross_level record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 8 bytes with
      | None => None
      | Some (timestamp_value, bytes) =>
          match decode_uint 2 bytes with
          | None => None
          | Some (tracking_number_value, bytes) =>
              match decode_uint 8 bytes with
              | None => None
              | Some (paired_quantity_value, bytes) =>
                  match decode_uint 4 bytes with
                  | None => None
                  | Some (order_book_value, bytes) =>
                      match decode_uint 4 bytes with
                      | None => None
                      | Some (equilibrium_price_value, bytes) =>
                          match decode_bytes 1 bytes with
                          | None => None
                          | Some (cross_type_value, bytes) =>
                              match decode_bytes 1 bytes with
                              | None => None
                              | Some (cross_level_value, bytes) =>
                                  Some ({| timestamp := timestamp_value; tracking_number := tracking_number_value; paired_quantity := paired_quantity_value; order_book := order_book_value; equilibrium_price := equilibrium_price_value; cross_type := cross_type_value; cross_level := cross_level_value |}, bytes)
                              end
                          end
                      end
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 28.
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
      rewrite decode_encode_uint by exact bound_1.
      rewrite decode_encode_uint by exact bound_2.
      rewrite decode_encode_uint by exact bound_3.
      rewrite decode_encode_uint by exact bound_4.
      rewrite decode_encode_bytes by exact bound_5.
      rewrite decode_encode_bytes by exact bound_6.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End MoiiMessage.

  Module ExecutionSummaryMessage.

    (** Summary information disseminated before the individual trades *)
    Record t := {
      timestamp : N;
      tracking_number : N;
      order_book : N;
      aggressing_side : list byte;
      quantity : N;
      hidden_quantity : N;
      stp_cancel_quantity : N;
      far_price : N;
      add_quantity : N;
      number_of_lit_executions : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (timestamp record < 256 ^ N.of_nat 8)%N /\
      (tracking_number record < 256 ^ N.of_nat 2)%N /\
      (order_book record < 256 ^ N.of_nat 4)%N /\
      Datatypes.length (aggressing_side record) = 1 /\
      (quantity record < 256 ^ N.of_nat 4)%N /\
      (hidden_quantity record < 256 ^ N.of_nat 4)%N /\
      (stp_cancel_quantity record < 256 ^ N.of_nat 4)%N /\
      (far_price record < 256 ^ N.of_nat 4)%N /\
      (add_quantity record < 256 ^ N.of_nat 4)%N /\
      (number_of_lit_executions record < 256 ^ N.of_nat 2)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 8 (timestamp record) ++
      encode_uint 2 (tracking_number record) ++
      encode_uint 4 (order_book record) ++
      encode_bytes 1 (aggressing_side record) ++
      encode_uint 4 (quantity record) ++
      encode_uint 4 (hidden_quantity record) ++
      encode_uint 4 (stp_cancel_quantity record) ++
      encode_uint 4 (far_price record) ++
      encode_uint 4 (add_quantity record) ++
      encode_uint 2 (number_of_lit_executions record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 8 bytes with
      | None => None
      | Some (timestamp_value, bytes) =>
          match decode_uint 2 bytes with
          | None => None
          | Some (tracking_number_value, bytes) =>
              match decode_uint 4 bytes with
              | None => None
              | Some (order_book_value, bytes) =>
                  match decode_bytes 1 bytes with
                  | None => None
                  | Some (aggressing_side_value, bytes) =>
                      match decode_uint 4 bytes with
                      | None => None
                      | Some (quantity_value, bytes) =>
                          match decode_uint 4 bytes with
                          | None => None
                          | Some (hidden_quantity_value, bytes) =>
                              match decode_uint 4 bytes with
                              | None => None
                              | Some (stp_cancel_quantity_value, bytes) =>
                                  match decode_uint 4 bytes with
                                  | None => None
                                  | Some (far_price_value, bytes) =>
                                      match decode_uint 4 bytes with
                                      | None => None
                                      | Some (add_quantity_value, bytes) =>
                                          match decode_uint 2 bytes with
                                          | None => None
                                          | Some (number_of_lit_executions_value, bytes) =>
                                              Some ({| timestamp := timestamp_value; tracking_number := tracking_number_value; order_book := order_book_value; aggressing_side := aggressing_side_value; quantity := quantity_value; hidden_quantity := hidden_quantity_value; stp_cancel_quantity := stp_cancel_quantity_value; far_price := far_price_value; add_quantity := add_quantity_value; number_of_lit_executions := number_of_lit_executions_value |}, bytes)
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

    Theorem encode_length : forall record, Datatypes.length (encode record) = 37.
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
      rewrite decode_encode_uint by exact bound_2.
      rewrite decode_encode_bytes by exact bound_3.
      rewrite decode_encode_uint by exact bound_4.
      rewrite decode_encode_uint by exact bound_5.
      rewrite decode_encode_uint by exact bound_6.
      rewrite decode_encode_uint by exact bound_7.
      rewrite decode_encode_uint by exact bound_8.
      rewrite decode_encode_uint by exact bound_9.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End ExecutionSummaryMessage.

End NordicEquitiesTotalViewV3046.
