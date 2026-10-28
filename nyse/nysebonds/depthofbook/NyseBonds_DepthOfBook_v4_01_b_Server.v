From Stdlib Require Import List.
From Stdlib Require Import NArith.
From Stdlib Require Import Lia.
From Stdlib Require Import Strings.Byte.
From Omi Require Import Wire.

Import ListNotations.

(** * New York Stock Exchange DepthOfBook

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
  *)

Module NyseBondsDepthOfBookV401BServer.

  Module MessageHeader.

    (** Nyse Arca Binary Protocol message header *)
    Record t := {
      message_body_length : N;
      message_type : list byte;
      padding : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (message_body_length record < 256 ^ N.of_nat 2)%N /\
      Datatypes.length (message_type record) = 1 /\
      Datatypes.length (padding record) = 1.

    Definition encode (record : t) : list byte :=
      encode_uint 2 (message_body_length record) ++
      encode_bytes 1 (message_type record) ++
      encode_bytes 1 (padding record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 2 bytes with
      | None => None
      | Some (message_body_length_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (message_type_value, bytes) =>
              match decode_bytes 1 bytes with
              | None => None
              | Some (padding_value, bytes) =>
                  Some ({| message_body_length := message_body_length_value; message_type := message_type_value; padding := padding_value |}, bytes)
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
      rewrite decode_encode_bytes by exact bound_1.
      rewrite decode_encode_bytes by exact bound_2.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End MessageHeader.

  Module LoginAcceptedMessage.

    (** Sent to indicate a successful login. Carries the current version of the Nyse ArcaBook protocol. *)
    Record t := {
      version_id : list byte;
      padding_ascii_1 : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (version_id record) = 5 /\
      Datatypes.length (padding_ascii_1 record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 5 (version_id record) ++
      encode_bytes 1 (padding_ascii_1 record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 5 bytes with
      | None => None
      | Some (version_id_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (padding_ascii_1_value, bytes) =>
              Some ({| version_id := version_id_value; padding_ascii_1 := padding_ascii_1_value |}, bytes)
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 6.
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

  End LoginAcceptedMessage.

  Module LoginRejectedMessage.

    (** Sent when login fails authentication, the client does not log in within 5 seconds, no order data feed was subscribed to, the sequence number was invalid, no connections are available, or a timeout occurred. The socket is closed afterwards. *)
    Record t := {
      reject_code : list byte;
      padding_ascii_1 : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (reject_code record) = 1 /\
      Datatypes.length (padding_ascii_1 record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 1 (reject_code record) ++
      encode_bytes 1 (padding_ascii_1 record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 1 bytes with
      | None => None
      | Some (reject_code_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (padding_ascii_1_value, bytes) =>
              Some ({| reject_code := reject_code_value; padding_ascii_1 := padding_ascii_1_value |}, bytes)
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 2.
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

  End LoginRejectedMessage.

  Module TestResponseMessage.

    (** Sent in response to a Test Request, echoing back any text the request carried. *)
    Record t := {
      test_message : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (test_message record) = 20.

    Definition encode (record : t) : list byte :=
      encode_bytes 20 (test_message record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 20 bytes with
      | None => None
      | Some (test_message_value, bytes) =>
          Some ({| test_message := test_message_value |}, bytes)
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

  End TestResponseMessage.

  Module AddOrderMessage.

    (** Sent for a new open order. The Order Reference Number is unique per order book, while the Sequence Number is unique across all order books. *)
    Record t := {
      time : N;
      sequence_number : N;
      order_reference_number : N;
      quantity : N;
      price : N;
      price_scale_code : list byte;
      exchange_code : list byte;
      system_code : list byte;
      buy_sell_indicator : list byte;
      flat_pricing : list byte;
      trading_action : N;
      security_type : N;
      order_type : N;
      nyse_bond_symbol : list byte;
      cusip_isin : list byte;
      quote_id : list byte;
      padding_ascii_3 : list byte;
      minimum_quantity : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (time record < 256 ^ N.of_nat 4)%N /\
      (sequence_number record < 256 ^ N.of_nat 4)%N /\
      (order_reference_number record < 256 ^ N.of_nat 4)%N /\
      (quantity record < 256 ^ N.of_nat 4)%N /\
      (price record < 256 ^ N.of_nat 4)%N /\
      Datatypes.length (price_scale_code record) = 1 /\
      Datatypes.length (exchange_code record) = 1 /\
      Datatypes.length (system_code record) = 1 /\
      Datatypes.length (buy_sell_indicator record) = 1 /\
      Datatypes.length (flat_pricing record) = 1 /\
      (trading_action record < 256 ^ N.of_nat 1)%N /\
      (security_type record < 256 ^ N.of_nat 1)%N /\
      (order_type record < 256 ^ N.of_nat 1)%N /\
      Datatypes.length (nyse_bond_symbol record) = 22 /\
      Datatypes.length (cusip_isin record) = 14 /\
      Datatypes.length (quote_id record) = 5 /\
      Datatypes.length (padding_ascii_3 record) = 3 /\
      (minimum_quantity record < 256 ^ N.of_nat 4)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 4 (time record) ++
      encode_uint 4 (sequence_number record) ++
      encode_uint 4 (order_reference_number record) ++
      encode_uint 4 (quantity record) ++
      encode_uint 4 (price record) ++
      encode_bytes 1 (price_scale_code record) ++
      encode_bytes 1 (exchange_code record) ++
      encode_bytes 1 (system_code record) ++
      encode_bytes 1 (buy_sell_indicator record) ++
      encode_bytes 1 (flat_pricing record) ++
      encode_uint 1 (trading_action record) ++
      encode_uint 1 (security_type record) ++
      encode_uint 1 (order_type record) ++
      encode_bytes 22 (nyse_bond_symbol record) ++
      encode_bytes 14 (cusip_isin record) ++
      encode_bytes 5 (quote_id record) ++
      encode_bytes 3 (padding_ascii_3 record) ++
      encode_uint 4 (minimum_quantity record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 4 bytes with
      | None => None
      | Some (time_value, bytes) =>
          match decode_uint 4 bytes with
          | None => None
          | Some (sequence_number_value, bytes) =>
              match decode_uint 4 bytes with
              | None => None
              | Some (order_reference_number_value, bytes) =>
                  match decode_uint 4 bytes with
                  | None => None
                  | Some (quantity_value, bytes) =>
                      match decode_uint 4 bytes with
                      | None => None
                      | Some (price_value, bytes) =>
                          match decode_bytes 1 bytes with
                          | None => None
                          | Some (price_scale_code_value, bytes) =>
                              match decode_bytes 1 bytes with
                              | None => None
                              | Some (exchange_code_value, bytes) =>
                                  match decode_bytes 1 bytes with
                                  | None => None
                                  | Some (system_code_value, bytes) =>
                                      match decode_bytes 1 bytes with
                                      | None => None
                                      | Some (buy_sell_indicator_value, bytes) =>
                                          match decode_bytes 1 bytes with
                                          | None => None
                                          | Some (flat_pricing_value, bytes) =>
                                              match decode_uint 1 bytes with
                                              | None => None
                                              | Some (trading_action_value, bytes) =>
                                                  match decode_uint 1 bytes with
                                                  | None => None
                                                  | Some (security_type_value, bytes) =>
                                                      match decode_uint 1 bytes with
                                                      | None => None
                                                      | Some (order_type_value, bytes) =>
                                                          match decode_bytes 22 bytes with
                                                          | None => None
                                                          | Some (nyse_bond_symbol_value, bytes) =>
                                                              match decode_bytes 14 bytes with
                                                              | None => None
                                                              | Some (cusip_isin_value, bytes) =>
                                                                  match decode_bytes 5 bytes with
                                                                  | None => None
                                                                  | Some (quote_id_value, bytes) =>
                                                                      match decode_bytes 3 bytes with
                                                                      | None => None
                                                                      | Some (padding_ascii_3_value, bytes) =>
                                                                          match decode_uint 4 bytes with
                                                                          | None => None
                                                                          | Some (minimum_quantity_value, bytes) =>
                                                                              Some ({| time := time_value; sequence_number := sequence_number_value; order_reference_number := order_reference_number_value; quantity := quantity_value; price := price_value; price_scale_code := price_scale_code_value; exchange_code := exchange_code_value; system_code := system_code_value; buy_sell_indicator := buy_sell_indicator_value; flat_pricing := flat_pricing_value; trading_action := trading_action_value; security_type := security_type_value; order_type := order_type_value; nyse_bond_symbol := nyse_bond_symbol_value; cusip_isin := cusip_isin_value; quote_id := quote_id_value; padding_ascii_3 := padding_ascii_3_value; minimum_quantity := minimum_quantity_value |}, bytes)
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

    Theorem encode_length : forall record, Datatypes.length (encode record) = 76.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_uint_length, !encode_bytes_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 [bound_1 [bound_2 [bound_3 [bound_4 [bound_5 [bound_6 [bound_7 [bound_8 [bound_9 [bound_10 [bound_11 [bound_12 [bound_13 [bound_14 [bound_15 [bound_16 bound_17]]]]]]]]]]]]]]]]].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_uint by exact bound_0.
      rewrite decode_encode_uint by exact bound_1.
      rewrite decode_encode_uint by exact bound_2.
      rewrite decode_encode_uint by exact bound_3.
      rewrite decode_encode_uint by exact bound_4.
      rewrite decode_encode_bytes by exact bound_5.
      rewrite decode_encode_bytes by exact bound_6.
      rewrite decode_encode_bytes by exact bound_7.
      rewrite decode_encode_bytes by exact bound_8.
      rewrite decode_encode_bytes by exact bound_9.
      rewrite decode_encode_uint by exact bound_10.
      rewrite decode_encode_uint by exact bound_11.
      rewrite decode_encode_uint by exact bound_12.
      rewrite decode_encode_bytes by exact bound_13.
      rewrite decode_encode_bytes by exact bound_14.
      rewrite decode_encode_bytes by exact bound_15.
      rewrite decode_encode_bytes by exact bound_16.
      rewrite decode_encode_uint by exact bound_17.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End AddOrderMessage.

  Module ModifyOrderMessage.

    (** Sent when an order in a Nyse Bonds book is modified: its price or size changes, it is partially filled, or it is routed away with shares remaining. The Order Reference Number refers to the original Add Order. *)
    Record t := {
      time : N;
      sequence_number : N;
      order_reference_number : N;
      quantity : N;
      price : N;
      price_scale_code : list byte;
      exchange_code : list byte;
      system_code : list byte;
      buy_sell_indicator : list byte;
      flat_pricing : list byte;
      trading_action : N;
      security_type : N;
      order_type : N;
      nyse_bond_symbol : list byte;
      cusip_isin : list byte;
      quote_id : list byte;
      padding_ascii_3 : list byte;
      minimum_quantity : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (time record < 256 ^ N.of_nat 4)%N /\
      (sequence_number record < 256 ^ N.of_nat 4)%N /\
      (order_reference_number record < 256 ^ N.of_nat 4)%N /\
      (quantity record < 256 ^ N.of_nat 4)%N /\
      (price record < 256 ^ N.of_nat 4)%N /\
      Datatypes.length (price_scale_code record) = 1 /\
      Datatypes.length (exchange_code record) = 1 /\
      Datatypes.length (system_code record) = 1 /\
      Datatypes.length (buy_sell_indicator record) = 1 /\
      Datatypes.length (flat_pricing record) = 1 /\
      (trading_action record < 256 ^ N.of_nat 1)%N /\
      (security_type record < 256 ^ N.of_nat 1)%N /\
      (order_type record < 256 ^ N.of_nat 1)%N /\
      Datatypes.length (nyse_bond_symbol record) = 22 /\
      Datatypes.length (cusip_isin record) = 14 /\
      Datatypes.length (quote_id record) = 5 /\
      Datatypes.length (padding_ascii_3 record) = 3 /\
      (minimum_quantity record < 256 ^ N.of_nat 4)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 4 (time record) ++
      encode_uint 4 (sequence_number record) ++
      encode_uint 4 (order_reference_number record) ++
      encode_uint 4 (quantity record) ++
      encode_uint 4 (price record) ++
      encode_bytes 1 (price_scale_code record) ++
      encode_bytes 1 (exchange_code record) ++
      encode_bytes 1 (system_code record) ++
      encode_bytes 1 (buy_sell_indicator record) ++
      encode_bytes 1 (flat_pricing record) ++
      encode_uint 1 (trading_action record) ++
      encode_uint 1 (security_type record) ++
      encode_uint 1 (order_type record) ++
      encode_bytes 22 (nyse_bond_symbol record) ++
      encode_bytes 14 (cusip_isin record) ++
      encode_bytes 5 (quote_id record) ++
      encode_bytes 3 (padding_ascii_3 record) ++
      encode_uint 4 (minimum_quantity record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 4 bytes with
      | None => None
      | Some (time_value, bytes) =>
          match decode_uint 4 bytes with
          | None => None
          | Some (sequence_number_value, bytes) =>
              match decode_uint 4 bytes with
              | None => None
              | Some (order_reference_number_value, bytes) =>
                  match decode_uint 4 bytes with
                  | None => None
                  | Some (quantity_value, bytes) =>
                      match decode_uint 4 bytes with
                      | None => None
                      | Some (price_value, bytes) =>
                          match decode_bytes 1 bytes with
                          | None => None
                          | Some (price_scale_code_value, bytes) =>
                              match decode_bytes 1 bytes with
                              | None => None
                              | Some (exchange_code_value, bytes) =>
                                  match decode_bytes 1 bytes with
                                  | None => None
                                  | Some (system_code_value, bytes) =>
                                      match decode_bytes 1 bytes with
                                      | None => None
                                      | Some (buy_sell_indicator_value, bytes) =>
                                          match decode_bytes 1 bytes with
                                          | None => None
                                          | Some (flat_pricing_value, bytes) =>
                                              match decode_uint 1 bytes with
                                              | None => None
                                              | Some (trading_action_value, bytes) =>
                                                  match decode_uint 1 bytes with
                                                  | None => None
                                                  | Some (security_type_value, bytes) =>
                                                      match decode_uint 1 bytes with
                                                      | None => None
                                                      | Some (order_type_value, bytes) =>
                                                          match decode_bytes 22 bytes with
                                                          | None => None
                                                          | Some (nyse_bond_symbol_value, bytes) =>
                                                              match decode_bytes 14 bytes with
                                                              | None => None
                                                              | Some (cusip_isin_value, bytes) =>
                                                                  match decode_bytes 5 bytes with
                                                                  | None => None
                                                                  | Some (quote_id_value, bytes) =>
                                                                      match decode_bytes 3 bytes with
                                                                      | None => None
                                                                      | Some (padding_ascii_3_value, bytes) =>
                                                                          match decode_uint 4 bytes with
                                                                          | None => None
                                                                          | Some (minimum_quantity_value, bytes) =>
                                                                              Some ({| time := time_value; sequence_number := sequence_number_value; order_reference_number := order_reference_number_value; quantity := quantity_value; price := price_value; price_scale_code := price_scale_code_value; exchange_code := exchange_code_value; system_code := system_code_value; buy_sell_indicator := buy_sell_indicator_value; flat_pricing := flat_pricing_value; trading_action := trading_action_value; security_type := security_type_value; order_type := order_type_value; nyse_bond_symbol := nyse_bond_symbol_value; cusip_isin := cusip_isin_value; quote_id := quote_id_value; padding_ascii_3 := padding_ascii_3_value; minimum_quantity := minimum_quantity_value |}, bytes)
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

    Theorem encode_length : forall record, Datatypes.length (encode record) = 76.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_uint_length, !encode_bytes_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 [bound_1 [bound_2 [bound_3 [bound_4 [bound_5 [bound_6 [bound_7 [bound_8 [bound_9 [bound_10 [bound_11 [bound_12 [bound_13 [bound_14 [bound_15 [bound_16 bound_17]]]]]]]]]]]]]]]]].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_uint by exact bound_0.
      rewrite decode_encode_uint by exact bound_1.
      rewrite decode_encode_uint by exact bound_2.
      rewrite decode_encode_uint by exact bound_3.
      rewrite decode_encode_uint by exact bound_4.
      rewrite decode_encode_bytes by exact bound_5.
      rewrite decode_encode_bytes by exact bound_6.
      rewrite decode_encode_bytes by exact bound_7.
      rewrite decode_encode_bytes by exact bound_8.
      rewrite decode_encode_bytes by exact bound_9.
      rewrite decode_encode_uint by exact bound_10.
      rewrite decode_encode_uint by exact bound_11.
      rewrite decode_encode_uint by exact bound_12.
      rewrite decode_encode_bytes by exact bound_13.
      rewrite decode_encode_bytes by exact bound_14.
      rewrite decode_encode_bytes by exact bound_15.
      rewrite decode_encode_bytes by exact bound_16.
      rewrite decode_encode_uint by exact bound_17.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End ModifyOrderMessage.

  Module DeleteOrderMessage.

    (** Sent when an order is taken off the open order book because it was cancelled, expired, routed to an away market, or filled. *)
    Record t := {
      time : N;
      sequence_number : N;
      order_reference_number : N;
      exchange_code : list byte;
      system_code : list byte;
      buy_sell_indicator : list byte;
      flat_pricing : list byte;
      trading_action : N;
      security_type : N;
      order_type : N;
      nyse_bond_symbol : list byte;
      cusip_isin : list byte;
      quote_id : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (time record < 256 ^ N.of_nat 4)%N /\
      (sequence_number record < 256 ^ N.of_nat 4)%N /\
      (order_reference_number record < 256 ^ N.of_nat 4)%N /\
      Datatypes.length (exchange_code record) = 1 /\
      Datatypes.length (system_code record) = 1 /\
      Datatypes.length (buy_sell_indicator record) = 1 /\
      Datatypes.length (flat_pricing record) = 1 /\
      (trading_action record < 256 ^ N.of_nat 1)%N /\
      (security_type record < 256 ^ N.of_nat 1)%N /\
      (order_type record < 256 ^ N.of_nat 1)%N /\
      Datatypes.length (nyse_bond_symbol record) = 22 /\
      Datatypes.length (cusip_isin record) = 14 /\
      Datatypes.length (quote_id record) = 5.

    Definition encode (record : t) : list byte :=
      encode_uint 4 (time record) ++
      encode_uint 4 (sequence_number record) ++
      encode_uint 4 (order_reference_number record) ++
      encode_bytes 1 (exchange_code record) ++
      encode_bytes 1 (system_code record) ++
      encode_bytes 1 (buy_sell_indicator record) ++
      encode_bytes 1 (flat_pricing record) ++
      encode_uint 1 (trading_action record) ++
      encode_uint 1 (security_type record) ++
      encode_uint 1 (order_type record) ++
      encode_bytes 22 (nyse_bond_symbol record) ++
      encode_bytes 14 (cusip_isin record) ++
      encode_bytes 5 (quote_id record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 4 bytes with
      | None => None
      | Some (time_value, bytes) =>
          match decode_uint 4 bytes with
          | None => None
          | Some (sequence_number_value, bytes) =>
              match decode_uint 4 bytes with
              | None => None
              | Some (order_reference_number_value, bytes) =>
                  match decode_bytes 1 bytes with
                  | None => None
                  | Some (exchange_code_value, bytes) =>
                      match decode_bytes 1 bytes with
                      | None => None
                      | Some (system_code_value, bytes) =>
                          match decode_bytes 1 bytes with
                          | None => None
                          | Some (buy_sell_indicator_value, bytes) =>
                              match decode_bytes 1 bytes with
                              | None => None
                              | Some (flat_pricing_value, bytes) =>
                                  match decode_uint 1 bytes with
                                  | None => None
                                  | Some (trading_action_value, bytes) =>
                                      match decode_uint 1 bytes with
                                      | None => None
                                      | Some (security_type_value, bytes) =>
                                          match decode_uint 1 bytes with
                                          | None => None
                                          | Some (order_type_value, bytes) =>
                                              match decode_bytes 22 bytes with
                                              | None => None
                                              | Some (nyse_bond_symbol_value, bytes) =>
                                                  match decode_bytes 14 bytes with
                                                  | None => None
                                                  | Some (cusip_isin_value, bytes) =>
                                                      match decode_bytes 5 bytes with
                                                      | None => None
                                                      | Some (quote_id_value, bytes) =>
                                                          Some ({| time := time_value; sequence_number := sequence_number_value; order_reference_number := order_reference_number_value; exchange_code := exchange_code_value; system_code := system_code_value; buy_sell_indicator := buy_sell_indicator_value; flat_pricing := flat_pricing_value; trading_action := trading_action_value; security_type := security_type_value; order_type := order_type_value; nyse_bond_symbol := nyse_bond_symbol_value; cusip_isin := cusip_isin_value; quote_id := quote_id_value |}, bytes)
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

    Theorem encode_length : forall record, Datatypes.length (encode record) = 60.
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
      rewrite decode_encode_uint by exact bound_1.
      rewrite decode_encode_uint by exact bound_2.
      rewrite decode_encode_bytes by exact bound_3.
      rewrite decode_encode_bytes by exact bound_4.
      rewrite decode_encode_bytes by exact bound_5.
      rewrite decode_encode_bytes by exact bound_6.
      rewrite decode_encode_uint by exact bound_7.
      rewrite decode_encode_uint by exact bound_8.
      rewrite decode_encode_uint by exact bound_9.
      rewrite decode_encode_bytes by exact bound_10.
      rewrite decode_encode_bytes by exact bound_11.
      rewrite decode_encode_bytes by exact bound_12.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End DeleteOrderMessage.

  Module ImbalanceMessage.

    (** Sent in response to orders submitted during pending auctions, at the conclusion of the Opening, Market Order and Closing Auctions, and for Halt Auctions. Total and market imbalance volumes are negative for a sell imbalance. *)
    Record t := {
      time : N;
      sequence_number : N;
      match_quantity : N;
      total_imbalance : N;
      market_imbalance : N;
      price : N;
      price_scale_code : list byte;
      exchange_code : list byte;
      system_code : list byte;
      auction_type : list byte;
      flat_pricing : list byte;
      trading_action : N;
      security_type : N;
      quote_condition : N;
      nyse_bond_symbol : list byte;
      cusip_isin : list byte;
      auction_time : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (time record < 256 ^ N.of_nat 4)%N /\
      (sequence_number record < 256 ^ N.of_nat 4)%N /\
      (match_quantity record < 256 ^ N.of_nat 4)%N /\
      (total_imbalance record < 256 ^ N.of_nat 4)%N /\
      (market_imbalance record < 256 ^ N.of_nat 4)%N /\
      (price record < 256 ^ N.of_nat 4)%N /\
      Datatypes.length (price_scale_code record) = 1 /\
      Datatypes.length (exchange_code record) = 1 /\
      Datatypes.length (system_code record) = 1 /\
      Datatypes.length (auction_type record) = 1 /\
      Datatypes.length (flat_pricing record) = 1 /\
      (trading_action record < 256 ^ N.of_nat 1)%N /\
      (security_type record < 256 ^ N.of_nat 1)%N /\
      (quote_condition record < 256 ^ N.of_nat 1)%N /\
      Datatypes.length (nyse_bond_symbol record) = 22 /\
      Datatypes.length (cusip_isin record) = 14 /\
      Datatypes.length (auction_time record) = 4.

    Definition encode (record : t) : list byte :=
      encode_uint 4 (time record) ++
      encode_uint 4 (sequence_number record) ++
      encode_uint 4 (match_quantity record) ++
      encode_uint 4 (total_imbalance record) ++
      encode_uint 4 (market_imbalance record) ++
      encode_uint 4 (price record) ++
      encode_bytes 1 (price_scale_code record) ++
      encode_bytes 1 (exchange_code record) ++
      encode_bytes 1 (system_code record) ++
      encode_bytes 1 (auction_type record) ++
      encode_bytes 1 (flat_pricing record) ++
      encode_uint 1 (trading_action record) ++
      encode_uint 1 (security_type record) ++
      encode_uint 1 (quote_condition record) ++
      encode_bytes 22 (nyse_bond_symbol record) ++
      encode_bytes 14 (cusip_isin record) ++
      encode_bytes 4 (auction_time record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 4 bytes with
      | None => None
      | Some (time_value, bytes) =>
          match decode_uint 4 bytes with
          | None => None
          | Some (sequence_number_value, bytes) =>
              match decode_uint 4 bytes with
              | None => None
              | Some (match_quantity_value, bytes) =>
                  match decode_uint 4 bytes with
                  | None => None
                  | Some (total_imbalance_value, bytes) =>
                      match decode_uint 4 bytes with
                      | None => None
                      | Some (market_imbalance_value, bytes) =>
                          match decode_uint 4 bytes with
                          | None => None
                          | Some (price_value, bytes) =>
                              match decode_bytes 1 bytes with
                              | None => None
                              | Some (price_scale_code_value, bytes) =>
                                  match decode_bytes 1 bytes with
                                  | None => None
                                  | Some (exchange_code_value, bytes) =>
                                      match decode_bytes 1 bytes with
                                      | None => None
                                      | Some (system_code_value, bytes) =>
                                          match decode_bytes 1 bytes with
                                          | None => None
                                          | Some (auction_type_value, bytes) =>
                                              match decode_bytes 1 bytes with
                                              | None => None
                                              | Some (flat_pricing_value, bytes) =>
                                                  match decode_uint 1 bytes with
                                                  | None => None
                                                  | Some (trading_action_value, bytes) =>
                                                      match decode_uint 1 bytes with
                                                      | None => None
                                                      | Some (security_type_value, bytes) =>
                                                          match decode_uint 1 bytes with
                                                          | None => None
                                                          | Some (quote_condition_value, bytes) =>
                                                              match decode_bytes 22 bytes with
                                                              | None => None
                                                              | Some (nyse_bond_symbol_value, bytes) =>
                                                                  match decode_bytes 14 bytes with
                                                                  | None => None
                                                                  | Some (cusip_isin_value, bytes) =>
                                                                      match decode_bytes 4 bytes with
                                                                      | None => None
                                                                      | Some (auction_time_value, bytes) =>
                                                                          Some ({| time := time_value; sequence_number := sequence_number_value; match_quantity := match_quantity_value; total_imbalance := total_imbalance_value; market_imbalance := market_imbalance_value; price := price_value; price_scale_code := price_scale_code_value; exchange_code := exchange_code_value; system_code := system_code_value; auction_type := auction_type_value; flat_pricing := flat_pricing_value; trading_action := trading_action_value; security_type := security_type_value; quote_condition := quote_condition_value; nyse_bond_symbol := nyse_bond_symbol_value; cusip_isin := cusip_isin_value; auction_time := auction_time_value |}, bytes)
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

    Theorem encode_length : forall record, Datatypes.length (encode record) = 72.
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
      rewrite decode_encode_uint by exact bound_1.
      rewrite decode_encode_uint by exact bound_2.
      rewrite decode_encode_uint by exact bound_3.
      rewrite decode_encode_uint by exact bound_4.
      rewrite decode_encode_uint by exact bound_5.
      rewrite decode_encode_bytes by exact bound_6.
      rewrite decode_encode_bytes by exact bound_7.
      rewrite decode_encode_bytes by exact bound_8.
      rewrite decode_encode_bytes by exact bound_9.
      rewrite decode_encode_bytes by exact bound_10.
      rewrite decode_encode_uint by exact bound_11.
      rewrite decode_encode_uint by exact bound_12.
      rewrite decode_encode_uint by exact bound_13.
      rewrite decode_encode_bytes by exact bound_14.
      rewrite decode_encode_bytes by exact bound_15.
      rewrite decode_encode_bytes by exact bound_16.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End ImbalanceMessage.

  Module SystemEventMessage.

    (** Sent to indicate a special system event to an order book. The Event Code says what happened and the System Code which book is affected. Also carries the next sequence number subscribers should expect, which is generally the current one plus one but may restart at 1. *)
    Record t := {
      time : N;
      sequence_number : N;
      next_expected_sequence_number : N;
      event_code : list byte;
      system_code : list byte;
      nyse_bond_symbol : list byte;
      cusip_isin : list byte;
      padding_ascii_2 : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (time record < 256 ^ N.of_nat 4)%N /\
      (sequence_number record < 256 ^ N.of_nat 4)%N /\
      (next_expected_sequence_number record < 256 ^ N.of_nat 4)%N /\
      Datatypes.length (event_code record) = 1 /\
      Datatypes.length (system_code record) = 1 /\
      Datatypes.length (nyse_bond_symbol record) = 22 /\
      Datatypes.length (cusip_isin record) = 14 /\
      Datatypes.length (padding_ascii_2 record) = 2.

    Definition encode (record : t) : list byte :=
      encode_uint 4 (time record) ++
      encode_uint 4 (sequence_number record) ++
      encode_uint 4 (next_expected_sequence_number record) ++
      encode_bytes 1 (event_code record) ++
      encode_bytes 1 (system_code record) ++
      encode_bytes 22 (nyse_bond_symbol record) ++
      encode_bytes 14 (cusip_isin record) ++
      encode_bytes 2 (padding_ascii_2 record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 4 bytes with
      | None => None
      | Some (time_value, bytes) =>
          match decode_uint 4 bytes with
          | None => None
          | Some (sequence_number_value, bytes) =>
              match decode_uint 4 bytes with
              | None => None
              | Some (next_expected_sequence_number_value, bytes) =>
                  match decode_bytes 1 bytes with
                  | None => None
                  | Some (event_code_value, bytes) =>
                      match decode_bytes 1 bytes with
                      | None => None
                      | Some (system_code_value, bytes) =>
                          match decode_bytes 22 bytes with
                          | None => None
                          | Some (nyse_bond_symbol_value, bytes) =>
                              match decode_bytes 14 bytes with
                              | None => None
                              | Some (cusip_isin_value, bytes) =>
                                  match decode_bytes 2 bytes with
                                  | None => None
                                  | Some (padding_ascii_2_value, bytes) =>
                                      Some ({| time := time_value; sequence_number := sequence_number_value; next_expected_sequence_number := next_expected_sequence_number_value; event_code := event_code_value; system_code := system_code_value; nyse_bond_symbol := nyse_bond_symbol_value; cusip_isin := cusip_isin_value; padding_ascii_2 := padding_ascii_2_value |}, bytes)
                                  end
                              end
                          end
                      end
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 52.
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
      rewrite decode_encode_bytes by exact bound_4.
      rewrite decode_encode_bytes by exact bound_5.
      rewrite decode_encode_bytes by exact bound_6.
      rewrite decode_encode_bytes by exact bound_7.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End SystemEventMessage.

End NyseBondsDepthOfBookV401BServer.
