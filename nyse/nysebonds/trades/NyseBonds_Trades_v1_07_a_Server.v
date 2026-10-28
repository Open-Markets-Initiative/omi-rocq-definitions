From Stdlib Require Import List.
From Stdlib Require Import NArith.
From Stdlib Require Import Lia.
From Stdlib Require Import Strings.Byte.
From Omi Require Import Wire.

Import ListNotations.

(** * New York Stock Exchange Trades

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

Module NyseBondsTradesV107AServer.

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

    (** Sent to indicate a successful login. Carries the current version of ArcaTrade. *)
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

    (** Sent when login fails authentication, the client does not log in within 30 seconds, no trade data feed was subscribed to, the sequence number was invalid, or no connections are available. The socket is closed afterwards. *)
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

  Module LastSaleMessage.

    (** Sent when an order partially trades or completely trades. *)
    Record t := {
      last_sale_time : N;
      sequence_number : N;
      trade_reference_number : N;
      quantity : N;
      price : N;
      price_scale_code : list byte;
      system_code : list byte;
      exchange_code : list byte;
      trade_condition : N;
      security_type : N;
      nyse_bond_symbol : list byte;
      cusip_isin : list byte;
      padding_ascii_3 : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (last_sale_time record < 256 ^ N.of_nat 4)%N /\
      (sequence_number record < 256 ^ N.of_nat 4)%N /\
      (trade_reference_number record < 256 ^ N.of_nat 4)%N /\
      (quantity record < 256 ^ N.of_nat 4)%N /\
      (price record < 256 ^ N.of_nat 4)%N /\
      Datatypes.length (price_scale_code record) = 1 /\
      Datatypes.length (system_code record) = 1 /\
      Datatypes.length (exchange_code record) = 1 /\
      (trade_condition record < 256 ^ N.of_nat 1)%N /\
      (security_type record < 256 ^ N.of_nat 1)%N /\
      Datatypes.length (nyse_bond_symbol record) = 22 /\
      Datatypes.length (cusip_isin record) = 14 /\
      Datatypes.length (padding_ascii_3 record) = 3.

    Definition encode (record : t) : list byte :=
      encode_uint 4 (last_sale_time record) ++
      encode_uint 4 (sequence_number record) ++
      encode_uint 4 (trade_reference_number record) ++
      encode_uint 4 (quantity record) ++
      encode_uint 4 (price record) ++
      encode_bytes 1 (price_scale_code record) ++
      encode_bytes 1 (system_code record) ++
      encode_bytes 1 (exchange_code record) ++
      encode_uint 1 (trade_condition record) ++
      encode_uint 1 (security_type record) ++
      encode_bytes 22 (nyse_bond_symbol record) ++
      encode_bytes 14 (cusip_isin record) ++
      encode_bytes 3 (padding_ascii_3 record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 4 bytes with
      | None => None
      | Some (last_sale_time_value, bytes) =>
          match decode_uint 4 bytes with
          | None => None
          | Some (sequence_number_value, bytes) =>
              match decode_uint 4 bytes with
              | None => None
              | Some (trade_reference_number_value, bytes) =>
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
                              | Some (system_code_value, bytes) =>
                                  match decode_bytes 1 bytes with
                                  | None => None
                                  | Some (exchange_code_value, bytes) =>
                                      match decode_uint 1 bytes with
                                      | None => None
                                      | Some (trade_condition_value, bytes) =>
                                          match decode_uint 1 bytes with
                                          | None => None
                                          | Some (security_type_value, bytes) =>
                                              match decode_bytes 22 bytes with
                                              | None => None
                                              | Some (nyse_bond_symbol_value, bytes) =>
                                                  match decode_bytes 14 bytes with
                                                  | None => None
                                                  | Some (cusip_isin_value, bytes) =>
                                                      match decode_bytes 3 bytes with
                                                      | None => None
                                                      | Some (padding_ascii_3_value, bytes) =>
                                                          Some ({| last_sale_time := last_sale_time_value; sequence_number := sequence_number_value; trade_reference_number := trade_reference_number_value; quantity := quantity_value; price := price_value; price_scale_code := price_scale_code_value; system_code := system_code_value; exchange_code := exchange_code_value; trade_condition := trade_condition_value; security_type := security_type_value; nyse_bond_symbol := nyse_bond_symbol_value; cusip_isin := cusip_isin_value; padding_ascii_3 := padding_ascii_3_value |}, bytes)
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

    Theorem encode_length : forall record, Datatypes.length (encode record) = 64.
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
      rewrite decode_encode_uint by exact bound_3.
      rewrite decode_encode_uint by exact bound_4.
      rewrite decode_encode_bytes by exact bound_5.
      rewrite decode_encode_bytes by exact bound_6.
      rewrite decode_encode_bytes by exact bound_7.
      rewrite decode_encode_uint by exact bound_8.
      rewrite decode_encode_uint by exact bound_9.
      rewrite decode_encode_bytes by exact bound_10.
      rewrite decode_encode_bytes by exact bound_11.
      rewrite decode_encode_bytes by exact bound_12.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End LastSaleMessage.

  Module TradeBustOrCorrectionMessage.

    (** Sent when trades are busted or corrected. The Event Code field says which. *)
    Record t := {
      last_sale_time : N;
      sequence_number : N;
      trade_reference_number : N;
      quantity : N;
      price : N;
      price_scale_code : list byte;
      system_code : list byte;
      event_code : list byte;
      exchange_code : list byte;
      trade_condition : N;
      security_type : N;
      nyse_bond_symbol : list byte;
      cusip_isin : list byte;
      padding_ascii_2 : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (last_sale_time record < 256 ^ N.of_nat 4)%N /\
      (sequence_number record < 256 ^ N.of_nat 4)%N /\
      (trade_reference_number record < 256 ^ N.of_nat 4)%N /\
      (quantity record < 256 ^ N.of_nat 4)%N /\
      (price record < 256 ^ N.of_nat 4)%N /\
      Datatypes.length (price_scale_code record) = 1 /\
      Datatypes.length (system_code record) = 1 /\
      Datatypes.length (event_code record) = 1 /\
      Datatypes.length (exchange_code record) = 1 /\
      (trade_condition record < 256 ^ N.of_nat 1)%N /\
      (security_type record < 256 ^ N.of_nat 1)%N /\
      Datatypes.length (nyse_bond_symbol record) = 22 /\
      Datatypes.length (cusip_isin record) = 14 /\
      Datatypes.length (padding_ascii_2 record) = 2.

    Definition encode (record : t) : list byte :=
      encode_uint 4 (last_sale_time record) ++
      encode_uint 4 (sequence_number record) ++
      encode_uint 4 (trade_reference_number record) ++
      encode_uint 4 (quantity record) ++
      encode_uint 4 (price record) ++
      encode_bytes 1 (price_scale_code record) ++
      encode_bytes 1 (system_code record) ++
      encode_bytes 1 (event_code record) ++
      encode_bytes 1 (exchange_code record) ++
      encode_uint 1 (trade_condition record) ++
      encode_uint 1 (security_type record) ++
      encode_bytes 22 (nyse_bond_symbol record) ++
      encode_bytes 14 (cusip_isin record) ++
      encode_bytes 2 (padding_ascii_2 record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 4 bytes with
      | None => None
      | Some (last_sale_time_value, bytes) =>
          match decode_uint 4 bytes with
          | None => None
          | Some (sequence_number_value, bytes) =>
              match decode_uint 4 bytes with
              | None => None
              | Some (trade_reference_number_value, bytes) =>
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
                              | Some (system_code_value, bytes) =>
                                  match decode_bytes 1 bytes with
                                  | None => None
                                  | Some (event_code_value, bytes) =>
                                      match decode_bytes 1 bytes with
                                      | None => None
                                      | Some (exchange_code_value, bytes) =>
                                          match decode_uint 1 bytes with
                                          | None => None
                                          | Some (trade_condition_value, bytes) =>
                                              match decode_uint 1 bytes with
                                              | None => None
                                              | Some (security_type_value, bytes) =>
                                                  match decode_bytes 22 bytes with
                                                  | None => None
                                                  | Some (nyse_bond_symbol_value, bytes) =>
                                                      match decode_bytes 14 bytes with
                                                      | None => None
                                                      | Some (cusip_isin_value, bytes) =>
                                                          match decode_bytes 2 bytes with
                                                          | None => None
                                                          | Some (padding_ascii_2_value, bytes) =>
                                                              Some ({| last_sale_time := last_sale_time_value; sequence_number := sequence_number_value; trade_reference_number := trade_reference_number_value; quantity := quantity_value; price := price_value; price_scale_code := price_scale_code_value; system_code := system_code_value; event_code := event_code_value; exchange_code := exchange_code_value; trade_condition := trade_condition_value; security_type := security_type_value; nyse_bond_symbol := nyse_bond_symbol_value; cusip_isin := cusip_isin_value; padding_ascii_2 := padding_ascii_2_value |}, bytes)
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

    Theorem encode_length : forall record, Datatypes.length (encode record) = 64.
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
      rewrite decode_encode_uint by exact bound_1.
      rewrite decode_encode_uint by exact bound_2.
      rewrite decode_encode_uint by exact bound_3.
      rewrite decode_encode_uint by exact bound_4.
      rewrite decode_encode_bytes by exact bound_5.
      rewrite decode_encode_bytes by exact bound_6.
      rewrite decode_encode_bytes by exact bound_7.
      rewrite decode_encode_bytes by exact bound_8.
      rewrite decode_encode_uint by exact bound_9.
      rewrite decode_encode_uint by exact bound_10.
      rewrite decode_encode_bytes by exact bound_11.
      rewrite decode_encode_bytes by exact bound_12.
      rewrite decode_encode_bytes by exact bound_13.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End TradeBustOrCorrectionMessage.

  Module NyseBondClosingPriceMessage.

    (** Sent during day end processing with the final closing price and volume for a bond. The specification notes this message is not supported at the time of writing and will be implemented in a future release. *)
    Record t := {
      closing_time : N;
      sequence_number : N;
      trade_reference_number : N;
      quantity : N;
      closing_price : N;
      price_scale_code : list byte;
      system_code : list byte;
      exchange_code : list byte;
      trade_condition : N;
      security_type : N;
      nyse_bond_symbol : list byte;
      cusip_isin : list byte;
      padding_ascii_3 : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (closing_time record < 256 ^ N.of_nat 4)%N /\
      (sequence_number record < 256 ^ N.of_nat 4)%N /\
      (trade_reference_number record < 256 ^ N.of_nat 4)%N /\
      (quantity record < 256 ^ N.of_nat 4)%N /\
      (closing_price record < 256 ^ N.of_nat 4)%N /\
      Datatypes.length (price_scale_code record) = 1 /\
      Datatypes.length (system_code record) = 1 /\
      Datatypes.length (exchange_code record) = 1 /\
      (trade_condition record < 256 ^ N.of_nat 1)%N /\
      (security_type record < 256 ^ N.of_nat 1)%N /\
      Datatypes.length (nyse_bond_symbol record) = 22 /\
      Datatypes.length (cusip_isin record) = 14 /\
      Datatypes.length (padding_ascii_3 record) = 3.

    Definition encode (record : t) : list byte :=
      encode_uint 4 (closing_time record) ++
      encode_uint 4 (sequence_number record) ++
      encode_uint 4 (trade_reference_number record) ++
      encode_uint 4 (quantity record) ++
      encode_uint 4 (closing_price record) ++
      encode_bytes 1 (price_scale_code record) ++
      encode_bytes 1 (system_code record) ++
      encode_bytes 1 (exchange_code record) ++
      encode_uint 1 (trade_condition record) ++
      encode_uint 1 (security_type record) ++
      encode_bytes 22 (nyse_bond_symbol record) ++
      encode_bytes 14 (cusip_isin record) ++
      encode_bytes 3 (padding_ascii_3 record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 4 bytes with
      | None => None
      | Some (closing_time_value, bytes) =>
          match decode_uint 4 bytes with
          | None => None
          | Some (sequence_number_value, bytes) =>
              match decode_uint 4 bytes with
              | None => None
              | Some (trade_reference_number_value, bytes) =>
                  match decode_uint 4 bytes with
                  | None => None
                  | Some (quantity_value, bytes) =>
                      match decode_uint 4 bytes with
                      | None => None
                      | Some (closing_price_value, bytes) =>
                          match decode_bytes 1 bytes with
                          | None => None
                          | Some (price_scale_code_value, bytes) =>
                              match decode_bytes 1 bytes with
                              | None => None
                              | Some (system_code_value, bytes) =>
                                  match decode_bytes 1 bytes with
                                  | None => None
                                  | Some (exchange_code_value, bytes) =>
                                      match decode_uint 1 bytes with
                                      | None => None
                                      | Some (trade_condition_value, bytes) =>
                                          match decode_uint 1 bytes with
                                          | None => None
                                          | Some (security_type_value, bytes) =>
                                              match decode_bytes 22 bytes with
                                              | None => None
                                              | Some (nyse_bond_symbol_value, bytes) =>
                                                  match decode_bytes 14 bytes with
                                                  | None => None
                                                  | Some (cusip_isin_value, bytes) =>
                                                      match decode_bytes 3 bytes with
                                                      | None => None
                                                      | Some (padding_ascii_3_value, bytes) =>
                                                          Some ({| closing_time := closing_time_value; sequence_number := sequence_number_value; trade_reference_number := trade_reference_number_value; quantity := quantity_value; closing_price := closing_price_value; price_scale_code := price_scale_code_value; system_code := system_code_value; exchange_code := exchange_code_value; trade_condition := trade_condition_value; security_type := security_type_value; nyse_bond_symbol := nyse_bond_symbol_value; cusip_isin := cusip_isin_value; padding_ascii_3 := padding_ascii_3_value |}, bytes)
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

    Theorem encode_length : forall record, Datatypes.length (encode record) = 64.
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
      rewrite decode_encode_uint by exact bound_3.
      rewrite decode_encode_uint by exact bound_4.
      rewrite decode_encode_bytes by exact bound_5.
      rewrite decode_encode_bytes by exact bound_6.
      rewrite decode_encode_bytes by exact bound_7.
      rewrite decode_encode_uint by exact bound_8.
      rewrite decode_encode_uint by exact bound_9.
      rewrite decode_encode_bytes by exact bound_10.
      rewrite decode_encode_bytes by exact bound_11.
      rewrite decode_encode_bytes by exact bound_12.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End NyseBondClosingPriceMessage.

End NyseBondsTradesV107AServer.
