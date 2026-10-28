From Stdlib Require Import List.
From Stdlib Require Import NArith.
From Stdlib Require Import Lia.
From Stdlib Require Import Strings.Byte.
From Omi Require Import Wire.

Import ListNotations.

(** * Bolsa Institucional de Valores Last Sale

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
  *)

Module BivaEquitiesLastSaleV112.

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

  Module TimeStampSecondsMessage.

    (** Itch timestamp, number of seconds since midnight of the system start *)
    Record t := {
      second : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (second record < 256 ^ N.of_nat 4)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 4 (second record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 4 bytes with
      | None => None
      | Some (second_value, bytes) =>
          Some ({| second := second_value |}, bytes)
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

  End TimeStampSecondsMessage.

  Module SystemEventMessage.

    (** System event message *)
    Record t := {
      nanoseconds : N;
      group : list byte;
      event_code : list byte;
      orderbook : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (nanoseconds record < 256 ^ N.of_nat 4)%N /\
      Datatypes.length (group record) = 8 /\
      Datatypes.length (event_code record) = 1 /\
      (orderbook record < 256 ^ N.of_nat 4)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 4 (nanoseconds record) ++
      encode_bytes 8 (group record) ++
      encode_bytes 1 (event_code record) ++
      encode_uint 4 (orderbook record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 4 bytes with
      | None => None
      | Some (nanoseconds_value, bytes) =>
          match decode_bytes 8 bytes with
          | None => None
          | Some (group_value, bytes) =>
              match decode_bytes 1 bytes with
              | None => None
              | Some (event_code_value, bytes) =>
                  match decode_uint 4 bytes with
                  | None => None
                  | Some (orderbook_value, bytes) =>
                      Some ({| nanoseconds := nanoseconds_value; group := group_value; event_code := event_code_value; orderbook := orderbook_value |}, bytes)
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 17.
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
      rewrite decode_encode_uint by exact bound_3.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End SystemEventMessage.

  Module PriceTickSizeMessage.

    (** Orderbook price tick table *)
    Record t := {
      nanoseconds : N;
      tick_size_table_id : N;
      price_tick_size : N;
      price_start : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (nanoseconds record < 256 ^ N.of_nat 4)%N /\
      (tick_size_table_id record < 256 ^ N.of_nat 4)%N /\
      (price_tick_size record < 256 ^ N.of_nat 4)%N /\
      (price_start record < 256 ^ N.of_nat 4)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 4 (nanoseconds record) ++
      encode_uint 4 (tick_size_table_id record) ++
      encode_uint 4 (price_tick_size record) ++
      encode_uint 4 (price_start record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 4 bytes with
      | None => None
      | Some (nanoseconds_value, bytes) =>
          match decode_uint 4 bytes with
          | None => None
          | Some (tick_size_table_id_value, bytes) =>
              match decode_uint 4 bytes with
              | None => None
              | Some (price_tick_size_value, bytes) =>
                  match decode_uint 4 bytes with
                  | None => None
                  | Some (price_start_value, bytes) =>
                      Some ({| nanoseconds := nanoseconds_value; tick_size_table_id := tick_size_table_id_value; price_tick_size := price_tick_size_value; price_start := price_start_value |}, bytes)
                  end
              end
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

  End PriceTickSizeMessage.

  Module QuantityTickSizeMessage.

    (** Orderbook quantity tick table *)
    Record t := {
      nanoseconds : N;
      tick_size_table_id : N;
      quantity_tick_size : N;
      quantity_start : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (nanoseconds record < 256 ^ N.of_nat 4)%N /\
      (tick_size_table_id record < 256 ^ N.of_nat 4)%N /\
      (quantity_tick_size record < 256 ^ N.of_nat 8)%N /\
      (quantity_start record < 256 ^ N.of_nat 8)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 4 (nanoseconds record) ++
      encode_uint 4 (tick_size_table_id record) ++
      encode_uint 8 (quantity_tick_size record) ++
      encode_uint 8 (quantity_start record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 4 bytes with
      | None => None
      | Some (nanoseconds_value, bytes) =>
          match decode_uint 4 bytes with
          | None => None
          | Some (tick_size_table_id_value, bytes) =>
              match decode_uint 8 bytes with
              | None => None
              | Some (quantity_tick_size_value, bytes) =>
                  match decode_uint 8 bytes with
                  | None => None
                  | Some (quantity_start_value, bytes) =>
                      Some ({| nanoseconds := nanoseconds_value; tick_size_table_id := tick_size_table_id_value; quantity_tick_size := quantity_tick_size_value; quantity_start := quantity_start_value |}, bytes)
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 24.
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

  End QuantityTickSizeMessage.

  Module OrderbookDirectoryMessage.

    (** Orderbook directory *)
    Record t := {
      nanoseconds : N;
      orderbook : N;
      isin : list byte;
      sec_code : list byte;
      currency : list byte;
      group : list byte;
      minimum_quantity : N;
      quantity_tick_size_table_id : N;
      quantity_decimals : N;
      price_tick_size_table_id : N;
      price_decimals : N;
      delisting_or_maturity_date : N;
      delisting_time : N;
      turnover_ratio : list byte;
      quotation_basis : list byte;
      instrument : list byte;
      listing_type : list byte;
      listing_exchange : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (nanoseconds record < 256 ^ N.of_nat 4)%N /\
      (orderbook record < 256 ^ N.of_nat 4)%N /\
      Datatypes.length (isin record) = 12 /\
      Datatypes.length (sec_code record) = 15 /\
      Datatypes.length (currency record) = 3 /\
      Datatypes.length (group record) = 8 /\
      (minimum_quantity record < 256 ^ N.of_nat 8)%N /\
      (quantity_tick_size_table_id record < 256 ^ N.of_nat 4)%N /\
      (quantity_decimals record < 256 ^ N.of_nat 4)%N /\
      (price_tick_size_table_id record < 256 ^ N.of_nat 4)%N /\
      (price_decimals record < 256 ^ N.of_nat 4)%N /\
      (delisting_or_maturity_date record < 256 ^ N.of_nat 4)%N /\
      (delisting_time record < 256 ^ N.of_nat 4)%N /\
      Datatypes.length (turnover_ratio record) = 1 /\
      Datatypes.length (quotation_basis record) = 3 /\
      Datatypes.length (instrument record) = 12 /\
      Datatypes.length (listing_type record) = 1 /\
      Datatypes.length (listing_exchange record) = 4.

    Definition encode (record : t) : list byte :=
      encode_uint 4 (nanoseconds record) ++
      encode_uint 4 (orderbook record) ++
      encode_bytes 12 (isin record) ++
      encode_bytes 15 (sec_code record) ++
      encode_bytes 3 (currency record) ++
      encode_bytes 8 (group record) ++
      encode_uint 8 (minimum_quantity record) ++
      encode_uint 4 (quantity_tick_size_table_id record) ++
      encode_uint 4 (quantity_decimals record) ++
      encode_uint 4 (price_tick_size_table_id record) ++
      encode_uint 4 (price_decimals record) ++
      encode_uint 4 (delisting_or_maturity_date record) ++
      encode_uint 4 (delisting_time record) ++
      encode_bytes 1 (turnover_ratio record) ++
      encode_bytes 3 (quotation_basis record) ++
      encode_bytes 12 (instrument record) ++
      encode_bytes 1 (listing_type record) ++
      encode_bytes 4 (listing_exchange record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 4 bytes with
      | None => None
      | Some (nanoseconds_value, bytes) =>
          match decode_uint 4 bytes with
          | None => None
          | Some (orderbook_value, bytes) =>
              match decode_bytes 12 bytes with
              | None => None
              | Some (isin_value, bytes) =>
                  match decode_bytes 15 bytes with
                  | None => None
                  | Some (sec_code_value, bytes) =>
                      match decode_bytes 3 bytes with
                      | None => None
                      | Some (currency_value, bytes) =>
                          match decode_bytes 8 bytes with
                          | None => None
                          | Some (group_value, bytes) =>
                              match decode_uint 8 bytes with
                              | None => None
                              | Some (minimum_quantity_value, bytes) =>
                                  match decode_uint 4 bytes with
                                  | None => None
                                  | Some (quantity_tick_size_table_id_value, bytes) =>
                                      match decode_uint 4 bytes with
                                      | None => None
                                      | Some (quantity_decimals_value, bytes) =>
                                          match decode_uint 4 bytes with
                                          | None => None
                                          | Some (price_tick_size_table_id_value, bytes) =>
                                              match decode_uint 4 bytes with
                                              | None => None
                                              | Some (price_decimals_value, bytes) =>
                                                  match decode_uint 4 bytes with
                                                  | None => None
                                                  | Some (delisting_or_maturity_date_value, bytes) =>
                                                      match decode_uint 4 bytes with
                                                      | None => None
                                                      | Some (delisting_time_value, bytes) =>
                                                          match decode_bytes 1 bytes with
                                                          | None => None
                                                          | Some (turnover_ratio_value, bytes) =>
                                                              match decode_bytes 3 bytes with
                                                              | None => None
                                                              | Some (quotation_basis_value, bytes) =>
                                                                  match decode_bytes 12 bytes with
                                                                  | None => None
                                                                  | Some (instrument_value, bytes) =>
                                                                      match decode_bytes 1 bytes with
                                                                      | None => None
                                                                      | Some (listing_type_value, bytes) =>
                                                                          match decode_bytes 4 bytes with
                                                                          | None => None
                                                                          | Some (listing_exchange_value, bytes) =>
                                                                              Some ({| nanoseconds := nanoseconds_value; orderbook := orderbook_value; isin := isin_value; sec_code := sec_code_value; currency := currency_value; group := group_value; minimum_quantity := minimum_quantity_value; quantity_tick_size_table_id := quantity_tick_size_table_id_value; quantity_decimals := quantity_decimals_value; price_tick_size_table_id := price_tick_size_table_id_value; price_decimals := price_decimals_value; delisting_or_maturity_date := delisting_or_maturity_date_value; delisting_time := delisting_time_value; turnover_ratio := turnover_ratio_value; quotation_basis := quotation_basis_value; instrument := instrument_value; listing_type := listing_type_value; listing_exchange := listing_exchange_value |}, bytes)
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

    Theorem encode_length : forall record, Datatypes.length (encode record) = 99.
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
      rewrite decode_encode_bytes by exact bound_2.
      rewrite decode_encode_bytes by exact bound_3.
      rewrite decode_encode_bytes by exact bound_4.
      rewrite decode_encode_bytes by exact bound_5.
      rewrite decode_encode_uint by exact bound_6.
      rewrite decode_encode_uint by exact bound_7.
      rewrite decode_encode_uint by exact bound_8.
      rewrite decode_encode_uint by exact bound_9.
      rewrite decode_encode_uint by exact bound_10.
      rewrite decode_encode_uint by exact bound_11.
      rewrite decode_encode_uint by exact bound_12.
      rewrite decode_encode_bytes by exact bound_13.
      rewrite decode_encode_bytes by exact bound_14.
      rewrite decode_encode_bytes by exact bound_15.
      rewrite decode_encode_bytes by exact bound_16.
      rewrite decode_encode_bytes by exact bound_17.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End OrderbookDirectoryMessage.

  Module ParticipantDirectoryMessage.

    (** Participant directory *)
    Record t := {
      nanoseconds : N;
      participant_id : N;
      participant_code : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (nanoseconds record < 256 ^ N.of_nat 4)%N /\
      (participant_id record < 256 ^ N.of_nat 4)%N /\
      Datatypes.length (participant_code record) = 12.

    Definition encode (record : t) : list byte :=
      encode_uint 4 (nanoseconds record) ++
      encode_uint 4 (participant_id record) ++
      encode_bytes 12 (participant_code record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 4 bytes with
      | None => None
      | Some (nanoseconds_value, bytes) =>
          match decode_uint 4 bytes with
          | None => None
          | Some (participant_id_value, bytes) =>
              match decode_bytes 12 bytes with
              | None => None
              | Some (participant_code_value, bytes) =>
                  Some ({| nanoseconds := nanoseconds_value; participant_id := participant_id_value; participant_code := participant_code_value |}, bytes)
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

  End ParticipantDirectoryMessage.

  Module OrderbookTradingActionMessage.

    (** Trading action message *)
    Record t := {
      nanoseconds : N;
      orderbook : N;
      trading_state : list byte;
      trading_action_reason : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (nanoseconds record < 256 ^ N.of_nat 4)%N /\
      (orderbook record < 256 ^ N.of_nat 4)%N /\
      Datatypes.length (trading_state record) = 1 /\
      Datatypes.length (trading_action_reason record) = 1.

    Definition encode (record : t) : list byte :=
      encode_uint 4 (nanoseconds record) ++
      encode_uint 4 (orderbook record) ++
      encode_bytes 1 (trading_state record) ++
      encode_bytes 1 (trading_action_reason record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 4 bytes with
      | None => None
      | Some (nanoseconds_value, bytes) =>
          match decode_uint 4 bytes with
          | None => None
          | Some (orderbook_value, bytes) =>
              match decode_bytes 1 bytes with
              | None => None
              | Some (trading_state_value, bytes) =>
                  match decode_bytes 1 bytes with
                  | None => None
                  | Some (trading_action_reason_value, bytes) =>
                      Some ({| nanoseconds := nanoseconds_value; orderbook := orderbook_value; trading_state := trading_state_value; trading_action_reason := trading_action_reason_value |}, bytes)
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 10.
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
      rewrite decode_encode_bytes by exact bound_2.
      rewrite decode_encode_bytes by exact bound_3.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End OrderbookTradingActionMessage.

  Module TradeMessage.

    (** Trade message *)
    Record t := {
      nanoseconds : N;
      executed_quantity : N;
      orderbook : N;
      printable : list byte;
      execution_price : N;
      match_number : N;
      trade_indicator : list byte;
      stat_update : list byte;
      buy_participant_id : N;
      sell_participant_id : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (nanoseconds record < 256 ^ N.of_nat 4)%N /\
      (executed_quantity record < 256 ^ N.of_nat 8)%N /\
      (orderbook record < 256 ^ N.of_nat 4)%N /\
      Datatypes.length (printable record) = 1 /\
      (execution_price record < 256 ^ N.of_nat 4)%N /\
      (match_number record < 256 ^ N.of_nat 8)%N /\
      Datatypes.length (trade_indicator record) = 1 /\
      Datatypes.length (stat_update record) = 1 /\
      (buy_participant_id record < 256 ^ N.of_nat 4)%N /\
      (sell_participant_id record < 256 ^ N.of_nat 4)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 4 (nanoseconds record) ++
      encode_uint 8 (executed_quantity record) ++
      encode_uint 4 (orderbook record) ++
      encode_bytes 1 (printable record) ++
      encode_uint 4 (execution_price record) ++
      encode_uint 8 (match_number record) ++
      encode_bytes 1 (trade_indicator record) ++
      encode_bytes 1 (stat_update record) ++
      encode_uint 4 (buy_participant_id record) ++
      encode_uint 4 (sell_participant_id record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 4 bytes with
      | None => None
      | Some (nanoseconds_value, bytes) =>
          match decode_uint 8 bytes with
          | None => None
          | Some (executed_quantity_value, bytes) =>
              match decode_uint 4 bytes with
              | None => None
              | Some (orderbook_value, bytes) =>
                  match decode_bytes 1 bytes with
                  | None => None
                  | Some (printable_value, bytes) =>
                      match decode_uint 4 bytes with
                      | None => None
                      | Some (execution_price_value, bytes) =>
                          match decode_uint 8 bytes with
                          | None => None
                          | Some (match_number_value, bytes) =>
                              match decode_bytes 1 bytes with
                              | None => None
                              | Some (trade_indicator_value, bytes) =>
                                  match decode_bytes 1 bytes with
                                  | None => None
                                  | Some (stat_update_value, bytes) =>
                                      match decode_uint 4 bytes with
                                      | None => None
                                      | Some (buy_participant_id_value, bytes) =>
                                          match decode_uint 4 bytes with
                                          | None => None
                                          | Some (sell_participant_id_value, bytes) =>
                                              Some ({| nanoseconds := nanoseconds_value; executed_quantity := executed_quantity_value; orderbook := orderbook_value; printable := printable_value; execution_price := execution_price_value; match_number := match_number_value; trade_indicator := trade_indicator_value; stat_update := stat_update_value; buy_participant_id := buy_participant_id_value; sell_participant_id := sell_participant_id_value |}, bytes)
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

    Theorem encode_length : forall record, Datatypes.length (encode record) = 39.
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
      rewrite decode_encode_bytes by exact bound_6.
      rewrite decode_encode_bytes by exact bound_7.
      rewrite decode_encode_uint by exact bound_8.
      rewrite decode_encode_uint by exact bound_9.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End TradeMessage.

  Module OrderbookReferencePriceMessage.

    (** Orderbook reference price message *)
    Record t := {
      nanoseconds : N;
      orderbook : N;
      reference_price : N;
      price_type : list byte;
      reference_price_reason : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (nanoseconds record < 256 ^ N.of_nat 4)%N /\
      (orderbook record < 256 ^ N.of_nat 4)%N /\
      (reference_price record < 256 ^ N.of_nat 4)%N /\
      Datatypes.length (price_type record) = 1 /\
      Datatypes.length (reference_price_reason record) = 1.

    Definition encode (record : t) : list byte :=
      encode_uint 4 (nanoseconds record) ++
      encode_uint 4 (orderbook record) ++
      encode_uint 4 (reference_price record) ++
      encode_bytes 1 (price_type record) ++
      encode_bytes 1 (reference_price_reason record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 4 bytes with
      | None => None
      | Some (nanoseconds_value, bytes) =>
          match decode_uint 4 bytes with
          | None => None
          | Some (orderbook_value, bytes) =>
              match decode_uint 4 bytes with
              | None => None
              | Some (reference_price_value, bytes) =>
                  match decode_bytes 1 bytes with
                  | None => None
                  | Some (price_type_value, bytes) =>
                      match decode_bytes 1 bytes with
                      | None => None
                      | Some (reference_price_reason_value, bytes) =>
                          Some ({| nanoseconds := nanoseconds_value; orderbook := orderbook_value; reference_price := reference_price_value; price_type := price_type_value; reference_price_reason := reference_price_reason_value |}, bytes)
                      end
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 14.
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

  End OrderbookReferencePriceMessage.

End BivaEquitiesLastSaleV112.
