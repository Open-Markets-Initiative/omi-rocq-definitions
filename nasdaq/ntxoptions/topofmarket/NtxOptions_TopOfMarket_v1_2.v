From Stdlib Require Import List.
From Stdlib Require Import NArith.
From Stdlib Require Import Lia.
From Stdlib Require Import Strings.Byte.
From Omi Require Import Wire.

Import ListNotations.

(** * National Association of Securities Dealers Automated Quotations (Nasdaq) Top Of Market

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

Module NtxOptionsTopOfMarketV12.

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

  Module TimestampMessage.

    (** For bandwidth efficiency reasons, the timestamp for a message is divided into two pieces: the seconds portion and sub-seconds portion. The seconds portion of the timestamp appears in the Timestamp Message, any message on the stream following this message has this seconds portion of time until the next timestamp message. The format is as follows: *)
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

  End TimestampMessage.

  Module SystemEventMessage.

    (** The system event message type is used to signal a market or data feed handler event. The format is as follows: *)
    Record t := {
      nanoseconds : N;
      event_code : list byte;
      version : N;
      sub_version : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (nanoseconds record < 256 ^ N.of_nat 4)%N /\
      Datatypes.length (event_code record) = 1 /\
      (version record < 256 ^ N.of_nat 1)%N /\
      (sub_version record < 256 ^ N.of_nat 1)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 4 (nanoseconds record) ++
      encode_bytes 1 (event_code record) ++
      encode_uint 1 (version record) ++
      encode_uint 1 (sub_version record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 4 bytes with
      | None => None
      | Some (nanoseconds_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (event_code_value, bytes) =>
              match decode_uint 1 bytes with
              | None => None
              | Some (version_value, bytes) =>
                  match decode_uint 1 bytes with
                  | None => None
                  | Some (sub_version_value, bytes) =>
                      Some ({| nanoseconds := nanoseconds_value; event_code := event_code_value; version := version_value; sub_version := sub_version_value |}, bytes)
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 7.
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

  End SystemEventMessage.

  Module OptionsDirectoryMessage.

    (** At the start of each trading day, the options system disseminates directory messages for all symbols eligible for the auction process in the options system. *)
    Record t := {
      nanoseconds : N;
      option_id : N;
      security_symbol : list byte;
      expiration_year : N;
      expiration_month : N;
      expiration_day : N;
      strike_price : N;
      option_type : list byte;
      source : N;
      underlying_symbol : list byte;
      option_closing_type : list byte;
      tradable : list byte;
      minimum_price_variation : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (nanoseconds record < 256 ^ N.of_nat 4)%N /\
      (option_id record < 256 ^ N.of_nat 4)%N /\
      Datatypes.length (security_symbol record) = 6 /\
      (expiration_year record < 256 ^ N.of_nat 1)%N /\
      (expiration_month record < 256 ^ N.of_nat 1)%N /\
      (expiration_day record < 256 ^ N.of_nat 1)%N /\
      (strike_price record < 256 ^ N.of_nat 4)%N /\
      Datatypes.length (option_type record) = 1 /\
      (source record < 256 ^ N.of_nat 1)%N /\
      Datatypes.length (underlying_symbol record) = 13 /\
      Datatypes.length (option_closing_type record) = 1 /\
      Datatypes.length (tradable record) = 1 /\
      Datatypes.length (minimum_price_variation record) = 1.

    Definition encode (record : t) : list byte :=
      encode_uint 4 (nanoseconds record) ++
      encode_uint 4 (option_id record) ++
      encode_bytes 6 (security_symbol record) ++
      encode_uint 1 (expiration_year record) ++
      encode_uint 1 (expiration_month record) ++
      encode_uint 1 (expiration_day record) ++
      encode_uint 4 (strike_price record) ++
      encode_bytes 1 (option_type record) ++
      encode_uint 1 (source record) ++
      encode_bytes 13 (underlying_symbol record) ++
      encode_bytes 1 (option_closing_type record) ++
      encode_bytes 1 (tradable record) ++
      encode_bytes 1 (minimum_price_variation record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 4 bytes with
      | None => None
      | Some (nanoseconds_value, bytes) =>
          match decode_uint 4 bytes with
          | None => None
          | Some (option_id_value, bytes) =>
              match decode_bytes 6 bytes with
              | None => None
              | Some (security_symbol_value, bytes) =>
                  match decode_uint 1 bytes with
                  | None => None
                  | Some (expiration_year_value, bytes) =>
                      match decode_uint 1 bytes with
                      | None => None
                      | Some (expiration_month_value, bytes) =>
                          match decode_uint 1 bytes with
                          | None => None
                          | Some (expiration_day_value, bytes) =>
                              match decode_uint 4 bytes with
                              | None => None
                              | Some (strike_price_value, bytes) =>
                                  match decode_bytes 1 bytes with
                                  | None => None
                                  | Some (option_type_value, bytes) =>
                                      match decode_uint 1 bytes with
                                      | None => None
                                      | Some (source_value, bytes) =>
                                          match decode_bytes 13 bytes with
                                          | None => None
                                          | Some (underlying_symbol_value, bytes) =>
                                              match decode_bytes 1 bytes with
                                              | None => None
                                              | Some (option_closing_type_value, bytes) =>
                                                  match decode_bytes 1 bytes with
                                                  | None => None
                                                  | Some (tradable_value, bytes) =>
                                                      match decode_bytes 1 bytes with
                                                      | None => None
                                                      | Some (minimum_price_variation_value, bytes) =>
                                                          Some ({| nanoseconds := nanoseconds_value; option_id := option_id_value; security_symbol := security_symbol_value; expiration_year := expiration_year_value; expiration_month := expiration_month_value; expiration_day := expiration_day_value; strike_price := strike_price_value; option_type := option_type_value; source := source_value; underlying_symbol := underlying_symbol_value; option_closing_type := option_closing_type_value; tradable := tradable_value; minimum_price_variation := minimum_price_variation_value |}, bytes)
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

    Theorem encode_length : forall record, Datatypes.length (encode record) = 39.
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
      rewrite decode_encode_bytes by exact bound_2.
      rewrite decode_encode_uint by exact bound_3.
      rewrite decode_encode_uint by exact bound_4.
      rewrite decode_encode_uint by exact bound_5.
      rewrite decode_encode_uint by exact bound_6.
      rewrite decode_encode_bytes by exact bound_7.
      rewrite decode_encode_uint by exact bound_8.
      rewrite decode_encode_bytes by exact bound_9.
      rewrite decode_encode_bytes by exact bound_10.
      rewrite decode_encode_bytes by exact bound_11.
      rewrite decode_encode_bytes by exact bound_12.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End OptionsDirectoryMessage.

  Module TradingActionMessage.

    (** The options system uses this administrative message to indicate the current trading status of an index or equity option within the options market. *)
    Record t := {
      nanoseconds : N;
      option_id : N;
      current_trading_state : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (nanoseconds record < 256 ^ N.of_nat 4)%N /\
      (option_id record < 256 ^ N.of_nat 4)%N /\
      Datatypes.length (current_trading_state record) = 1.

    Definition encode (record : t) : list byte :=
      encode_uint 4 (nanoseconds record) ++
      encode_uint 4 (option_id record) ++
      encode_bytes 1 (current_trading_state record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 4 bytes with
      | None => None
      | Some (nanoseconds_value, bytes) =>
          match decode_uint 4 bytes with
          | None => None
          | Some (option_id_value, bytes) =>
              match decode_bytes 1 bytes with
              | None => None
              | Some (current_trading_state_value, bytes) =>
                  Some ({| nanoseconds := nanoseconds_value; option_id := option_id_value; current_trading_state := current_trading_state_value |}, bytes)
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 9.
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

  End TradingActionMessage.

  Module SecurityOpenMessage.

    (** The options system uses this administrative message to indicate when an option has completed the opening process and is now available for auto execution or when the option has closed and is no longer available for auto execution. *)
    Record t := {
      nanoseconds : N;
      option_id : N;
      open_state : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (nanoseconds record < 256 ^ N.of_nat 4)%N /\
      (option_id record < 256 ^ N.of_nat 4)%N /\
      Datatypes.length (open_state record) = 1.

    Definition encode (record : t) : list byte :=
      encode_uint 4 (nanoseconds record) ++
      encode_uint 4 (option_id record) ++
      encode_bytes 1 (open_state record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 4 bytes with
      | None => None
      | Some (nanoseconds_value, bytes) =>
          match decode_uint 4 bytes with
          | None => None
          | Some (option_id_value, bytes) =>
              match decode_bytes 1 bytes with
              | None => None
              | Some (open_state_value, bytes) =>
                  Some ({| nanoseconds := nanoseconds_value; option_id := option_id_value; open_state := open_state_value |}, bytes)
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 9.
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

  End SecurityOpenMessage.

  Module BestBidAndAskUpdateShortFormMessage.

    (** The options system will continuously calculate its best bid and offer position for active options contracts on the options market during the trading day. Whenever the best bid and ask position changes on both sides, the options system will send its best bid and ask update via the data feed for the affected security. A change in bid or ask implies a change in price and/or size. The quote will reflect the highest price displayable in the options system for buy orders/quotes and the lowest price displayable in the options system for sell orders/quotes. *)
    Record t := {
      nanoseconds : N;
      option_id : N;
      quote_condition : list byte;
      bid_price : N;
      bid_size : N;
      ask_price : N;
      ask_size : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (nanoseconds record < 256 ^ N.of_nat 4)%N /\
      (option_id record < 256 ^ N.of_nat 4)%N /\
      Datatypes.length (quote_condition record) = 1 /\
      (bid_price record < 256 ^ N.of_nat 2)%N /\
      (bid_size record < 256 ^ N.of_nat 2)%N /\
      (ask_price record < 256 ^ N.of_nat 2)%N /\
      (ask_size record < 256 ^ N.of_nat 2)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 4 (nanoseconds record) ++
      encode_uint 4 (option_id record) ++
      encode_bytes 1 (quote_condition record) ++
      encode_uint 2 (bid_price record) ++
      encode_uint 2 (bid_size record) ++
      encode_uint 2 (ask_price record) ++
      encode_uint 2 (ask_size record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 4 bytes with
      | None => None
      | Some (nanoseconds_value, bytes) =>
          match decode_uint 4 bytes with
          | None => None
          | Some (option_id_value, bytes) =>
              match decode_bytes 1 bytes with
              | None => None
              | Some (quote_condition_value, bytes) =>
                  match decode_uint 2 bytes with
                  | None => None
                  | Some (bid_price_value, bytes) =>
                      match decode_uint 2 bytes with
                      | None => None
                      | Some (bid_size_value, bytes) =>
                          match decode_uint 2 bytes with
                          | None => None
                          | Some (ask_price_value, bytes) =>
                              match decode_uint 2 bytes with
                              | None => None
                              | Some (ask_size_value, bytes) =>
                                  Some ({| nanoseconds := nanoseconds_value; option_id := option_id_value; quote_condition := quote_condition_value; bid_price := bid_price_value; bid_size := bid_size_value; ask_price := ask_price_value; ask_size := ask_size_value |}, bytes)
                              end
                          end
                      end
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
      destruct bound as [bound_0 [bound_1 [bound_2 [bound_3 [bound_4 [bound_5 bound_6]]]]]].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_uint by exact bound_0.
      rewrite decode_encode_uint by exact bound_1.
      rewrite decode_encode_bytes by exact bound_2.
      rewrite decode_encode_uint by exact bound_3.
      rewrite decode_encode_uint by exact bound_4.
      rewrite decode_encode_uint by exact bound_5.
      rewrite decode_encode_uint by exact bound_6.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End BestBidAndAskUpdateShortFormMessage.

  Module BestBidAndAskUpdateLongFormMessage.

    (** This message is the same as the Best Bid AND Ask Update Message – Short Form described above except that Prices and Sizes are 4 byte Integers, the price having 4 implied decimal places. *)
    Record t := {
      nanoseconds : N;
      option_id : N;
      quote_condition : list byte;
      bid_price_long : N;
      bid_size_long : N;
      ask_price_long : N;
      ask_size_long : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (nanoseconds record < 256 ^ N.of_nat 4)%N /\
      (option_id record < 256 ^ N.of_nat 4)%N /\
      Datatypes.length (quote_condition record) = 1 /\
      (bid_price_long record < 256 ^ N.of_nat 4)%N /\
      (bid_size_long record < 256 ^ N.of_nat 4)%N /\
      (ask_price_long record < 256 ^ N.of_nat 4)%N /\
      (ask_size_long record < 256 ^ N.of_nat 4)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 4 (nanoseconds record) ++
      encode_uint 4 (option_id record) ++
      encode_bytes 1 (quote_condition record) ++
      encode_uint 4 (bid_price_long record) ++
      encode_uint 4 (bid_size_long record) ++
      encode_uint 4 (ask_price_long record) ++
      encode_uint 4 (ask_size_long record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 4 bytes with
      | None => None
      | Some (nanoseconds_value, bytes) =>
          match decode_uint 4 bytes with
          | None => None
          | Some (option_id_value, bytes) =>
              match decode_bytes 1 bytes with
              | None => None
              | Some (quote_condition_value, bytes) =>
                  match decode_uint 4 bytes with
                  | None => None
                  | Some (bid_price_long_value, bytes) =>
                      match decode_uint 4 bytes with
                      | None => None
                      | Some (bid_size_long_value, bytes) =>
                          match decode_uint 4 bytes with
                          | None => None
                          | Some (ask_price_long_value, bytes) =>
                              match decode_uint 4 bytes with
                              | None => None
                              | Some (ask_size_long_value, bytes) =>
                                  Some ({| nanoseconds := nanoseconds_value; option_id := option_id_value; quote_condition := quote_condition_value; bid_price_long := bid_price_long_value; bid_size_long := bid_size_long_value; ask_price_long := ask_price_long_value; ask_size_long := ask_size_long_value |}, bytes)
                              end
                          end
                      end
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 25.
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
      rewrite decode_encode_bytes by exact bound_2.
      rewrite decode_encode_uint by exact bound_3.
      rewrite decode_encode_uint by exact bound_4.
      rewrite decode_encode_uint by exact bound_5.
      rewrite decode_encode_uint by exact bound_6.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End BestBidAndAskUpdateLongFormMessage.

  Module BestBidUpdateShortFormMessage.

    (** The options system will continuously calculate its best bid and offer position for active options contracts on the options market during the trading day. Whenever the best bid or ask position changes on one side but not the other side, the options system will send its best bid or ask update via this feed for the affected security. A change in bid or ask implies a change in price and/or size. The quote will reflect the highest price displayable in the options system for buy orders/quotes and the lowest price displayable in the options system for sell orders/quotes. *)
    Record t := {
      nanoseconds : N;
      option_id : N;
      quote_condition : list byte;
      price : N;
      size : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (nanoseconds record < 256 ^ N.of_nat 4)%N /\
      (option_id record < 256 ^ N.of_nat 4)%N /\
      Datatypes.length (quote_condition record) = 1 /\
      (price record < 256 ^ N.of_nat 2)%N /\
      (size record < 256 ^ N.of_nat 2)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 4 (nanoseconds record) ++
      encode_uint 4 (option_id record) ++
      encode_bytes 1 (quote_condition record) ++
      encode_uint 2 (price record) ++
      encode_uint 2 (size record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 4 bytes with
      | None => None
      | Some (nanoseconds_value, bytes) =>
          match decode_uint 4 bytes with
          | None => None
          | Some (option_id_value, bytes) =>
              match decode_bytes 1 bytes with
              | None => None
              | Some (quote_condition_value, bytes) =>
                  match decode_uint 2 bytes with
                  | None => None
                  | Some (price_value, bytes) =>
                      match decode_uint 2 bytes with
                      | None => None
                      | Some (size_value, bytes) =>
                          Some ({| nanoseconds := nanoseconds_value; option_id := option_id_value; quote_condition := quote_condition_value; price := price_value; size := size_value |}, bytes)
                      end
                  end
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
      destruct bound as [bound_0 [bound_1 [bound_2 [bound_3 bound_4]]]].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_uint by exact bound_0.
      rewrite decode_encode_uint by exact bound_1.
      rewrite decode_encode_bytes by exact bound_2.
      rewrite decode_encode_uint by exact bound_3.
      rewrite decode_encode_uint by exact bound_4.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End BestBidUpdateShortFormMessage.

  Module BestAskUpdateShortFormMessage.

    (** The options system will continuously calculate its best bid and offer position for active options contracts on the options market during the trading day. Whenever the best bid or ask position changes on one side but not the other side, the options system will send its best bid or ask update via this feed for the affected security. A change in bid or ask implies a change in price and/or size. The quote will reflect the highest price displayable in the options system for buy orders/quotes and the lowest price displayable in the options system for sell orders/quotes. *)
    Record t := {
      nanoseconds : N;
      option_id : N;
      quote_condition : list byte;
      price : N;
      size : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (nanoseconds record < 256 ^ N.of_nat 4)%N /\
      (option_id record < 256 ^ N.of_nat 4)%N /\
      Datatypes.length (quote_condition record) = 1 /\
      (price record < 256 ^ N.of_nat 2)%N /\
      (size record < 256 ^ N.of_nat 2)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 4 (nanoseconds record) ++
      encode_uint 4 (option_id record) ++
      encode_bytes 1 (quote_condition record) ++
      encode_uint 2 (price record) ++
      encode_uint 2 (size record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 4 bytes with
      | None => None
      | Some (nanoseconds_value, bytes) =>
          match decode_uint 4 bytes with
          | None => None
          | Some (option_id_value, bytes) =>
              match decode_bytes 1 bytes with
              | None => None
              | Some (quote_condition_value, bytes) =>
                  match decode_uint 2 bytes with
                  | None => None
                  | Some (price_value, bytes) =>
                      match decode_uint 2 bytes with
                      | None => None
                      | Some (size_value, bytes) =>
                          Some ({| nanoseconds := nanoseconds_value; option_id := option_id_value; quote_condition := quote_condition_value; price := price_value; size := size_value |}, bytes)
                      end
                  end
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
      destruct bound as [bound_0 [bound_1 [bound_2 [bound_3 bound_4]]]].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_uint by exact bound_0.
      rewrite decode_encode_uint by exact bound_1.
      rewrite decode_encode_bytes by exact bound_2.
      rewrite decode_encode_uint by exact bound_3.
      rewrite decode_encode_uint by exact bound_4.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End BestAskUpdateShortFormMessage.

  Module BestBidUpdateLongFormMessage.

    (** This message is the same as the Best Bid OR Ask Update Message – Short Form described above except that Prices and Sizes are 4 byte Integers, the price having 4 implied decimal places. *)
    Record t := {
      nanoseconds : N;
      option_id : N;
      quote_condition : list byte;
      price_long : N;
      size_long : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (nanoseconds record < 256 ^ N.of_nat 4)%N /\
      (option_id record < 256 ^ N.of_nat 4)%N /\
      Datatypes.length (quote_condition record) = 1 /\
      (price_long record < 256 ^ N.of_nat 4)%N /\
      (size_long record < 256 ^ N.of_nat 4)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 4 (nanoseconds record) ++
      encode_uint 4 (option_id record) ++
      encode_bytes 1 (quote_condition record) ++
      encode_uint 4 (price_long record) ++
      encode_uint 4 (size_long record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 4 bytes with
      | None => None
      | Some (nanoseconds_value, bytes) =>
          match decode_uint 4 bytes with
          | None => None
          | Some (option_id_value, bytes) =>
              match decode_bytes 1 bytes with
              | None => None
              | Some (quote_condition_value, bytes) =>
                  match decode_uint 4 bytes with
                  | None => None
                  | Some (price_long_value, bytes) =>
                      match decode_uint 4 bytes with
                      | None => None
                      | Some (size_long_value, bytes) =>
                          Some ({| nanoseconds := nanoseconds_value; option_id := option_id_value; quote_condition := quote_condition_value; price_long := price_long_value; size_long := size_long_value |}, bytes)
                      end
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
      destruct bound as [bound_0 [bound_1 [bound_2 [bound_3 bound_4]]]].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_uint by exact bound_0.
      rewrite decode_encode_uint by exact bound_1.
      rewrite decode_encode_bytes by exact bound_2.
      rewrite decode_encode_uint by exact bound_3.
      rewrite decode_encode_uint by exact bound_4.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End BestBidUpdateLongFormMessage.

  Module BestAskUpdateLongFormMessage.

    (** This message is the same as the Best Bid OR Ask Update Message – Short Form described above except that Prices and Sizes are 4 byte Integers, the price having 4 implied decimal places. *)
    Record t := {
      nanoseconds : N;
      option_id : N;
      quote_condition : list byte;
      price_long : N;
      size_long : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (nanoseconds record < 256 ^ N.of_nat 4)%N /\
      (option_id record < 256 ^ N.of_nat 4)%N /\
      Datatypes.length (quote_condition record) = 1 /\
      (price_long record < 256 ^ N.of_nat 4)%N /\
      (size_long record < 256 ^ N.of_nat 4)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 4 (nanoseconds record) ++
      encode_uint 4 (option_id record) ++
      encode_bytes 1 (quote_condition record) ++
      encode_uint 4 (price_long record) ++
      encode_uint 4 (size_long record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 4 bytes with
      | None => None
      | Some (nanoseconds_value, bytes) =>
          match decode_uint 4 bytes with
          | None => None
          | Some (option_id_value, bytes) =>
              match decode_bytes 1 bytes with
              | None => None
              | Some (quote_condition_value, bytes) =>
                  match decode_uint 4 bytes with
                  | None => None
                  | Some (price_long_value, bytes) =>
                      match decode_uint 4 bytes with
                      | None => None
                      | Some (size_long_value, bytes) =>
                          Some ({| nanoseconds := nanoseconds_value; option_id := option_id_value; quote_condition := quote_condition_value; price_long := price_long_value; size_long := size_long_value |}, bytes)
                      end
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
      destruct bound as [bound_0 [bound_1 [bound_2 [bound_3 bound_4]]]].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_uint by exact bound_0.
      rewrite decode_encode_uint by exact bound_1.
      rewrite decode_encode_bytes by exact bound_2.
      rewrite decode_encode_uint by exact bound_3.
      rewrite decode_encode_uint by exact bound_4.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End BestAskUpdateLongFormMessage.

  Module TradeReportMessage.

    (** The Trade Report message will be used to relay execution system transactions that are reported during the current business day. The options system only reports one-side of a trade execution on the feed and other data feed products. *)
    Record t := {
      nanoseconds : N;
      option_id : N;
      cross_id : N;
      trade_condition : list byte;
      price_long : N;
      volume : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (nanoseconds record < 256 ^ N.of_nat 4)%N /\
      (option_id record < 256 ^ N.of_nat 4)%N /\
      (cross_id record < 256 ^ N.of_nat 4)%N /\
      Datatypes.length (trade_condition record) = 1 /\
      (price_long record < 256 ^ N.of_nat 4)%N /\
      (volume record < 256 ^ N.of_nat 4)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 4 (nanoseconds record) ++
      encode_uint 4 (option_id record) ++
      encode_uint 4 (cross_id record) ++
      encode_bytes 1 (trade_condition record) ++
      encode_uint 4 (price_long record) ++
      encode_uint 4 (volume record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 4 bytes with
      | None => None
      | Some (nanoseconds_value, bytes) =>
          match decode_uint 4 bytes with
          | None => None
          | Some (option_id_value, bytes) =>
              match decode_uint 4 bytes with
              | None => None
              | Some (cross_id_value, bytes) =>
                  match decode_bytes 1 bytes with
                  | None => None
                  | Some (trade_condition_value, bytes) =>
                      match decode_uint 4 bytes with
                      | None => None
                      | Some (price_long_value, bytes) =>
                          match decode_uint 4 bytes with
                          | None => None
                          | Some (volume_value, bytes) =>
                              Some ({| nanoseconds := nanoseconds_value; option_id := option_id_value; cross_id := cross_id_value; trade_condition := trade_condition_value; price_long := price_long_value; volume := volume_value |}, bytes)
                          end
                      end
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 21.
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
      rewrite decode_encode_uint by exact bound_4.
      rewrite decode_encode_uint by exact bound_5.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End TradeReportMessage.

  Module BrokenTradeReportMessage.

    (** The following message is used in the event that an options trade transaction is broken on the same business day that it is reported. *)
    Record t := {
      nanoseconds : N;
      option_id : N;
      original_cross_id : N;
      original_price : N;
      original_volume : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (nanoseconds record < 256 ^ N.of_nat 4)%N /\
      (option_id record < 256 ^ N.of_nat 4)%N /\
      (original_cross_id record < 256 ^ N.of_nat 4)%N /\
      (original_price record < 256 ^ N.of_nat 4)%N /\
      (original_volume record < 256 ^ N.of_nat 4)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 4 (nanoseconds record) ++
      encode_uint 4 (option_id record) ++
      encode_uint 4 (original_cross_id record) ++
      encode_uint 4 (original_price record) ++
      encode_uint 4 (original_volume record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 4 bytes with
      | None => None
      | Some (nanoseconds_value, bytes) =>
          match decode_uint 4 bytes with
          | None => None
          | Some (option_id_value, bytes) =>
              match decode_uint 4 bytes with
              | None => None
              | Some (original_cross_id_value, bytes) =>
                  match decode_uint 4 bytes with
                  | None => None
                  | Some (original_price_value, bytes) =>
                      match decode_uint 4 bytes with
                      | None => None
                      | Some (original_volume_value, bytes) =>
                          Some ({| nanoseconds := nanoseconds_value; option_id := option_id_value; original_cross_id := original_cross_id_value; original_price := original_price_value; original_volume := original_volume_value |}, bytes)
                      end
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 20.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_uint_length. reflexivity.
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
      rewrite decode_encode_uint by exact bound_3.
      rewrite decode_encode_uint by exact bound_4.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec]. Defined.

  End BrokenTradeReportMessage.

End NtxOptionsTopOfMarketV12.
