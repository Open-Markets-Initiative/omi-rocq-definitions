From Stdlib Require Import List.
From Stdlib Require Import NArith.
From Stdlib Require Import Lia.
From Stdlib Require Import Strings.Byte.
From Omi Require Import Wire.

Import ListNotations.

(** * Miami International Holdings Complex Top of Market

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
      - a length prefix framing what follows
      - a run counted by a field
  *)

Module EmeraldOptionsComplexTopOfMarketV10AUdp.

  Module MachPacketHeader.

    (** Mach packet header (12 bytes) *)
    Record t := {
      sequence_number : N;
      packet_length : N;
      packet_type : N;
      session_number : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (sequence_number record < 256 ^ N.of_nat 8)%N /\
      (packet_length record < 256 ^ N.of_nat 2)%N /\
      (packet_type record < 256 ^ N.of_nat 1)%N /\
      (session_number record < 256 ^ N.of_nat 1)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 8 (sequence_number record) ++
      encode_uint 2 (packet_length record) ++
      encode_uint 1 (packet_type record) ++
      encode_uint 1 (session_number record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 8 bytes with
      | None => None
      | Some (sequence_number_value, bytes) =>
          match decode_uint 2 bytes with
          | None => None
          | Some (packet_length_value, bytes) =>
              match decode_uint 1 bytes with
              | None => None
              | Some (packet_type_value, bytes) =>
                  match decode_uint 1 bytes with
                  | None => None
                  | Some (session_number_value, bytes) =>
                      Some ({| sequence_number := sequence_number_value; packet_length := packet_length_value; packet_type := packet_type_value; session_number := session_number_value |}, bytes)
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 12.
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

  End MachPacketHeader.

  Module SystemTimeMessage.

    (** This is the message format that will be used to disseminate the "seconds" part of the timestamp that is applicable to all messages that are sent in the current second. *)
    Record t := {
      seconds : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (seconds record < 256 ^ N.of_nat 4)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 4 (seconds record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 4 bytes with
      | None => None
      | Some (seconds_value, bytes) =>
          Some ({| seconds := seconds_value |}, bytes)
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

  End SystemTimeMessage.

  Module SimpleSeriesUpdateMessage.

    (** This is the message format that will be used to disseminate all Option series traded on Emerald for the current session. *)
    Record t := {
      nanoseconds : N;
      product_id : N;
      underlying_symbol : list byte;
      security_symbol : list byte;
      expiration_date : list byte;
      strike_price : N;
      call_or_put : list byte;
      opening_time : list byte;
      closing_time : list byte;
      restricted_option : list byte;
      long_term_option : list byte;
      active_on_emerald : list byte;
      emerald_bbo_posting_increment_indicator : list byte;
      liquidity_acceptance_increment_indicator : list byte;
      opening_underlying_market_code : list byte;
      priority_quote_width : N;
      reserved_8 : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (nanoseconds record < 256 ^ N.of_nat 4)%N /\
      (product_id record < 256 ^ N.of_nat 4)%N /\
      Datatypes.length (underlying_symbol record) = 11 /\
      Datatypes.length (security_symbol record) = 6 /\
      Datatypes.length (expiration_date record) = 8 /\
      (strike_price record < 256 ^ N.of_nat 4)%N /\
      Datatypes.length (call_or_put record) = 1 /\
      Datatypes.length (opening_time record) = 8 /\
      Datatypes.length (closing_time record) = 8 /\
      Datatypes.length (restricted_option record) = 1 /\
      Datatypes.length (long_term_option record) = 1 /\
      Datatypes.length (active_on_emerald record) = 1 /\
      Datatypes.length (emerald_bbo_posting_increment_indicator record) = 1 /\
      Datatypes.length (liquidity_acceptance_increment_indicator record) = 1 /\
      Datatypes.length (opening_underlying_market_code record) = 1 /\
      (priority_quote_width record < 256 ^ N.of_nat 4)%N /\
      (reserved_8 record < 256 ^ N.of_nat 8)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 4 (nanoseconds record) ++
      encode_uint 4 (product_id record) ++
      encode_bytes 11 (underlying_symbol record) ++
      encode_bytes 6 (security_symbol record) ++
      encode_bytes 8 (expiration_date record) ++
      encode_uint 4 (strike_price record) ++
      encode_bytes 1 (call_or_put record) ++
      encode_bytes 8 (opening_time record) ++
      encode_bytes 8 (closing_time record) ++
      encode_bytes 1 (restricted_option record) ++
      encode_bytes 1 (long_term_option record) ++
      encode_bytes 1 (active_on_emerald record) ++
      encode_bytes 1 (emerald_bbo_posting_increment_indicator record) ++
      encode_bytes 1 (liquidity_acceptance_increment_indicator record) ++
      encode_bytes 1 (opening_underlying_market_code record) ++
      encode_uint 4 (priority_quote_width record) ++
      encode_uint 8 (reserved_8 record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 4 bytes with
      | None => None
      | Some (nanoseconds_value, bytes) =>
          match decode_uint 4 bytes with
          | None => None
          | Some (product_id_value, bytes) =>
              match decode_bytes 11 bytes with
              | None => None
              | Some (underlying_symbol_value, bytes) =>
                  match decode_bytes 6 bytes with
                  | None => None
                  | Some (security_symbol_value, bytes) =>
                      match decode_bytes 8 bytes with
                      | None => None
                      | Some (expiration_date_value, bytes) =>
                          match decode_uint 4 bytes with
                          | None => None
                          | Some (strike_price_value, bytes) =>
                              match decode_bytes 1 bytes with
                              | None => None
                              | Some (call_or_put_value, bytes) =>
                                  match decode_bytes 8 bytes with
                                  | None => None
                                  | Some (opening_time_value, bytes) =>
                                      match decode_bytes 8 bytes with
                                      | None => None
                                      | Some (closing_time_value, bytes) =>
                                          match decode_bytes 1 bytes with
                                          | None => None
                                          | Some (restricted_option_value, bytes) =>
                                              match decode_bytes 1 bytes with
                                              | None => None
                                              | Some (long_term_option_value, bytes) =>
                                                  match decode_bytes 1 bytes with
                                                  | None => None
                                                  | Some (active_on_emerald_value, bytes) =>
                                                      match decode_bytes 1 bytes with
                                                      | None => None
                                                      | Some (emerald_bbo_posting_increment_indicator_value, bytes) =>
                                                          match decode_bytes 1 bytes with
                                                          | None => None
                                                          | Some (liquidity_acceptance_increment_indicator_value, bytes) =>
                                                              match decode_bytes 1 bytes with
                                                              | None => None
                                                              | Some (opening_underlying_market_code_value, bytes) =>
                                                                  match decode_uint 4 bytes with
                                                                  | None => None
                                                                  | Some (priority_quote_width_value, bytes) =>
                                                                      match decode_uint 8 bytes with
                                                                      | None => None
                                                                      | Some (reserved_8_value, bytes) =>
                                                                          Some ({| nanoseconds := nanoseconds_value; product_id := product_id_value; underlying_symbol := underlying_symbol_value; security_symbol := security_symbol_value; expiration_date := expiration_date_value; strike_price := strike_price_value; call_or_put := call_or_put_value; opening_time := opening_time_value; closing_time := closing_time_value; restricted_option := restricted_option_value; long_term_option := long_term_option_value; active_on_emerald := active_on_emerald_value; emerald_bbo_posting_increment_indicator := emerald_bbo_posting_increment_indicator_value; liquidity_acceptance_increment_indicator := liquidity_acceptance_increment_indicator_value; opening_underlying_market_code := opening_underlying_market_code_value; priority_quote_width := priority_quote_width_value; reserved_8 := reserved_8_value |}, bytes)
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
      rewrite decode_encode_bytes by exact bound_2.
      rewrite decode_encode_bytes by exact bound_3.
      rewrite decode_encode_bytes by exact bound_4.
      rewrite decode_encode_uint by exact bound_5.
      rewrite decode_encode_bytes by exact bound_6.
      rewrite decode_encode_bytes by exact bound_7.
      rewrite decode_encode_bytes by exact bound_8.
      rewrite decode_encode_bytes by exact bound_9.
      rewrite decode_encode_bytes by exact bound_10.
      rewrite decode_encode_bytes by exact bound_11.
      rewrite decode_encode_bytes by exact bound_12.
      rewrite decode_encode_bytes by exact bound_13.
      rewrite decode_encode_bytes by exact bound_14.
      rewrite decode_encode_uint by exact bound_15.
      rewrite decode_encode_uint by exact bound_16.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End SimpleSeriesUpdateMessage.

  Module SystemStateMessage.

    (** This message format is used to notify the firms of the state changes of the system. This is a notification that applies to each Underlying group. Firms can use notifications as triggers in their system to ensure electronic synchronization of systems. *)
    Record t := {
      nanoseconds : N;
      c_to_m_version : list byte;
      session_id : N;
      system_status : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (nanoseconds record < 256 ^ N.of_nat 4)%N /\
      Datatypes.length (c_to_m_version record) = 8 /\
      (session_id record < 256 ^ N.of_nat 4)%N /\
      Datatypes.length (system_status record) = 1.

    Definition encode (record : t) : list byte :=
      encode_uint 4 (nanoseconds record) ++
      encode_bytes 8 (c_to_m_version record) ++
      encode_uint 4 (session_id record) ++
      encode_bytes 1 (system_status record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 4 bytes with
      | None => None
      | Some (nanoseconds_value, bytes) =>
          match decode_bytes 8 bytes with
          | None => None
          | Some (c_to_m_version_value, bytes) =>
              match decode_uint 4 bytes with
              | None => None
              | Some (session_id_value, bytes) =>
                  match decode_bytes 1 bytes with
                  | None => None
                  | Some (system_status_value, bytes) =>
                      Some ({| nanoseconds := nanoseconds_value; c_to_m_version := c_to_m_version_value; session_id := session_id_value; system_status := system_status_value |}, bytes)
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
      rewrite decode_encode_uint by exact bound_2.
      rewrite decode_encode_bytes by exact bound_3.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End SystemStateMessage.

  Module ComplexTopOfMarketBestBidOrOfferCompactFormatBidMessage.

    (** This is the message format that will be used to disseminate each side of the Emerald Complex Top of Market for strategies with low Net Price and small aggregate Emerald Best Bid or Offer (MBBO) size. Emerald Complex Top of Market on Bid side. *)
    Record t := {
      nanoseconds : N;
      strategy_id : N;
      price_short : N;
      size_short : N;
      priority_customer_size_short : N;
      condition : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (nanoseconds record < 256 ^ N.of_nat 4)%N /\
      (strategy_id record < 256 ^ N.of_nat 4)%N /\
      (price_short record < 256 ^ N.of_nat 2)%N /\
      (size_short record < 256 ^ N.of_nat 2)%N /\
      (priority_customer_size_short record < 256 ^ N.of_nat 2)%N /\
      Datatypes.length (condition record) = 1.

    Definition encode (record : t) : list byte :=
      encode_uint 4 (nanoseconds record) ++
      encode_uint 4 (strategy_id record) ++
      encode_uint 2 (price_short record) ++
      encode_uint 2 (size_short record) ++
      encode_uint 2 (priority_customer_size_short record) ++
      encode_bytes 1 (condition record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 4 bytes with
      | None => None
      | Some (nanoseconds_value, bytes) =>
          match decode_uint 4 bytes with
          | None => None
          | Some (strategy_id_value, bytes) =>
              match decode_uint 2 bytes with
              | None => None
              | Some (price_short_value, bytes) =>
                  match decode_uint 2 bytes with
                  | None => None
                  | Some (size_short_value, bytes) =>
                      match decode_uint 2 bytes with
                      | None => None
                      | Some (priority_customer_size_short_value, bytes) =>
                          match decode_bytes 1 bytes with
                          | None => None
                          | Some (condition_value, bytes) =>
                              Some ({| nanoseconds := nanoseconds_value; strategy_id := strategy_id_value; price_short := price_short_value; size_short := size_short_value; priority_customer_size_short := priority_customer_size_short_value; condition := condition_value |}, bytes)
                          end
                      end
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 15.
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
      rewrite decode_encode_uint by exact bound_3.
      rewrite decode_encode_uint by exact bound_4.
      rewrite decode_encode_bytes by exact bound_5.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End ComplexTopOfMarketBestBidOrOfferCompactFormatBidMessage.

  Module ComplexTopOfMarketBestBidOrOfferCompactFormatOfferMessage.

    (** This is the message format that will be used to disseminate each side of the Emerald Complex Top of Market for strategies with low Net Price and small aggregate Emerald Best Bid or Offer (MBBO) size. Emerald Complex Top of Market on Offer side. *)
    Record t := {
      nanoseconds : N;
      strategy_id : N;
      price_short : N;
      size_short : N;
      priority_customer_size_short : N;
      condition : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (nanoseconds record < 256 ^ N.of_nat 4)%N /\
      (strategy_id record < 256 ^ N.of_nat 4)%N /\
      (price_short record < 256 ^ N.of_nat 2)%N /\
      (size_short record < 256 ^ N.of_nat 2)%N /\
      (priority_customer_size_short record < 256 ^ N.of_nat 2)%N /\
      Datatypes.length (condition record) = 1.

    Definition encode (record : t) : list byte :=
      encode_uint 4 (nanoseconds record) ++
      encode_uint 4 (strategy_id record) ++
      encode_uint 2 (price_short record) ++
      encode_uint 2 (size_short record) ++
      encode_uint 2 (priority_customer_size_short record) ++
      encode_bytes 1 (condition record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 4 bytes with
      | None => None
      | Some (nanoseconds_value, bytes) =>
          match decode_uint 4 bytes with
          | None => None
          | Some (strategy_id_value, bytes) =>
              match decode_uint 2 bytes with
              | None => None
              | Some (price_short_value, bytes) =>
                  match decode_uint 2 bytes with
                  | None => None
                  | Some (size_short_value, bytes) =>
                      match decode_uint 2 bytes with
                      | None => None
                      | Some (priority_customer_size_short_value, bytes) =>
                          match decode_bytes 1 bytes with
                          | None => None
                          | Some (condition_value, bytes) =>
                              Some ({| nanoseconds := nanoseconds_value; strategy_id := strategy_id_value; price_short := price_short_value; size_short := size_short_value; priority_customer_size_short := priority_customer_size_short_value; condition := condition_value |}, bytes)
                          end
                      end
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 15.
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
      rewrite decode_encode_uint by exact bound_3.
      rewrite decode_encode_uint by exact bound_4.
      rewrite decode_encode_bytes by exact bound_5.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End ComplexTopOfMarketBestBidOrOfferCompactFormatOfferMessage.

  Module ComplexTopOfMarketBestBidOrOfferWideFormatBidMessage.

    (** This is the message format that will be used to disseminate Emerald Complex Top of Market for strategies with high net price or large aggregate Emerald Best Bid or Offer (EBBO) size. Emerald Complex Top of Market on Bid side. *)
    Record t := {
      nanoseconds : N;
      strategy_id : N;
      price_long : N;
      size_long : N;
      priority_customer_size_long : N;
      condition : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (nanoseconds record < 256 ^ N.of_nat 4)%N /\
      (strategy_id record < 256 ^ N.of_nat 4)%N /\
      (price_long record < 256 ^ N.of_nat 8)%N /\
      (size_long record < 256 ^ N.of_nat 4)%N /\
      (priority_customer_size_long record < 256 ^ N.of_nat 4)%N /\
      Datatypes.length (condition record) = 1.

    Definition encode (record : t) : list byte :=
      encode_uint 4 (nanoseconds record) ++
      encode_uint 4 (strategy_id record) ++
      encode_uint 8 (price_long record) ++
      encode_uint 4 (size_long record) ++
      encode_uint 4 (priority_customer_size_long record) ++
      encode_bytes 1 (condition record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 4 bytes with
      | None => None
      | Some (nanoseconds_value, bytes) =>
          match decode_uint 4 bytes with
          | None => None
          | Some (strategy_id_value, bytes) =>
              match decode_uint 8 bytes with
              | None => None
              | Some (price_long_value, bytes) =>
                  match decode_uint 4 bytes with
                  | None => None
                  | Some (size_long_value, bytes) =>
                      match decode_uint 4 bytes with
                      | None => None
                      | Some (priority_customer_size_long_value, bytes) =>
                          match decode_bytes 1 bytes with
                          | None => None
                          | Some (condition_value, bytes) =>
                              Some ({| nanoseconds := nanoseconds_value; strategy_id := strategy_id_value; price_long := price_long_value; size_long := size_long_value; priority_customer_size_long := priority_customer_size_long_value; condition := condition_value |}, bytes)
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
      destruct bound as [bound_0 [bound_1 [bound_2 [bound_3 [bound_4 bound_5]]]]].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_uint by exact bound_0.
      rewrite decode_encode_uint by exact bound_1.
      rewrite decode_encode_uint by exact bound_2.
      rewrite decode_encode_uint by exact bound_3.
      rewrite decode_encode_uint by exact bound_4.
      rewrite decode_encode_bytes by exact bound_5.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End ComplexTopOfMarketBestBidOrOfferWideFormatBidMessage.

  Module ComplexTopOfMarketBestBidOrOfferWideFormatOfferMessage.

    (** This is the message format that will be used to disseminate Emerald Complex Top of Market for strategies with high net price or large aggregate Emerald Best Bid or Offer (EBBO) size. Emerald Complex Top of Market on Offer side. *)
    Record t := {
      nanoseconds : N;
      strategy_id : N;
      price_long : N;
      size_long : N;
      priority_customer_size_long : N;
      condition : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (nanoseconds record < 256 ^ N.of_nat 4)%N /\
      (strategy_id record < 256 ^ N.of_nat 4)%N /\
      (price_long record < 256 ^ N.of_nat 8)%N /\
      (size_long record < 256 ^ N.of_nat 4)%N /\
      (priority_customer_size_long record < 256 ^ N.of_nat 4)%N /\
      Datatypes.length (condition record) = 1.

    Definition encode (record : t) : list byte :=
      encode_uint 4 (nanoseconds record) ++
      encode_uint 4 (strategy_id record) ++
      encode_uint 8 (price_long record) ++
      encode_uint 4 (size_long record) ++
      encode_uint 4 (priority_customer_size_long record) ++
      encode_bytes 1 (condition record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 4 bytes with
      | None => None
      | Some (nanoseconds_value, bytes) =>
          match decode_uint 4 bytes with
          | None => None
          | Some (strategy_id_value, bytes) =>
              match decode_uint 8 bytes with
              | None => None
              | Some (price_long_value, bytes) =>
                  match decode_uint 4 bytes with
                  | None => None
                  | Some (size_long_value, bytes) =>
                      match decode_uint 4 bytes with
                      | None => None
                      | Some (priority_customer_size_long_value, bytes) =>
                          match decode_bytes 1 bytes with
                          | None => None
                          | Some (condition_value, bytes) =>
                              Some ({| nanoseconds := nanoseconds_value; strategy_id := strategy_id_value; price_long := price_long_value; size_long := size_long_value; priority_customer_size_long := priority_customer_size_long_value; condition := condition_value |}, bytes)
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
      destruct bound as [bound_0 [bound_1 [bound_2 [bound_3 [bound_4 bound_5]]]]].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_uint by exact bound_0.
      rewrite decode_encode_uint by exact bound_1.
      rewrite decode_encode_uint by exact bound_2.
      rewrite decode_encode_uint by exact bound_3.
      rewrite decode_encode_uint by exact bound_4.
      rewrite decode_encode_bytes by exact bound_5.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End ComplexTopOfMarketBestBidOrOfferWideFormatOfferMessage.

  Module ComplexDoubleSidedTopOfMarketBestBidAndOfferCompactFormatMessage.

    (** This is the message format that will be used to disseminate both sides of the Emerald top of market for strategies (cEBBO) with low net price and small aggregate size. *)
    Record t := {
      nanoseconds : N;
      strategy_id : N;
      bid_price_short : N;
      bid_size_short : N;
      bid_priority_customer_size_short : N;
      bid_condition : list byte;
      offer_price_short : N;
      offer_size_short : N;
      offer_priority_customer_size_short : N;
      offer_condition : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (nanoseconds record < 256 ^ N.of_nat 4)%N /\
      (strategy_id record < 256 ^ N.of_nat 4)%N /\
      (bid_price_short record < 256 ^ N.of_nat 2)%N /\
      (bid_size_short record < 256 ^ N.of_nat 2)%N /\
      (bid_priority_customer_size_short record < 256 ^ N.of_nat 2)%N /\
      Datatypes.length (bid_condition record) = 1 /\
      (offer_price_short record < 256 ^ N.of_nat 2)%N /\
      (offer_size_short record < 256 ^ N.of_nat 2)%N /\
      (offer_priority_customer_size_short record < 256 ^ N.of_nat 2)%N /\
      Datatypes.length (offer_condition record) = 1.

    Definition encode (record : t) : list byte :=
      encode_uint 4 (nanoseconds record) ++
      encode_uint 4 (strategy_id record) ++
      encode_uint 2 (bid_price_short record) ++
      encode_uint 2 (bid_size_short record) ++
      encode_uint 2 (bid_priority_customer_size_short record) ++
      encode_bytes 1 (bid_condition record) ++
      encode_uint 2 (offer_price_short record) ++
      encode_uint 2 (offer_size_short record) ++
      encode_uint 2 (offer_priority_customer_size_short record) ++
      encode_bytes 1 (offer_condition record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 4 bytes with
      | None => None
      | Some (nanoseconds_value, bytes) =>
          match decode_uint 4 bytes with
          | None => None
          | Some (strategy_id_value, bytes) =>
              match decode_uint 2 bytes with
              | None => None
              | Some (bid_price_short_value, bytes) =>
                  match decode_uint 2 bytes with
                  | None => None
                  | Some (bid_size_short_value, bytes) =>
                      match decode_uint 2 bytes with
                      | None => None
                      | Some (bid_priority_customer_size_short_value, bytes) =>
                          match decode_bytes 1 bytes with
                          | None => None
                          | Some (bid_condition_value, bytes) =>
                              match decode_uint 2 bytes with
                              | None => None
                              | Some (offer_price_short_value, bytes) =>
                                  match decode_uint 2 bytes with
                                  | None => None
                                  | Some (offer_size_short_value, bytes) =>
                                      match decode_uint 2 bytes with
                                      | None => None
                                      | Some (offer_priority_customer_size_short_value, bytes) =>
                                          match decode_bytes 1 bytes with
                                          | None => None
                                          | Some (offer_condition_value, bytes) =>
                                              Some ({| nanoseconds := nanoseconds_value; strategy_id := strategy_id_value; bid_price_short := bid_price_short_value; bid_size_short := bid_size_short_value; bid_priority_customer_size_short := bid_priority_customer_size_short_value; bid_condition := bid_condition_value; offer_price_short := offer_price_short_value; offer_size_short := offer_size_short_value; offer_priority_customer_size_short := offer_priority_customer_size_short_value; offer_condition := offer_condition_value |}, bytes)
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

    Theorem encode_length : forall record, Datatypes.length (encode record) = 22.
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
      rewrite decode_encode_uint by exact bound_3.
      rewrite decode_encode_uint by exact bound_4.
      rewrite decode_encode_bytes by exact bound_5.
      rewrite decode_encode_uint by exact bound_6.
      rewrite decode_encode_uint by exact bound_7.
      rewrite decode_encode_uint by exact bound_8.
      rewrite decode_encode_bytes by exact bound_9.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End ComplexDoubleSidedTopOfMarketBestBidAndOfferCompactFormatMessage.

  Module ComplexDoubleSidedTopOfMarketBestBidAndOfferWideFormatMessage.

    (** This is the message format that will be used to disseminate both sides of the Emerald top of market for strategies (cEBBO) with net prices or aggregate sizes which cannot be specified in the compact format. *)
    Record t := {
      nanoseconds : N;
      strategy_id : N;
      bid_price_long : N;
      bid_size_long : N;
      bid_priority_customer_size_long : N;
      bid_condition : list byte;
      offer_price_long : N;
      offer_size_long : N;
      offer_priority_customer_size_long : N;
      offer_condition : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (nanoseconds record < 256 ^ N.of_nat 4)%N /\
      (strategy_id record < 256 ^ N.of_nat 4)%N /\
      (bid_price_long record < 256 ^ N.of_nat 8)%N /\
      (bid_size_long record < 256 ^ N.of_nat 4)%N /\
      (bid_priority_customer_size_long record < 256 ^ N.of_nat 4)%N /\
      Datatypes.length (bid_condition record) = 1 /\
      (offer_price_long record < 256 ^ N.of_nat 8)%N /\
      (offer_size_long record < 256 ^ N.of_nat 4)%N /\
      (offer_priority_customer_size_long record < 256 ^ N.of_nat 4)%N /\
      Datatypes.length (offer_condition record) = 1.

    Definition encode (record : t) : list byte :=
      encode_uint 4 (nanoseconds record) ++
      encode_uint 4 (strategy_id record) ++
      encode_uint 8 (bid_price_long record) ++
      encode_uint 4 (bid_size_long record) ++
      encode_uint 4 (bid_priority_customer_size_long record) ++
      encode_bytes 1 (bid_condition record) ++
      encode_uint 8 (offer_price_long record) ++
      encode_uint 4 (offer_size_long record) ++
      encode_uint 4 (offer_priority_customer_size_long record) ++
      encode_bytes 1 (offer_condition record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 4 bytes with
      | None => None
      | Some (nanoseconds_value, bytes) =>
          match decode_uint 4 bytes with
          | None => None
          | Some (strategy_id_value, bytes) =>
              match decode_uint 8 bytes with
              | None => None
              | Some (bid_price_long_value, bytes) =>
                  match decode_uint 4 bytes with
                  | None => None
                  | Some (bid_size_long_value, bytes) =>
                      match decode_uint 4 bytes with
                      | None => None
                      | Some (bid_priority_customer_size_long_value, bytes) =>
                          match decode_bytes 1 bytes with
                          | None => None
                          | Some (bid_condition_value, bytes) =>
                              match decode_uint 8 bytes with
                              | None => None
                              | Some (offer_price_long_value, bytes) =>
                                  match decode_uint 4 bytes with
                                  | None => None
                                  | Some (offer_size_long_value, bytes) =>
                                      match decode_uint 4 bytes with
                                      | None => None
                                      | Some (offer_priority_customer_size_long_value, bytes) =>
                                          match decode_bytes 1 bytes with
                                          | None => None
                                          | Some (offer_condition_value, bytes) =>
                                              Some ({| nanoseconds := nanoseconds_value; strategy_id := strategy_id_value; bid_price_long := bid_price_long_value; bid_size_long := bid_size_long_value; bid_priority_customer_size_long := bid_priority_customer_size_long_value; bid_condition := bid_condition_value; offer_price_long := offer_price_long_value; offer_size_long := offer_size_long_value; offer_priority_customer_size_long := offer_priority_customer_size_long_value; offer_condition := offer_condition_value |}, bytes)
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

    Theorem encode_length : forall record, Datatypes.length (encode record) = 42.
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
      rewrite decode_encode_uint by exact bound_3.
      rewrite decode_encode_uint by exact bound_4.
      rewrite decode_encode_bytes by exact bound_5.
      rewrite decode_encode_uint by exact bound_6.
      rewrite decode_encode_uint by exact bound_7.
      rewrite decode_encode_uint by exact bound_8.
      rewrite decode_encode_bytes by exact bound_9.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End ComplexDoubleSidedTopOfMarketBestBidAndOfferWideFormatMessage.

  Module StrategyLastSaleMessage.

    (** This is the message format that will be used to disseminate Trades that are resulting from executions on Emerald during the current trading session. *)
    Record t := {
      nanoseconds : N;
      strategy_id : N;
      trade_id : N;
      net_price : N;
      size_long : N;
      condition : list byte;
      reserved_16 : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (nanoseconds record < 256 ^ N.of_nat 4)%N /\
      (strategy_id record < 256 ^ N.of_nat 4)%N /\
      (trade_id record < 256 ^ N.of_nat 4)%N /\
      (net_price record < 256 ^ N.of_nat 8)%N /\
      (size_long record < 256 ^ N.of_nat 4)%N /\
      Datatypes.length (condition record) = 1 /\
      Datatypes.length (reserved_16 record) = 16.

    Definition encode (record : t) : list byte :=
      encode_uint 4 (nanoseconds record) ++
      encode_uint 4 (strategy_id record) ++
      encode_uint 4 (trade_id record) ++
      encode_uint 8 (net_price record) ++
      encode_uint 4 (size_long record) ++
      encode_bytes 1 (condition record) ++
      encode_bytes 16 (reserved_16 record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 4 bytes with
      | None => None
      | Some (nanoseconds_value, bytes) =>
          match decode_uint 4 bytes with
          | None => None
          | Some (strategy_id_value, bytes) =>
              match decode_uint 4 bytes with
              | None => None
              | Some (trade_id_value, bytes) =>
                  match decode_uint 8 bytes with
                  | None => None
                  | Some (net_price_value, bytes) =>
                      match decode_uint 4 bytes with
                      | None => None
                      | Some (size_long_value, bytes) =>
                          match decode_bytes 1 bytes with
                          | None => None
                          | Some (condition_value, bytes) =>
                              match decode_bytes 16 bytes with
                              | None => None
                              | Some (reserved_16_value, bytes) =>
                                  Some ({| nanoseconds := nanoseconds_value; strategy_id := strategy_id_value; trade_id := trade_id_value; net_price := net_price_value; size_long := size_long_value; condition := condition_value; reserved_16 := reserved_16_value |}, bytes)
                              end
                          end
                      end
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 41.
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

  End StrategyLastSaleMessage.

  Module UnderlyingTradingStatusNotificationMessage.

    (** This message format will be used to notify firms of changes to the trading status of all the options of an underlying. *)
    Record t := {
      nanoseconds : N;
      underlying_symbol : list byte;
      trading_status : list byte;
      event_reason : list byte;
      expected_event_time_seconds_part : N;
      expected_event_time_nano_seconds_part : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (nanoseconds record < 256 ^ N.of_nat 4)%N /\
      Datatypes.length (underlying_symbol record) = 11 /\
      Datatypes.length (trading_status record) = 1 /\
      Datatypes.length (event_reason record) = 1 /\
      (expected_event_time_seconds_part record < 256 ^ N.of_nat 4)%N /\
      (expected_event_time_nano_seconds_part record < 256 ^ N.of_nat 4)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 4 (nanoseconds record) ++
      encode_bytes 11 (underlying_symbol record) ++
      encode_bytes 1 (trading_status record) ++
      encode_bytes 1 (event_reason record) ++
      encode_uint 4 (expected_event_time_seconds_part record) ++
      encode_uint 4 (expected_event_time_nano_seconds_part record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 4 bytes with
      | None => None
      | Some (nanoseconds_value, bytes) =>
          match decode_bytes 11 bytes with
          | None => None
          | Some (underlying_symbol_value, bytes) =>
              match decode_bytes 1 bytes with
              | None => None
              | Some (trading_status_value, bytes) =>
                  match decode_bytes 1 bytes with
                  | None => None
                  | Some (event_reason_value, bytes) =>
                      match decode_uint 4 bytes with
                      | None => None
                      | Some (expected_event_time_seconds_part_value, bytes) =>
                          match decode_uint 4 bytes with
                          | None => None
                          | Some (expected_event_time_nano_seconds_part_value, bytes) =>
                              Some ({| nanoseconds := nanoseconds_value; underlying_symbol := underlying_symbol_value; trading_status := trading_status_value; event_reason := event_reason_value; expected_event_time_seconds_part := expected_event_time_seconds_part_value; expected_event_time_nano_seconds_part := expected_event_time_nano_seconds_part_value |}, bytes)
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
      destruct bound as [bound_0 [bound_1 [bound_2 [bound_3 [bound_4 bound_5]]]]].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_uint by exact bound_0.
      rewrite decode_encode_bytes by exact bound_1.
      rewrite decode_encode_bytes by exact bound_2.
      rewrite decode_encode_bytes by exact bound_3.
      rewrite decode_encode_uint by exact bound_4.
      rewrite decode_encode_uint by exact bound_5.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End UnderlyingTradingStatusNotificationMessage.

End EmeraldOptionsComplexTopOfMarketV10AUdp.
