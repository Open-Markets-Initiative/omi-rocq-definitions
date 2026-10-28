From Stdlib Require Import List.
From Stdlib Require Import NArith.
From Stdlib Require Import Lia.
From Stdlib Require Import Strings.Byte.
From Omi Require Import Wire.

Import ListNotations.

(** * Miami International Holdings Top of Market

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

Module SapphireOptionsTopOfMarketV20Tcp.

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

  Module RefreshRequestMessage.

    (** Sent by the firm over the ToM Retransmission Interface (SesM Unsequenced Data Packet) to request a Last Value Refresh of a particular data set identified by Refresh Message Type. *)
    Record t := {
      refresh_message_type : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (refresh_message_type record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 1 (refresh_message_type record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 1 bytes with
      | None => None
      | Some (refresh_message_type_value, bytes) =>
          Some ({| refresh_message_type := refresh_message_type_value |}, bytes)
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

  End RefreshRequestMessage.

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

  Module SeriesUpdateMessage.

    (** This is the message format that will be used to disseminate all Option series traded on Sapphire for the current session. The product ID sent in this message is what will be disseminated in Top of Market BBO and Last Sale messages. *)
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
      active_on_sapphire : list byte;
      sapphire_bbo_posting_increment_indicator : list byte;
      liquidity_acceptance_increment_indicator : list byte;
      opening_underlying_market_code : list byte;
      reserved_12 : list byte;
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
      Datatypes.length (active_on_sapphire record) = 1 /\
      Datatypes.length (sapphire_bbo_posting_increment_indicator record) = 1 /\
      Datatypes.length (liquidity_acceptance_increment_indicator record) = 1 /\
      Datatypes.length (opening_underlying_market_code record) = 1 /\
      Datatypes.length (reserved_12 record) = 12.

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
      encode_bytes 1 (active_on_sapphire record) ++
      encode_bytes 1 (sapphire_bbo_posting_increment_indicator record) ++
      encode_bytes 1 (liquidity_acceptance_increment_indicator record) ++
      encode_bytes 1 (opening_underlying_market_code record) ++
      encode_bytes 12 (reserved_12 record).

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
                                                  | Some (active_on_sapphire_value, bytes) =>
                                                      match decode_bytes 1 bytes with
                                                      | None => None
                                                      | Some (sapphire_bbo_posting_increment_indicator_value, bytes) =>
                                                          match decode_bytes 1 bytes with
                                                          | None => None
                                                          | Some (liquidity_acceptance_increment_indicator_value, bytes) =>
                                                              match decode_bytes 1 bytes with
                                                              | None => None
                                                              | Some (opening_underlying_market_code_value, bytes) =>
                                                                  match decode_bytes 12 bytes with
                                                                  | None => None
                                                                  | Some (reserved_12_value, bytes) =>
                                                                      Some ({| nanoseconds := nanoseconds_value; product_id := product_id_value; underlying_symbol := underlying_symbol_value; security_symbol := security_symbol_value; expiration_date := expiration_date_value; strike_price := strike_price_value; call_or_put := call_or_put_value; opening_time := opening_time_value; closing_time := closing_time_value; restricted_option := restricted_option_value; long_term_option := long_term_option_value; active_on_sapphire := active_on_sapphire_value; sapphire_bbo_posting_increment_indicator := sapphire_bbo_posting_increment_indicator_value; liquidity_acceptance_increment_indicator := liquidity_acceptance_increment_indicator_value; opening_underlying_market_code := opening_underlying_market_code_value; reserved_12 := reserved_12_value |}, bytes)
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
      destruct bound as [bound_0 [bound_1 [bound_2 [bound_3 [bound_4 [bound_5 [bound_6 [bound_7 [bound_8 [bound_9 [bound_10 [bound_11 [bound_12 [bound_13 [bound_14 bound_15]]]]]]]]]]]]]]].
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
      rewrite decode_encode_bytes by exact bound_15.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End SeriesUpdateMessage.

  Module SystemStateMessage.

    (** This message format is used to notify the firms of the state changes of the system. This is a notification that applies to each Underlying group. Firms can use notifications as triggers in their system to ensure electronic synchronization of systems. *)
    Record t := {
      nanoseconds : N;
      to_m_version : list byte;
      session_id : N;
      system_status : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (nanoseconds record < 256 ^ N.of_nat 4)%N /\
      Datatypes.length (to_m_version record) = 8 /\
      (session_id record < 256 ^ N.of_nat 4)%N /\
      Datatypes.length (system_status record) = 1.

    Definition encode (record : t) : list byte :=
      encode_uint 4 (nanoseconds record) ++
      encode_bytes 8 (to_m_version record) ++
      encode_uint 4 (session_id record) ++
      encode_bytes 1 (system_status record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 4 bytes with
      | None => None
      | Some (nanoseconds_value, bytes) =>
          match decode_bytes 8 bytes with
          | None => None
          | Some (to_m_version_value, bytes) =>
              match decode_uint 4 bytes with
              | None => None
              | Some (session_id_value, bytes) =>
                  match decode_bytes 1 bytes with
                  | None => None
                  | Some (system_status_value, bytes) =>
                      Some ({| nanoseconds := nanoseconds_value; to_m_version := to_m_version_value; session_id := session_id_value; system_status := system_status_value |}, bytes)
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

  Module SimpleTopOfMarketBestBidOrOfferCompactFormatBidMessage.

    (** This is the message format that will be used to disseminate each side of the Sapphire Top of Market for options with low premiums and small aggregate Sapphire Best Bid or Offer (SBBO) size. "B" = Top of Market on Bid side. *)
    Record t := {
      nanoseconds : N;
      product_id : N;
      s_b_b_o_price_short : N;
      s_b_b_o_size_short : N;
      s_b_b_o_priority_customer_size_short : N;
      sbbo_condition : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (nanoseconds record < 256 ^ N.of_nat 4)%N /\
      (product_id record < 256 ^ N.of_nat 4)%N /\
      (s_b_b_o_price_short record < 256 ^ N.of_nat 2)%N /\
      (s_b_b_o_size_short record < 256 ^ N.of_nat 2)%N /\
      (s_b_b_o_priority_customer_size_short record < 256 ^ N.of_nat 2)%N /\
      Datatypes.length (sbbo_condition record) = 1.

    Definition encode (record : t) : list byte :=
      encode_uint 4 (nanoseconds record) ++
      encode_uint 4 (product_id record) ++
      encode_uint 2 (s_b_b_o_price_short record) ++
      encode_uint 2 (s_b_b_o_size_short record) ++
      encode_uint 2 (s_b_b_o_priority_customer_size_short record) ++
      encode_bytes 1 (sbbo_condition record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 4 bytes with
      | None => None
      | Some (nanoseconds_value, bytes) =>
          match decode_uint 4 bytes with
          | None => None
          | Some (product_id_value, bytes) =>
              match decode_uint 2 bytes with
              | None => None
              | Some (s_b_b_o_price_short_value, bytes) =>
                  match decode_uint 2 bytes with
                  | None => None
                  | Some (s_b_b_o_size_short_value, bytes) =>
                      match decode_uint 2 bytes with
                      | None => None
                      | Some (s_b_b_o_priority_customer_size_short_value, bytes) =>
                          match decode_bytes 1 bytes with
                          | None => None
                          | Some (sbbo_condition_value, bytes) =>
                              Some ({| nanoseconds := nanoseconds_value; product_id := product_id_value; s_b_b_o_price_short := s_b_b_o_price_short_value; s_b_b_o_size_short := s_b_b_o_size_short_value; s_b_b_o_priority_customer_size_short := s_b_b_o_priority_customer_size_short_value; sbbo_condition := sbbo_condition_value |}, bytes)
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

  End SimpleTopOfMarketBestBidOrOfferCompactFormatBidMessage.

  Module SimpleTopOfMarketBestBidOrOfferCompactFormatBidPriorityCustomerMessage.

    (** Simple Top of Market on Bid side with Priority Customer establishing new aggressive price. *)
    Record t := {
      nanoseconds : N;
      product_id : N;
      s_b_b_o_price_short : N;
      s_b_b_o_size_short : N;
      s_b_b_o_priority_customer_size_short : N;
      sbbo_condition : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (nanoseconds record < 256 ^ N.of_nat 4)%N /\
      (product_id record < 256 ^ N.of_nat 4)%N /\
      (s_b_b_o_price_short record < 256 ^ N.of_nat 2)%N /\
      (s_b_b_o_size_short record < 256 ^ N.of_nat 2)%N /\
      (s_b_b_o_priority_customer_size_short record < 256 ^ N.of_nat 2)%N /\
      Datatypes.length (sbbo_condition record) = 1.

    Definition encode (record : t) : list byte :=
      encode_uint 4 (nanoseconds record) ++
      encode_uint 4 (product_id record) ++
      encode_uint 2 (s_b_b_o_price_short record) ++
      encode_uint 2 (s_b_b_o_size_short record) ++
      encode_uint 2 (s_b_b_o_priority_customer_size_short record) ++
      encode_bytes 1 (sbbo_condition record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 4 bytes with
      | None => None
      | Some (nanoseconds_value, bytes) =>
          match decode_uint 4 bytes with
          | None => None
          | Some (product_id_value, bytes) =>
              match decode_uint 2 bytes with
              | None => None
              | Some (s_b_b_o_price_short_value, bytes) =>
                  match decode_uint 2 bytes with
                  | None => None
                  | Some (s_b_b_o_size_short_value, bytes) =>
                      match decode_uint 2 bytes with
                      | None => None
                      | Some (s_b_b_o_priority_customer_size_short_value, bytes) =>
                          match decode_bytes 1 bytes with
                          | None => None
                          | Some (sbbo_condition_value, bytes) =>
                              Some ({| nanoseconds := nanoseconds_value; product_id := product_id_value; s_b_b_o_price_short := s_b_b_o_price_short_value; s_b_b_o_size_short := s_b_b_o_size_short_value; s_b_b_o_priority_customer_size_short := s_b_b_o_priority_customer_size_short_value; sbbo_condition := sbbo_condition_value |}, bytes)
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

  End SimpleTopOfMarketBestBidOrOfferCompactFormatBidPriorityCustomerMessage.

  Module SimpleTopOfMarketBestBidOrOfferCompactFormatOfferMessage.

    (** This is the message format that will be used to disseminate each side of the Sapphire Top of Market for options with low premiums and small aggregate Sapphire Best Bid or Offer (SBBO) size. "O" = Top of Market on Offer side. *)
    Record t := {
      nanoseconds : N;
      product_id : N;
      s_b_b_o_price_short : N;
      s_b_b_o_size_short : N;
      s_b_b_o_priority_customer_size_short : N;
      sbbo_condition : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (nanoseconds record < 256 ^ N.of_nat 4)%N /\
      (product_id record < 256 ^ N.of_nat 4)%N /\
      (s_b_b_o_price_short record < 256 ^ N.of_nat 2)%N /\
      (s_b_b_o_size_short record < 256 ^ N.of_nat 2)%N /\
      (s_b_b_o_priority_customer_size_short record < 256 ^ N.of_nat 2)%N /\
      Datatypes.length (sbbo_condition record) = 1.

    Definition encode (record : t) : list byte :=
      encode_uint 4 (nanoseconds record) ++
      encode_uint 4 (product_id record) ++
      encode_uint 2 (s_b_b_o_price_short record) ++
      encode_uint 2 (s_b_b_o_size_short record) ++
      encode_uint 2 (s_b_b_o_priority_customer_size_short record) ++
      encode_bytes 1 (sbbo_condition record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 4 bytes with
      | None => None
      | Some (nanoseconds_value, bytes) =>
          match decode_uint 4 bytes with
          | None => None
          | Some (product_id_value, bytes) =>
              match decode_uint 2 bytes with
              | None => None
              | Some (s_b_b_o_price_short_value, bytes) =>
                  match decode_uint 2 bytes with
                  | None => None
                  | Some (s_b_b_o_size_short_value, bytes) =>
                      match decode_uint 2 bytes with
                      | None => None
                      | Some (s_b_b_o_priority_customer_size_short_value, bytes) =>
                          match decode_bytes 1 bytes with
                          | None => None
                          | Some (sbbo_condition_value, bytes) =>
                              Some ({| nanoseconds := nanoseconds_value; product_id := product_id_value; s_b_b_o_price_short := s_b_b_o_price_short_value; s_b_b_o_size_short := s_b_b_o_size_short_value; s_b_b_o_priority_customer_size_short := s_b_b_o_priority_customer_size_short_value; sbbo_condition := sbbo_condition_value |}, bytes)
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

  End SimpleTopOfMarketBestBidOrOfferCompactFormatOfferMessage.

  Module SimpleTopOfMarketBestBidOrOfferCompactFormatOfferPriorityCustomerMessage.

    (** Simple Top of Market on Offer side with Priority Customer establishing new aggressive price. *)
    Record t := {
      nanoseconds : N;
      product_id : N;
      s_b_b_o_price_short : N;
      s_b_b_o_size_short : N;
      s_b_b_o_priority_customer_size_short : N;
      sbbo_condition : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (nanoseconds record < 256 ^ N.of_nat 4)%N /\
      (product_id record < 256 ^ N.of_nat 4)%N /\
      (s_b_b_o_price_short record < 256 ^ N.of_nat 2)%N /\
      (s_b_b_o_size_short record < 256 ^ N.of_nat 2)%N /\
      (s_b_b_o_priority_customer_size_short record < 256 ^ N.of_nat 2)%N /\
      Datatypes.length (sbbo_condition record) = 1.

    Definition encode (record : t) : list byte :=
      encode_uint 4 (nanoseconds record) ++
      encode_uint 4 (product_id record) ++
      encode_uint 2 (s_b_b_o_price_short record) ++
      encode_uint 2 (s_b_b_o_size_short record) ++
      encode_uint 2 (s_b_b_o_priority_customer_size_short record) ++
      encode_bytes 1 (sbbo_condition record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 4 bytes with
      | None => None
      | Some (nanoseconds_value, bytes) =>
          match decode_uint 4 bytes with
          | None => None
          | Some (product_id_value, bytes) =>
              match decode_uint 2 bytes with
              | None => None
              | Some (s_b_b_o_price_short_value, bytes) =>
                  match decode_uint 2 bytes with
                  | None => None
                  | Some (s_b_b_o_size_short_value, bytes) =>
                      match decode_uint 2 bytes with
                      | None => None
                      | Some (s_b_b_o_priority_customer_size_short_value, bytes) =>
                          match decode_bytes 1 bytes with
                          | None => None
                          | Some (sbbo_condition_value, bytes) =>
                              Some ({| nanoseconds := nanoseconds_value; product_id := product_id_value; s_b_b_o_price_short := s_b_b_o_price_short_value; s_b_b_o_size_short := s_b_b_o_size_short_value; s_b_b_o_priority_customer_size_short := s_b_b_o_priority_customer_size_short_value; sbbo_condition := sbbo_condition_value |}, bytes)
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

  End SimpleTopOfMarketBestBidOrOfferCompactFormatOfferPriorityCustomerMessage.

  Module SimpleTopOfMarketBestBidOrOfferWideFormatBidMessage.

    (** This is the message format that will be used to disseminate Sapphire Top of Market for options with high premiums or large aggregate Sapphire Best Bid or Offer (SBBO) size. "W" = Simple Top of Market on Bid side. *)
    Record t := {
      nanoseconds : N;
      product_id : N;
      s_b_b_o_price_long : N;
      s_b_b_o_size_long : N;
      s_b_b_o_priority_customer_size_long : N;
      sbbo_condition : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (nanoseconds record < 256 ^ N.of_nat 4)%N /\
      (product_id record < 256 ^ N.of_nat 4)%N /\
      (s_b_b_o_price_long record < 256 ^ N.of_nat 4)%N /\
      (s_b_b_o_size_long record < 256 ^ N.of_nat 4)%N /\
      (s_b_b_o_priority_customer_size_long record < 256 ^ N.of_nat 4)%N /\
      Datatypes.length (sbbo_condition record) = 1.

    Definition encode (record : t) : list byte :=
      encode_uint 4 (nanoseconds record) ++
      encode_uint 4 (product_id record) ++
      encode_uint 4 (s_b_b_o_price_long record) ++
      encode_uint 4 (s_b_b_o_size_long record) ++
      encode_uint 4 (s_b_b_o_priority_customer_size_long record) ++
      encode_bytes 1 (sbbo_condition record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 4 bytes with
      | None => None
      | Some (nanoseconds_value, bytes) =>
          match decode_uint 4 bytes with
          | None => None
          | Some (product_id_value, bytes) =>
              match decode_uint 4 bytes with
              | None => None
              | Some (s_b_b_o_price_long_value, bytes) =>
                  match decode_uint 4 bytes with
                  | None => None
                  | Some (s_b_b_o_size_long_value, bytes) =>
                      match decode_uint 4 bytes with
                      | None => None
                      | Some (s_b_b_o_priority_customer_size_long_value, bytes) =>
                          match decode_bytes 1 bytes with
                          | None => None
                          | Some (sbbo_condition_value, bytes) =>
                              Some ({| nanoseconds := nanoseconds_value; product_id := product_id_value; s_b_b_o_price_long := s_b_b_o_price_long_value; s_b_b_o_size_long := s_b_b_o_size_long_value; s_b_b_o_priority_customer_size_long := s_b_b_o_priority_customer_size_long_value; sbbo_condition := sbbo_condition_value |}, bytes)
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
      rewrite decode_encode_uint by exact bound_3.
      rewrite decode_encode_uint by exact bound_4.
      rewrite decode_encode_bytes by exact bound_5.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End SimpleTopOfMarketBestBidOrOfferWideFormatBidMessage.

  Module SimpleTopOfMarketBestBidOrOfferWideFormatBidPriorityCustomerMessage.

    (** Simple Top of Market on Bid side with Priority Customer establishing new aggressive price. *)
    Record t := {
      nanoseconds : N;
      product_id : N;
      s_b_b_o_price_long : N;
      s_b_b_o_size_long : N;
      s_b_b_o_priority_customer_size_long : N;
      sbbo_condition : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (nanoseconds record < 256 ^ N.of_nat 4)%N /\
      (product_id record < 256 ^ N.of_nat 4)%N /\
      (s_b_b_o_price_long record < 256 ^ N.of_nat 4)%N /\
      (s_b_b_o_size_long record < 256 ^ N.of_nat 4)%N /\
      (s_b_b_o_priority_customer_size_long record < 256 ^ N.of_nat 4)%N /\
      Datatypes.length (sbbo_condition record) = 1.

    Definition encode (record : t) : list byte :=
      encode_uint 4 (nanoseconds record) ++
      encode_uint 4 (product_id record) ++
      encode_uint 4 (s_b_b_o_price_long record) ++
      encode_uint 4 (s_b_b_o_size_long record) ++
      encode_uint 4 (s_b_b_o_priority_customer_size_long record) ++
      encode_bytes 1 (sbbo_condition record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 4 bytes with
      | None => None
      | Some (nanoseconds_value, bytes) =>
          match decode_uint 4 bytes with
          | None => None
          | Some (product_id_value, bytes) =>
              match decode_uint 4 bytes with
              | None => None
              | Some (s_b_b_o_price_long_value, bytes) =>
                  match decode_uint 4 bytes with
                  | None => None
                  | Some (s_b_b_o_size_long_value, bytes) =>
                      match decode_uint 4 bytes with
                      | None => None
                      | Some (s_b_b_o_priority_customer_size_long_value, bytes) =>
                          match decode_bytes 1 bytes with
                          | None => None
                          | Some (sbbo_condition_value, bytes) =>
                              Some ({| nanoseconds := nanoseconds_value; product_id := product_id_value; s_b_b_o_price_long := s_b_b_o_price_long_value; s_b_b_o_size_long := s_b_b_o_size_long_value; s_b_b_o_priority_customer_size_long := s_b_b_o_priority_customer_size_long_value; sbbo_condition := sbbo_condition_value |}, bytes)
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
      rewrite decode_encode_uint by exact bound_3.
      rewrite decode_encode_uint by exact bound_4.
      rewrite decode_encode_bytes by exact bound_5.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End SimpleTopOfMarketBestBidOrOfferWideFormatBidPriorityCustomerMessage.

  Module SimpleTopOfMarketBestBidOrOfferWideFormatOfferMessage.

    (** This is the message format that will be used to disseminate Sapphire Top of Market for options with high premiums or large aggregate Sapphire Best Bid or Offer (SBBO) size. "A" = Simple Top of Market on Offer side. *)
    Record t := {
      nanoseconds : N;
      product_id : N;
      s_b_b_o_price_long : N;
      s_b_b_o_size_long : N;
      s_b_b_o_priority_customer_size_long : N;
      sbbo_condition : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (nanoseconds record < 256 ^ N.of_nat 4)%N /\
      (product_id record < 256 ^ N.of_nat 4)%N /\
      (s_b_b_o_price_long record < 256 ^ N.of_nat 4)%N /\
      (s_b_b_o_size_long record < 256 ^ N.of_nat 4)%N /\
      (s_b_b_o_priority_customer_size_long record < 256 ^ N.of_nat 4)%N /\
      Datatypes.length (sbbo_condition record) = 1.

    Definition encode (record : t) : list byte :=
      encode_uint 4 (nanoseconds record) ++
      encode_uint 4 (product_id record) ++
      encode_uint 4 (s_b_b_o_price_long record) ++
      encode_uint 4 (s_b_b_o_size_long record) ++
      encode_uint 4 (s_b_b_o_priority_customer_size_long record) ++
      encode_bytes 1 (sbbo_condition record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 4 bytes with
      | None => None
      | Some (nanoseconds_value, bytes) =>
          match decode_uint 4 bytes with
          | None => None
          | Some (product_id_value, bytes) =>
              match decode_uint 4 bytes with
              | None => None
              | Some (s_b_b_o_price_long_value, bytes) =>
                  match decode_uint 4 bytes with
                  | None => None
                  | Some (s_b_b_o_size_long_value, bytes) =>
                      match decode_uint 4 bytes with
                      | None => None
                      | Some (s_b_b_o_priority_customer_size_long_value, bytes) =>
                          match decode_bytes 1 bytes with
                          | None => None
                          | Some (sbbo_condition_value, bytes) =>
                              Some ({| nanoseconds := nanoseconds_value; product_id := product_id_value; s_b_b_o_price_long := s_b_b_o_price_long_value; s_b_b_o_size_long := s_b_b_o_size_long_value; s_b_b_o_priority_customer_size_long := s_b_b_o_priority_customer_size_long_value; sbbo_condition := sbbo_condition_value |}, bytes)
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
      rewrite decode_encode_uint by exact bound_3.
      rewrite decode_encode_uint by exact bound_4.
      rewrite decode_encode_bytes by exact bound_5.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End SimpleTopOfMarketBestBidOrOfferWideFormatOfferMessage.

  Module SimpleTopOfMarketBestBidOrOfferWideFormatOfferPriorityCustomerMessage.

    (** Simple Top of Market on Offer side with Priority Customer establishing new aggressive price. *)
    Record t := {
      nanoseconds : N;
      product_id : N;
      s_b_b_o_price_long : N;
      s_b_b_o_size_long : N;
      s_b_b_o_priority_customer_size_long : N;
      sbbo_condition : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (nanoseconds record < 256 ^ N.of_nat 4)%N /\
      (product_id record < 256 ^ N.of_nat 4)%N /\
      (s_b_b_o_price_long record < 256 ^ N.of_nat 4)%N /\
      (s_b_b_o_size_long record < 256 ^ N.of_nat 4)%N /\
      (s_b_b_o_priority_customer_size_long record < 256 ^ N.of_nat 4)%N /\
      Datatypes.length (sbbo_condition record) = 1.

    Definition encode (record : t) : list byte :=
      encode_uint 4 (nanoseconds record) ++
      encode_uint 4 (product_id record) ++
      encode_uint 4 (s_b_b_o_price_long record) ++
      encode_uint 4 (s_b_b_o_size_long record) ++
      encode_uint 4 (s_b_b_o_priority_customer_size_long record) ++
      encode_bytes 1 (sbbo_condition record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 4 bytes with
      | None => None
      | Some (nanoseconds_value, bytes) =>
          match decode_uint 4 bytes with
          | None => None
          | Some (product_id_value, bytes) =>
              match decode_uint 4 bytes with
              | None => None
              | Some (s_b_b_o_price_long_value, bytes) =>
                  match decode_uint 4 bytes with
                  | None => None
                  | Some (s_b_b_o_size_long_value, bytes) =>
                      match decode_uint 4 bytes with
                      | None => None
                      | Some (s_b_b_o_priority_customer_size_long_value, bytes) =>
                          match decode_bytes 1 bytes with
                          | None => None
                          | Some (sbbo_condition_value, bytes) =>
                              Some ({| nanoseconds := nanoseconds_value; product_id := product_id_value; s_b_b_o_price_long := s_b_b_o_price_long_value; s_b_b_o_size_long := s_b_b_o_size_long_value; s_b_b_o_priority_customer_size_long := s_b_b_o_priority_customer_size_long_value; sbbo_condition := sbbo_condition_value |}, bytes)
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
      rewrite decode_encode_uint by exact bound_3.
      rewrite decode_encode_uint by exact bound_4.
      rewrite decode_encode_bytes by exact bound_5.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End SimpleTopOfMarketBestBidOrOfferWideFormatOfferPriorityCustomerMessage.

  Module SimpleDoubleSidedTopOfMarketBestBidOrOfferCompactFormatMessage.

    (** This is the message format that will be used, in the refresh service and during trading hours, to disseminate both sides of the Sapphire Top of Market for options with low premiums and small aggregate Sapphire Best Bid or Offer (SBBO) size. *)
    Record t := {
      nanoseconds : N;
      product_id : N;
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
      (product_id record < 256 ^ N.of_nat 4)%N /\
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
      encode_uint 4 (product_id record) ++
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
          | Some (product_id_value, bytes) =>
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
                                              Some ({| nanoseconds := nanoseconds_value; product_id := product_id_value; bid_price_short := bid_price_short_value; bid_size_short := bid_size_short_value; bid_priority_customer_size_short := bid_priority_customer_size_short_value; bid_condition := bid_condition_value; offer_price_short := offer_price_short_value; offer_size_short := offer_size_short_value; offer_priority_customer_size_short := offer_priority_customer_size_short_value; offer_condition := offer_condition_value |}, bytes)
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

  End SimpleDoubleSidedTopOfMarketBestBidOrOfferCompactFormatMessage.

  Module SimpleDoubleSidedTopOfMarketBestBidOrOfferWideFormatMessage.

    (** This is the message format that will be used, in the refresh service and during trading hours, to disseminate both sides of the Sapphire Top of Market for options with high premiums or large aggregate Sapphire Best Bid or Offer (SBBO) sizes. *)
    Record t := {
      nanoseconds : N;
      product_id : N;
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
      (product_id record < 256 ^ N.of_nat 4)%N /\
      (bid_price_long record < 256 ^ N.of_nat 4)%N /\
      (bid_size_long record < 256 ^ N.of_nat 4)%N /\
      (bid_priority_customer_size_long record < 256 ^ N.of_nat 4)%N /\
      Datatypes.length (bid_condition record) = 1 /\
      (offer_price_long record < 256 ^ N.of_nat 4)%N /\
      (offer_size_long record < 256 ^ N.of_nat 4)%N /\
      (offer_priority_customer_size_long record < 256 ^ N.of_nat 4)%N /\
      Datatypes.length (offer_condition record) = 1.

    Definition encode (record : t) : list byte :=
      encode_uint 4 (nanoseconds record) ++
      encode_uint 4 (product_id record) ++
      encode_uint 4 (bid_price_long record) ++
      encode_uint 4 (bid_size_long record) ++
      encode_uint 4 (bid_priority_customer_size_long record) ++
      encode_bytes 1 (bid_condition record) ++
      encode_uint 4 (offer_price_long record) ++
      encode_uint 4 (offer_size_long record) ++
      encode_uint 4 (offer_priority_customer_size_long record) ++
      encode_bytes 1 (offer_condition record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 4 bytes with
      | None => None
      | Some (nanoseconds_value, bytes) =>
          match decode_uint 4 bytes with
          | None => None
          | Some (product_id_value, bytes) =>
              match decode_uint 4 bytes with
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
                              match decode_uint 4 bytes with
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
                                              Some ({| nanoseconds := nanoseconds_value; product_id := product_id_value; bid_price_long := bid_price_long_value; bid_size_long := bid_size_long_value; bid_priority_customer_size_long := bid_priority_customer_size_long_value; bid_condition := bid_condition_value; offer_price_long := offer_price_long_value; offer_size_long := offer_size_long_value; offer_priority_customer_size_long := offer_priority_customer_size_long_value; offer_condition := offer_condition_value |}, bytes)
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

    Theorem encode_length : forall record, Datatypes.length (encode record) = 34.
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

  End SimpleDoubleSidedTopOfMarketBestBidOrOfferWideFormatMessage.

  Module LastSaleMessage.

    (** This is the message format that will be used to disseminate Trades that are resulting from executions on Sapphire during the current trading session. *)
    Record t := {
      nanoseconds : N;
      product_id : N;
      trade_id : N;
      correction_number : N;
      reference_trade_id : N;
      reference_correction_number : N;
      trade_price : N;
      trade_size : N;
      trade_condition : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (nanoseconds record < 256 ^ N.of_nat 4)%N /\
      (product_id record < 256 ^ N.of_nat 4)%N /\
      (trade_id record < 256 ^ N.of_nat 4)%N /\
      (correction_number record < 256 ^ N.of_nat 1)%N /\
      (reference_trade_id record < 256 ^ N.of_nat 4)%N /\
      (reference_correction_number record < 256 ^ N.of_nat 1)%N /\
      (trade_price record < 256 ^ N.of_nat 4)%N /\
      (trade_size record < 256 ^ N.of_nat 4)%N /\
      Datatypes.length (trade_condition record) = 1.

    Definition encode (record : t) : list byte :=
      encode_uint 4 (nanoseconds record) ++
      encode_uint 4 (product_id record) ++
      encode_uint 4 (trade_id record) ++
      encode_uint 1 (correction_number record) ++
      encode_uint 4 (reference_trade_id record) ++
      encode_uint 1 (reference_correction_number record) ++
      encode_uint 4 (trade_price record) ++
      encode_uint 4 (trade_size record) ++
      encode_bytes 1 (trade_condition record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 4 bytes with
      | None => None
      | Some (nanoseconds_value, bytes) =>
          match decode_uint 4 bytes with
          | None => None
          | Some (product_id_value, bytes) =>
              match decode_uint 4 bytes with
              | None => None
              | Some (trade_id_value, bytes) =>
                  match decode_uint 1 bytes with
                  | None => None
                  | Some (correction_number_value, bytes) =>
                      match decode_uint 4 bytes with
                      | None => None
                      | Some (reference_trade_id_value, bytes) =>
                          match decode_uint 1 bytes with
                          | None => None
                          | Some (reference_correction_number_value, bytes) =>
                              match decode_uint 4 bytes with
                              | None => None
                              | Some (trade_price_value, bytes) =>
                                  match decode_uint 4 bytes with
                                  | None => None
                                  | Some (trade_size_value, bytes) =>
                                      match decode_bytes 1 bytes with
                                      | None => None
                                      | Some (trade_condition_value, bytes) =>
                                          Some ({| nanoseconds := nanoseconds_value; product_id := product_id_value; trade_id := trade_id_value; correction_number := correction_number_value; reference_trade_id := reference_trade_id_value; reference_correction_number := reference_correction_number_value; trade_price := trade_price_value; trade_size := trade_size_value; trade_condition := trade_condition_value |}, bytes)
                                      end
                                  end
                              end
                          end
                      end
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 27.
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
      rewrite decode_encode_uint by exact bound_6.
      rewrite decode_encode_uint by exact bound_7.
      rewrite decode_encode_bytes by exact bound_8.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End LastSaleMessage.

  Module TradeCancelMessage.

    (** This is the message format that will be used to disseminate canceled Trades that are resulting from Trade cancellations or corrections on Sapphire during the current trading session. *)
    Record t := {
      nanoseconds : N;
      product_id : N;
      trade_id : N;
      correction_number : N;
      trade_price : N;
      trade_size : N;
      trade_condition : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (nanoseconds record < 256 ^ N.of_nat 4)%N /\
      (product_id record < 256 ^ N.of_nat 4)%N /\
      (trade_id record < 256 ^ N.of_nat 4)%N /\
      (correction_number record < 256 ^ N.of_nat 1)%N /\
      (trade_price record < 256 ^ N.of_nat 4)%N /\
      (trade_size record < 256 ^ N.of_nat 4)%N /\
      Datatypes.length (trade_condition record) = 1.

    Definition encode (record : t) : list byte :=
      encode_uint 4 (nanoseconds record) ++
      encode_uint 4 (product_id record) ++
      encode_uint 4 (trade_id record) ++
      encode_uint 1 (correction_number record) ++
      encode_uint 4 (trade_price record) ++
      encode_uint 4 (trade_size record) ++
      encode_bytes 1 (trade_condition record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 4 bytes with
      | None => None
      | Some (nanoseconds_value, bytes) =>
          match decode_uint 4 bytes with
          | None => None
          | Some (product_id_value, bytes) =>
              match decode_uint 4 bytes with
              | None => None
              | Some (trade_id_value, bytes) =>
                  match decode_uint 1 bytes with
                  | None => None
                  | Some (correction_number_value, bytes) =>
                      match decode_uint 4 bytes with
                      | None => None
                      | Some (trade_price_value, bytes) =>
                          match decode_uint 4 bytes with
                          | None => None
                          | Some (trade_size_value, bytes) =>
                              match decode_bytes 1 bytes with
                              | None => None
                              | Some (trade_condition_value, bytes) =>
                                  Some ({| nanoseconds := nanoseconds_value; product_id := product_id_value; trade_id := trade_id_value; correction_number := correction_number_value; trade_price := trade_price_value; trade_size := trade_size_value; trade_condition := trade_condition_value |}, bytes)
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
      destruct bound as [bound_0 [bound_1 [bound_2 [bound_3 [bound_4 [bound_5 bound_6]]]]]].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_uint by exact bound_0.
      rewrite decode_encode_uint by exact bound_1.
      rewrite decode_encode_uint by exact bound_2.
      rewrite decode_encode_uint by exact bound_3.
      rewrite decode_encode_uint by exact bound_4.
      rewrite decode_encode_uint by exact bound_5.
      rewrite decode_encode_bytes by exact bound_6.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End TradeCancelMessage.

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

  Module EndOfRefreshNotificationMessage.

    (** Sent by MIAX Sapphire over the ToM Retransmission Interface (SesM Unsequenced Data Packet) when the refresh response is complete. *)
    Record t := {
      refresh_message_type : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (refresh_message_type record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 1 (refresh_message_type record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 1 bytes with
      | None => None
      | Some (refresh_message_type_value, bytes) =>
          Some ({| refresh_message_type := refresh_message_type_value |}, bytes)
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

  End EndOfRefreshNotificationMessage.

  Module LoginRequest.

    (** The SesM client must send a Login request packet immediately upon establishing a new TCP/IP socket connection to the server *)
    Record t := {
      sesm_version : list byte;
      username : list byte;
      computer_id : list byte;
      application_protocol : list byte;
      requested_trading_session_id : N;
      requested_sequence_number : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (sesm_version record) = 5 /\
      Datatypes.length (username record) = 5 /\
      Datatypes.length (computer_id record) = 8 /\
      Datatypes.length (application_protocol record) = 8 /\
      (requested_trading_session_id record < 256 ^ N.of_nat 1)%N /\
      (requested_sequence_number record < 256 ^ N.of_nat 8)%N.

    Definition encode (record : t) : list byte :=
      encode_bytes 5 (sesm_version record) ++
      encode_bytes 5 (username record) ++
      encode_bytes 8 (computer_id record) ++
      encode_bytes 8 (application_protocol record) ++
      encode_uint 1 (requested_trading_session_id record) ++
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
                      | Some (requested_trading_session_id_value, bytes) =>
                          match decode_uint 8 bytes with
                          | None => None
                          | Some (requested_sequence_number_value, bytes) =>
                              Some ({| sesm_version := sesm_version_value; username := username_value; computer_id := computer_id_value; application_protocol := application_protocol_value; requested_trading_session_id := requested_trading_session_id_value; requested_sequence_number := requested_sequence_number_value |}, bytes)
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
      number_of_matching_engines : N;
      login_status : list byte;
      trading_session_id : N;
      highest_sequence_number : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (number_of_matching_engines record < 256 ^ N.of_nat 1)%N /\
      Datatypes.length (login_status record) = 1 /\
      (trading_session_id record < 256 ^ N.of_nat 1)%N /\
      (highest_sequence_number record < 256 ^ N.of_nat 8)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 1 (number_of_matching_engines record) ++
      encode_bytes 1 (login_status record) ++
      encode_uint 1 (trading_session_id record) ++
      encode_uint 8 (highest_sequence_number record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 1 bytes with
      | None => None
      | Some (number_of_matching_engines_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (login_status_value, bytes) =>
              match decode_uint 1 bytes with
              | None => None
              | Some (trading_session_id_value, bytes) =>
                  match decode_uint 8 bytes with
                  | None => None
                  | Some (highest_sequence_number_value, bytes) =>
                      Some ({| number_of_matching_engines := number_of_matching_engines_value; login_status := login_status_value; trading_session_id := trading_session_id_value; highest_sequence_number := highest_sequence_number_value |}, bytes)
                  end
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

  End LoginResponse.

  Module SynchronizationComplete.

    (** The SesM server sends a Login response packet in response a Login request packet from the client *)
    Record t := {
      number_of_matching_engines : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (number_of_matching_engines record < 256 ^ N.of_nat 1)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 1 (number_of_matching_engines record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 1 bytes with
      | None => None
      | Some (number_of_matching_engines_value, bytes) =>
          Some ({| number_of_matching_engines := number_of_matching_engines_value |}, bytes)
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 1.
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

  End SynchronizationComplete.

  Module RetransmissionRequest.

    (** The SesM client uses this packet to request a retransmission server to retransmit a range of packets *)
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

End SapphireOptionsTopOfMarketV20Tcp.
