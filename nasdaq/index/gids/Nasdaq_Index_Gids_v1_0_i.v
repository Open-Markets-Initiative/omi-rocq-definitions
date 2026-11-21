From Stdlib Require Import List.
From Stdlib Require Import NArith.
From Stdlib Require Import Lia.
From Stdlib Require Import Strings.Byte.
From Omi Require Import Wire.

Import ListNotations.

(** * National Association of Securities Dealers Automated Quotations (Nasdaq) Global Index Data Service

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
      - a length prefix framing what follows

    License: MIT No Attribution
  *)

Module NasdaqIndexGidsV10I.

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

  Module TimestampSecondsMessage.

    (** For every second during which there is at least one payload message, the seconds since the Unix epoch. *)
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

  End TimestampSecondsMessage.

  Module SystemEventMessage.

    (** Signals a data feed handler event. *)
    Record t := {
      nanoseconds : N;
      event_code : list byte;
      schedule : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (nanoseconds record < 256 ^ N.of_nat 4)%N /\
      Datatypes.length (event_code record) = 1 /\
      Datatypes.length (schedule record) = 3.

    Definition encode (record : t) : list byte :=
      encode_uint 4 (nanoseconds record) ++
      encode_bytes 1 (event_code record) ++
      encode_bytes 3 (schedule record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 4 bytes with
      | None => None
      | Some (nanoseconds_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (event_code_value, bytes) =>
              match decode_bytes 3 bytes with
              | None => None
              | Some (schedule_value, bytes) =>
                  Some ({| nanoseconds := nanoseconds_value; event_code := event_code_value; schedule := schedule_value |}, bytes)
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 8.
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

  End SystemEventMessage.

  Module IntradayIndexValueMessage.

    (** The Intraday Index Value for a given instrument, disseminated at a defined frequency and schedule. *)
    Record t := {
      nanoseconds : N;
      financial_product_type : list byte;
      brand : list byte;
      series : list byte;
      instrument_id : list byte;
      tick_value : N;
      tick_direction : list byte;
      currency : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (nanoseconds record < 256 ^ N.of_nat 4)%N /\
      Datatypes.length (financial_product_type record) = 1 /\
      Datatypes.length (brand record) = 2 /\
      Datatypes.length (series record) = 3 /\
      Datatypes.length (instrument_id record) = 18 /\
      (tick_value record < 256 ^ N.of_nat 8)%N /\
      Datatypes.length (tick_direction record) = 1 /\
      Datatypes.length (currency record) = 3.

    Definition encode (record : t) : list byte :=
      encode_uint 4 (nanoseconds record) ++
      encode_bytes 1 (financial_product_type record) ++
      encode_bytes 2 (brand record) ++
      encode_bytes 3 (series record) ++
      encode_bytes 18 (instrument_id record) ++
      encode_uint 8 (tick_value record) ++
      encode_bytes 1 (tick_direction record) ++
      encode_bytes 3 (currency record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 4 bytes with
      | None => None
      | Some (nanoseconds_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (financial_product_type_value, bytes) =>
              match decode_bytes 2 bytes with
              | None => None
              | Some (brand_value, bytes) =>
                  match decode_bytes 3 bytes with
                  | None => None
                  | Some (series_value, bytes) =>
                      match decode_bytes 18 bytes with
                      | None => None
                      | Some (instrument_id_value, bytes) =>
                          match decode_uint 8 bytes with
                          | None => None
                          | Some (tick_value_value, bytes) =>
                              match decode_bytes 1 bytes with
                              | None => None
                              | Some (tick_direction_value, bytes) =>
                                  match decode_bytes 3 bytes with
                                  | None => None
                                  | Some (currency_value, bytes) =>
                                      Some ({| nanoseconds := nanoseconds_value; financial_product_type := financial_product_type_value; brand := brand_value; series := series_value; instrument_id := instrument_id_value; tick_value := tick_value_value; tick_direction := tick_direction_value; currency := currency_value |}, bytes)
                                  end
                              end
                          end
                      end
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 40.
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
      rewrite decode_encode_bytes by exact bound_2.
      rewrite decode_encode_bytes by exact bound_3.
      rewrite decode_encode_bytes by exact bound_4.
      rewrite decode_encode_uint by exact bound_5.
      rewrite decode_encode_bytes by exact bound_6.
      rewrite decode_encode_bytes by exact bound_7.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End IntradayIndexValueMessage.

  Module SettlementValueMessage.

    (** Sends the official settlement price and settlement session used to settle cash derivatives on financial products when they expire. *)
    Record t := {
      nanoseconds : N;
      financial_product_type : list byte;
      brand : list byte;
      series : list byte;
      instrument_id : list byte;
      settlement_value : N;
      settlement_type : list byte;
      currency : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (nanoseconds record < 256 ^ N.of_nat 4)%N /\
      Datatypes.length (financial_product_type record) = 1 /\
      Datatypes.length (brand record) = 2 /\
      Datatypes.length (series record) = 3 /\
      Datatypes.length (instrument_id record) = 18 /\
      (settlement_value record < 256 ^ N.of_nat 8)%N /\
      Datatypes.length (settlement_type record) = 1 /\
      Datatypes.length (currency record) = 3.

    Definition encode (record : t) : list byte :=
      encode_uint 4 (nanoseconds record) ++
      encode_bytes 1 (financial_product_type record) ++
      encode_bytes 2 (brand record) ++
      encode_bytes 3 (series record) ++
      encode_bytes 18 (instrument_id record) ++
      encode_uint 8 (settlement_value record) ++
      encode_bytes 1 (settlement_type record) ++
      encode_bytes 3 (currency record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 4 bytes with
      | None => None
      | Some (nanoseconds_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (financial_product_type_value, bytes) =>
              match decode_bytes 2 bytes with
              | None => None
              | Some (brand_value, bytes) =>
                  match decode_bytes 3 bytes with
                  | None => None
                  | Some (series_value, bytes) =>
                      match decode_bytes 18 bytes with
                      | None => None
                      | Some (instrument_id_value, bytes) =>
                          match decode_uint 8 bytes with
                          | None => None
                          | Some (settlement_value_value, bytes) =>
                              match decode_bytes 1 bytes with
                              | None => None
                              | Some (settlement_type_value, bytes) =>
                                  match decode_bytes 3 bytes with
                                  | None => None
                                  | Some (currency_value, bytes) =>
                                      Some ({| nanoseconds := nanoseconds_value; financial_product_type := financial_product_type_value; brand := brand_value; series := series_value; instrument_id := instrument_id_value; settlement_value := settlement_value_value; settlement_type := settlement_type_value; currency := currency_value |}, bytes)
                                  end
                              end
                          end
                      end
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 40.
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
      rewrite decode_encode_bytes by exact bound_2.
      rewrite decode_encode_bytes by exact bound_3.
      rewrite decode_encode_bytes by exact bound_4.
      rewrite decode_encode_uint by exact bound_5.
      rewrite decode_encode_bytes by exact bound_6.
      rewrite decode_encode_bytes by exact bound_7.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End SettlementValueMessage.

  Module EquitiesSummaryMessage.

    (** Relays the summary of the current trading day's activity for an equity index. *)
    Record t := {
      nanoseconds : N;
      financial_product_type : list byte;
      brand : list byte;
      series : list byte;
      instrument_id : list byte;
      summary_type : list byte;
      sod_value : N;
      high : N;
      low : N;
      eod_value : N;
      net_change : N;
      effective_date : N;
      currency : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (nanoseconds record < 256 ^ N.of_nat 4)%N /\
      Datatypes.length (financial_product_type record) = 1 /\
      Datatypes.length (brand record) = 2 /\
      Datatypes.length (series record) = 3 /\
      Datatypes.length (instrument_id record) = 18 /\
      Datatypes.length (summary_type record) = 3 /\
      (sod_value record < 256 ^ N.of_nat 8)%N /\
      (high record < 256 ^ N.of_nat 8)%N /\
      (low record < 256 ^ N.of_nat 8)%N /\
      (eod_value record < 256 ^ N.of_nat 8)%N /\
      (net_change record < 256 ^ N.of_nat 8)%N /\
      (effective_date record < 256 ^ N.of_nat 4)%N /\
      Datatypes.length (currency record) = 3.

    Definition encode (record : t) : list byte :=
      encode_uint 4 (nanoseconds record) ++
      encode_bytes 1 (financial_product_type record) ++
      encode_bytes 2 (brand record) ++
      encode_bytes 3 (series record) ++
      encode_bytes 18 (instrument_id record) ++
      encode_bytes 3 (summary_type record) ++
      encode_uint 8 (sod_value record) ++
      encode_uint 8 (high record) ++
      encode_uint 8 (low record) ++
      encode_uint 8 (eod_value record) ++
      encode_uint 8 (net_change record) ++
      encode_uint 4 (effective_date record) ++
      encode_bytes 3 (currency record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 4 bytes with
      | None => None
      | Some (nanoseconds_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (financial_product_type_value, bytes) =>
              match decode_bytes 2 bytes with
              | None => None
              | Some (brand_value, bytes) =>
                  match decode_bytes 3 bytes with
                  | None => None
                  | Some (series_value, bytes) =>
                      match decode_bytes 18 bytes with
                      | None => None
                      | Some (instrument_id_value, bytes) =>
                          match decode_bytes 3 bytes with
                          | None => None
                          | Some (summary_type_value, bytes) =>
                              match decode_uint 8 bytes with
                              | None => None
                              | Some (sod_value_value, bytes) =>
                                  match decode_uint 8 bytes with
                                  | None => None
                                  | Some (high_value, bytes) =>
                                      match decode_uint 8 bytes with
                                      | None => None
                                      | Some (low_value, bytes) =>
                                          match decode_uint 8 bytes with
                                          | None => None
                                          | Some (eod_value_value, bytes) =>
                                              match decode_uint 8 bytes with
                                              | None => None
                                              | Some (net_change_value, bytes) =>
                                                  match decode_uint 4 bytes with
                                                  | None => None
                                                  | Some (effective_date_value, bytes) =>
                                                      match decode_bytes 3 bytes with
                                                      | None => None
                                                      | Some (currency_value, bytes) =>
                                                          Some ({| nanoseconds := nanoseconds_value; financial_product_type := financial_product_type_value; brand := brand_value; series := series_value; instrument_id := instrument_id_value; summary_type := summary_type_value; sod_value := sod_value_value; high := high_value; low := low_value; eod_value := eod_value_value; net_change := net_change_value; effective_date := effective_date_value; currency := currency_value |}, bytes)
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

    Theorem encode_length : forall record, Datatypes.length (encode record) = 78.
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
      rewrite decode_encode_bytes by exact bound_12.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End EquitiesSummaryMessage.

  Module FixedIncomeSummaryMessage.

    (** Relays the summary of the current trading day's activity for a fixed income index. *)
    Record t := {
      nanoseconds : N;
      financial_product_type : list byte;
      brand : list byte;
      series : list byte;
      instrument_id : list byte;
      summary_type : list byte;
      sod_value : N;
      high : N;
      low : N;
      eod_value : N;
      net_change : N;
      effective_date : N;
      yield : N;
      duration : N;
      coupon : N;
      currency : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (nanoseconds record < 256 ^ N.of_nat 4)%N /\
      Datatypes.length (financial_product_type record) = 1 /\
      Datatypes.length (brand record) = 2 /\
      Datatypes.length (series record) = 3 /\
      Datatypes.length (instrument_id record) = 18 /\
      Datatypes.length (summary_type record) = 3 /\
      (sod_value record < 256 ^ N.of_nat 8)%N /\
      (high record < 256 ^ N.of_nat 8)%N /\
      (low record < 256 ^ N.of_nat 8)%N /\
      (eod_value record < 256 ^ N.of_nat 8)%N /\
      (net_change record < 256 ^ N.of_nat 8)%N /\
      (effective_date record < 256 ^ N.of_nat 4)%N /\
      (yield record < 256 ^ N.of_nat 8)%N /\
      (duration record < 256 ^ N.of_nat 8)%N /\
      (coupon record < 256 ^ N.of_nat 8)%N /\
      Datatypes.length (currency record) = 3.

    Definition encode (record : t) : list byte :=
      encode_uint 4 (nanoseconds record) ++
      encode_bytes 1 (financial_product_type record) ++
      encode_bytes 2 (brand record) ++
      encode_bytes 3 (series record) ++
      encode_bytes 18 (instrument_id record) ++
      encode_bytes 3 (summary_type record) ++
      encode_uint 8 (sod_value record) ++
      encode_uint 8 (high record) ++
      encode_uint 8 (low record) ++
      encode_uint 8 (eod_value record) ++
      encode_uint 8 (net_change record) ++
      encode_uint 4 (effective_date record) ++
      encode_uint 8 (yield record) ++
      encode_uint 8 (duration record) ++
      encode_uint 8 (coupon record) ++
      encode_bytes 3 (currency record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 4 bytes with
      | None => None
      | Some (nanoseconds_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (financial_product_type_value, bytes) =>
              match decode_bytes 2 bytes with
              | None => None
              | Some (brand_value, bytes) =>
                  match decode_bytes 3 bytes with
                  | None => None
                  | Some (series_value, bytes) =>
                      match decode_bytes 18 bytes with
                      | None => None
                      | Some (instrument_id_value, bytes) =>
                          match decode_bytes 3 bytes with
                          | None => None
                          | Some (summary_type_value, bytes) =>
                              match decode_uint 8 bytes with
                              | None => None
                              | Some (sod_value_value, bytes) =>
                                  match decode_uint 8 bytes with
                                  | None => None
                                  | Some (high_value, bytes) =>
                                      match decode_uint 8 bytes with
                                      | None => None
                                      | Some (low_value, bytes) =>
                                          match decode_uint 8 bytes with
                                          | None => None
                                          | Some (eod_value_value, bytes) =>
                                              match decode_uint 8 bytes with
                                              | None => None
                                              | Some (net_change_value, bytes) =>
                                                  match decode_uint 4 bytes with
                                                  | None => None
                                                  | Some (effective_date_value, bytes) =>
                                                      match decode_uint 8 bytes with
                                                      | None => None
                                                      | Some (yield_value, bytes) =>
                                                          match decode_uint 8 bytes with
                                                          | None => None
                                                          | Some (duration_value, bytes) =>
                                                              match decode_uint 8 bytes with
                                                              | None => None
                                                              | Some (coupon_value, bytes) =>
                                                                  match decode_bytes 3 bytes with
                                                                  | None => None
                                                                  | Some (currency_value, bytes) =>
                                                                      Some ({| nanoseconds := nanoseconds_value; financial_product_type := financial_product_type_value; brand := brand_value; series := series_value; instrument_id := instrument_id_value; summary_type := summary_type_value; sod_value := sod_value_value; high := high_value; low := low_value; eod_value := eod_value_value; net_change := net_change_value; effective_date := effective_date_value; yield := yield_value; duration := duration_value; coupon := coupon_value; currency := currency_value |}, bytes)
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

    Theorem encode_length : forall record, Datatypes.length (encode record) = 102.
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
      rewrite decode_encode_bytes by exact bound_1.
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
      rewrite decode_encode_uint by exact bound_13.
      rewrite decode_encode_uint by exact bound_14.
      rewrite decode_encode_bytes by exact bound_15.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End FixedIncomeSummaryMessage.

  Module CommoditySummaryMessage.

    (** Relays the summary of the current trading day's activity for a commodity index. *)
    Record t := {
      nanoseconds : N;
      financial_product_type : list byte;
      brand : list byte;
      series : list byte;
      instrument_id : list byte;
      summary_type : list byte;
      sod_value : N;
      high : N;
      low : N;
      eod_value : N;
      net_change : N;
      effective_date : N;
      currency : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (nanoseconds record < 256 ^ N.of_nat 4)%N /\
      Datatypes.length (financial_product_type record) = 1 /\
      Datatypes.length (brand record) = 2 /\
      Datatypes.length (series record) = 3 /\
      Datatypes.length (instrument_id record) = 18 /\
      Datatypes.length (summary_type record) = 3 /\
      (sod_value record < 256 ^ N.of_nat 8)%N /\
      (high record < 256 ^ N.of_nat 8)%N /\
      (low record < 256 ^ N.of_nat 8)%N /\
      (eod_value record < 256 ^ N.of_nat 8)%N /\
      (net_change record < 256 ^ N.of_nat 8)%N /\
      (effective_date record < 256 ^ N.of_nat 4)%N /\
      Datatypes.length (currency record) = 3.

    Definition encode (record : t) : list byte :=
      encode_uint 4 (nanoseconds record) ++
      encode_bytes 1 (financial_product_type record) ++
      encode_bytes 2 (brand record) ++
      encode_bytes 3 (series record) ++
      encode_bytes 18 (instrument_id record) ++
      encode_bytes 3 (summary_type record) ++
      encode_uint 8 (sod_value record) ++
      encode_uint 8 (high record) ++
      encode_uint 8 (low record) ++
      encode_uint 8 (eod_value record) ++
      encode_uint 8 (net_change record) ++
      encode_uint 4 (effective_date record) ++
      encode_bytes 3 (currency record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 4 bytes with
      | None => None
      | Some (nanoseconds_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (financial_product_type_value, bytes) =>
              match decode_bytes 2 bytes with
              | None => None
              | Some (brand_value, bytes) =>
                  match decode_bytes 3 bytes with
                  | None => None
                  | Some (series_value, bytes) =>
                      match decode_bytes 18 bytes with
                      | None => None
                      | Some (instrument_id_value, bytes) =>
                          match decode_bytes 3 bytes with
                          | None => None
                          | Some (summary_type_value, bytes) =>
                              match decode_uint 8 bytes with
                              | None => None
                              | Some (sod_value_value, bytes) =>
                                  match decode_uint 8 bytes with
                                  | None => None
                                  | Some (high_value, bytes) =>
                                      match decode_uint 8 bytes with
                                      | None => None
                                      | Some (low_value, bytes) =>
                                          match decode_uint 8 bytes with
                                          | None => None
                                          | Some (eod_value_value, bytes) =>
                                              match decode_uint 8 bytes with
                                              | None => None
                                              | Some (net_change_value, bytes) =>
                                                  match decode_uint 4 bytes with
                                                  | None => None
                                                  | Some (effective_date_value, bytes) =>
                                                      match decode_bytes 3 bytes with
                                                      | None => None
                                                      | Some (currency_value, bytes) =>
                                                          Some ({| nanoseconds := nanoseconds_value; financial_product_type := financial_product_type_value; brand := brand_value; series := series_value; instrument_id := instrument_id_value; summary_type := summary_type_value; sod_value := sod_value_value; high := high_value; low := low_value; eod_value := eod_value_value; net_change := net_change_value; effective_date := effective_date_value; currency := currency_value |}, bytes)
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

    Theorem encode_length : forall record, Datatypes.length (encode record) = 78.
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
      rewrite decode_encode_bytes by exact bound_12.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End CommoditySummaryMessage.

  Module EtpIntraDayValuationMessage.

    (** Disseminates the Intraday Portfolio Value (IPV) of an ETF or the Intra-Day Indicative Value (IIV) of an ETMF. *)
    Record t := {
      nanoseconds : N;
      financial_product_type : list byte;
      ipv_symbol : list byte;
      ipv_value : N;
      currency : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (nanoseconds record < 256 ^ N.of_nat 4)%N /\
      Datatypes.length (financial_product_type record) = 1 /\
      Datatypes.length (ipv_symbol record) = 18 /\
      (ipv_value record < 256 ^ N.of_nat 8)%N /\
      Datatypes.length (currency record) = 3.

    Definition encode (record : t) : list byte :=
      encode_uint 4 (nanoseconds record) ++
      encode_bytes 1 (financial_product_type record) ++
      encode_bytes 18 (ipv_symbol record) ++
      encode_uint 8 (ipv_value record) ++
      encode_bytes 3 (currency record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 4 bytes with
      | None => None
      | Some (nanoseconds_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (financial_product_type_value, bytes) =>
              match decode_bytes 18 bytes with
              | None => None
              | Some (ipv_symbol_value, bytes) =>
                  match decode_uint 8 bytes with
                  | None => None
                  | Some (ipv_value_value, bytes) =>
                      match decode_bytes 3 bytes with
                      | None => None
                      | Some (currency_value, bytes) =>
                          Some ({| nanoseconds := nanoseconds_value; financial_product_type := financial_product_type_value; ipv_symbol := ipv_symbol_value; ipv_value := ipv_value_value; currency := currency_value |}, bytes)
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
      destruct bound as [bound_0 [bound_1 [bound_2 [bound_3 bound_4]]]].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_uint by exact bound_0.
      rewrite decode_encode_bytes by exact bound_1.
      rewrite decode_encode_bytes by exact bound_2.
      rewrite decode_encode_uint by exact bound_3.
      rewrite decode_encode_bytes by exact bound_4.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End EtpIntraDayValuationMessage.

  Module EtpSummaryMessage.

    (** Relays the summary of the current trading day's IPV activity for an ETF or the IIV activity for an ETMF. *)
    Record t := {
      nanoseconds : N;
      financial_product_type : list byte;
      summary_type : list byte;
      ipv_or_iiv_symbol : list byte;
      sod_value : N;
      high : N;
      low : N;
      eod_value : N;
      net_change : N;
      effective_date : N;
      currency : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (nanoseconds record < 256 ^ N.of_nat 4)%N /\
      Datatypes.length (financial_product_type record) = 1 /\
      Datatypes.length (summary_type record) = 3 /\
      Datatypes.length (ipv_or_iiv_symbol record) = 18 /\
      (sod_value record < 256 ^ N.of_nat 8)%N /\
      (high record < 256 ^ N.of_nat 8)%N /\
      (low record < 256 ^ N.of_nat 8)%N /\
      (eod_value record < 256 ^ N.of_nat 8)%N /\
      (net_change record < 256 ^ N.of_nat 8)%N /\
      (effective_date record < 256 ^ N.of_nat 4)%N /\
      Datatypes.length (currency record) = 3.

    Definition encode (record : t) : list byte :=
      encode_uint 4 (nanoseconds record) ++
      encode_bytes 1 (financial_product_type record) ++
      encode_bytes 3 (summary_type record) ++
      encode_bytes 18 (ipv_or_iiv_symbol record) ++
      encode_uint 8 (sod_value record) ++
      encode_uint 8 (high record) ++
      encode_uint 8 (low record) ++
      encode_uint 8 (eod_value record) ++
      encode_uint 8 (net_change record) ++
      encode_uint 4 (effective_date record) ++
      encode_bytes 3 (currency record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 4 bytes with
      | None => None
      | Some (nanoseconds_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (financial_product_type_value, bytes) =>
              match decode_bytes 3 bytes with
              | None => None
              | Some (summary_type_value, bytes) =>
                  match decode_bytes 18 bytes with
                  | None => None
                  | Some (ipv_or_iiv_symbol_value, bytes) =>
                      match decode_uint 8 bytes with
                      | None => None
                      | Some (sod_value_value, bytes) =>
                          match decode_uint 8 bytes with
                          | None => None
                          | Some (high_value, bytes) =>
                              match decode_uint 8 bytes with
                              | None => None
                              | Some (low_value, bytes) =>
                                  match decode_uint 8 bytes with
                                  | None => None
                                  | Some (eod_value_value, bytes) =>
                                      match decode_uint 8 bytes with
                                      | None => None
                                      | Some (net_change_value, bytes) =>
                                          match decode_uint 4 bytes with
                                          | None => None
                                          | Some (effective_date_value, bytes) =>
                                              match decode_bytes 3 bytes with
                                              | None => None
                                              | Some (currency_value, bytes) =>
                                                  Some ({| nanoseconds := nanoseconds_value; financial_product_type := financial_product_type_value; summary_type := summary_type_value; ipv_or_iiv_symbol := ipv_or_iiv_symbol_value; sod_value := sod_value_value; high := high_value; low := low_value; eod_value := eod_value_value; net_change := net_change_value; effective_date := effective_date_value; currency := currency_value |}, bytes)
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

    Theorem encode_length : forall record, Datatypes.length (encode record) = 73.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_uint_length, !encode_bytes_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 [bound_1 [bound_2 [bound_3 [bound_4 [bound_5 [bound_6 [bound_7 [bound_8 [bound_9 bound_10]]]]]]]]]].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_uint by exact bound_0.
      rewrite decode_encode_bytes by exact bound_1.
      rewrite decode_encode_bytes by exact bound_2.
      rewrite decode_encode_bytes by exact bound_3.
      rewrite decode_encode_uint by exact bound_4.
      rewrite decode_encode_uint by exact bound_5.
      rewrite decode_encode_uint by exact bound_6.
      rewrite decode_encode_uint by exact bound_7.
      rewrite decode_encode_uint by exact bound_8.
      rewrite decode_encode_uint by exact bound_9.
      rewrite decode_encode_bytes by exact bound_10.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End EtpSummaryMessage.

End NasdaqIndexGidsV10I.
