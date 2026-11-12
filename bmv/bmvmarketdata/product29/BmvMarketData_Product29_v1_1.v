From Stdlib Require Import List.
From Stdlib Require Import NArith.
From Stdlib Require Import Lia.
From Stdlib Require Import Strings.Byte.
From Omi Require Import Wire.

Import ListNotations.

(** * Bolsa Mexicana de Valores Bmv Market Data Product 29

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
      - a run counted by a field

    License: MIT No Attribution
  *)

Module BmvMarketDataProduct29V11.

  Module INTRAMulticastHeader.

    (** BMV INTRA Multicast Header *)
    Record t := {
      length_ : N;
      total_messages : N;
      market_data_group : N;
      session : N;
      sequence_number : N;
      datetime : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (length_ record < 256 ^ N.of_nat 2)%N /\
      (total_messages record < 256 ^ N.of_nat 1)%N /\
      (market_data_group record < 256 ^ N.of_nat 1)%N /\
      (session record < 256 ^ N.of_nat 1)%N /\
      (sequence_number record < 256 ^ N.of_nat 4)%N /\
      (datetime record < 256 ^ N.of_nat 8)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 2 (length_ record) ++
      encode_uint 1 (total_messages record) ++
      encode_uint 1 (market_data_group record) ++
      encode_uint 1 (session record) ++
      encode_uint 4 (sequence_number record) ++
      encode_uint 8 (datetime record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 2 bytes with
      | None => None
      | Some (length__value, bytes) =>
          match decode_uint 1 bytes with
          | None => None
          | Some (total_messages_value, bytes) =>
              match decode_uint 1 bytes with
              | None => None
              | Some (market_data_group_value, bytes) =>
                  match decode_uint 1 bytes with
                  | None => None
                  | Some (session_value, bytes) =>
                      match decode_uint 4 bytes with
                      | None => None
                      | Some (sequence_number_value, bytes) =>
                          match decode_uint 8 bytes with
                          | None => None
                          | Some (datetime_value, bytes) =>
                              Some ({| length_ := length__value; total_messages := total_messages_value; market_data_group := market_data_group_value; session := session_value; sequence_number := sequence_number_value; datetime := datetime_value |}, bytes)
                          end
                      end
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 17.
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

  End INTRAMulticastHeader.

  Module MessageHeader.

    (** Message length and message type *)
    Record t := {
      message_length : N;
      message_type : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (message_length record < 256 ^ N.of_nat 2)%N /\
      (message_type record < 256 ^ N.of_nat 1)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 2 (message_length record) ++
      encode_uint 1 (message_type record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 2 bytes with
      | None => None
      | Some (message_length_value, bytes) =>
          match decode_uint 1 bytes with
          | None => None
          | Some (message_type_value, bytes) =>
              Some ({| message_length := message_length_value; message_type := message_type_value |}, bytes)
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 3.
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

  End MessageHeader.

  Module LastQuoteMessage.

    (** Message sent by instrument when the best bid is modified in the electronic book by the Origin Exchange; denotes the side that is modified, the sale or the purchase. *)
    Record t := {
      instrument_number : N;
      origin : list byte;
      volume : N;
      price_rate : N;
      direction_of_the_bid : list byte;
      type_of_trading : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (instrument_number record < 256 ^ N.of_nat 4)%N /\
      Datatypes.length (origin record) = 1 /\
      (volume record < 256 ^ N.of_nat 8)%N /\
      (price_rate record < 256 ^ N.of_nat 8)%N /\
      Datatypes.length (direction_of_the_bid record) = 1 /\
      Datatypes.length (type_of_trading record) = 1.

    Definition encode (record : t) : list byte :=
      encode_uint 4 (instrument_number record) ++
      encode_bytes 1 (origin record) ++
      encode_uint 8 (volume record) ++
      encode_uint 8 (price_rate record) ++
      encode_bytes 1 (direction_of_the_bid record) ++
      encode_bytes 1 (type_of_trading record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 4 bytes with
      | None => None
      | Some (instrument_number_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (origin_value, bytes) =>
              match decode_uint 8 bytes with
              | None => None
              | Some (volume_value, bytes) =>
                  match decode_uint 8 bytes with
                  | None => None
                  | Some (price_rate_value, bytes) =>
                      match decode_bytes 1 bytes with
                      | None => None
                      | Some (direction_of_the_bid_value, bytes) =>
                          match decode_bytes 1 bytes with
                          | None => None
                          | Some (type_of_trading_value, bytes) =>
                              Some ({| instrument_number := instrument_number_value; origin := origin_value; volume := volume_value; price_rate := price_rate_value; direction_of_the_bid := direction_of_the_bid_value; type_of_trading := type_of_trading_value |}, bytes)
                          end
                      end
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 23.
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
      rewrite decode_encode_uint by exact bound_3.
      rewrite decode_encode_bytes by exact bound_4.
      rewrite decode_encode_bytes by exact bound_5.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End LastQuoteMessage.

  Module BenchmarkTradeMessage.

    (** Trading statistics by trade. *)
    Record t := {
      origin : list byte;
      average_volume : N;
      average_traded_value : N;
      market : list byte;
      sector : N;
      instrument_number : N;
      indices : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (origin record) = 1 /\
      (average_volume record < 256 ^ N.of_nat 8)%N /\
      (average_traded_value record < 256 ^ N.of_nat 8)%N /\
      Datatypes.length (market record) = 1 /\
      (sector record < 256 ^ N.of_nat 1)%N /\
      (instrument_number record < 256 ^ N.of_nat 4)%N /\
      Datatypes.length (indices record) = 2.

    Definition encode (record : t) : list byte :=
      encode_bytes 1 (origin record) ++
      encode_uint 8 (average_volume record) ++
      encode_uint 8 (average_traded_value record) ++
      encode_bytes 1 (market record) ++
      encode_uint 1 (sector record) ++
      encode_uint 4 (instrument_number record) ++
      encode_bytes 2 (indices record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 1 bytes with
      | None => None
      | Some (origin_value, bytes) =>
          match decode_uint 8 bytes with
          | None => None
          | Some (average_volume_value, bytes) =>
              match decode_uint 8 bytes with
              | None => None
              | Some (average_traded_value_value, bytes) =>
                  match decode_bytes 1 bytes with
                  | None => None
                  | Some (market_value, bytes) =>
                      match decode_uint 1 bytes with
                      | None => None
                      | Some (sector_value, bytes) =>
                          match decode_uint 4 bytes with
                          | None => None
                          | Some (instrument_number_value, bytes) =>
                              match decode_bytes 2 bytes with
                              | None => None
                              | Some (indices_value, bytes) =>
                                  Some ({| origin := origin_value; average_volume := average_volume_value; average_traded_value := average_traded_value_value; market := market_value; sector := sector_value; instrument_number := instrument_number_value; indices := indices_value |}, bytes)
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
      rewrite !length_app, !encode_bytes_length, !encode_uint_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 [bound_1 [bound_2 [bound_3 [bound_4 [bound_5 bound_6]]]]]].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_bytes by exact bound_0.
      rewrite decode_encode_uint by exact bound_1.
      rewrite decode_encode_uint by exact bound_2.
      rewrite decode_encode_bytes by exact bound_3.
      rewrite decode_encode_uint by exact bound_4.
      rewrite decode_encode_uint by exact bound_5.
      rewrite decode_encode_bytes by exact bound_6.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End BenchmarkTradeMessage.

  Module PriceLeaderboardMessage.

    (** Measures time proportion that a stock Exchange maintains the best bid and (or) ask throughout the session. *)
    Record t := {
      origin : list byte;
      t_best_bid : N;
      t_tie_best_bid : N;
      t_without_best_bid : N;
      t_best_ask : N;
      t_tie_best_ask : N;
      t_without_best_ask : N;
      market : list byte;
      sector : N;
      instrument_number : N;
      indices : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (origin record) = 1 /\
      (t_best_bid record < 256 ^ N.of_nat 4)%N /\
      (t_tie_best_bid record < 256 ^ N.of_nat 4)%N /\
      (t_without_best_bid record < 256 ^ N.of_nat 4)%N /\
      (t_best_ask record < 256 ^ N.of_nat 4)%N /\
      (t_tie_best_ask record < 256 ^ N.of_nat 4)%N /\
      (t_without_best_ask record < 256 ^ N.of_nat 4)%N /\
      Datatypes.length (market record) = 1 /\
      (sector record < 256 ^ N.of_nat 1)%N /\
      (instrument_number record < 256 ^ N.of_nat 4)%N /\
      Datatypes.length (indices record) = 2.

    Definition encode (record : t) : list byte :=
      encode_bytes 1 (origin record) ++
      encode_uint 4 (t_best_bid record) ++
      encode_uint 4 (t_tie_best_bid record) ++
      encode_uint 4 (t_without_best_bid record) ++
      encode_uint 4 (t_best_ask record) ++
      encode_uint 4 (t_tie_best_ask record) ++
      encode_uint 4 (t_without_best_ask record) ++
      encode_bytes 1 (market record) ++
      encode_uint 1 (sector record) ++
      encode_uint 4 (instrument_number record) ++
      encode_bytes 2 (indices record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 1 bytes with
      | None => None
      | Some (origin_value, bytes) =>
          match decode_uint 4 bytes with
          | None => None
          | Some (t_best_bid_value, bytes) =>
              match decode_uint 4 bytes with
              | None => None
              | Some (t_tie_best_bid_value, bytes) =>
                  match decode_uint 4 bytes with
                  | None => None
                  | Some (t_without_best_bid_value, bytes) =>
                      match decode_uint 4 bytes with
                      | None => None
                      | Some (t_best_ask_value, bytes) =>
                          match decode_uint 4 bytes with
                          | None => None
                          | Some (t_tie_best_ask_value, bytes) =>
                              match decode_uint 4 bytes with
                              | None => None
                              | Some (t_without_best_ask_value, bytes) =>
                                  match decode_bytes 1 bytes with
                                  | None => None
                                  | Some (market_value, bytes) =>
                                      match decode_uint 1 bytes with
                                      | None => None
                                      | Some (sector_value, bytes) =>
                                          match decode_uint 4 bytes with
                                          | None => None
                                          | Some (instrument_number_value, bytes) =>
                                              match decode_bytes 2 bytes with
                                              | None => None
                                              | Some (indices_value, bytes) =>
                                                  Some ({| origin := origin_value; t_best_bid := t_best_bid_value; t_tie_best_bid := t_tie_best_bid_value; t_without_best_bid := t_without_best_bid_value; t_best_ask := t_best_ask_value; t_tie_best_ask := t_tie_best_ask_value; t_without_best_ask := t_without_best_ask_value; market := market_value; sector := sector_value; instrument_number := instrument_number_value; indices := indices_value |}, bytes)
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

    Theorem encode_length : forall record, Datatypes.length (encode record) = 33.
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
      rewrite decode_encode_uint by exact bound_1.
      rewrite decode_encode_uint by exact bound_2.
      rewrite decode_encode_uint by exact bound_3.
      rewrite decode_encode_uint by exact bound_4.
      rewrite decode_encode_uint by exact bound_5.
      rewrite decode_encode_uint by exact bound_6.
      rewrite decode_encode_bytes by exact bound_7.
      rewrite decode_encode_uint by exact bound_8.
      rewrite decode_encode_uint by exact bound_9.
      rewrite decode_encode_bytes by exact bound_10.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End PriceLeaderboardMessage.

  Module TradingSniperMessage.

    (** Quotes composition analysis, full and first ten depth levels *)
    Record t := {
      origin : list byte;
      depth_bid : N;
      depth_ask : N;
      depth_bid_10_l : N;
      depth_ask_10_l : N;
      vwp_bid_10_l : N;
      vwp_ask_10_l : N;
      vwp_bid : N;
      vwp_ask : N;
      market : list byte;
      sector : N;
      instrument_number : N;
      indices : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (origin record) = 1 /\
      (depth_bid record < 256 ^ N.of_nat 8)%N /\
      (depth_ask record < 256 ^ N.of_nat 8)%N /\
      (depth_bid_10_l record < 256 ^ N.of_nat 8)%N /\
      (depth_ask_10_l record < 256 ^ N.of_nat 8)%N /\
      (vwp_bid_10_l record < 256 ^ N.of_nat 8)%N /\
      (vwp_ask_10_l record < 256 ^ N.of_nat 8)%N /\
      (vwp_bid record < 256 ^ N.of_nat 8)%N /\
      (vwp_ask record < 256 ^ N.of_nat 8)%N /\
      Datatypes.length (market record) = 1 /\
      (sector record < 256 ^ N.of_nat 1)%N /\
      (instrument_number record < 256 ^ N.of_nat 4)%N /\
      Datatypes.length (indices record) = 2.

    Definition encode (record : t) : list byte :=
      encode_bytes 1 (origin record) ++
      encode_uint 8 (depth_bid record) ++
      encode_uint 8 (depth_ask record) ++
      encode_uint 8 (depth_bid_10_l record) ++
      encode_uint 8 (depth_ask_10_l record) ++
      encode_uint 8 (vwp_bid_10_l record) ++
      encode_uint 8 (vwp_ask_10_l record) ++
      encode_uint 8 (vwp_bid record) ++
      encode_uint 8 (vwp_ask record) ++
      encode_bytes 1 (market record) ++
      encode_uint 1 (sector record) ++
      encode_uint 4 (instrument_number record) ++
      encode_bytes 2 (indices record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 1 bytes with
      | None => None
      | Some (origin_value, bytes) =>
          match decode_uint 8 bytes with
          | None => None
          | Some (depth_bid_value, bytes) =>
              match decode_uint 8 bytes with
              | None => None
              | Some (depth_ask_value, bytes) =>
                  match decode_uint 8 bytes with
                  | None => None
                  | Some (depth_bid_10_l_value, bytes) =>
                      match decode_uint 8 bytes with
                      | None => None
                      | Some (depth_ask_10_l_value, bytes) =>
                          match decode_uint 8 bytes with
                          | None => None
                          | Some (vwp_bid_10_l_value, bytes) =>
                              match decode_uint 8 bytes with
                              | None => None
                              | Some (vwp_ask_10_l_value, bytes) =>
                                  match decode_uint 8 bytes with
                                  | None => None
                                  | Some (vwp_bid_value, bytes) =>
                                      match decode_uint 8 bytes with
                                      | None => None
                                      | Some (vwp_ask_value, bytes) =>
                                          match decode_bytes 1 bytes with
                                          | None => None
                                          | Some (market_value, bytes) =>
                                              match decode_uint 1 bytes with
                                              | None => None
                                              | Some (sector_value, bytes) =>
                                                  match decode_uint 4 bytes with
                                                  | None => None
                                                  | Some (instrument_number_value, bytes) =>
                                                      match decode_bytes 2 bytes with
                                                      | None => None
                                                      | Some (indices_value, bytes) =>
                                                          Some ({| origin := origin_value; depth_bid := depth_bid_value; depth_ask := depth_ask_value; depth_bid_10_l := depth_bid_10_l_value; depth_ask_10_l := depth_ask_10_l_value; vwp_bid_10_l := vwp_bid_10_l_value; vwp_ask_10_l := vwp_ask_10_l_value; vwp_bid := vwp_bid_value; vwp_ask := vwp_ask_value; market := market_value; sector := sector_value; instrument_number := instrument_number_value; indices := indices_value |}, bytes)
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

    Theorem encode_length : forall record, Datatypes.length (encode record) = 73.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_bytes_length, !encode_uint_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 [bound_1 [bound_2 [bound_3 [bound_4 [bound_5 [bound_6 [bound_7 [bound_8 [bound_9 [bound_10 [bound_11 bound_12]]]]]]]]]]]].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_bytes by exact bound_0.
      rewrite decode_encode_uint by exact bound_1.
      rewrite decode_encode_uint by exact bound_2.
      rewrite decode_encode_uint by exact bound_3.
      rewrite decode_encode_uint by exact bound_4.
      rewrite decode_encode_uint by exact bound_5.
      rewrite decode_encode_uint by exact bound_6.
      rewrite decode_encode_uint by exact bound_7.
      rewrite decode_encode_uint by exact bound_8.
      rewrite decode_encode_bytes by exact bound_9.
      rewrite decode_encode_uint by exact bound_10.
      rewrite decode_encode_uint by exact bound_11.
      rewrite decode_encode_bytes by exact bound_12.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End TradingSniperMessage.

  Module DepthAtBestPricesMessage.

    (** Identify the deepest quotes depth for the national best bid and offer. *)
    Record t := {
      origin : list byte;
      instruments_bb : N;
      instruments_gv_bb : N;
      ratio_v_at_bb : N;
      instruments_ba : N;
      instruments_gv_ba : N;
      ratio_v_at_ba : N;
      market : list byte;
      sector : N;
      instrument_number : N;
      indices : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (origin record) = 1 /\
      (instruments_bb record < 256 ^ N.of_nat 2)%N /\
      (instruments_gv_bb record < 256 ^ N.of_nat 2)%N /\
      (ratio_v_at_bb record < 256 ^ N.of_nat 4)%N /\
      (instruments_ba record < 256 ^ N.of_nat 2)%N /\
      (instruments_gv_ba record < 256 ^ N.of_nat 2)%N /\
      (ratio_v_at_ba record < 256 ^ N.of_nat 4)%N /\
      Datatypes.length (market record) = 1 /\
      (sector record < 256 ^ N.of_nat 1)%N /\
      (instrument_number record < 256 ^ N.of_nat 4)%N /\
      Datatypes.length (indices record) = 2.

    Definition encode (record : t) : list byte :=
      encode_bytes 1 (origin record) ++
      encode_uint 2 (instruments_bb record) ++
      encode_uint 2 (instruments_gv_bb record) ++
      encode_uint 4 (ratio_v_at_bb record) ++
      encode_uint 2 (instruments_ba record) ++
      encode_uint 2 (instruments_gv_ba record) ++
      encode_uint 4 (ratio_v_at_ba record) ++
      encode_bytes 1 (market record) ++
      encode_uint 1 (sector record) ++
      encode_uint 4 (instrument_number record) ++
      encode_bytes 2 (indices record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 1 bytes with
      | None => None
      | Some (origin_value, bytes) =>
          match decode_uint 2 bytes with
          | None => None
          | Some (instruments_bb_value, bytes) =>
              match decode_uint 2 bytes with
              | None => None
              | Some (instruments_gv_bb_value, bytes) =>
                  match decode_uint 4 bytes with
                  | None => None
                  | Some (ratio_v_at_bb_value, bytes) =>
                      match decode_uint 2 bytes with
                      | None => None
                      | Some (instruments_ba_value, bytes) =>
                          match decode_uint 2 bytes with
                          | None => None
                          | Some (instruments_gv_ba_value, bytes) =>
                              match decode_uint 4 bytes with
                              | None => None
                              | Some (ratio_v_at_ba_value, bytes) =>
                                  match decode_bytes 1 bytes with
                                  | None => None
                                  | Some (market_value, bytes) =>
                                      match decode_uint 1 bytes with
                                      | None => None
                                      | Some (sector_value, bytes) =>
                                          match decode_uint 4 bytes with
                                          | None => None
                                          | Some (instrument_number_value, bytes) =>
                                              match decode_bytes 2 bytes with
                                              | None => None
                                              | Some (indices_value, bytes) =>
                                                  Some ({| origin := origin_value; instruments_bb := instruments_bb_value; instruments_gv_bb := instruments_gv_bb_value; ratio_v_at_bb := ratio_v_at_bb_value; instruments_ba := instruments_ba_value; instruments_gv_ba := instruments_gv_ba_value; ratio_v_at_ba := ratio_v_at_ba_value; market := market_value; sector := sector_value; instrument_number := instrument_number_value; indices := indices_value |}, bytes)
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

    Theorem encode_length : forall record, Datatypes.length (encode record) = 25.
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
      rewrite decode_encode_uint by exact bound_1.
      rewrite decode_encode_uint by exact bound_2.
      rewrite decode_encode_uint by exact bound_3.
      rewrite decode_encode_uint by exact bound_4.
      rewrite decode_encode_uint by exact bound_5.
      rewrite decode_encode_uint by exact bound_6.
      rewrite decode_encode_bytes by exact bound_7.
      rewrite decode_encode_uint by exact bound_8.
      rewrite decode_encode_uint by exact bound_9.
      rewrite decode_encode_bytes by exact bound_10.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End DepthAtBestPricesMessage.

End BmvMarketDataProduct29V11.
