From Stdlib Require Import List.
From Stdlib Require Import NArith.
From Stdlib Require Import Lia.
From Stdlib Require Import Strings.Byte.
From Omi Require Import Wire.

Import ListNotations.

(** * Bolsa Mexicana de Valores Bmv Market Data Product 33

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

Module BmvMarketDataProduct33V11.

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

  Module BigPictureMessage.

    (** Market share summary of the stock exchanges. *)
    Record t := {
      origin : list byte;
      trades : N;
      volume : N;
      traded_value : N;
      market_share_amount : N;
      market_share_trades : N;
      market : list byte;
      sector : N;
      instrument_number : N;
      indices : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (origin record) = 1 /\
      (trades record < 256 ^ N.of_nat 4)%N /\
      (volume record < 256 ^ N.of_nat 8)%N /\
      (traded_value record < 256 ^ N.of_nat 8)%N /\
      (market_share_amount record < 256 ^ N.of_nat 4)%N /\
      (market_share_trades record < 256 ^ N.of_nat 4)%N /\
      Datatypes.length (market record) = 1 /\
      (sector record < 256 ^ N.of_nat 1)%N /\
      (instrument_number record < 256 ^ N.of_nat 4)%N /\
      Datatypes.length (indices record) = 2.

    Definition encode (record : t) : list byte :=
      encode_bytes 1 (origin record) ++
      encode_uint 4 (trades record) ++
      encode_uint 8 (volume record) ++
      encode_uint 8 (traded_value record) ++
      encode_uint 4 (market_share_amount record) ++
      encode_uint 4 (market_share_trades record) ++
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
          | Some (trades_value, bytes) =>
              match decode_uint 8 bytes with
              | None => None
              | Some (volume_value, bytes) =>
                  match decode_uint 8 bytes with
                  | None => None
                  | Some (traded_value_value, bytes) =>
                      match decode_uint 4 bytes with
                      | None => None
                      | Some (market_share_amount_value, bytes) =>
                          match decode_uint 4 bytes with
                          | None => None
                          | Some (market_share_trades_value, bytes) =>
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
                                              Some ({| origin := origin_value; trades := trades_value; volume := volume_value; traded_value := traded_value_value; market_share_amount := market_share_amount_value; market_share_trades := market_share_trades_value; market := market_value; sector := sector_value; instrument_number := instrument_number_value; indices := indices_value |}, bytes)
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
      rewrite !length_app, !encode_bytes_length, !encode_uint_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 [bound_1 [bound_2 [bound_3 [bound_4 [bound_5 [bound_6 [bound_7 [bound_8 bound_9]]]]]]]]].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_bytes by exact bound_0.
      rewrite decode_encode_uint by exact bound_1.
      rewrite decode_encode_uint by exact bound_2.
      rewrite decode_encode_uint by exact bound_3.
      rewrite decode_encode_uint by exact bound_4.
      rewrite decode_encode_uint by exact bound_5.
      rewrite decode_encode_bytes by exact bound_6.
      rewrite decode_encode_uint by exact bound_7.
      rewrite decode_encode_uint by exact bound_8.
      rewrite decode_encode_bytes by exact bound_9.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End BigPictureMessage.

  Module EffectiveSpreadMessage.

    (** Transaction cost analysis benchmark. *)
    Record t := {
      origin : list byte;
      es_mxn : N;
      es_basis_points : N;
      es_mxn_bid : N;
      es_basis_points_bid : N;
      es_mxn_ask : N;
      es_basis_points_ask : N;
      market : list byte;
      sector : N;
      instrument_number : N;
      indices : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (origin record) = 1 /\
      (es_mxn record < 256 ^ N.of_nat 4)%N /\
      (es_basis_points record < 256 ^ N.of_nat 4)%N /\
      (es_mxn_bid record < 256 ^ N.of_nat 4)%N /\
      (es_basis_points_bid record < 256 ^ N.of_nat 4)%N /\
      (es_mxn_ask record < 256 ^ N.of_nat 4)%N /\
      (es_basis_points_ask record < 256 ^ N.of_nat 4)%N /\
      Datatypes.length (market record) = 1 /\
      (sector record < 256 ^ N.of_nat 1)%N /\
      (instrument_number record < 256 ^ N.of_nat 4)%N /\
      Datatypes.length (indices record) = 2.

    Definition encode (record : t) : list byte :=
      encode_bytes 1 (origin record) ++
      encode_uint 4 (es_mxn record) ++
      encode_uint 4 (es_basis_points record) ++
      encode_uint 4 (es_mxn_bid record) ++
      encode_uint 4 (es_basis_points_bid record) ++
      encode_uint 4 (es_mxn_ask record) ++
      encode_uint 4 (es_basis_points_ask record) ++
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
          | Some (es_mxn_value, bytes) =>
              match decode_uint 4 bytes with
              | None => None
              | Some (es_basis_points_value, bytes) =>
                  match decode_uint 4 bytes with
                  | None => None
                  | Some (es_mxn_bid_value, bytes) =>
                      match decode_uint 4 bytes with
                      | None => None
                      | Some (es_basis_points_bid_value, bytes) =>
                          match decode_uint 4 bytes with
                          | None => None
                          | Some (es_mxn_ask_value, bytes) =>
                              match decode_uint 4 bytes with
                              | None => None
                              | Some (es_basis_points_ask_value, bytes) =>
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
                                                  Some ({| origin := origin_value; es_mxn := es_mxn_value; es_basis_points := es_basis_points_value; es_mxn_bid := es_mxn_bid_value; es_basis_points_bid := es_basis_points_bid_value; es_mxn_ask := es_mxn_ask_value; es_basis_points_ask := es_basis_points_ask_value; market := market_value; sector := sector_value; instrument_number := instrument_number_value; indices := indices_value |}, bytes)
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

  End EffectiveSpreadMessage.

  Module SpreadQualityMessage.

    (** Quality of the quoted spread throughout the session. *)
    Record t := {
      origin : list byte;
      time_best_spread : N;
      time_tie_best_spread : N;
      time_without_best_spread : N;
      market : list byte;
      sector : N;
      instrument_number : N;
      indices : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (origin record) = 1 /\
      (time_best_spread record < 256 ^ N.of_nat 4)%N /\
      (time_tie_best_spread record < 256 ^ N.of_nat 4)%N /\
      (time_without_best_spread record < 256 ^ N.of_nat 4)%N /\
      Datatypes.length (market record) = 1 /\
      (sector record < 256 ^ N.of_nat 1)%N /\
      (instrument_number record < 256 ^ N.of_nat 4)%N /\
      Datatypes.length (indices record) = 2.

    Definition encode (record : t) : list byte :=
      encode_bytes 1 (origin record) ++
      encode_uint 4 (time_best_spread record) ++
      encode_uint 4 (time_tie_best_spread record) ++
      encode_uint 4 (time_without_best_spread record) ++
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
          | Some (time_best_spread_value, bytes) =>
              match decode_uint 4 bytes with
              | None => None
              | Some (time_tie_best_spread_value, bytes) =>
                  match decode_uint 4 bytes with
                  | None => None
                  | Some (time_without_best_spread_value, bytes) =>
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
                                      Some ({| origin := origin_value; time_best_spread := time_best_spread_value; time_tie_best_spread := time_tie_best_spread_value; time_without_best_spread := time_without_best_spread_value; market := market_value; sector := sector_value; instrument_number := instrument_number_value; indices := indices_value |}, bytes)
                                  end
                              end
                          end
                      end
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 21.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_bytes_length, !encode_uint_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 [bound_1 [bound_2 [bound_3 [bound_4 [bound_5 [bound_6 bound_7]]]]]]].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_bytes by exact bound_0.
      rewrite decode_encode_uint by exact bound_1.
      rewrite decode_encode_uint by exact bound_2.
      rewrite decode_encode_uint by exact bound_3.
      rewrite decode_encode_bytes by exact bound_4.
      rewrite decode_encode_uint by exact bound_5.
      rewrite decode_encode_uint by exact bound_6.
      rewrite decode_encode_bytes by exact bound_7.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End SpreadQualityMessage.

  Module SpreadMessage.

    (** Evolution of the simple spread throughout the session. *)
    Record t := {
      origin : list byte;
      spread_mxn : N;
      spread_basis_points : N;
      spread_average : N;
      number_of_spreads : N;
      market : list byte;
      sector : N;
      instrument_number : N;
      indices : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (origin record) = 1 /\
      (spread_mxn record < 256 ^ N.of_nat 4)%N /\
      (spread_basis_points record < 256 ^ N.of_nat 4)%N /\
      (spread_average record < 256 ^ N.of_nat 4)%N /\
      (number_of_spreads record < 256 ^ N.of_nat 4)%N /\
      Datatypes.length (market record) = 1 /\
      (sector record < 256 ^ N.of_nat 1)%N /\
      (instrument_number record < 256 ^ N.of_nat 4)%N /\
      Datatypes.length (indices record) = 2.

    Definition encode (record : t) : list byte :=
      encode_bytes 1 (origin record) ++
      encode_uint 4 (spread_mxn record) ++
      encode_uint 4 (spread_basis_points record) ++
      encode_uint 4 (spread_average record) ++
      encode_uint 4 (number_of_spreads record) ++
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
          | Some (spread_mxn_value, bytes) =>
              match decode_uint 4 bytes with
              | None => None
              | Some (spread_basis_points_value, bytes) =>
                  match decode_uint 4 bytes with
                  | None => None
                  | Some (spread_average_value, bytes) =>
                      match decode_uint 4 bytes with
                      | None => None
                      | Some (number_of_spreads_value, bytes) =>
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
                                          Some ({| origin := origin_value; spread_mxn := spread_mxn_value; spread_basis_points := spread_basis_points_value; spread_average := spread_average_value; number_of_spreads := number_of_spreads_value; market := market_value; sector := sector_value; instrument_number := instrument_number_value; indices := indices_value |}, bytes)
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
      destruct bound as [bound_0 [bound_1 [bound_2 [bound_3 [bound_4 [bound_5 [bound_6 [bound_7 bound_8]]]]]]]].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_bytes by exact bound_0.
      rewrite decode_encode_uint by exact bound_1.
      rewrite decode_encode_uint by exact bound_2.
      rewrite decode_encode_uint by exact bound_3.
      rewrite decode_encode_uint by exact bound_4.
      rewrite decode_encode_bytes by exact bound_5.
      rewrite decode_encode_uint by exact bound_6.
      rewrite decode_encode_uint by exact bound_7.
      rewrite decode_encode_bytes by exact bound_8.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End SpreadMessage.

End BmvMarketDataProduct33V11.
