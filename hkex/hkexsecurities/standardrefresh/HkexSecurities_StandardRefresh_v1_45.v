From Stdlib Require Import List.
From Stdlib Require Import NArith.
From Stdlib Require Import Lia.
From Stdlib Require Import Strings.Byte.
From Omi Require Import Wire.

Import ListNotations.

(** * Hong Kong Exchanges and Clearing Orion Market Data Cash Standard Refresh

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
      - a Encoding rule
      - a Composite rule
  *)

Module HkexSecuritiesStandardRefreshV145.

  Module PacketHeader.

    (** Omd packet header (no payload compression; byte 3 is Filler) *)
    Record t := {
      pkt_size : N;
      msg_count : N;
      filler : N;
      seq_num : N;
      send_time : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (pkt_size record < 256 ^ N.of_nat 2)%N /\
      (msg_count record < 256 ^ N.of_nat 1)%N /\
      (filler record < 256 ^ N.of_nat 1)%N /\
      (seq_num record < 256 ^ N.of_nat 4)%N /\
      (send_time record < 256 ^ N.of_nat 8)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 2 (pkt_size record) ++
      encode_uint 1 (msg_count record) ++
      encode_uint 1 (filler record) ++
      encode_uint 4 (seq_num record) ++
      encode_uint 8 (send_time record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 2 bytes with
      | None => None
      | Some (pkt_size_value, bytes) =>
          match decode_uint 1 bytes with
          | None => None
          | Some (msg_count_value, bytes) =>
              match decode_uint 1 bytes with
              | None => None
              | Some (filler_value, bytes) =>
                  match decode_uint 4 bytes with
                  | None => None
                  | Some (seq_num_value, bytes) =>
                      match decode_uint 8 bytes with
                      | None => None
                      | Some (send_time_value, bytes) =>
                          Some ({| pkt_size := pkt_size_value; msg_count := msg_count_value; filler := filler_value; seq_num := seq_num_value; send_time := send_time_value |}, bytes)
                      end
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

  End PacketHeader.

  Module MsgHeader.

    (** Omd message header *)
    Record t := {
      msg_size : N;
      msg_type : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (msg_size record < 256 ^ N.of_nat 2)%N /\
      (msg_type record < 256 ^ N.of_nat 2)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 2 (msg_size record) ++
      encode_uint 2 (msg_type record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 2 bytes with
      | None => None
      | Some (msg_size_value, bytes) =>
          match decode_uint 2 bytes with
          | None => None
          | Some (msg_type_value, bytes) =>
              Some ({| msg_size := msg_size_value; msg_type := msg_type_value |}, bytes)
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 4.
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

  End MsgHeader.

  Module ClosingPriceMessage.

    (** The Closing Price message is generated near the end of the business day for each security. If the closing price is not available, ClosingPrice is set to 0. NumberOfTrades is not populated for SS (OMD Securities Standard) clients. *)
    Record t := {
      security_code : N;
      closing_price : N;
      number_of_trades : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (security_code record < 256 ^ N.of_nat 4)%N /\
      (closing_price record < 256 ^ N.of_nat 4)%N /\
      (number_of_trades record < 256 ^ N.of_nat 4)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 4 (security_code record) ++
      encode_uint 4 (closing_price record) ++
      encode_uint 4 (number_of_trades record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 4 bytes with
      | None => None
      | Some (security_code_value, bytes) =>
          match decode_uint 4 bytes with
          | None => None
          | Some (closing_price_value, bytes) =>
              match decode_uint 4 bytes with
              | None => None
              | Some (number_of_trades_value, bytes) =>
                  Some ({| security_code := security_code_value; closing_price := closing_price_value; number_of_trades := number_of_trades_value |}, bytes)
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

  End ClosingPriceMessage.

  Module IndicativeEquilibriumPriceMessage.

    (** The Indicative Equilibrium Price (IEP) message is generated whenever there is change of the IEP or Indicative Equilibrium Volume (IEV) during Pre-Opening Session (POS) or Closing Auction Session (CAS). The IEP is 0 when IEP does not exist. *)
    Record t := {
      security_code : N;
      price : N;
      aggregate_quantity : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (security_code record < 256 ^ N.of_nat 4)%N /\
      (price record < 256 ^ N.of_nat 4)%N /\
      (aggregate_quantity record < 256 ^ N.of_nat 8)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 4 (security_code record) ++
      encode_uint 4 (price record) ++
      encode_uint 8 (aggregate_quantity record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 4 bytes with
      | None => None
      | Some (security_code_value, bytes) =>
          match decode_uint 4 bytes with
          | None => None
          | Some (price_value, bytes) =>
              match decode_uint 8 bytes with
              | None => None
              | Some (aggregate_quantity_value, bytes) =>
                  Some ({| security_code := security_code_value; price := price_value; aggregate_quantity := aggregate_quantity_value |}, bytes)
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

  End IndicativeEquilibriumPriceMessage.

  Module NominalPriceMessage.

    (** The Nominal message may be generated when an order is added, deleted or modified in a book or when trade or trade cancel is performed. Before the first Nominal Price message, the nominal price should be the same as the previous closing price provided in Security Definition (11). *)
    Record t := {
      security_code : N;
      nominal_price : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (security_code record < 256 ^ N.of_nat 4)%N /\
      (nominal_price record < 256 ^ N.of_nat 4)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 4 (security_code record) ++
      encode_uint 4 (nominal_price record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 4 bytes with
      | None => None
      | Some (security_code_value, bytes) =>
          match decode_uint 4 bytes with
          | None => None
          | Some (nominal_price_value, bytes) =>
              Some ({| security_code := security_code_value; nominal_price := nominal_price_value |}, bytes)
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 8.
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

  End NominalPriceMessage.

  Module OrderImbalanceMessage.

    (** The Order Imbalance message provides order imbalance information at the Indicative Equilibrium Price (IEP) during the Pre-Opening Session (POS) and Closing Auction Session (CAS). *)
    Record t := {
      security_code : N;
      order_imbalance_direction : list byte;
      filler_1 : N;
      order_imbalance_quantity : N;
      filler_2 : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (security_code record < 256 ^ N.of_nat 4)%N /\
      Datatypes.length (order_imbalance_direction record) = 1 /\
      (filler_1 record < 256 ^ N.of_nat 1)%N /\
      (order_imbalance_quantity record < 256 ^ N.of_nat 8)%N /\
      (filler_2 record < 256 ^ N.of_nat 2)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 4 (security_code record) ++
      encode_bytes 1 (order_imbalance_direction record) ++
      encode_uint 1 (filler_1 record) ++
      encode_uint 8 (order_imbalance_quantity record) ++
      encode_uint 2 (filler_2 record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 4 bytes with
      | None => None
      | Some (security_code_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (order_imbalance_direction_value, bytes) =>
              match decode_uint 1 bytes with
              | None => None
              | Some (filler_1_value, bytes) =>
                  match decode_uint 8 bytes with
                  | None => None
                  | Some (order_imbalance_quantity_value, bytes) =>
                      match decode_uint 2 bytes with
                      | None => None
                      | Some (filler_2_value, bytes) =>
                          Some ({| security_code := security_code_value; order_imbalance_direction := order_imbalance_direction_value; filler_1 := filler_1_value; order_imbalance_quantity := order_imbalance_quantity_value; filler_2 := filler_2_value |}, bytes)
                      end
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 16.
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
      rewrite decode_encode_uint by exact bound_2.
      rewrite decode_encode_uint by exact bound_3.
      rewrite decode_encode_uint by exact bound_4.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End OrderImbalanceMessage.

  Module MarketDefinitionMessage.

    (** The Market Definition message is generated at the start of the business day for each market segment. *)
    Record t := {
      market_code : list byte;
      market_name : list byte;
      currency_code : list byte;
      number_of_securities : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (market_code record) = 4 /\
      Datatypes.length (market_name record) = 25 /\
      Datatypes.length (currency_code record) = 3 /\
      (number_of_securities record < 256 ^ N.of_nat 4)%N.

    Definition encode (record : t) : list byte :=
      encode_bytes 4 (market_code record) ++
      encode_bytes 25 (market_name record) ++
      encode_bytes 3 (currency_code record) ++
      encode_uint 4 (number_of_securities record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 4 bytes with
      | None => None
      | Some (market_code_value, bytes) =>
          match decode_bytes 25 bytes with
          | None => None
          | Some (market_name_value, bytes) =>
              match decode_bytes 3 bytes with
              | None => None
              | Some (currency_code_value, bytes) =>
                  match decode_uint 4 bytes with
                  | None => None
                  | Some (number_of_securities_value, bytes) =>
                      Some ({| market_code := market_code_value; market_name := market_name_value; currency_code := currency_code_value; number_of_securities := number_of_securities_value |}, bytes)
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 36.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_bytes_length, !encode_uint_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 [bound_1 [bound_2 bound_3]]].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_bytes by exact bound_0.
      rewrite decode_encode_bytes by exact bound_1.
      rewrite decode_encode_bytes by exact bound_2.
      rewrite decode_encode_uint by exact bound_3.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End MarketDefinitionMessage.

  Module CurrencyRateMessage.

    (** The Currency Rate message provides the foreign exchange conversion rates between various foreign currencies and the Hong Kong dollar. *)
    Record t := {
      currency_code : list byte;
      filler_1 : N;
      currency_factor : N;
      filler_2 : N;
      currency_rate : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (currency_code record) = 3 /\
      (filler_1 record < 256 ^ N.of_nat 1)%N /\
      (currency_factor record < 256 ^ N.of_nat 2)%N /\
      (filler_2 record < 256 ^ N.of_nat 2)%N /\
      (currency_rate record < 256 ^ N.of_nat 4)%N.

    Definition encode (record : t) : list byte :=
      encode_bytes 3 (currency_code record) ++
      encode_uint 1 (filler_1 record) ++
      encode_uint 2 (currency_factor record) ++
      encode_uint 2 (filler_2 record) ++
      encode_uint 4 (currency_rate record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 3 bytes with
      | None => None
      | Some (currency_code_value, bytes) =>
          match decode_uint 1 bytes with
          | None => None
          | Some (filler_1_value, bytes) =>
              match decode_uint 2 bytes with
              | None => None
              | Some (currency_factor_value, bytes) =>
                  match decode_uint 2 bytes with
                  | None => None
                  | Some (filler_2_value, bytes) =>
                      match decode_uint 4 bytes with
                      | None => None
                      | Some (currency_rate_value, bytes) =>
                          Some ({| currency_code := currency_code_value; filler_1 := filler_1_value; currency_factor := currency_factor_value; filler_2 := filler_2_value; currency_rate := currency_rate_value |}, bytes)
                      end
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 12.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_bytes_length, !encode_uint_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 [bound_1 [bound_2 [bound_3 bound_4]]]].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_bytes by exact bound_0.
      rewrite decode_encode_uint by exact bound_1.
      rewrite decode_encode_uint by exact bound_2.
      rewrite decode_encode_uint by exact bound_3.
      rewrite decode_encode_uint by exact bound_4.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End CurrencyRateMessage.

  Module ReferencePriceMessage.

    (** Reference price, lower and upper price limits for order input during an applicable auction session (POS or CAS). Sent again when there is any change. *)
    Record t := {
      security_code : N;
      reference_price : N;
      lower_price : N;
      upper_price : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (security_code record < 256 ^ N.of_nat 4)%N /\
      (reference_price record < 256 ^ N.of_nat 4)%N /\
      (lower_price record < 256 ^ N.of_nat 4)%N /\
      (upper_price record < 256 ^ N.of_nat 4)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 4 (security_code record) ++
      encode_uint 4 (reference_price record) ++
      encode_uint 4 (lower_price record) ++
      encode_uint 4 (upper_price record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 4 bytes with
      | None => None
      | Some (security_code_value, bytes) =>
          match decode_uint 4 bytes with
          | None => None
          | Some (reference_price_value, bytes) =>
              match decode_uint 4 bytes with
              | None => None
              | Some (lower_price_value, bytes) =>
                  match decode_uint 4 bytes with
                  | None => None
                  | Some (upper_price_value, bytes) =>
                      Some ({| security_code := security_code_value; reference_price := reference_price_value; lower_price := lower_price_value; upper_price := upper_price_value |}, bytes)
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

  End ReferencePriceMessage.

  Module RefreshCompleteMessage.

    (** This message is published to mark the end of a refresh. *)
    Record t := {
      last_seq_num : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (last_seq_num record < 256 ^ N.of_nat 4)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 4 (last_seq_num record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 4 bytes with
      | None => None
      | Some (last_seq_num_value, bytes) =>
          Some ({| last_seq_num := last_seq_num_value |}, bytes)
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

  End RefreshCompleteMessage.

  Module StatisticsMessage.

    (** The Statistics message provides statistics including volume-weighted average price and turnover. Generated (excluding overseas trades) once after CTS/auction match, manual trade, odd lot trade, or trade cancel. VWAP is not populated for SS (OMD Securities Standard) clients. *)
    Record t := {
      security_code : N;
      shares_traded : N;
      turnover : N;
      high_price : N;
      low_price : N;
      last_price : N;
      vwap : N;
      short_sell_shares_traded : N;
      short_sell_turnover : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (security_code record < 256 ^ N.of_nat 4)%N /\
      (shares_traded record < 256 ^ N.of_nat 8)%N /\
      (turnover record < 256 ^ N.of_nat 8)%N /\
      (high_price record < 256 ^ N.of_nat 4)%N /\
      (low_price record < 256 ^ N.of_nat 4)%N /\
      (last_price record < 256 ^ N.of_nat 4)%N /\
      (vwap record < 256 ^ N.of_nat 4)%N /\
      (short_sell_shares_traded record < 256 ^ N.of_nat 4)%N /\
      (short_sell_turnover record < 256 ^ N.of_nat 8)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 4 (security_code record) ++
      encode_uint 8 (shares_traded record) ++
      encode_uint 8 (turnover record) ++
      encode_uint 4 (high_price record) ++
      encode_uint 4 (low_price record) ++
      encode_uint 4 (last_price record) ++
      encode_uint 4 (vwap record) ++
      encode_uint 4 (short_sell_shares_traded record) ++
      encode_uint 8 (short_sell_turnover record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 4 bytes with
      | None => None
      | Some (security_code_value, bytes) =>
          match decode_uint 8 bytes with
          | None => None
          | Some (shares_traded_value, bytes) =>
              match decode_uint 8 bytes with
              | None => None
              | Some (turnover_value, bytes) =>
                  match decode_uint 4 bytes with
                  | None => None
                  | Some (high_price_value, bytes) =>
                      match decode_uint 4 bytes with
                      | None => None
                      | Some (low_price_value, bytes) =>
                          match decode_uint 4 bytes with
                          | None => None
                          | Some (last_price_value, bytes) =>
                              match decode_uint 4 bytes with
                              | None => None
                              | Some (vwap_value, bytes) =>
                                  match decode_uint 4 bytes with
                                  | None => None
                                  | Some (short_sell_shares_traded_value, bytes) =>
                                      match decode_uint 8 bytes with
                                      | None => None
                                      | Some (short_sell_turnover_value, bytes) =>
                                          Some ({| security_code := security_code_value; shares_traded := shares_traded_value; turnover := turnover_value; high_price := high_price_value; low_price := low_price_value; last_price := last_price_value; vwap := vwap_value; short_sell_shares_traded := short_sell_shares_traded_value; short_sell_turnover := short_sell_turnover_value |}, bytes)
                                      end
                                  end
                              end
                          end
                      end
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 48.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_uint_length. reflexivity.
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
      rewrite decode_encode_uint by exact bound_8.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec]. Defined.

  End StatisticsMessage.

  Module MarketTurnoverMessage.

    (** The Market Turnover message contains the total turnover (excluding overseas trades) for all securities on a given market segment for a given trading currency. When CurrencyCode is blank, the turnover represents the total for all trading currencies, expressed in HKD. Updates disseminated around every 2 seconds during trading hours. *)
    Record t := {
      market_code : list byte;
      currency_code : list byte;
      filler_1 : N;
      turnover : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (market_code record) = 4 /\
      Datatypes.length (currency_code record) = 3 /\
      (filler_1 record < 256 ^ N.of_nat 1)%N /\
      (turnover record < 256 ^ N.of_nat 8)%N.

    Definition encode (record : t) : list byte :=
      encode_bytes 4 (market_code record) ++
      encode_bytes 3 (currency_code record) ++
      encode_uint 1 (filler_1 record) ++
      encode_uint 8 (turnover record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 4 bytes with
      | None => None
      | Some (market_code_value, bytes) =>
          match decode_bytes 3 bytes with
          | None => None
          | Some (currency_code_value, bytes) =>
              match decode_uint 1 bytes with
              | None => None
              | Some (filler_1_value, bytes) =>
                  match decode_uint 8 bytes with
                  | None => None
                  | Some (turnover_value, bytes) =>
                      Some ({| market_code := market_code_value; currency_code := currency_code_value; filler_1 := filler_1_value; turnover := turnover_value |}, bytes)
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 16.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_bytes_length, !encode_uint_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 [bound_1 [bound_2 bound_3]]].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_bytes by exact bound_0.
      rewrite decode_encode_bytes by exact bound_1.
      rewrite decode_encode_uint by exact bound_2.
      rewrite decode_encode_uint by exact bound_3.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End MarketTurnoverMessage.

  Module YieldMessage.

    (** The Yield message is generated for bond securities when their yield percentage changes. *)
    Record t := {
      security_code : N;
      yield : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (security_code record < 256 ^ N.of_nat 4)%N /\
      (yield record < 256 ^ N.of_nat 4)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 4 (security_code record) ++
      encode_uint 4 (yield record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 4 bytes with
      | None => None
      | Some (security_code_value, bytes) =>
          match decode_uint 4 bytes with
          | None => None
          | Some (yield_value, bytes) =>
              Some ({| security_code := security_code_value; yield := yield_value |}, bytes)
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 8.
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

  End YieldMessage.

  Module TradingSessionStatusMessage.

    (** The Trading Session Status provides information on the status of a market segment. It is sent whenever there is change of trading session. This message may be sent on a separate multicast channel from order and trade data and therefore may not be synchronized. *)
    Record t := {
      market_code : list byte;
      filler_1 : N;
      trading_session_sub_id : N;
      trading_ses_status : N;
      trading_ses_control_flag : list byte;
      filler_4 : N;
      start_date_time : N;
      end_date_time : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (market_code record) = 4 /\
      (filler_1 record < 256 ^ N.of_nat 1)%N /\
      (trading_session_sub_id record < 256 ^ N.of_nat 1)%N /\
      (trading_ses_status record < 256 ^ N.of_nat 1)%N /\
      Datatypes.length (trading_ses_control_flag record) = 1 /\
      (filler_4 record < 256 ^ N.of_nat 4)%N /\
      (start_date_time record < 256 ^ N.of_nat 8)%N /\
      (end_date_time record < 256 ^ N.of_nat 8)%N.

    Definition encode (record : t) : list byte :=
      encode_bytes 4 (market_code record) ++
      encode_uint 1 (filler_1 record) ++
      encode_uint 1 (trading_session_sub_id record) ++
      encode_uint 1 (trading_ses_status record) ++
      encode_bytes 1 (trading_ses_control_flag record) ++
      encode_uint 4 (filler_4 record) ++
      encode_uint 8 (start_date_time record) ++
      encode_uint 8 (end_date_time record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 4 bytes with
      | None => None
      | Some (market_code_value, bytes) =>
          match decode_uint 1 bytes with
          | None => None
          | Some (filler_1_value, bytes) =>
              match decode_uint 1 bytes with
              | None => None
              | Some (trading_session_sub_id_value, bytes) =>
                  match decode_uint 1 bytes with
                  | None => None
                  | Some (trading_ses_status_value, bytes) =>
                      match decode_bytes 1 bytes with
                      | None => None
                      | Some (trading_ses_control_flag_value, bytes) =>
                          match decode_uint 4 bytes with
                          | None => None
                          | Some (filler_4_value, bytes) =>
                              match decode_uint 8 bytes with
                              | None => None
                              | Some (start_date_time_value, bytes) =>
                                  match decode_uint 8 bytes with
                                  | None => None
                                  | Some (end_date_time_value, bytes) =>
                                      Some ({| market_code := market_code_value; filler_1 := filler_1_value; trading_session_sub_id := trading_session_sub_id_value; trading_ses_status := trading_ses_status_value; trading_ses_control_flag := trading_ses_control_flag_value; filler_4 := filler_4_value; start_date_time := start_date_time_value; end_date_time := end_date_time_value |}, bytes)
                                  end
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
      rewrite decode_encode_uint by exact bound_7.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End TradingSessionStatusMessage.

  Module SecurityStatusMessage.

    (** The Security Status message is generated at the start of the business day if the security is not available for trading, and whenever a security state changes. *)
    Record t := {
      security_code : N;
      suspension_indicator : N;
      filler_3 : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (security_code record < 256 ^ N.of_nat 4)%N /\
      (suspension_indicator record < 256 ^ N.of_nat 1)%N /\
      (filler_3 record < 256 ^ N.of_nat 3)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 4 (security_code record) ++
      encode_uint 1 (suspension_indicator record) ++
      encode_uint 3 (filler_3 record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 4 bytes with
      | None => None
      | Some (security_code_value, bytes) =>
          match decode_uint 1 bytes with
          | None => None
          | Some (suspension_indicator_value, bytes) =>
              match decode_uint 3 bytes with
              | None => None
              | Some (filler_3_value, bytes) =>
                  Some ({| security_code := security_code_value; suspension_indicator := suspension_indicator_value; filler_3 := filler_3_value |}, bytes)
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 8.
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

  End SecurityStatusMessage.

  Module VcmTriggerMessage.

    (** The VCM Trigger message is generated whenever a cooling off period is triggered by Volatility Control Mechanism (VCM). *)
    Record t := {
      security_code : N;
      cooling_off_start_time : N;
      cooling_off_end_time : N;
      vcm_reference_price : N;
      vcm_lower_price : N;
      vcm_upper_price : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (security_code record < 256 ^ N.of_nat 4)%N /\
      (cooling_off_start_time record < 256 ^ N.of_nat 8)%N /\
      (cooling_off_end_time record < 256 ^ N.of_nat 8)%N /\
      (vcm_reference_price record < 256 ^ N.of_nat 4)%N /\
      (vcm_lower_price record < 256 ^ N.of_nat 4)%N /\
      (vcm_upper_price record < 256 ^ N.of_nat 4)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 4 (security_code record) ++
      encode_uint 8 (cooling_off_start_time record) ++
      encode_uint 8 (cooling_off_end_time record) ++
      encode_uint 4 (vcm_reference_price record) ++
      encode_uint 4 (vcm_lower_price record) ++
      encode_uint 4 (vcm_upper_price record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 4 bytes with
      | None => None
      | Some (security_code_value, bytes) =>
          match decode_uint 8 bytes with
          | None => None
          | Some (cooling_off_start_time_value, bytes) =>
              match decode_uint 8 bytes with
              | None => None
              | Some (cooling_off_end_time_value, bytes) =>
                  match decode_uint 4 bytes with
                  | None => None
                  | Some (vcm_reference_price_value, bytes) =>
                      match decode_uint 4 bytes with
                      | None => None
                      | Some (vcm_lower_price_value, bytes) =>
                          match decode_uint 4 bytes with
                          | None => None
                          | Some (vcm_upper_price_value, bytes) =>
                              Some ({| security_code := security_code_value; cooling_off_start_time := cooling_off_start_time_value; cooling_off_end_time := cooling_off_end_time_value; vcm_reference_price := vcm_reference_price_value; vcm_lower_price := vcm_lower_price_value; vcm_upper_price := vcm_upper_price_value |}, bytes)
                          end
                      end
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 32.
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

  End VcmTriggerMessage.

End HkexSecuritiesStandardRefreshV145.
