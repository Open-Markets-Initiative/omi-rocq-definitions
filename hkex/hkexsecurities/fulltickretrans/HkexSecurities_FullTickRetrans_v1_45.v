From Stdlib Require Import List.
From Stdlib Require Import NArith.
From Stdlib Require Import Lia.
From Stdlib Require Import Strings.Byte.
From Omi Require Import Wire.

Import ListNotations.

(** * Hong Kong Exchanges and Clearing Orion Market Data Cash FullTick Retransmission

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
      - a Reassemble rule
      - a run counted by a field
      - a Composite rule
  *)

Module HkexSecuritiesFullTickRetransV145.

  Module PacketHeader.

    (** Omd packet header (byte-identical to the Udp form; SeqNum and SendTime set to 0 on Tcp per §3.5) *)
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

  Module AddOrderMessage.

    (** The Add Order message is generated when a new order is inserted into the order book. The OrderId is unique per security but will not increment consecutively. Note for Securities instruments the OrderBookPosition is always set to zero. *)
    Record t := {
      security_code : N;
      order_id : N;
      price : N;
      quantity : N;
      side : N;
      order_type : list byte;
      filler_1 : N;
      order_book_position : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (security_code record < 256 ^ N.of_nat 4)%N /\
      (order_id record < 256 ^ N.of_nat 8)%N /\
      (price record < 256 ^ N.of_nat 4)%N /\
      (quantity record < 256 ^ N.of_nat 4)%N /\
      (side record < 256 ^ N.of_nat 2)%N /\
      Datatypes.length (order_type record) = 1 /\
      (filler_1 record < 256 ^ N.of_nat 1)%N /\
      (order_book_position record < 256 ^ N.of_nat 4)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 4 (security_code record) ++
      encode_uint 8 (order_id record) ++
      encode_uint 4 (price record) ++
      encode_uint 4 (quantity record) ++
      encode_uint 2 (side record) ++
      encode_bytes 1 (order_type record) ++
      encode_uint 1 (filler_1 record) ++
      encode_uint 4 (order_book_position record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 4 bytes with
      | None => None
      | Some (security_code_value, bytes) =>
          match decode_uint 8 bytes with
          | None => None
          | Some (order_id_value, bytes) =>
              match decode_uint 4 bytes with
              | None => None
              | Some (price_value, bytes) =>
                  match decode_uint 4 bytes with
                  | None => None
                  | Some (quantity_value, bytes) =>
                      match decode_uint 2 bytes with
                      | None => None
                      | Some (side_value, bytes) =>
                          match decode_bytes 1 bytes with
                          | None => None
                          | Some (order_type_value, bytes) =>
                              match decode_uint 1 bytes with
                              | None => None
                              | Some (filler_1_value, bytes) =>
                                  match decode_uint 4 bytes with
                                  | None => None
                                  | Some (order_book_position_value, bytes) =>
                                      Some ({| security_code := security_code_value; order_id := order_id_value; price := price_value; quantity := quantity_value; side := side_value; order_type := order_type_value; filler_1 := filler_1_value; order_book_position := order_book_position_value |}, bytes)
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
      rewrite decode_encode_uint by exact bound_3.
      rewrite decode_encode_uint by exact bound_4.
      rewrite decode_encode_bytes by exact bound_5.
      rewrite decode_encode_uint by exact bound_6.
      rewrite decode_encode_uint by exact bound_7.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End AddOrderMessage.

  Module SequenceResetMessage.

    (** The Sequence Reset message is sent on each multicast channel at start of day. It may also be sent when there is a need for the rectification of stock reference data before market open. *)
    Record t := {
      new_seq_no : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (new_seq_no record < 256 ^ N.of_nat 4)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 4 (new_seq_no record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 4 bytes with
      | None => None
      | Some (new_seq_no_value, bytes) =>
          Some ({| new_seq_no := new_seq_no_value |}, bytes)
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

  End SequenceResetMessage.

  Module DisasterRecoverySignalMessage.

    (** The Disaster Recovery (DR) Signal message is sent on a dedicated multicast channel whenever a site failover scenario is triggered. *)
    Record t := {
      dr_status : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (dr_status record < 256 ^ N.of_nat 4)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 4 (dr_status record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 4 bytes with
      | None => None
      | Some (dr_status_value, bytes) =>
          Some ({| dr_status := dr_status_value |}, bytes)
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

  End DisasterRecoverySignalMessage.

  Module DeleteOrderMessage.

    (** The Delete Order message is generated when an existing order identified by the OrderId is deleted. *)
    Record t := {
      security_code : N;
      order_id : N;
      side : N;
      filler_2 : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (security_code record < 256 ^ N.of_nat 4)%N /\
      (order_id record < 256 ^ N.of_nat 8)%N /\
      (side record < 256 ^ N.of_nat 2)%N /\
      (filler_2 record < 256 ^ N.of_nat 2)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 4 (security_code record) ++
      encode_uint 8 (order_id record) ++
      encode_uint 2 (side record) ++
      encode_uint 2 (filler_2 record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 4 bytes with
      | None => None
      | Some (security_code_value, bytes) =>
          match decode_uint 8 bytes with
          | None => None
          | Some (order_id_value, bytes) =>
              match decode_uint 2 bytes with
              | None => None
              | Some (side_value, bytes) =>
                  match decode_uint 2 bytes with
                  | None => None
                  | Some (filler_2_value, bytes) =>
                      Some ({| security_code := security_code_value; order_id := order_id_value; side := side_value; filler_2 := filler_2_value |}, bytes)
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

  End DeleteOrderMessage.

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

  Module ModifyOrderMessage.

    (** The Modify Order message is generated when an existing order identified by the OrderId is modified. The only attribute that can be modified is the quantity. Note for Securities instruments the OrderBookPosition is always set to zero. *)
    Record t := {
      security_code : N;
      order_id : N;
      quantity : N;
      side : N;
      filler_2 : N;
      order_book_position : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (security_code record < 256 ^ N.of_nat 4)%N /\
      (order_id record < 256 ^ N.of_nat 8)%N /\
      (quantity record < 256 ^ N.of_nat 4)%N /\
      (side record < 256 ^ N.of_nat 2)%N /\
      (filler_2 record < 256 ^ N.of_nat 2)%N /\
      (order_book_position record < 256 ^ N.of_nat 4)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 4 (security_code record) ++
      encode_uint 8 (order_id record) ++
      encode_uint 4 (quantity record) ++
      encode_uint 2 (side record) ++
      encode_uint 2 (filler_2 record) ++
      encode_uint 4 (order_book_position record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 4 bytes with
      | None => None
      | Some (security_code_value, bytes) =>
          match decode_uint 8 bytes with
          | None => None
          | Some (order_id_value, bytes) =>
              match decode_uint 4 bytes with
              | None => None
              | Some (quantity_value, bytes) =>
                  match decode_uint 2 bytes with
                  | None => None
                  | Some (side_value, bytes) =>
                      match decode_uint 2 bytes with
                      | None => None
                      | Some (filler_2_value, bytes) =>
                          match decode_uint 4 bytes with
                          | None => None
                          | Some (order_book_position_value, bytes) =>
                              Some ({| security_code := security_code_value; order_id := order_id_value; quantity := quantity_value; side := side_value; filler_2 := filler_2_value; order_book_position := order_book_position_value |}, bytes)
                          end
                      end
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

  End ModifyOrderMessage.

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

  Module LogonMessage.

    (** The Logon message enables client authentication. Not required for multicast channels; only used for retransmission requests. *)
    Record t := {
      username : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (username record) = 12.

    Definition encode (record : t) : list byte :=
      encode_bytes 12 (username record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 12 bytes with
      | None => None
      | Some (username_value, bytes) =>
          Some ({| username := username_value |}, bytes)
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 12.
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

  End LogonMessage.

  Module LogonResponseMessage.

    (** Response to a Logon request indicating session status. *)
    Record t := {
      session_status : N;
      filler_3 : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (session_status record < 256 ^ N.of_nat 1)%N /\
      (filler_3 record < 256 ^ N.of_nat 3)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 1 (session_status record) ++
      encode_uint 3 (filler_3 record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 1 bytes with
      | None => None
      | Some (session_status_value, bytes) =>
          match decode_uint 3 bytes with
          | None => None
          | Some (filler_3_value, bytes) =>
              Some ({| session_status := session_status_value; filler_3 := filler_3_value |}, bytes)
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

  End LogonResponseMessage.

  Module RetransmissionRequestMessage.

    (** Client-initiated request to retransmit a range of messages from a specific multicast channel. *)
    Record t := {
      channel_id : N;
      filler_2 : N;
      begin_seq_num : N;
      end_seq_num : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (channel_id record < 256 ^ N.of_nat 2)%N /\
      (filler_2 record < 256 ^ N.of_nat 2)%N /\
      (begin_seq_num record < 256 ^ N.of_nat 4)%N /\
      (end_seq_num record < 256 ^ N.of_nat 4)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 2 (channel_id record) ++
      encode_uint 2 (filler_2 record) ++
      encode_uint 4 (begin_seq_num record) ++
      encode_uint 4 (end_seq_num record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 2 bytes with
      | None => None
      | Some (channel_id_value, bytes) =>
          match decode_uint 2 bytes with
          | None => None
          | Some (filler_2_value, bytes) =>
              match decode_uint 4 bytes with
              | None => None
              | Some (begin_seq_num_value, bytes) =>
                  match decode_uint 4 bytes with
                  | None => None
                  | Some (end_seq_num_value, bytes) =>
                      Some ({| channel_id := channel_id_value; filler_2 := filler_2_value; begin_seq_num := begin_seq_num_value; end_seq_num := end_seq_num_value |}, bytes)
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

  End RetransmissionRequestMessage.

  Module RetransmissionResponseMessage.

    (** Server response to a Retransmission Request indicating whether the range can be resent. *)
    Record t := {
      channel_id : N;
      retrans_status : N;
      filler_1 : N;
      begin_seq_num : N;
      end_seq_num : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (channel_id record < 256 ^ N.of_nat 2)%N /\
      (retrans_status record < 256 ^ N.of_nat 1)%N /\
      (filler_1 record < 256 ^ N.of_nat 1)%N /\
      (begin_seq_num record < 256 ^ N.of_nat 4)%N /\
      (end_seq_num record < 256 ^ N.of_nat 4)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 2 (channel_id record) ++
      encode_uint 1 (retrans_status record) ++
      encode_uint 1 (filler_1 record) ++
      encode_uint 4 (begin_seq_num record) ++
      encode_uint 4 (end_seq_num record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 2 bytes with
      | None => None
      | Some (channel_id_value, bytes) =>
          match decode_uint 1 bytes with
          | None => None
          | Some (retrans_status_value, bytes) =>
              match decode_uint 1 bytes with
              | None => None
              | Some (filler_1_value, bytes) =>
                  match decode_uint 4 bytes with
                  | None => None
                  | Some (begin_seq_num_value, bytes) =>
                      match decode_uint 4 bytes with
                      | None => None
                      | Some (end_seq_num_value, bytes) =>
                          Some ({| channel_id := channel_id_value; retrans_status := retrans_status_value; filler_1 := filler_1_value; begin_seq_num := begin_seq_num_value; end_seq_num := end_seq_num_value |}, bytes)
                      end
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

  End RetransmissionResponseMessage.

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

  Module TradeMessage.

    (** The Trade message is generated each time a trade has been performed. *)
    Record t := {
      security_code : N;
      trade_id : N;
      price : N;
      quantity : N;
      trd_type : N;
      filler_2 : N;
      trade_time : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (security_code record < 256 ^ N.of_nat 4)%N /\
      (trade_id record < 256 ^ N.of_nat 4)%N /\
      (price record < 256 ^ N.of_nat 4)%N /\
      (quantity record < 256 ^ N.of_nat 4)%N /\
      (trd_type record < 256 ^ N.of_nat 2)%N /\
      (filler_2 record < 256 ^ N.of_nat 2)%N /\
      (trade_time record < 256 ^ N.of_nat 8)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 4 (security_code record) ++
      encode_uint 4 (trade_id record) ++
      encode_uint 4 (price record) ++
      encode_uint 4 (quantity record) ++
      encode_uint 2 (trd_type record) ++
      encode_uint 2 (filler_2 record) ++
      encode_uint 8 (trade_time record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 4 bytes with
      | None => None
      | Some (security_code_value, bytes) =>
          match decode_uint 4 bytes with
          | None => None
          | Some (trade_id_value, bytes) =>
              match decode_uint 4 bytes with
              | None => None
              | Some (price_value, bytes) =>
                  match decode_uint 4 bytes with
                  | None => None
                  | Some (quantity_value, bytes) =>
                      match decode_uint 2 bytes with
                      | None => None
                      | Some (trd_type_value, bytes) =>
                          match decode_uint 2 bytes with
                          | None => None
                          | Some (filler_2_value, bytes) =>
                              match decode_uint 8 bytes with
                              | None => None
                              | Some (trade_time_value, bytes) =>
                                  Some ({| security_code := security_code_value; trade_id := trade_id_value; price := price_value; quantity := quantity_value; trd_type := trd_type_value; filler_2 := filler_2_value; trade_time := trade_time_value |}, bytes)
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
      rewrite !length_app, !encode_uint_length. reflexivity.
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
      rewrite decode_encode_uint by exact bound_6.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec]. Defined.

  End TradeMessage.

  Module TradeCancelMessage.

    (** The Trade Cancel message is generated when a trade has been cancelled. *)
    Record t := {
      security_code : N;
      trade_id : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (security_code record < 256 ^ N.of_nat 4)%N /\
      (trade_id record < 256 ^ N.of_nat 4)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 4 (security_code record) ++
      encode_uint 4 (trade_id record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 4 bytes with
      | None => None
      | Some (security_code_value, bytes) =>
          match decode_uint 4 bytes with
          | None => None
          | Some (trade_id_value, bytes) =>
              Some ({| security_code := security_code_value; trade_id := trade_id_value |}, bytes)
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

  End TradeCancelMessage.

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

End HkexSecuritiesFullTickRetransV145.
