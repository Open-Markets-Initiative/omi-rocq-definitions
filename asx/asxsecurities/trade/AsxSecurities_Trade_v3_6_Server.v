From Stdlib Require Import List.
From Stdlib Require Import NArith.
From Stdlib Require Import Lia.
From Stdlib Require Import Strings.Byte.
From Omi Require Import Wire.

Import ListNotations.

(** * Australian Securities Exchange Asx Trade

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
      - a field read in bits
  *)

Module AsxSecuritiesTradeV36Server.

  Module ServerPacketHeader.

    (** Packet header of a packet sent by the server *)
    Record t := {
      packet_length : N;
      server_packet_type : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (packet_length record < 256 ^ N.of_nat 2)%N /\
      Datatypes.length (server_packet_type record) = 1.

    Definition encode (record : t) : list byte :=
      encode_uint 2 (packet_length record) ++
      encode_bytes 1 (server_packet_type record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 2 bytes with
      | None => None
      | Some (packet_length_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (server_packet_type_value, bytes) =>
              Some ({| packet_length := packet_length_value; server_packet_type := server_packet_type_value |}, bytes)
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

  End ServerPacketHeader.

  Module LoginAcceptedPacket.

    (** The SoupBinTCP server sends a Login Accepted Packet in response to receiving a valid Login Request from the client *)
    Record t := {
      accepted_session : list byte;
      accepted_sequence_number : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (accepted_session record) = 10 /\
      Datatypes.length (accepted_sequence_number record) = 20.

    Definition encode (record : t) : list byte :=
      encode_bytes 10 (accepted_session record) ++
      encode_bytes 20 (accepted_sequence_number record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 10 bytes with
      | None => None
      | Some (accepted_session_value, bytes) =>
          match decode_bytes 20 bytes with
          | None => None
          | Some (accepted_sequence_number_value, bytes) =>
              Some ({| accepted_session := accepted_session_value; accepted_sequence_number := accepted_sequence_number_value |}, bytes)
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 30.
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

  End LoginAcceptedPacket.

  Module LoginRejectedPacket.

    (** The SoupBinTCP server sends this packet in response to an invalid Login Request Packet from the client *)
    Record t := {
      reject_reason_code : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (reject_reason_code record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 1 (reject_reason_code record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 1 bytes with
      | None => None
      | Some (reject_reason_code_value, bytes) =>
          Some ({| reject_reason_code := reject_reason_code_value |}, bytes)
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

  End LoginRejectedPacket.

  Module RegulatoryData.

    (** Regulatory Data *)
    Record t := {
      capacity_of_participant : list byte;
      directed_wholesale : list byte;
      execution_venue : list byte;
      intermediary_id : list byte;
      order_origin : list byte;
      filler : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (capacity_of_participant record) = 1 /\
      Datatypes.length (directed_wholesale record) = 1 /\
      Datatypes.length (execution_venue record) = 4 /\
      Datatypes.length (intermediary_id record) = 10 /\
      Datatypes.length (order_origin record) = 20 /\
      Datatypes.length (filler record) = 8.

    Definition encode (record : t) : list byte :=
      encode_bytes 1 (capacity_of_participant record) ++
      encode_bytes 1 (directed_wholesale record) ++
      encode_bytes 4 (execution_venue record) ++
      encode_bytes 10 (intermediary_id record) ++
      encode_bytes 20 (order_origin record) ++
      encode_bytes 8 (filler record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 1 bytes with
      | None => None
      | Some (capacity_of_participant_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (directed_wholesale_value, bytes) =>
              match decode_bytes 4 bytes with
              | None => None
              | Some (execution_venue_value, bytes) =>
                  match decode_bytes 10 bytes with
                  | None => None
                  | Some (intermediary_id_value, bytes) =>
                      match decode_bytes 20 bytes with
                      | None => None
                      | Some (order_origin_value, bytes) =>
                          match decode_bytes 8 bytes with
                          | None => None
                          | Some (filler_value, bytes) =>
                              Some ({| capacity_of_participant := capacity_of_participant_value; directed_wholesale := directed_wholesale_value; execution_venue := execution_venue_value; intermediary_id := intermediary_id_value; order_origin := order_origin_value; filler := filler_value |}, bytes)
                          end
                      end
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 44.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_bytes_length. reflexivity.
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
      rewrite decode_encode_bytes by exact bound_4.
      rewrite decode_encode_bytes by exact bound_5.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End RegulatoryData.

  Module OrderAcceptedMessage.

    (** The Order Accepted message acknowledges the receipt and acceptance of a valid Enter Order message. The data fields from the Enter Order message are echoed back in the Order Accepted message, but some of the accepted values may differ from the entered values for some fields, depending on the state of the order. If the order for example traded immediately at entry, the Order Accepted message will show the state of the order after the trade. *)
    Record t := {
      timestamp_nanoseconds : N;
      order_token : list byte;
      order_book_id : N;
      side : list byte;
      order_id : N;
      quantity : N;
      price : N;
      time_in_force : N;
      open_close : N;
      client_account : list byte;
      order_state : N;
      customer_info : list byte;
      exchange_info : list byte;
      clearing_participant : list byte;
      crossing_key : N;
      regulatory_data : RegulatoryData.t;
      ouch_order_type : list byte;
      short_sell_quantity : N;
      minimum_acceptable_quantity : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (timestamp_nanoseconds record < 256 ^ N.of_nat 8)%N /\
      Datatypes.length (order_token record) = 14 /\
      (order_book_id record < 256 ^ N.of_nat 4)%N /\
      Datatypes.length (side record) = 1 /\
      (order_id record < 256 ^ N.of_nat 8)%N /\
      (quantity record < 256 ^ N.of_nat 8)%N /\
      (price record < 256 ^ N.of_nat 4)%N /\
      (time_in_force record < 256 ^ N.of_nat 1)%N /\
      (open_close record < 256 ^ N.of_nat 1)%N /\
      Datatypes.length (client_account record) = 10 /\
      (order_state record < 256 ^ N.of_nat 1)%N /\
      Datatypes.length (customer_info record) = 15 /\
      Datatypes.length (exchange_info record) = 32 /\
      Datatypes.length (clearing_participant record) = 1 /\
      (crossing_key record < 256 ^ N.of_nat 4)%N /\
      RegulatoryData.bounded (regulatory_data record) /\
      Datatypes.length (ouch_order_type record) = 1 /\
      (short_sell_quantity record < 256 ^ N.of_nat 8)%N /\
      (minimum_acceptable_quantity record < 256 ^ N.of_nat 8)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 8 (timestamp_nanoseconds record) ++
      encode_bytes 14 (order_token record) ++
      encode_uint 4 (order_book_id record) ++
      encode_bytes 1 (side record) ++
      encode_uint 8 (order_id record) ++
      encode_uint 8 (quantity record) ++
      encode_uint 4 (price record) ++
      encode_uint 1 (time_in_force record) ++
      encode_uint 1 (open_close record) ++
      encode_bytes 10 (client_account record) ++
      encode_uint 1 (order_state record) ++
      encode_bytes 15 (customer_info record) ++
      encode_bytes 32 (exchange_info record) ++
      encode_bytes 1 (clearing_participant record) ++
      encode_uint 4 (crossing_key record) ++
      RegulatoryData.encode (regulatory_data record) ++
      encode_bytes 1 (ouch_order_type record) ++
      encode_uint 8 (short_sell_quantity record) ++
      encode_uint 8 (minimum_acceptable_quantity record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 8 bytes with
      | None => None
      | Some (timestamp_nanoseconds_value, bytes) =>
          match decode_bytes 14 bytes with
          | None => None
          | Some (order_token_value, bytes) =>
              match decode_uint 4 bytes with
              | None => None
              | Some (order_book_id_value, bytes) =>
                  match decode_bytes 1 bytes with
                  | None => None
                  | Some (side_value, bytes) =>
                      match decode_uint 8 bytes with
                      | None => None
                      | Some (order_id_value, bytes) =>
                          match decode_uint 8 bytes with
                          | None => None
                          | Some (quantity_value, bytes) =>
                              match decode_uint 4 bytes with
                              | None => None
                              | Some (price_value, bytes) =>
                                  match decode_uint 1 bytes with
                                  | None => None
                                  | Some (time_in_force_value, bytes) =>
                                      match decode_uint 1 bytes with
                                      | None => None
                                      | Some (open_close_value, bytes) =>
                                          match decode_bytes 10 bytes with
                                          | None => None
                                          | Some (client_account_value, bytes) =>
                                              match decode_uint 1 bytes with
                                              | None => None
                                              | Some (order_state_value, bytes) =>
                                                  match decode_bytes 15 bytes with
                                                  | None => None
                                                  | Some (customer_info_value, bytes) =>
                                                      match decode_bytes 32 bytes with
                                                      | None => None
                                                      | Some (exchange_info_value, bytes) =>
                                                          match decode_bytes 1 bytes with
                                                          | None => None
                                                          | Some (clearing_participant_value, bytes) =>
                                                              match decode_uint 4 bytes with
                                                              | None => None
                                                              | Some (crossing_key_value, bytes) =>
                                                                  match RegulatoryData.decode bytes with
                                                                  | None => None
                                                                  | Some (regulatory_data_value, bytes) =>
                                                                      match decode_bytes 1 bytes with
                                                                      | None => None
                                                                      | Some (ouch_order_type_value, bytes) =>
                                                                          match decode_uint 8 bytes with
                                                                          | None => None
                                                                          | Some (short_sell_quantity_value, bytes) =>
                                                                              match decode_uint 8 bytes with
                                                                              | None => None
                                                                              | Some (minimum_acceptable_quantity_value, bytes) =>
                                                                                  Some ({| timestamp_nanoseconds := timestamp_nanoseconds_value; order_token := order_token_value; order_book_id := order_book_id_value; side := side_value; order_id := order_id_value; quantity := quantity_value; price := price_value; time_in_force := time_in_force_value; open_close := open_close_value; client_account := client_account_value; order_state := order_state_value; customer_info := customer_info_value; exchange_info := exchange_info_value; clearing_participant := clearing_participant_value; crossing_key := crossing_key_value; regulatory_data := regulatory_data_value; ouch_order_type := ouch_order_type_value; short_sell_quantity := short_sell_quantity_value; minimum_acceptable_quantity := minimum_acceptable_quantity_value |}, bytes)
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
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 173.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_uint_length, !encode_bytes_length, !RegulatoryData.encode_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 [bound_1 [bound_2 [bound_3 [bound_4 [bound_5 [bound_6 [bound_7 [bound_8 [bound_9 [bound_10 [bound_11 [bound_12 [bound_13 [bound_14 [bound_15 [bound_16 [bound_17 bound_18]]]]]]]]]]]]]]]]]].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_uint by exact bound_0.
      rewrite decode_encode_bytes by exact bound_1.
      rewrite decode_encode_uint by exact bound_2.
      rewrite decode_encode_bytes by exact bound_3.
      rewrite decode_encode_uint by exact bound_4.
      rewrite decode_encode_uint by exact bound_5.
      rewrite decode_encode_uint by exact bound_6.
      rewrite decode_encode_uint by exact bound_7.
      rewrite decode_encode_uint by exact bound_8.
      rewrite decode_encode_bytes by exact bound_9.
      rewrite decode_encode_uint by exact bound_10.
      rewrite decode_encode_bytes by exact bound_11.
      rewrite decode_encode_bytes by exact bound_12.
      rewrite decode_encode_bytes by exact bound_13.
      rewrite decode_encode_uint by exact bound_14.
      rewrite RegulatoryData.decode_encode by exact bound_15.
      rewrite decode_encode_bytes by exact bound_16.
      rewrite decode_encode_uint by exact bound_17.
      rewrite decode_encode_uint by exact bound_18.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec) | apply RegulatoryData.eq_dec]. Defined.

  End OrderAcceptedMessage.

  Module OrderRejectedMessage.

    (** This message is returned when an Enter Order, Replace Order, Cancel Order or Cancel By Order ID message is rejected *)
    Record t := {
      timestamp_nanoseconds : N;
      order_token : list byte;
      reject_code : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (timestamp_nanoseconds record < 256 ^ N.of_nat 8)%N /\
      Datatypes.length (order_token record) = 14 /\
      (reject_code record < 256 ^ N.of_nat 4)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 8 (timestamp_nanoseconds record) ++
      encode_bytes 14 (order_token record) ++
      encode_uint 4 (reject_code record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 8 bytes with
      | None => None
      | Some (timestamp_nanoseconds_value, bytes) =>
          match decode_bytes 14 bytes with
          | None => None
          | Some (order_token_value, bytes) =>
              match decode_uint 4 bytes with
              | None => None
              | Some (reject_code_value, bytes) =>
                  Some ({| timestamp_nanoseconds := timestamp_nanoseconds_value; order_token := order_token_value; reject_code := reject_code_value |}, bytes)
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 26.
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
      rewrite decode_encode_uint by exact bound_2.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End OrderRejectedMessage.

  Module RegulatoryData2.

    (** Regulatory Data *)
    Record t := {
      capacity_of_participant : list byte;
      directed_wholesale : list byte;
      execution_venue : list byte;
      intermediary_id : list byte;
      order_origin : list byte;
      filler : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (capacity_of_participant record) = 1 /\
      Datatypes.length (directed_wholesale record) = 1 /\
      Datatypes.length (execution_venue record) = 4 /\
      Datatypes.length (intermediary_id record) = 10 /\
      Datatypes.length (order_origin record) = 20 /\
      Datatypes.length (filler record) = 8.

    Definition encode (record : t) : list byte :=
      encode_bytes 1 (capacity_of_participant record) ++
      encode_bytes 1 (directed_wholesale record) ++
      encode_bytes 4 (execution_venue record) ++
      encode_bytes 10 (intermediary_id record) ++
      encode_bytes 20 (order_origin record) ++
      encode_bytes 8 (filler record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 1 bytes with
      | None => None
      | Some (capacity_of_participant_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (directed_wholesale_value, bytes) =>
              match decode_bytes 4 bytes with
              | None => None
              | Some (execution_venue_value, bytes) =>
                  match decode_bytes 10 bytes with
                  | None => None
                  | Some (intermediary_id_value, bytes) =>
                      match decode_bytes 20 bytes with
                      | None => None
                      | Some (order_origin_value, bytes) =>
                          match decode_bytes 8 bytes with
                          | None => None
                          | Some (filler_value, bytes) =>
                              Some ({| capacity_of_participant := capacity_of_participant_value; directed_wholesale := directed_wholesale_value; execution_venue := execution_venue_value; intermediary_id := intermediary_id_value; order_origin := order_origin_value; filler := filler_value |}, bytes)
                          end
                      end
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 44.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_bytes_length. reflexivity.
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
      rewrite decode_encode_bytes by exact bound_4.
      rewrite decode_encode_bytes by exact bound_5.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End RegulatoryData2.

  Module OrderReplacedMessage.

    (** The Order Replaced message acknowledges the receipt and acceptance of a valid Replace Order message. *)
    Record t := {
      timestamp_nanoseconds : N;
      replacement_order_token : list byte;
      previous_order_token : list byte;
      order_book_id : N;
      side : list byte;
      order_id : N;
      quantity : N;
      price : N;
      time_in_force : N;
      open_close : N;
      client_account : list byte;
      order_state : N;
      customer_info : list byte;
      exchange_info : list byte;
      clearing_participant : list byte;
      crossing_key : N;
      regulatory_data : RegulatoryData2.t;
      ouch_order_type : list byte;
      short_sell_quantity : N;
      minimum_acceptable_quantity : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (timestamp_nanoseconds record < 256 ^ N.of_nat 8)%N /\
      Datatypes.length (replacement_order_token record) = 14 /\
      Datatypes.length (previous_order_token record) = 14 /\
      (order_book_id record < 256 ^ N.of_nat 4)%N /\
      Datatypes.length (side record) = 1 /\
      (order_id record < 256 ^ N.of_nat 8)%N /\
      (quantity record < 256 ^ N.of_nat 8)%N /\
      (price record < 256 ^ N.of_nat 4)%N /\
      (time_in_force record < 256 ^ N.of_nat 1)%N /\
      (open_close record < 256 ^ N.of_nat 1)%N /\
      Datatypes.length (client_account record) = 10 /\
      (order_state record < 256 ^ N.of_nat 1)%N /\
      Datatypes.length (customer_info record) = 15 /\
      Datatypes.length (exchange_info record) = 32 /\
      Datatypes.length (clearing_participant record) = 1 /\
      (crossing_key record < 256 ^ N.of_nat 4)%N /\
      RegulatoryData2.bounded (regulatory_data record) /\
      Datatypes.length (ouch_order_type record) = 1 /\
      (short_sell_quantity record < 256 ^ N.of_nat 8)%N /\
      (minimum_acceptable_quantity record < 256 ^ N.of_nat 8)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 8 (timestamp_nanoseconds record) ++
      encode_bytes 14 (replacement_order_token record) ++
      encode_bytes 14 (previous_order_token record) ++
      encode_uint 4 (order_book_id record) ++
      encode_bytes 1 (side record) ++
      encode_uint 8 (order_id record) ++
      encode_uint 8 (quantity record) ++
      encode_uint 4 (price record) ++
      encode_uint 1 (time_in_force record) ++
      encode_uint 1 (open_close record) ++
      encode_bytes 10 (client_account record) ++
      encode_uint 1 (order_state record) ++
      encode_bytes 15 (customer_info record) ++
      encode_bytes 32 (exchange_info record) ++
      encode_bytes 1 (clearing_participant record) ++
      encode_uint 4 (crossing_key record) ++
      RegulatoryData2.encode (regulatory_data record) ++
      encode_bytes 1 (ouch_order_type record) ++
      encode_uint 8 (short_sell_quantity record) ++
      encode_uint 8 (minimum_acceptable_quantity record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 8 bytes with
      | None => None
      | Some (timestamp_nanoseconds_value, bytes) =>
          match decode_bytes 14 bytes with
          | None => None
          | Some (replacement_order_token_value, bytes) =>
              match decode_bytes 14 bytes with
              | None => None
              | Some (previous_order_token_value, bytes) =>
                  match decode_uint 4 bytes with
                  | None => None
                  | Some (order_book_id_value, bytes) =>
                      match decode_bytes 1 bytes with
                      | None => None
                      | Some (side_value, bytes) =>
                          match decode_uint 8 bytes with
                          | None => None
                          | Some (order_id_value, bytes) =>
                              match decode_uint 8 bytes with
                              | None => None
                              | Some (quantity_value, bytes) =>
                                  match decode_uint 4 bytes with
                                  | None => None
                                  | Some (price_value, bytes) =>
                                      match decode_uint 1 bytes with
                                      | None => None
                                      | Some (time_in_force_value, bytes) =>
                                          match decode_uint 1 bytes with
                                          | None => None
                                          | Some (open_close_value, bytes) =>
                                              match decode_bytes 10 bytes with
                                              | None => None
                                              | Some (client_account_value, bytes) =>
                                                  match decode_uint 1 bytes with
                                                  | None => None
                                                  | Some (order_state_value, bytes) =>
                                                      match decode_bytes 15 bytes with
                                                      | None => None
                                                      | Some (customer_info_value, bytes) =>
                                                          match decode_bytes 32 bytes with
                                                          | None => None
                                                          | Some (exchange_info_value, bytes) =>
                                                              match decode_bytes 1 bytes with
                                                              | None => None
                                                              | Some (clearing_participant_value, bytes) =>
                                                                  match decode_uint 4 bytes with
                                                                  | None => None
                                                                  | Some (crossing_key_value, bytes) =>
                                                                      match RegulatoryData2.decode bytes with
                                                                      | None => None
                                                                      | Some (regulatory_data_value, bytes) =>
                                                                          match decode_bytes 1 bytes with
                                                                          | None => None
                                                                          | Some (ouch_order_type_value, bytes) =>
                                                                              match decode_uint 8 bytes with
                                                                              | None => None
                                                                              | Some (short_sell_quantity_value, bytes) =>
                                                                                  match decode_uint 8 bytes with
                                                                                  | None => None
                                                                                  | Some (minimum_acceptable_quantity_value, bytes) =>
                                                                                      Some ({| timestamp_nanoseconds := timestamp_nanoseconds_value; replacement_order_token := replacement_order_token_value; previous_order_token := previous_order_token_value; order_book_id := order_book_id_value; side := side_value; order_id := order_id_value; quantity := quantity_value; price := price_value; time_in_force := time_in_force_value; open_close := open_close_value; client_account := client_account_value; order_state := order_state_value; customer_info := customer_info_value; exchange_info := exchange_info_value; clearing_participant := clearing_participant_value; crossing_key := crossing_key_value; regulatory_data := regulatory_data_value; ouch_order_type := ouch_order_type_value; short_sell_quantity := short_sell_quantity_value; minimum_acceptable_quantity := minimum_acceptable_quantity_value |}, bytes)
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
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 187.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_uint_length, !encode_bytes_length, !RegulatoryData2.encode_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 [bound_1 [bound_2 [bound_3 [bound_4 [bound_5 [bound_6 [bound_7 [bound_8 [bound_9 [bound_10 [bound_11 [bound_12 [bound_13 [bound_14 [bound_15 [bound_16 [bound_17 [bound_18 bound_19]]]]]]]]]]]]]]]]]]].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_uint by exact bound_0.
      rewrite decode_encode_bytes by exact bound_1.
      rewrite decode_encode_bytes by exact bound_2.
      rewrite decode_encode_uint by exact bound_3.
      rewrite decode_encode_bytes by exact bound_4.
      rewrite decode_encode_uint by exact bound_5.
      rewrite decode_encode_uint by exact bound_6.
      rewrite decode_encode_uint by exact bound_7.
      rewrite decode_encode_uint by exact bound_8.
      rewrite decode_encode_uint by exact bound_9.
      rewrite decode_encode_bytes by exact bound_10.
      rewrite decode_encode_uint by exact bound_11.
      rewrite decode_encode_bytes by exact bound_12.
      rewrite decode_encode_bytes by exact bound_13.
      rewrite decode_encode_bytes by exact bound_14.
      rewrite decode_encode_uint by exact bound_15.
      rewrite RegulatoryData2.decode_encode by exact bound_16.
      rewrite decode_encode_bytes by exact bound_17.
      rewrite decode_encode_uint by exact bound_18.
      rewrite decode_encode_uint by exact bound_19.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec) | apply RegulatoryData2.eq_dec]. Defined.

  End OrderReplacedMessage.

  Module OrderCancelledMessage.

    (** The Order Cancelled message informs the ASX Trade OUCH user that an order has been cancelled. This could be to acknowledge a Cancel Order or Cancel By Order Id message, or it could be as a result of system cancellation of an order. *)
    Record t := {
      timestamp_nanoseconds : N;
      order_token : list byte;
      order_book_id : N;
      side : list byte;
      order_id : N;
      reason : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (timestamp_nanoseconds record < 256 ^ N.of_nat 8)%N /\
      Datatypes.length (order_token record) = 14 /\
      (order_book_id record < 256 ^ N.of_nat 4)%N /\
      Datatypes.length (side record) = 1 /\
      (order_id record < 256 ^ N.of_nat 8)%N /\
      (reason record < 256 ^ N.of_nat 1)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 8 (timestamp_nanoseconds record) ++
      encode_bytes 14 (order_token record) ++
      encode_uint 4 (order_book_id record) ++
      encode_bytes 1 (side record) ++
      encode_uint 8 (order_id record) ++
      encode_uint 1 (reason record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 8 bytes with
      | None => None
      | Some (timestamp_nanoseconds_value, bytes) =>
          match decode_bytes 14 bytes with
          | None => None
          | Some (order_token_value, bytes) =>
              match decode_uint 4 bytes with
              | None => None
              | Some (order_book_id_value, bytes) =>
                  match decode_bytes 1 bytes with
                  | None => None
                  | Some (side_value, bytes) =>
                      match decode_uint 8 bytes with
                      | None => None
                      | Some (order_id_value, bytes) =>
                          match decode_uint 1 bytes with
                          | None => None
                          | Some (reason_value, bytes) =>
                              Some ({| timestamp_nanoseconds := timestamp_nanoseconds_value; order_token := order_token_value; order_book_id := order_book_id_value; side := side_value; order_id := order_id_value; reason := reason_value |}, bytes)
                          end
                      end
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 36.
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
      rewrite decode_encode_bytes by exact bound_3.
      rewrite decode_encode_uint by exact bound_4.
      rewrite decode_encode_uint by exact bound_5.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End OrderCancelledMessage.

End AsxSecuritiesTradeV36Server.
