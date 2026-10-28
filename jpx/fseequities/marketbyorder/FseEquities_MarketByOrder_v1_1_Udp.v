From Stdlib Require Import List.
From Stdlib Require Import NArith.
From Stdlib Require Import Lia.
From Stdlib Require Import Strings.Byte.
From Omi Require Import Wire.

Import ListNotations.

(** * Japan Exchange Group Market By Order

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
  *)

Module FseEquitiesMarketByOrderV11Udp.

  Module PacketHeader.

    (** Jpx Flex 26 byte packet header *)
    Record t := {
      multicast_group_number : N;
      number_of_system_reboots : N;
      sequence_number : N;
      issue_code : list byte;
      update_number : N;
      packet_number : N;
      total_number_of_packets : N;
      utility_flag : N;
      message_count : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (multicast_group_number record < 256 ^ N.of_nat 1)%N /\
      (number_of_system_reboots record < 256 ^ N.of_nat 1)%N /\
      (sequence_number record < 256 ^ N.of_nat 4)%N /\
      Datatypes.length (issue_code record) = 12 /\
      (update_number record < 256 ^ N.of_nat 4)%N /\
      (packet_number record < 256 ^ N.of_nat 1)%N /\
      (total_number_of_packets record < 256 ^ N.of_nat 1)%N /\
      (utility_flag record < 256 ^ N.of_nat 1)%N /\
      (message_count record < 256 ^ N.of_nat 1)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 1 (multicast_group_number record) ++
      encode_uint 1 (number_of_system_reboots record) ++
      encode_uint 4 (sequence_number record) ++
      encode_bytes 12 (issue_code record) ++
      encode_uint 4 (update_number record) ++
      encode_uint 1 (packet_number record) ++
      encode_uint 1 (total_number_of_packets record) ++
      encode_uint 1 (utility_flag record) ++
      encode_uint 1 (message_count record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 1 bytes with
      | None => None
      | Some (multicast_group_number_value, bytes) =>
          match decode_uint 1 bytes with
          | None => None
          | Some (number_of_system_reboots_value, bytes) =>
              match decode_uint 4 bytes with
              | None => None
              | Some (sequence_number_value, bytes) =>
                  match decode_bytes 12 bytes with
                  | None => None
                  | Some (issue_code_value, bytes) =>
                      match decode_uint 4 bytes with
                      | None => None
                      | Some (update_number_value, bytes) =>
                          match decode_uint 1 bytes with
                          | None => None
                          | Some (packet_number_value, bytes) =>
                              match decode_uint 1 bytes with
                              | None => None
                              | Some (total_number_of_packets_value, bytes) =>
                                  match decode_uint 1 bytes with
                                  | None => None
                                  | Some (utility_flag_value, bytes) =>
                                      match decode_uint 1 bytes with
                                      | None => None
                                      | Some (message_count_value, bytes) =>
                                          Some ({| multicast_group_number := multicast_group_number_value; number_of_system_reboots := number_of_system_reboots_value; sequence_number := sequence_number_value; issue_code := issue_code_value; update_number := update_number_value; packet_number := packet_number_value; total_number_of_packets := total_number_of_packets_value; utility_flag := utility_flag_value; message_count := message_count_value |}, bytes)
                                      end
                                  end
                              end
                          end
                      end
                  end
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
      destruct bound as [bound_0 [bound_1 [bound_2 [bound_3 [bound_4 [bound_5 [bound_6 [bound_7 bound_8]]]]]]]].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_uint by exact bound_0.
      rewrite decode_encode_uint by exact bound_1.
      rewrite decode_encode_uint by exact bound_2.
      rewrite decode_encode_bytes by exact bound_3.
      rewrite decode_encode_uint by exact bound_4.
      rewrite decode_encode_uint by exact bound_5.
      rewrite decode_encode_uint by exact bound_6.
      rewrite decode_encode_uint by exact bound_7.
      rewrite decode_encode_uint by exact bound_8.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End PacketHeader.

  Module MessageHeader.

    (** Jpx Flex tag header carrying length prefix and message type discriminator *)
    Record t := {
      tag_length : N;
      message_type : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (tag_length record < 256 ^ N.of_nat 1)%N /\
      Datatypes.length (message_type record) = 1.

    Definition encode (record : t) : list byte :=
      encode_uint 1 (tag_length record) ++
      encode_bytes 1 (message_type record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 1 bytes with
      | None => None
      | Some (tag_length_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (message_type_value, bytes) =>
              Some ({| tag_length := tag_length_value; message_type := message_type_value |}, bytes)
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 2.
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

  Module SecondsTimestampMessage.

    (** Provides information about the time of processing on the Trading Server to the nearest second. Always delivered at the time the information is generated, except for Reset and Communication Control. Only one tag is delivered per process and stored at the top of the first packet. *)
    Record t := {
      time_seconds : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (time_seconds record < 256 ^ N.of_nat 4)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 4 (time_seconds record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 4 bytes with
      | None => None
      | Some (time_seconds_value, bytes) =>
          Some ({| time_seconds := time_seconds_value |}, bytes)
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

  End SecondsTimestampMessage.

  Module TradingStatusMessage.

    (** Provides information about the status of trading on a per-issue basis. Delivered when there is a change in the tag. *)
    Record t := {
      time_microseconds : N;
      market_status : N;
      status_flag : list byte;
      short_selling_status : N;
      pricing_method : N;
      book_center_price : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (time_microseconds record < 256 ^ N.of_nat 4)%N /\
      (market_status record < 256 ^ N.of_nat 1)%N /\
      Datatypes.length (status_flag record) = 2 /\
      (short_selling_status record < 256 ^ N.of_nat 1)%N /\
      (pricing_method record < 256 ^ N.of_nat 1)%N /\
      (book_center_price record < 256 ^ N.of_nat 8)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 4 (time_microseconds record) ++
      encode_uint 1 (market_status record) ++
      encode_bytes 2 (status_flag record) ++
      encode_uint 1 (short_selling_status record) ++
      encode_uint 1 (pricing_method record) ++
      encode_uint 8 (book_center_price record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 4 bytes with
      | None => None
      | Some (time_microseconds_value, bytes) =>
          match decode_uint 1 bytes with
          | None => None
          | Some (market_status_value, bytes) =>
              match decode_bytes 2 bytes with
              | None => None
              | Some (status_flag_value, bytes) =>
                  match decode_uint 1 bytes with
                  | None => None
                  | Some (short_selling_status_value, bytes) =>
                      match decode_uint 1 bytes with
                      | None => None
                      | Some (pricing_method_value, bytes) =>
                          match decode_uint 8 bytes with
                          | None => None
                          | Some (book_center_price_value, bytes) =>
                              Some ({| time_microseconds := time_microseconds_value; market_status := market_status_value; status_flag := status_flag_value; short_selling_status := short_selling_status_value; pricing_method := pricing_method_value; book_center_price := book_center_price_value |}, bytes)
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
      destruct bound as [bound_0 [bound_1 [bound_2 [bound_3 [bound_4 bound_5]]]]].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_uint by exact bound_0.
      rewrite decode_encode_uint by exact bound_1.
      rewrite decode_encode_bytes by exact bound_2.
      rewrite decode_encode_uint by exact bound_3.
      rewrite decode_encode_uint by exact bound_4.
      rewrite decode_encode_uint by exact bound_5.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End TradingStatusMessage.

  Module ExecutionSummaryMessage.

    (** Provides summary information about execution. Delivered when an execution occurs. *)
    Record t := {
      time_microseconds : N;
      triggered_side : list byte;
      total_volume : N;
      total_invalidation : N;
      last_price : N;
      match_id : N;
      best_offer : N;
      best_bid : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (time_microseconds record < 256 ^ N.of_nat 4)%N /\
      Datatypes.length (triggered_side record) = 1 /\
      (total_volume record < 256 ^ N.of_nat 6)%N /\
      (total_invalidation record < 256 ^ N.of_nat 6)%N /\
      (last_price record < 256 ^ N.of_nat 8)%N /\
      (match_id record < 256 ^ N.of_nat 4)%N /\
      (best_offer record < 256 ^ N.of_nat 8)%N /\
      (best_bid record < 256 ^ N.of_nat 8)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 4 (time_microseconds record) ++
      encode_bytes 1 (triggered_side record) ++
      encode_uint 6 (total_volume record) ++
      encode_uint 6 (total_invalidation record) ++
      encode_uint 8 (last_price record) ++
      encode_uint 4 (match_id record) ++
      encode_uint 8 (best_offer record) ++
      encode_uint 8 (best_bid record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 4 bytes with
      | None => None
      | Some (time_microseconds_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (triggered_side_value, bytes) =>
              match decode_uint 6 bytes with
              | None => None
              | Some (total_volume_value, bytes) =>
                  match decode_uint 6 bytes with
                  | None => None
                  | Some (total_invalidation_value, bytes) =>
                      match decode_uint 8 bytes with
                      | None => None
                      | Some (last_price_value, bytes) =>
                          match decode_uint 4 bytes with
                          | None => None
                          | Some (match_id_value, bytes) =>
                              match decode_uint 8 bytes with
                              | None => None
                              | Some (best_offer_value, bytes) =>
                                  match decode_uint 8 bytes with
                                  | None => None
                                  | Some (best_bid_value, bytes) =>
                                      Some ({| time_microseconds := time_microseconds_value; triggered_side := triggered_side_value; total_volume := total_volume_value; total_invalidation := total_invalidation_value; last_price := last_price_value; match_id := match_id_value; best_offer := best_offer_value; best_bid := best_bid_value |}, bytes)
                                  end
                              end
                          end
                      end
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 45.
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
      rewrite decode_encode_uint by exact bound_2.
      rewrite decode_encode_uint by exact bound_3.
      rewrite decode_encode_uint by exact bound_4.
      rewrite decode_encode_uint by exact bound_5.
      rewrite decode_encode_uint by exact bound_6.
      rewrite decode_encode_uint by exact bound_7.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End ExecutionSummaryMessage.

  Module AddOrderMessage.

    (** Provides information about book registration. Delivered when a new order or modification order is registered. *)
    Record t := {
      time_microseconds : N;
      order_id : N;
      side : list byte;
      quantity : N;
      price : N;
      order_condition : N;
      modification_flag : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (time_microseconds record < 256 ^ N.of_nat 4)%N /\
      (order_id record < 256 ^ N.of_nat 4)%N /\
      Datatypes.length (side record) = 1 /\
      (quantity record < 256 ^ N.of_nat 6)%N /\
      (price record < 256 ^ N.of_nat 8)%N /\
      (order_condition record < 256 ^ N.of_nat 1)%N /\
      (modification_flag record < 256 ^ N.of_nat 1)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 4 (time_microseconds record) ++
      encode_uint 4 (order_id record) ++
      encode_bytes 1 (side record) ++
      encode_uint 6 (quantity record) ++
      encode_uint 8 (price record) ++
      encode_uint 1 (order_condition record) ++
      encode_uint 1 (modification_flag record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 4 bytes with
      | None => None
      | Some (time_microseconds_value, bytes) =>
          match decode_uint 4 bytes with
          | None => None
          | Some (order_id_value, bytes) =>
              match decode_bytes 1 bytes with
              | None => None
              | Some (side_value, bytes) =>
                  match decode_uint 6 bytes with
                  | None => None
                  | Some (quantity_value, bytes) =>
                      match decode_uint 8 bytes with
                      | None => None
                      | Some (price_value, bytes) =>
                          match decode_uint 1 bytes with
                          | None => None
                          | Some (order_condition_value, bytes) =>
                              match decode_uint 1 bytes with
                              | None => None
                              | Some (modification_flag_value, bytes) =>
                                  Some ({| time_microseconds := time_microseconds_value; order_id := order_id_value; side := side_value; quantity := quantity_value; price := price_value; order_condition := order_condition_value; modification_flag := modification_flag_value |}, bytes)
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

  End AddOrderMessage.

  Module OrderExecutedMessage.

    (** Provides information about registered orders in case of Zaraba execution. Delivered when an execution occurs in Zaraba. *)
    Record t := {
      time_microseconds : N;
      order_id : N;
      side : list byte;
      volume : N;
      match_id : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (time_microseconds record < 256 ^ N.of_nat 4)%N /\
      (order_id record < 256 ^ N.of_nat 4)%N /\
      Datatypes.length (side record) = 1 /\
      (volume record < 256 ^ N.of_nat 6)%N /\
      (match_id record < 256 ^ N.of_nat 4)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 4 (time_microseconds record) ++
      encode_uint 4 (order_id record) ++
      encode_bytes 1 (side record) ++
      encode_uint 6 (volume record) ++
      encode_uint 4 (match_id record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 4 bytes with
      | None => None
      | Some (time_microseconds_value, bytes) =>
          match decode_uint 4 bytes with
          | None => None
          | Some (order_id_value, bytes) =>
              match decode_bytes 1 bytes with
              | None => None
              | Some (side_value, bytes) =>
                  match decode_uint 6 bytes with
                  | None => None
                  | Some (volume_value, bytes) =>
                      match decode_uint 4 bytes with
                      | None => None
                      | Some (match_id_value, bytes) =>
                          Some ({| time_microseconds := time_microseconds_value; order_id := order_id_value; side := side_value; volume := volume_value; match_id := match_id_value |}, bytes)
                      end
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 19.
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

  End OrderExecutedMessage.

  Module OrderExecutedWithPriceMessage.

    (** Provides information about registered orders in case of Itayose execution. Delivered when an execution occurs by the Itayose method or while an SQ or STQ is displayed. *)
    Record t := {
      time_microseconds : N;
      order_id : N;
      side : list byte;
      volume : N;
      match_id : N;
      execution_price : N;
      adopted_pricing_method : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (time_microseconds record < 256 ^ N.of_nat 4)%N /\
      (order_id record < 256 ^ N.of_nat 4)%N /\
      Datatypes.length (side record) = 1 /\
      (volume record < 256 ^ N.of_nat 6)%N /\
      (match_id record < 256 ^ N.of_nat 4)%N /\
      (execution_price record < 256 ^ N.of_nat 8)%N /\
      (adopted_pricing_method record < 256 ^ N.of_nat 1)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 4 (time_microseconds record) ++
      encode_uint 4 (order_id record) ++
      encode_bytes 1 (side record) ++
      encode_uint 6 (volume record) ++
      encode_uint 4 (match_id record) ++
      encode_uint 8 (execution_price record) ++
      encode_uint 1 (adopted_pricing_method record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 4 bytes with
      | None => None
      | Some (time_microseconds_value, bytes) =>
          match decode_uint 4 bytes with
          | None => None
          | Some (order_id_value, bytes) =>
              match decode_bytes 1 bytes with
              | None => None
              | Some (side_value, bytes) =>
                  match decode_uint 6 bytes with
                  | None => None
                  | Some (volume_value, bytes) =>
                      match decode_uint 4 bytes with
                      | None => None
                      | Some (match_id_value, bytes) =>
                          match decode_uint 8 bytes with
                          | None => None
                          | Some (execution_price_value, bytes) =>
                              match decode_uint 1 bytes with
                              | None => None
                              | Some (adopted_pricing_method_value, bytes) =>
                                  Some ({| time_microseconds := time_microseconds_value; order_id := order_id_value; side := side_value; volume := volume_value; match_id := match_id_value; execution_price := execution_price_value; adopted_pricing_method := adopted_pricing_method_value |}, bytes)
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

  End OrderExecutedWithPriceMessage.

  Module OrderDeleteMessage.

    (** Provides information about order deletion from the order book. Delivered when an order is deleted via a cancel order or a modification order or when a registered order expires. *)
    Record t := {
      time_microseconds : N;
      order_id : N;
      side : list byte;
      modification_flag : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (time_microseconds record < 256 ^ N.of_nat 4)%N /\
      (order_id record < 256 ^ N.of_nat 4)%N /\
      Datatypes.length (side record) = 1 /\
      (modification_flag record < 256 ^ N.of_nat 1)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 4 (time_microseconds record) ++
      encode_uint 4 (order_id record) ++
      encode_bytes 1 (side record) ++
      encode_uint 1 (modification_flag record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 4 bytes with
      | None => None
      | Some (time_microseconds_value, bytes) =>
          match decode_uint 4 bytes with
          | None => None
          | Some (order_id_value, bytes) =>
              match decode_bytes 1 bytes with
              | None => None
              | Some (side_value, bytes) =>
                  match decode_uint 1 bytes with
                  | None => None
                  | Some (modification_flag_value, bytes) =>
                      Some ({| time_microseconds := time_microseconds_value; order_id := order_id_value; side := side_value; modification_flag := modification_flag_value |}, bytes)
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
      rewrite decode_encode_uint by exact bound_3.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End OrderDeleteMessage.

  Module ResetMessage.

    (** A tag requesting the resetting (i.e. cancellation) of all distributed information. When the user receives this tag, the user must clear all valid A tags. *)
    Record t := {
      reset_start_end_flag : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (reset_start_end_flag record < 256 ^ N.of_nat 1)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 1 (reset_start_end_flag record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 1 bytes with
      | None => None
      | Some (reset_start_end_flag_value, bytes) =>
          Some ({| reset_start_end_flag := reset_start_end_flag_value |}, bytes)
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

  End ResetMessage.

  Module CommunicationControlMessage.

    (** Provides information about communication control. Delivered when communication starts and ends, and in between at minute intervals. *)
    Record t := {
      test_mode_flag : N;
      communication_start_end_flag : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (test_mode_flag record < 256 ^ N.of_nat 1)%N /\
      (communication_start_end_flag record < 256 ^ N.of_nat 1)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 1 (test_mode_flag record) ++
      encode_uint 1 (communication_start_end_flag record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 1 bytes with
      | None => None
      | Some (test_mode_flag_value, bytes) =>
          match decode_uint 1 bytes with
          | None => None
          | Some (communication_start_end_flag_value, bytes) =>
              Some ({| test_mode_flag := test_mode_flag_value; communication_start_end_flag := communication_start_end_flag_value |}, bytes)
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 2.
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

  End CommunicationControlMessage.

End FseEquitiesMarketByOrderV11Udp.
