From Stdlib Require Import List.
From Stdlib Require Import NArith.
From Stdlib Require Import Lia.
From Stdlib Require Import Strings.Byte.
From Omi Require Import Wire.

Import ListNotations.

(** * National Association of Securities Dealers Automated Quotations (Nasdaq) ISE Options Spread Orders

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

Module IseOptionsSpreadOrdersV21Udp.

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

  Module SystemEventMessage.

    (** The system event message type is used to signal a market or data feed handler event. *)
    Record t := {
      tracking_number : N;
      timestamp : N;
      event_code : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (tracking_number record < 256 ^ N.of_nat 2)%N /\
      (timestamp record < 256 ^ N.of_nat 8)%N /\
      Datatypes.length (event_code record) = 1.

    Definition encode (record : t) : list byte :=
      encode_uint 2 (tracking_number record) ++
      encode_uint 8 (timestamp record) ++
      encode_bytes 1 (event_code record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 2 bytes with
      | None => None
      | Some (tracking_number_value, bytes) =>
          match decode_uint 8 bytes with
          | None => None
          | Some (timestamp_value, bytes) =>
              match decode_bytes 1 bytes with
              | None => None
              | Some (event_code_value, bytes) =>
                  Some ({| tracking_number := tracking_number_value; timestamp := timestamp_value; event_code := event_code_value |}, bytes)
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

  End SystemEventMessage.

  Module StrategyTradingActionMessage.

    (** The options system uses this administrative message to indicate the current trading status of an index or equity option within the options market. *)
    Record t := {
      tracking_number : N;
      timestamp : N;
      strategy_id : N;
      current_trading_state : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (tracking_number record < 256 ^ N.of_nat 2)%N /\
      (timestamp record < 256 ^ N.of_nat 8)%N /\
      (strategy_id record < 256 ^ N.of_nat 4)%N /\
      Datatypes.length (current_trading_state record) = 1.

    Definition encode (record : t) : list byte :=
      encode_uint 2 (tracking_number record) ++
      encode_uint 8 (timestamp record) ++
      encode_uint 4 (strategy_id record) ++
      encode_bytes 1 (current_trading_state record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 2 bytes with
      | None => None
      | Some (tracking_number_value, bytes) =>
          match decode_uint 8 bytes with
          | None => None
          | Some (timestamp_value, bytes) =>
              match decode_uint 4 bytes with
              | None => None
              | Some (strategy_id_value, bytes) =>
                  match decode_bytes 1 bytes with
                  | None => None
                  | Some (current_trading_state_value, bytes) =>
                      Some ({| tracking_number := tracking_number_value; timestamp := timestamp_value; strategy_id := strategy_id_value; current_trading_state := current_trading_state_value |}, bytes)
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
      destruct bound as [bound_0 [bound_1 [bound_2 bound_3]]].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_uint by exact bound_0.
      rewrite decode_encode_uint by exact bound_1.
      rewrite decode_encode_uint by exact bound_2.
      rewrite decode_encode_bytes by exact bound_3.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End StrategyTradingActionMessage.

  Module ComplexAddOrderMessage.

    (** A Complex Add Order message is generated for all the following situations whenever an order free from any display restrictions is reported by the matching engine. *)
    Record t := {
      tracking_number : N;
      timestamp : N;
      strategy_id : N;
      order_reference_number : N;
      side : list byte;
      original_order_volume : N;
      executable_order_volume : N;
      order_status : list byte;
      order_type : list byte;
      limit_price : N;
      time_in_force : list byte;
      order_capacity : list byte;
      scope : list byte;
      owner_id : list byte;
      giveup : list byte;
      cmta : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (tracking_number record < 256 ^ N.of_nat 2)%N /\
      (timestamp record < 256 ^ N.of_nat 8)%N /\
      (strategy_id record < 256 ^ N.of_nat 4)%N /\
      (order_reference_number record < 256 ^ N.of_nat 8)%N /\
      Datatypes.length (side record) = 1 /\
      (original_order_volume record < 256 ^ N.of_nat 4)%N /\
      (executable_order_volume record < 256 ^ N.of_nat 4)%N /\
      Datatypes.length (order_status record) = 1 /\
      Datatypes.length (order_type record) = 1 /\
      (limit_price record < 256 ^ N.of_nat 4)%N /\
      Datatypes.length (time_in_force record) = 1 /\
      Datatypes.length (order_capacity record) = 1 /\
      Datatypes.length (scope record) = 1 /\
      Datatypes.length (owner_id record) = 6 /\
      Datatypes.length (giveup record) = 6 /\
      Datatypes.length (cmta record) = 6.

    Definition encode (record : t) : list byte :=
      encode_uint 2 (tracking_number record) ++
      encode_uint 8 (timestamp record) ++
      encode_uint 4 (strategy_id record) ++
      encode_uint 8 (order_reference_number record) ++
      encode_bytes 1 (side record) ++
      encode_uint 4 (original_order_volume record) ++
      encode_uint 4 (executable_order_volume record) ++
      encode_bytes 1 (order_status record) ++
      encode_bytes 1 (order_type record) ++
      encode_uint 4 (limit_price record) ++
      encode_bytes 1 (time_in_force record) ++
      encode_bytes 1 (order_capacity record) ++
      encode_bytes 1 (scope record) ++
      encode_bytes 6 (owner_id record) ++
      encode_bytes 6 (giveup record) ++
      encode_bytes 6 (cmta record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 2 bytes with
      | None => None
      | Some (tracking_number_value, bytes) =>
          match decode_uint 8 bytes with
          | None => None
          | Some (timestamp_value, bytes) =>
              match decode_uint 4 bytes with
              | None => None
              | Some (strategy_id_value, bytes) =>
                  match decode_uint 8 bytes with
                  | None => None
                  | Some (order_reference_number_value, bytes) =>
                      match decode_bytes 1 bytes with
                      | None => None
                      | Some (side_value, bytes) =>
                          match decode_uint 4 bytes with
                          | None => None
                          | Some (original_order_volume_value, bytes) =>
                              match decode_uint 4 bytes with
                              | None => None
                              | Some (executable_order_volume_value, bytes) =>
                                  match decode_bytes 1 bytes with
                                  | None => None
                                  | Some (order_status_value, bytes) =>
                                      match decode_bytes 1 bytes with
                                      | None => None
                                      | Some (order_type_value, bytes) =>
                                          match decode_uint 4 bytes with
                                          | None => None
                                          | Some (limit_price_value, bytes) =>
                                              match decode_bytes 1 bytes with
                                              | None => None
                                              | Some (time_in_force_value, bytes) =>
                                                  match decode_bytes 1 bytes with
                                                  | None => None
                                                  | Some (order_capacity_value, bytes) =>
                                                      match decode_bytes 1 bytes with
                                                      | None => None
                                                      | Some (scope_value, bytes) =>
                                                          match decode_bytes 6 bytes with
                                                          | None => None
                                                          | Some (owner_id_value, bytes) =>
                                                              match decode_bytes 6 bytes with
                                                              | None => None
                                                              | Some (giveup_value, bytes) =>
                                                                  match decode_bytes 6 bytes with
                                                                  | None => None
                                                                  | Some (cmta_value, bytes) =>
                                                                      Some ({| tracking_number := tracking_number_value; timestamp := timestamp_value; strategy_id := strategy_id_value; order_reference_number := order_reference_number_value; side := side_value; original_order_volume := original_order_volume_value; executable_order_volume := executable_order_volume_value; order_status := order_status_value; order_type := order_type_value; limit_price := limit_price_value; time_in_force := time_in_force_value; order_capacity := order_capacity_value; scope := scope_value; owner_id := owner_id_value; giveup := giveup_value; cmta := cmta_value |}, bytes)
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

    Theorem encode_length : forall record, Datatypes.length (encode record) = 58.
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
      rewrite decode_encode_uint by exact bound_2.
      rewrite decode_encode_uint by exact bound_3.
      rewrite decode_encode_bytes by exact bound_4.
      rewrite decode_encode_uint by exact bound_5.
      rewrite decode_encode_uint by exact bound_6.
      rewrite decode_encode_bytes by exact bound_7.
      rewrite decode_encode_bytes by exact bound_8.
      rewrite decode_encode_uint by exact bound_9.
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

  End ComplexAddOrderMessage.

End IseOptionsSpreadOrdersV21Udp.
