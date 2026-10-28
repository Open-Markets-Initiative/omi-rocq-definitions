From Stdlib Require Import List.
From Stdlib Require Import NArith.
From Stdlib Require Import Lia.
From Stdlib Require Import Strings.Byte.
From Omi Require Import Wire.

Import ListNotations.

(** * National Association of Securities Dealers Automated Quotations (Nasdaq) Ise Order Feed Market Data

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

Module IseOptionsOrderFeedV11.

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
      timestamp : N;
      event_code : list byte;
      current_year : N;
      current_month : N;
      current_day : N;
      version : N;
      sub_version : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (timestamp record < 256 ^ N.of_nat 6)%N /\
      Datatypes.length (event_code record) = 1 /\
      (current_year record < 256 ^ N.of_nat 2)%N /\
      (current_month record < 256 ^ N.of_nat 1)%N /\
      (current_day record < 256 ^ N.of_nat 1)%N /\
      (version record < 256 ^ N.of_nat 1)%N /\
      (sub_version record < 256 ^ N.of_nat 1)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 6 (timestamp record) ++
      encode_bytes 1 (event_code record) ++
      encode_uint 2 (current_year record) ++
      encode_uint 1 (current_month record) ++
      encode_uint 1 (current_day record) ++
      encode_uint 1 (version record) ++
      encode_uint 1 (sub_version record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 6 bytes with
      | None => None
      | Some (timestamp_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (event_code_value, bytes) =>
              match decode_uint 2 bytes with
              | None => None
              | Some (current_year_value, bytes) =>
                  match decode_uint 1 bytes with
                  | None => None
                  | Some (current_month_value, bytes) =>
                      match decode_uint 1 bytes with
                      | None => None
                      | Some (current_day_value, bytes) =>
                          match decode_uint 1 bytes with
                          | None => None
                          | Some (version_value, bytes) =>
                              match decode_uint 1 bytes with
                              | None => None
                              | Some (sub_version_value, bytes) =>
                                  Some ({| timestamp := timestamp_value; event_code := event_code_value; current_year := current_year_value; current_month := current_month_value; current_day := current_day_value; version := version_value; sub_version := sub_version_value |}, bytes)
                              end
                          end
                      end
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 13.
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
      rewrite decode_encode_bytes by exact bound_1.
      rewrite decode_encode_uint by exact bound_2.
      rewrite decode_encode_uint by exact bound_3.
      rewrite decode_encode_uint by exact bound_4.
      rewrite decode_encode_uint by exact bound_5.
      rewrite decode_encode_uint by exact bound_6.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End SystemEventMessage.

  Module OptionDirectoryMessage.

    (** At the start of each trading day, the options system disseminates directory messages for all symbols eligible for trading in the options system. *)
    Record t := {
      timestamp : N;
      option_id : N;
      security_symbol : list byte;
      expiration_year : N;
      expiration_month : N;
      expiration_day : N;
      strike_price : N;
      option_type : list byte;
      source : N;
      underlying_symbol : list byte;
      trading_type : list byte;
      contract_size : N;
      option_closing_type : list byte;
      tradable : list byte;
      mpv : list byte;
      closing_only : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (timestamp record < 256 ^ N.of_nat 6)%N /\
      (option_id record < 256 ^ N.of_nat 4)%N /\
      Datatypes.length (security_symbol record) = 6 /\
      (expiration_year record < 256 ^ N.of_nat 1)%N /\
      (expiration_month record < 256 ^ N.of_nat 1)%N /\
      (expiration_day record < 256 ^ N.of_nat 1)%N /\
      (strike_price record < 256 ^ N.of_nat 8)%N /\
      Datatypes.length (option_type record) = 1 /\
      (source record < 256 ^ N.of_nat 1)%N /\
      Datatypes.length (underlying_symbol record) = 13 /\
      Datatypes.length (trading_type record) = 1 /\
      (contract_size record < 256 ^ N.of_nat 2)%N /\
      Datatypes.length (option_closing_type record) = 1 /\
      Datatypes.length (tradable record) = 1 /\
      Datatypes.length (mpv record) = 1 /\
      Datatypes.length (closing_only record) = 1.

    Definition encode (record : t) : list byte :=
      encode_uint 6 (timestamp record) ++
      encode_uint 4 (option_id record) ++
      encode_bytes 6 (security_symbol record) ++
      encode_uint 1 (expiration_year record) ++
      encode_uint 1 (expiration_month record) ++
      encode_uint 1 (expiration_day record) ++
      encode_uint 8 (strike_price record) ++
      encode_bytes 1 (option_type record) ++
      encode_uint 1 (source record) ++
      encode_bytes 13 (underlying_symbol record) ++
      encode_bytes 1 (trading_type record) ++
      encode_uint 2 (contract_size record) ++
      encode_bytes 1 (option_closing_type record) ++
      encode_bytes 1 (tradable record) ++
      encode_bytes 1 (mpv record) ++
      encode_bytes 1 (closing_only record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 6 bytes with
      | None => None
      | Some (timestamp_value, bytes) =>
          match decode_uint 4 bytes with
          | None => None
          | Some (option_id_value, bytes) =>
              match decode_bytes 6 bytes with
              | None => None
              | Some (security_symbol_value, bytes) =>
                  match decode_uint 1 bytes with
                  | None => None
                  | Some (expiration_year_value, bytes) =>
                      match decode_uint 1 bytes with
                      | None => None
                      | Some (expiration_month_value, bytes) =>
                          match decode_uint 1 bytes with
                          | None => None
                          | Some (expiration_day_value, bytes) =>
                              match decode_uint 8 bytes with
                              | None => None
                              | Some (strike_price_value, bytes) =>
                                  match decode_bytes 1 bytes with
                                  | None => None
                                  | Some (option_type_value, bytes) =>
                                      match decode_uint 1 bytes with
                                      | None => None
                                      | Some (source_value, bytes) =>
                                          match decode_bytes 13 bytes with
                                          | None => None
                                          | Some (underlying_symbol_value, bytes) =>
                                              match decode_bytes 1 bytes with
                                              | None => None
                                              | Some (trading_type_value, bytes) =>
                                                  match decode_uint 2 bytes with
                                                  | None => None
                                                  | Some (contract_size_value, bytes) =>
                                                      match decode_bytes 1 bytes with
                                                      | None => None
                                                      | Some (option_closing_type_value, bytes) =>
                                                          match decode_bytes 1 bytes with
                                                          | None => None
                                                          | Some (tradable_value, bytes) =>
                                                              match decode_bytes 1 bytes with
                                                              | None => None
                                                              | Some (mpv_value, bytes) =>
                                                                  match decode_bytes 1 bytes with
                                                                  | None => None
                                                                  | Some (closing_only_value, bytes) =>
                                                                      Some ({| timestamp := timestamp_value; option_id := option_id_value; security_symbol := security_symbol_value; expiration_year := expiration_year_value; expiration_month := expiration_month_value; expiration_day := expiration_day_value; strike_price := strike_price_value; option_type := option_type_value; source := source_value; underlying_symbol := underlying_symbol_value; trading_type := trading_type_value; contract_size := contract_size_value; option_closing_type := option_closing_type_value; tradable := tradable_value; mpv := mpv_value; closing_only := closing_only_value |}, bytes)
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

    Theorem encode_length : forall record, Datatypes.length (encode record) = 49.
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
      rewrite decode_encode_uint by exact bound_3.
      rewrite decode_encode_uint by exact bound_4.
      rewrite decode_encode_uint by exact bound_5.
      rewrite decode_encode_uint by exact bound_6.
      rewrite decode_encode_bytes by exact bound_7.
      rewrite decode_encode_uint by exact bound_8.
      rewrite decode_encode_bytes by exact bound_9.
      rewrite decode_encode_bytes by exact bound_10.
      rewrite decode_encode_uint by exact bound_11.
      rewrite decode_encode_bytes by exact bound_12.
      rewrite decode_encode_bytes by exact bound_13.
      rewrite decode_encode_bytes by exact bound_14.
      rewrite decode_encode_bytes by exact bound_15.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End OptionDirectoryMessage.

  Module TradingActionMessage.

    (** The options system uses this administrative message to indicate the current trading status of an index or equity option within the options market. *)
    Record t := {
      timestamp : N;
      option_id : N;
      current_trading_state : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (timestamp record < 256 ^ N.of_nat 6)%N /\
      (option_id record < 256 ^ N.of_nat 4)%N /\
      Datatypes.length (current_trading_state record) = 1.

    Definition encode (record : t) : list byte :=
      encode_uint 6 (timestamp record) ++
      encode_uint 4 (option_id record) ++
      encode_bytes 1 (current_trading_state record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 6 bytes with
      | None => None
      | Some (timestamp_value, bytes) =>
          match decode_uint 4 bytes with
          | None => None
          | Some (option_id_value, bytes) =>
              match decode_bytes 1 bytes with
              | None => None
              | Some (current_trading_state_value, bytes) =>
                  Some ({| timestamp := timestamp_value; option_id := option_id_value; current_trading_state := current_trading_state_value |}, bytes)
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

  End TradingActionMessage.

  Module SecurityOpenClosedMessage.

    (** The options system uses this administrative message to indicate when an option has completed the opening process and is now available for auto execution or when the option has closed and is no longer available for auto execution. *)
    Record t := {
      timestamp : N;
      option_id : N;
      open_state : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (timestamp record < 256 ^ N.of_nat 6)%N /\
      (option_id record < 256 ^ N.of_nat 4)%N /\
      Datatypes.length (open_state record) = 1.

    Definition encode (record : t) : list byte :=
      encode_uint 6 (timestamp record) ++
      encode_uint 4 (option_id record) ++
      encode_bytes 1 (open_state record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 6 bytes with
      | None => None
      | Some (timestamp_value, bytes) =>
          match decode_uint 4 bytes with
          | None => None
          | Some (option_id_value, bytes) =>
              match decode_bytes 1 bytes with
              | None => None
              | Some (open_state_value, bytes) =>
                  Some ({| timestamp := timestamp_value; option_id := option_id_value; open_state := open_state_value |}, bytes)
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

  End SecurityOpenClosedMessage.

  Module OpeningImbalanceMessage.

    (** Nasdaq disseminates Opening Imbalance information at regular intervals in the time leading up to the Nasdaq Opening Auction events. *)
    Record t := {
      timestamp : N;
      option_id : N;
      paired_contracts : N;
      imbalance_direction : list byte;
      imbalance_price : N;
      imbalance_volume : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (timestamp record < 256 ^ N.of_nat 6)%N /\
      (option_id record < 256 ^ N.of_nat 4)%N /\
      (paired_contracts record < 256 ^ N.of_nat 4)%N /\
      Datatypes.length (imbalance_direction record) = 1 /\
      (imbalance_price record < 256 ^ N.of_nat 4)%N /\
      (imbalance_volume record < 256 ^ N.of_nat 4)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 6 (timestamp record) ++
      encode_uint 4 (option_id record) ++
      encode_uint 4 (paired_contracts record) ++
      encode_bytes 1 (imbalance_direction record) ++
      encode_uint 4 (imbalance_price record) ++
      encode_uint 4 (imbalance_volume record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 6 bytes with
      | None => None
      | Some (timestamp_value, bytes) =>
          match decode_uint 4 bytes with
          | None => None
          | Some (option_id_value, bytes) =>
              match decode_uint 4 bytes with
              | None => None
              | Some (paired_contracts_value, bytes) =>
                  match decode_bytes 1 bytes with
                  | None => None
                  | Some (imbalance_direction_value, bytes) =>
                      match decode_uint 4 bytes with
                      | None => None
                      | Some (imbalance_price_value, bytes) =>
                          match decode_uint 4 bytes with
                          | None => None
                          | Some (imbalance_volume_value, bytes) =>
                              Some ({| timestamp := timestamp_value; option_id := option_id_value; paired_contracts := paired_contracts_value; imbalance_direction := imbalance_direction_value; imbalance_price := imbalance_price_value; imbalance_volume := imbalance_volume_value |}, bytes)
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
      rewrite decode_encode_uint by exact bound_1.
      rewrite decode_encode_uint by exact bound_2.
      rewrite decode_encode_bytes by exact bound_3.
      rewrite decode_encode_uint by exact bound_4.
      rewrite decode_encode_uint by exact bound_5.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End OpeningImbalanceMessage.

  Module OrderOnBookMessage.

    (** An Order on Book message is generated for all the following situations whenever an order free from any display restrictions is reported by the matching engine. *)
    Record t := {
      timestamp : N;
      option_id : N;
      order_type : list byte;
      side : list byte;
      price : N;
      size : N;
      exec_flag : list byte;
      order_capacity : list byte;
      owner_id : list byte;
      giveup : list byte;
      cmta : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (timestamp record < 256 ^ N.of_nat 6)%N /\
      (option_id record < 256 ^ N.of_nat 4)%N /\
      Datatypes.length (order_type record) = 1 /\
      Datatypes.length (side record) = 1 /\
      (price record < 256 ^ N.of_nat 4)%N /\
      (size record < 256 ^ N.of_nat 4)%N /\
      Datatypes.length (exec_flag record) = 1 /\
      Datatypes.length (order_capacity record) = 1 /\
      Datatypes.length (owner_id record) = 6 /\
      Datatypes.length (giveup record) = 6 /\
      Datatypes.length (cmta record) = 6.

    Definition encode (record : t) : list byte :=
      encode_uint 6 (timestamp record) ++
      encode_uint 4 (option_id record) ++
      encode_bytes 1 (order_type record) ++
      encode_bytes 1 (side record) ++
      encode_uint 4 (price record) ++
      encode_uint 4 (size record) ++
      encode_bytes 1 (exec_flag record) ++
      encode_bytes 1 (order_capacity record) ++
      encode_bytes 6 (owner_id record) ++
      encode_bytes 6 (giveup record) ++
      encode_bytes 6 (cmta record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 6 bytes with
      | None => None
      | Some (timestamp_value, bytes) =>
          match decode_uint 4 bytes with
          | None => None
          | Some (option_id_value, bytes) =>
              match decode_bytes 1 bytes with
              | None => None
              | Some (order_type_value, bytes) =>
                  match decode_bytes 1 bytes with
                  | None => None
                  | Some (side_value, bytes) =>
                      match decode_uint 4 bytes with
                      | None => None
                      | Some (price_value, bytes) =>
                          match decode_uint 4 bytes with
                          | None => None
                          | Some (size_value, bytes) =>
                              match decode_bytes 1 bytes with
                              | None => None
                              | Some (exec_flag_value, bytes) =>
                                  match decode_bytes 1 bytes with
                                  | None => None
                                  | Some (order_capacity_value, bytes) =>
                                      match decode_bytes 6 bytes with
                                      | None => None
                                      | Some (owner_id_value, bytes) =>
                                          match decode_bytes 6 bytes with
                                          | None => None
                                          | Some (giveup_value, bytes) =>
                                              match decode_bytes 6 bytes with
                                              | None => None
                                              | Some (cmta_value, bytes) =>
                                                  Some ({| timestamp := timestamp_value; option_id := option_id_value; order_type := order_type_value; side := side_value; price := price_value; size := size_value; exec_flag := exec_flag_value; order_capacity := order_capacity_value; owner_id := owner_id_value; giveup := giveup_value; cmta := cmta_value |}, bytes)
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

    Theorem encode_length : forall record, Datatypes.length (encode record) = 40.
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
      rewrite decode_encode_uint by exact bound_1.
      rewrite decode_encode_bytes by exact bound_2.
      rewrite decode_encode_bytes by exact bound_3.
      rewrite decode_encode_uint by exact bound_4.
      rewrite decode_encode_uint by exact bound_5.
      rewrite decode_encode_bytes by exact bound_6.
      rewrite decode_encode_bytes by exact bound_7.
      rewrite decode_encode_bytes by exact bound_8.
      rewrite decode_encode_bytes by exact bound_9.
      rewrite decode_encode_bytes by exact bound_10.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End OrderOnBookMessage.

End IseOptionsOrderFeedV11.
