From Stdlib Require Import List.
From Stdlib Require Import NArith.
From Stdlib Require Import Lia.
From Stdlib Require Import Strings.Byte.
From Omi Require Import Wire.

Import ListNotations.

(** * New York Stock Exchange 

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
      - a Composite rule
      - a run filling what frames it
  *)

Module NyseOptionsDeepFeedV13A.

  Module MessageHeader.

    Record t := {
      message_size : N;
      message_type : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (message_size record < 256 ^ N.of_nat 2)%N /\
      (message_type record < 256 ^ N.of_nat 2)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 2 (message_size record) ++
      encode_uint 2 (message_type record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 2 bytes with
      | None => None
      | Some (message_size_value, bytes) =>
          match decode_uint 2 bytes with
          | None => None
          | Some (message_type_value, bytes) =>
              Some ({| message_size := message_size_value; message_type := message_type_value |}, bytes)
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

  End MessageHeader.

  Module OutrightMarketDepthBuyMessage.

    (** The Buy Market Depth message provides prices and aggregated volumes for each of the best three Buy levels. *)
    Record t := {
      source_time : N;
      source_ns : N;
      series_index : N;
      symbol_seq_num : N;
      first_level_price : N;
      second_level_price : N;
      third_level_price : N;
      first_level_volume : N;
      second_level_volume : N;
      third_level_volume : N;
      quote_condition : list byte;
      reserved_1 : N;
      first_level_customer_volume : N;
      second_level_customer_volume : N;
      third_level_customer_volume : N;
      reserved_2 : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (source_time record < 256 ^ N.of_nat 4)%N /\
      (source_ns record < 256 ^ N.of_nat 4)%N /\
      (series_index record < 256 ^ N.of_nat 4)%N /\
      (symbol_seq_num record < 256 ^ N.of_nat 4)%N /\
      (first_level_price record < 256 ^ N.of_nat 4)%N /\
      (second_level_price record < 256 ^ N.of_nat 4)%N /\
      (third_level_price record < 256 ^ N.of_nat 4)%N /\
      (first_level_volume record < 256 ^ N.of_nat 2)%N /\
      (second_level_volume record < 256 ^ N.of_nat 2)%N /\
      (third_level_volume record < 256 ^ N.of_nat 2)%N /\
      Datatypes.length (quote_condition record) = 1 /\
      (reserved_1 record < 256 ^ N.of_nat 1)%N /\
      (first_level_customer_volume record < 256 ^ N.of_nat 2)%N /\
      (second_level_customer_volume record < 256 ^ N.of_nat 2)%N /\
      (third_level_customer_volume record < 256 ^ N.of_nat 2)%N /\
      (reserved_2 record < 256 ^ N.of_nat 2)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 4 (source_time record) ++
      encode_uint 4 (source_ns record) ++
      encode_uint 4 (series_index record) ++
      encode_uint 4 (symbol_seq_num record) ++
      encode_uint 4 (first_level_price record) ++
      encode_uint 4 (second_level_price record) ++
      encode_uint 4 (third_level_price record) ++
      encode_uint 2 (first_level_volume record) ++
      encode_uint 2 (second_level_volume record) ++
      encode_uint 2 (third_level_volume record) ++
      encode_bytes 1 (quote_condition record) ++
      encode_uint 1 (reserved_1 record) ++
      encode_uint 2 (first_level_customer_volume record) ++
      encode_uint 2 (second_level_customer_volume record) ++
      encode_uint 2 (third_level_customer_volume record) ++
      encode_uint 2 (reserved_2 record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 4 bytes with
      | None => None
      | Some (source_time_value, bytes) =>
          match decode_uint 4 bytes with
          | None => None
          | Some (source_ns_value, bytes) =>
              match decode_uint 4 bytes with
              | None => None
              | Some (series_index_value, bytes) =>
                  match decode_uint 4 bytes with
                  | None => None
                  | Some (symbol_seq_num_value, bytes) =>
                      match decode_uint 4 bytes with
                      | None => None
                      | Some (first_level_price_value, bytes) =>
                          match decode_uint 4 bytes with
                          | None => None
                          | Some (second_level_price_value, bytes) =>
                              match decode_uint 4 bytes with
                              | None => None
                              | Some (third_level_price_value, bytes) =>
                                  match decode_uint 2 bytes with
                                  | None => None
                                  | Some (first_level_volume_value, bytes) =>
                                      match decode_uint 2 bytes with
                                      | None => None
                                      | Some (second_level_volume_value, bytes) =>
                                          match decode_uint 2 bytes with
                                          | None => None
                                          | Some (third_level_volume_value, bytes) =>
                                              match decode_bytes 1 bytes with
                                              | None => None
                                              | Some (quote_condition_value, bytes) =>
                                                  match decode_uint 1 bytes with
                                                  | None => None
                                                  | Some (reserved_1_value, bytes) =>
                                                      match decode_uint 2 bytes with
                                                      | None => None
                                                      | Some (first_level_customer_volume_value, bytes) =>
                                                          match decode_uint 2 bytes with
                                                          | None => None
                                                          | Some (second_level_customer_volume_value, bytes) =>
                                                              match decode_uint 2 bytes with
                                                              | None => None
                                                              | Some (third_level_customer_volume_value, bytes) =>
                                                                  match decode_uint 2 bytes with
                                                                  | None => None
                                                                  | Some (reserved_2_value, bytes) =>
                                                                      Some ({| source_time := source_time_value; source_ns := source_ns_value; series_index := series_index_value; symbol_seq_num := symbol_seq_num_value; first_level_price := first_level_price_value; second_level_price := second_level_price_value; third_level_price := third_level_price_value; first_level_volume := first_level_volume_value; second_level_volume := second_level_volume_value; third_level_volume := third_level_volume_value; quote_condition := quote_condition_value; reserved_1 := reserved_1_value; first_level_customer_volume := first_level_customer_volume_value; second_level_customer_volume := second_level_customer_volume_value; third_level_customer_volume := third_level_customer_volume_value; reserved_2 := reserved_2_value |}, bytes)
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

    Theorem encode_length : forall record, Datatypes.length (encode record) = 44.
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
      rewrite decode_encode_uint by exact bound_4.
      rewrite decode_encode_uint by exact bound_5.
      rewrite decode_encode_uint by exact bound_6.
      rewrite decode_encode_uint by exact bound_7.
      rewrite decode_encode_uint by exact bound_8.
      rewrite decode_encode_uint by exact bound_9.
      rewrite decode_encode_bytes by exact bound_10.
      rewrite decode_encode_uint by exact bound_11.
      rewrite decode_encode_uint by exact bound_12.
      rewrite decode_encode_uint by exact bound_13.
      rewrite decode_encode_uint by exact bound_14.
      rewrite decode_encode_uint by exact bound_15.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End OutrightMarketDepthBuyMessage.

  Module OutrightMarketDepthSellMessage.

    (** The Sell Market Depth message provides prices and aggregated volumes for each of the best three Sell levels. *)
    Record t := {
      source_time : N;
      source_ns : N;
      series_index : N;
      symbol_seq_num : N;
      first_level_price : N;
      second_level_price : N;
      third_level_price : N;
      first_volume : N;
      second_volume : N;
      third_volume : N;
      quote_condition : list byte;
      reserved_1 : N;
      first_level_customer_volume : N;
      second_level_customer_volume : N;
      third_level_customer_volume : N;
      reserved_2 : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (source_time record < 256 ^ N.of_nat 4)%N /\
      (source_ns record < 256 ^ N.of_nat 4)%N /\
      (series_index record < 256 ^ N.of_nat 4)%N /\
      (symbol_seq_num record < 256 ^ N.of_nat 4)%N /\
      (first_level_price record < 256 ^ N.of_nat 4)%N /\
      (second_level_price record < 256 ^ N.of_nat 4)%N /\
      (third_level_price record < 256 ^ N.of_nat 4)%N /\
      (first_volume record < 256 ^ N.of_nat 2)%N /\
      (second_volume record < 256 ^ N.of_nat 2)%N /\
      (third_volume record < 256 ^ N.of_nat 2)%N /\
      Datatypes.length (quote_condition record) = 1 /\
      (reserved_1 record < 256 ^ N.of_nat 1)%N /\
      (first_level_customer_volume record < 256 ^ N.of_nat 2)%N /\
      (second_level_customer_volume record < 256 ^ N.of_nat 2)%N /\
      (third_level_customer_volume record < 256 ^ N.of_nat 2)%N /\
      (reserved_2 record < 256 ^ N.of_nat 2)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 4 (source_time record) ++
      encode_uint 4 (source_ns record) ++
      encode_uint 4 (series_index record) ++
      encode_uint 4 (symbol_seq_num record) ++
      encode_uint 4 (first_level_price record) ++
      encode_uint 4 (second_level_price record) ++
      encode_uint 4 (third_level_price record) ++
      encode_uint 2 (first_volume record) ++
      encode_uint 2 (second_volume record) ++
      encode_uint 2 (third_volume record) ++
      encode_bytes 1 (quote_condition record) ++
      encode_uint 1 (reserved_1 record) ++
      encode_uint 2 (first_level_customer_volume record) ++
      encode_uint 2 (second_level_customer_volume record) ++
      encode_uint 2 (third_level_customer_volume record) ++
      encode_uint 2 (reserved_2 record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 4 bytes with
      | None => None
      | Some (source_time_value, bytes) =>
          match decode_uint 4 bytes with
          | None => None
          | Some (source_ns_value, bytes) =>
              match decode_uint 4 bytes with
              | None => None
              | Some (series_index_value, bytes) =>
                  match decode_uint 4 bytes with
                  | None => None
                  | Some (symbol_seq_num_value, bytes) =>
                      match decode_uint 4 bytes with
                      | None => None
                      | Some (first_level_price_value, bytes) =>
                          match decode_uint 4 bytes with
                          | None => None
                          | Some (second_level_price_value, bytes) =>
                              match decode_uint 4 bytes with
                              | None => None
                              | Some (third_level_price_value, bytes) =>
                                  match decode_uint 2 bytes with
                                  | None => None
                                  | Some (first_volume_value, bytes) =>
                                      match decode_uint 2 bytes with
                                      | None => None
                                      | Some (second_volume_value, bytes) =>
                                          match decode_uint 2 bytes with
                                          | None => None
                                          | Some (third_volume_value, bytes) =>
                                              match decode_bytes 1 bytes with
                                              | None => None
                                              | Some (quote_condition_value, bytes) =>
                                                  match decode_uint 1 bytes with
                                                  | None => None
                                                  | Some (reserved_1_value, bytes) =>
                                                      match decode_uint 2 bytes with
                                                      | None => None
                                                      | Some (first_level_customer_volume_value, bytes) =>
                                                          match decode_uint 2 bytes with
                                                          | None => None
                                                          | Some (second_level_customer_volume_value, bytes) =>
                                                              match decode_uint 2 bytes with
                                                              | None => None
                                                              | Some (third_level_customer_volume_value, bytes) =>
                                                                  match decode_uint 2 bytes with
                                                                  | None => None
                                                                  | Some (reserved_2_value, bytes) =>
                                                                      Some ({| source_time := source_time_value; source_ns := source_ns_value; series_index := series_index_value; symbol_seq_num := symbol_seq_num_value; first_level_price := first_level_price_value; second_level_price := second_level_price_value; third_level_price := third_level_price_value; first_volume := first_volume_value; second_volume := second_volume_value; third_volume := third_volume_value; quote_condition := quote_condition_value; reserved_1 := reserved_1_value; first_level_customer_volume := first_level_customer_volume_value; second_level_customer_volume := second_level_customer_volume_value; third_level_customer_volume := third_level_customer_volume_value; reserved_2 := reserved_2_value |}, bytes)
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

    Theorem encode_length : forall record, Datatypes.length (encode record) = 44.
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
      rewrite decode_encode_uint by exact bound_4.
      rewrite decode_encode_uint by exact bound_5.
      rewrite decode_encode_uint by exact bound_6.
      rewrite decode_encode_uint by exact bound_7.
      rewrite decode_encode_uint by exact bound_8.
      rewrite decode_encode_uint by exact bound_9.
      rewrite decode_encode_bytes by exact bound_10.
      rewrite decode_encode_uint by exact bound_11.
      rewrite decode_encode_uint by exact bound_12.
      rewrite decode_encode_uint by exact bound_13.
      rewrite decode_encode_uint by exact bound_14.
      rewrite decode_encode_uint by exact bound_15.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End OutrightMarketDepthSellMessage.

  Module UnderlyingStatusMessage.

    (** The Underlying Status message is used to inform the subscribers of changes in the status of an Underlying symbol. *)
    Record t := {
      source_time : N;
      source_time_ns : N;
      underlying_index : N;
      underlying_seq_num : N;
      security_status : list byte;
      halt_condition : list byte;
      reserved_2 : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (source_time record < 256 ^ N.of_nat 4)%N /\
      (source_time_ns record < 256 ^ N.of_nat 4)%N /\
      (underlying_index record < 256 ^ N.of_nat 4)%N /\
      (underlying_seq_num record < 256 ^ N.of_nat 4)%N /\
      Datatypes.length (security_status record) = 1 /\
      Datatypes.length (halt_condition record) = 1 /\
      (reserved_2 record < 256 ^ N.of_nat 2)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 4 (source_time record) ++
      encode_uint 4 (source_time_ns record) ++
      encode_uint 4 (underlying_index record) ++
      encode_uint 4 (underlying_seq_num record) ++
      encode_bytes 1 (security_status record) ++
      encode_bytes 1 (halt_condition record) ++
      encode_uint 2 (reserved_2 record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 4 bytes with
      | None => None
      | Some (source_time_value, bytes) =>
          match decode_uint 4 bytes with
          | None => None
          | Some (source_time_ns_value, bytes) =>
              match decode_uint 4 bytes with
              | None => None
              | Some (underlying_index_value, bytes) =>
                  match decode_uint 4 bytes with
                  | None => None
                  | Some (underlying_seq_num_value, bytes) =>
                      match decode_bytes 1 bytes with
                      | None => None
                      | Some (security_status_value, bytes) =>
                          match decode_bytes 1 bytes with
                          | None => None
                          | Some (halt_condition_value, bytes) =>
                              match decode_uint 2 bytes with
                              | None => None
                              | Some (reserved_2_value, bytes) =>
                                  Some ({| source_time := source_time_value; source_time_ns := source_time_ns_value; underlying_index := underlying_index_value; underlying_seq_num := underlying_seq_num_value; security_status := security_status_value; halt_condition := halt_condition_value; reserved_2 := reserved_2_value |}, bytes)
                              end
                          end
                      end
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 20.
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
      rewrite decode_encode_bytes by exact bound_4.
      rewrite decode_encode_bytes by exact bound_5.
      rewrite decode_encode_uint by exact bound_6.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End UnderlyingStatusMessage.

  Module OutrightSeriesStatusMessage.

    (** The Series Status message is used to inform the subscribers of changes in symbol status of an outright symbol. *)
    Record t := {
      source_time : N;
      source_time_ns : N;
      series_index : N;
      symbol_seq_num : N;
      security_status : list byte;
      halt_condition : list byte;
      reserved_2 : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (source_time record < 256 ^ N.of_nat 4)%N /\
      (source_time_ns record < 256 ^ N.of_nat 4)%N /\
      (series_index record < 256 ^ N.of_nat 4)%N /\
      (symbol_seq_num record < 256 ^ N.of_nat 4)%N /\
      Datatypes.length (security_status record) = 1 /\
      Datatypes.length (halt_condition record) = 1 /\
      (reserved_2 record < 256 ^ N.of_nat 2)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 4 (source_time record) ++
      encode_uint 4 (source_time_ns record) ++
      encode_uint 4 (series_index record) ++
      encode_uint 4 (symbol_seq_num record) ++
      encode_bytes 1 (security_status record) ++
      encode_bytes 1 (halt_condition record) ++
      encode_uint 2 (reserved_2 record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 4 bytes with
      | None => None
      | Some (source_time_value, bytes) =>
          match decode_uint 4 bytes with
          | None => None
          | Some (source_time_ns_value, bytes) =>
              match decode_uint 4 bytes with
              | None => None
              | Some (series_index_value, bytes) =>
                  match decode_uint 4 bytes with
                  | None => None
                  | Some (symbol_seq_num_value, bytes) =>
                      match decode_bytes 1 bytes with
                      | None => None
                      | Some (security_status_value, bytes) =>
                          match decode_bytes 1 bytes with
                          | None => None
                          | Some (halt_condition_value, bytes) =>
                              match decode_uint 2 bytes with
                              | None => None
                              | Some (reserved_2_value, bytes) =>
                                  Some ({| source_time := source_time_value; source_time_ns := source_time_ns_value; series_index := series_index_value; symbol_seq_num := symbol_seq_num_value; security_status := security_status_value; halt_condition := halt_condition_value; reserved_2 := reserved_2_value |}, bytes)
                              end
                          end
                      end
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 20.
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
      rewrite decode_encode_bytes by exact bound_4.
      rewrite decode_encode_bytes by exact bound_5.
      rewrite decode_encode_uint by exact bound_6.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End OutrightSeriesStatusMessage.

  Module RefreshOutrightMarketDepthBuyMessage.

    (** The Refresh Market Depth Buy message is sent in the event no Buy Market Depth messages are published for the symbol for 2 consecutive minutes. *)
    Record t := {
      source_time : N;
      source_ns : N;
      series_index : N;
      symbol_seq_num : N;
      first_level_price : N;
      second_level_price : N;
      third_level_price : N;
      first_volume : N;
      second_volume : N;
      third_volume : N;
      quote_condition : list byte;
      reserved_1 : N;
      first_level_customer_volume : N;
      second_level_customer_volume : N;
      third_level_customer_volume : N;
      reserved_2 : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (source_time record < 256 ^ N.of_nat 4)%N /\
      (source_ns record < 256 ^ N.of_nat 4)%N /\
      (series_index record < 256 ^ N.of_nat 4)%N /\
      (symbol_seq_num record < 256 ^ N.of_nat 4)%N /\
      (first_level_price record < 256 ^ N.of_nat 4)%N /\
      (second_level_price record < 256 ^ N.of_nat 4)%N /\
      (third_level_price record < 256 ^ N.of_nat 4)%N /\
      (first_volume record < 256 ^ N.of_nat 2)%N /\
      (second_volume record < 256 ^ N.of_nat 2)%N /\
      (third_volume record < 256 ^ N.of_nat 2)%N /\
      Datatypes.length (quote_condition record) = 1 /\
      (reserved_1 record < 256 ^ N.of_nat 1)%N /\
      (first_level_customer_volume record < 256 ^ N.of_nat 2)%N /\
      (second_level_customer_volume record < 256 ^ N.of_nat 2)%N /\
      (third_level_customer_volume record < 256 ^ N.of_nat 2)%N /\
      (reserved_2 record < 256 ^ N.of_nat 2)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 4 (source_time record) ++
      encode_uint 4 (source_ns record) ++
      encode_uint 4 (series_index record) ++
      encode_uint 4 (symbol_seq_num record) ++
      encode_uint 4 (first_level_price record) ++
      encode_uint 4 (second_level_price record) ++
      encode_uint 4 (third_level_price record) ++
      encode_uint 2 (first_volume record) ++
      encode_uint 2 (second_volume record) ++
      encode_uint 2 (third_volume record) ++
      encode_bytes 1 (quote_condition record) ++
      encode_uint 1 (reserved_1 record) ++
      encode_uint 2 (first_level_customer_volume record) ++
      encode_uint 2 (second_level_customer_volume record) ++
      encode_uint 2 (third_level_customer_volume record) ++
      encode_uint 2 (reserved_2 record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 4 bytes with
      | None => None
      | Some (source_time_value, bytes) =>
          match decode_uint 4 bytes with
          | None => None
          | Some (source_ns_value, bytes) =>
              match decode_uint 4 bytes with
              | None => None
              | Some (series_index_value, bytes) =>
                  match decode_uint 4 bytes with
                  | None => None
                  | Some (symbol_seq_num_value, bytes) =>
                      match decode_uint 4 bytes with
                      | None => None
                      | Some (first_level_price_value, bytes) =>
                          match decode_uint 4 bytes with
                          | None => None
                          | Some (second_level_price_value, bytes) =>
                              match decode_uint 4 bytes with
                              | None => None
                              | Some (third_level_price_value, bytes) =>
                                  match decode_uint 2 bytes with
                                  | None => None
                                  | Some (first_volume_value, bytes) =>
                                      match decode_uint 2 bytes with
                                      | None => None
                                      | Some (second_volume_value, bytes) =>
                                          match decode_uint 2 bytes with
                                          | None => None
                                          | Some (third_volume_value, bytes) =>
                                              match decode_bytes 1 bytes with
                                              | None => None
                                              | Some (quote_condition_value, bytes) =>
                                                  match decode_uint 1 bytes with
                                                  | None => None
                                                  | Some (reserved_1_value, bytes) =>
                                                      match decode_uint 2 bytes with
                                                      | None => None
                                                      | Some (first_level_customer_volume_value, bytes) =>
                                                          match decode_uint 2 bytes with
                                                          | None => None
                                                          | Some (second_level_customer_volume_value, bytes) =>
                                                              match decode_uint 2 bytes with
                                                              | None => None
                                                              | Some (third_level_customer_volume_value, bytes) =>
                                                                  match decode_uint 2 bytes with
                                                                  | None => None
                                                                  | Some (reserved_2_value, bytes) =>
                                                                      Some ({| source_time := source_time_value; source_ns := source_ns_value; series_index := series_index_value; symbol_seq_num := symbol_seq_num_value; first_level_price := first_level_price_value; second_level_price := second_level_price_value; third_level_price := third_level_price_value; first_volume := first_volume_value; second_volume := second_volume_value; third_volume := third_volume_value; quote_condition := quote_condition_value; reserved_1 := reserved_1_value; first_level_customer_volume := first_level_customer_volume_value; second_level_customer_volume := second_level_customer_volume_value; third_level_customer_volume := third_level_customer_volume_value; reserved_2 := reserved_2_value |}, bytes)
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

    Theorem encode_length : forall record, Datatypes.length (encode record) = 44.
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
      rewrite decode_encode_uint by exact bound_4.
      rewrite decode_encode_uint by exact bound_5.
      rewrite decode_encode_uint by exact bound_6.
      rewrite decode_encode_uint by exact bound_7.
      rewrite decode_encode_uint by exact bound_8.
      rewrite decode_encode_uint by exact bound_9.
      rewrite decode_encode_bytes by exact bound_10.
      rewrite decode_encode_uint by exact bound_11.
      rewrite decode_encode_uint by exact bound_12.
      rewrite decode_encode_uint by exact bound_13.
      rewrite decode_encode_uint by exact bound_14.
      rewrite decode_encode_uint by exact bound_15.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End RefreshOutrightMarketDepthBuyMessage.

  Module RefreshOutrightMarketDepthSellMessage.

    (** The Refresh Market Depth Sell message is sent in the event no Sell Market Depth messages are published for the symbol for 2 consecutive minutes. *)
    Record t := {
      source_time : N;
      source_time_ns : N;
      series_index : N;
      symbol_seq_num : N;
      first_level_price : N;
      second_level_price : N;
      third_level_price : N;
      first_volume : N;
      second_volume : N;
      third_volume : N;
      quote_condition : list byte;
      reserved_1 : N;
      first_level_customer_volume : N;
      second_level_customer_volume : N;
      third_level_customer_volume : N;
      reserved_2 : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (source_time record < 256 ^ N.of_nat 4)%N /\
      (source_time_ns record < 256 ^ N.of_nat 4)%N /\
      (series_index record < 256 ^ N.of_nat 4)%N /\
      (symbol_seq_num record < 256 ^ N.of_nat 4)%N /\
      (first_level_price record < 256 ^ N.of_nat 4)%N /\
      (second_level_price record < 256 ^ N.of_nat 4)%N /\
      (third_level_price record < 256 ^ N.of_nat 4)%N /\
      (first_volume record < 256 ^ N.of_nat 2)%N /\
      (second_volume record < 256 ^ N.of_nat 2)%N /\
      (third_volume record < 256 ^ N.of_nat 2)%N /\
      Datatypes.length (quote_condition record) = 1 /\
      (reserved_1 record < 256 ^ N.of_nat 1)%N /\
      (first_level_customer_volume record < 256 ^ N.of_nat 2)%N /\
      (second_level_customer_volume record < 256 ^ N.of_nat 2)%N /\
      (third_level_customer_volume record < 256 ^ N.of_nat 2)%N /\
      (reserved_2 record < 256 ^ N.of_nat 2)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 4 (source_time record) ++
      encode_uint 4 (source_time_ns record) ++
      encode_uint 4 (series_index record) ++
      encode_uint 4 (symbol_seq_num record) ++
      encode_uint 4 (first_level_price record) ++
      encode_uint 4 (second_level_price record) ++
      encode_uint 4 (third_level_price record) ++
      encode_uint 2 (first_volume record) ++
      encode_uint 2 (second_volume record) ++
      encode_uint 2 (third_volume record) ++
      encode_bytes 1 (quote_condition record) ++
      encode_uint 1 (reserved_1 record) ++
      encode_uint 2 (first_level_customer_volume record) ++
      encode_uint 2 (second_level_customer_volume record) ++
      encode_uint 2 (third_level_customer_volume record) ++
      encode_uint 2 (reserved_2 record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 4 bytes with
      | None => None
      | Some (source_time_value, bytes) =>
          match decode_uint 4 bytes with
          | None => None
          | Some (source_time_ns_value, bytes) =>
              match decode_uint 4 bytes with
              | None => None
              | Some (series_index_value, bytes) =>
                  match decode_uint 4 bytes with
                  | None => None
                  | Some (symbol_seq_num_value, bytes) =>
                      match decode_uint 4 bytes with
                      | None => None
                      | Some (first_level_price_value, bytes) =>
                          match decode_uint 4 bytes with
                          | None => None
                          | Some (second_level_price_value, bytes) =>
                              match decode_uint 4 bytes with
                              | None => None
                              | Some (third_level_price_value, bytes) =>
                                  match decode_uint 2 bytes with
                                  | None => None
                                  | Some (first_volume_value, bytes) =>
                                      match decode_uint 2 bytes with
                                      | None => None
                                      | Some (second_volume_value, bytes) =>
                                          match decode_uint 2 bytes with
                                          | None => None
                                          | Some (third_volume_value, bytes) =>
                                              match decode_bytes 1 bytes with
                                              | None => None
                                              | Some (quote_condition_value, bytes) =>
                                                  match decode_uint 1 bytes with
                                                  | None => None
                                                  | Some (reserved_1_value, bytes) =>
                                                      match decode_uint 2 bytes with
                                                      | None => None
                                                      | Some (first_level_customer_volume_value, bytes) =>
                                                          match decode_uint 2 bytes with
                                                          | None => None
                                                          | Some (second_level_customer_volume_value, bytes) =>
                                                              match decode_uint 2 bytes with
                                                              | None => None
                                                              | Some (third_level_customer_volume_value, bytes) =>
                                                                  match decode_uint 2 bytes with
                                                                  | None => None
                                                                  | Some (reserved_2_value, bytes) =>
                                                                      Some ({| source_time := source_time_value; source_time_ns := source_time_ns_value; series_index := series_index_value; symbol_seq_num := symbol_seq_num_value; first_level_price := first_level_price_value; second_level_price := second_level_price_value; third_level_price := third_level_price_value; first_volume := first_volume_value; second_volume := second_volume_value; third_volume := third_volume_value; quote_condition := quote_condition_value; reserved_1 := reserved_1_value; first_level_customer_volume := first_level_customer_volume_value; second_level_customer_volume := second_level_customer_volume_value; third_level_customer_volume := third_level_customer_volume_value; reserved_2 := reserved_2_value |}, bytes)
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

    Theorem encode_length : forall record, Datatypes.length (encode record) = 44.
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
      rewrite decode_encode_uint by exact bound_4.
      rewrite decode_encode_uint by exact bound_5.
      rewrite decode_encode_uint by exact bound_6.
      rewrite decode_encode_uint by exact bound_7.
      rewrite decode_encode_uint by exact bound_8.
      rewrite decode_encode_uint by exact bound_9.
      rewrite decode_encode_bytes by exact bound_10.
      rewrite decode_encode_uint by exact bound_11.
      rewrite decode_encode_uint by exact bound_12.
      rewrite decode_encode_uint by exact bound_13.
      rewrite decode_encode_uint by exact bound_14.
      rewrite decode_encode_uint by exact bound_15.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End RefreshOutrightMarketDepthSellMessage.

  Module UnderlyingIndexMappingMessage.

    (** On system startup, each multicast channel sends all the symbols on its channel. Underlying Index Mapping messages are published first, followed by all Series Index Mapping messages, and for the Complex feed, Complex Symbol Definitions last of all. *)
    Record t := {
      underlying_index : N;
      underlying_symbol : list byte;
      channel_id : N;
      market_id : N;
      system_id : N;
      exchange_code : list byte;
      price_scale_code : N;
      security_type : list byte;
      price_resolution : N;
      reserved_1 : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (underlying_index record < 256 ^ N.of_nat 4)%N /\
      Datatypes.length (underlying_symbol record) = 11 /\
      (channel_id record < 256 ^ N.of_nat 1)%N /\
      (market_id record < 256 ^ N.of_nat 2)%N /\
      (system_id record < 256 ^ N.of_nat 1)%N /\
      Datatypes.length (exchange_code record) = 1 /\
      (price_scale_code record < 256 ^ N.of_nat 1)%N /\
      Datatypes.length (security_type record) = 1 /\
      (price_resolution record < 256 ^ N.of_nat 1)%N /\
      (reserved_1 record < 256 ^ N.of_nat 1)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 4 (underlying_index record) ++
      encode_bytes 11 (underlying_symbol record) ++
      encode_uint 1 (channel_id record) ++
      encode_uint 2 (market_id record) ++
      encode_uint 1 (system_id record) ++
      encode_bytes 1 (exchange_code record) ++
      encode_uint 1 (price_scale_code record) ++
      encode_bytes 1 (security_type record) ++
      encode_uint 1 (price_resolution record) ++
      encode_uint 1 (reserved_1 record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 4 bytes with
      | None => None
      | Some (underlying_index_value, bytes) =>
          match decode_bytes 11 bytes with
          | None => None
          | Some (underlying_symbol_value, bytes) =>
              match decode_uint 1 bytes with
              | None => None
              | Some (channel_id_value, bytes) =>
                  match decode_uint 2 bytes with
                  | None => None
                  | Some (market_id_value, bytes) =>
                      match decode_uint 1 bytes with
                      | None => None
                      | Some (system_id_value, bytes) =>
                          match decode_bytes 1 bytes with
                          | None => None
                          | Some (exchange_code_value, bytes) =>
                              match decode_uint 1 bytes with
                              | None => None
                              | Some (price_scale_code_value, bytes) =>
                                  match decode_bytes 1 bytes with
                                  | None => None
                                  | Some (security_type_value, bytes) =>
                                      match decode_uint 1 bytes with
                                      | None => None
                                      | Some (price_resolution_value, bytes) =>
                                          match decode_uint 1 bytes with
                                          | None => None
                                          | Some (reserved_1_value, bytes) =>
                                              Some ({| underlying_index := underlying_index_value; underlying_symbol := underlying_symbol_value; channel_id := channel_id_value; market_id := market_id_value; system_id := system_id_value; exchange_code := exchange_code_value; price_scale_code := price_scale_code_value; security_type := security_type_value; price_resolution := price_resolution_value; reserved_1 := reserved_1_value |}, bytes)
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

    Theorem encode_length : forall record, Datatypes.length (encode record) = 24.
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
      rewrite decode_encode_bytes by exact bound_1.
      rewrite decode_encode_uint by exact bound_2.
      rewrite decode_encode_uint by exact bound_3.
      rewrite decode_encode_uint by exact bound_4.
      rewrite decode_encode_bytes by exact bound_5.
      rewrite decode_encode_uint by exact bound_6.
      rewrite decode_encode_bytes by exact bound_7.
      rewrite decode_encode_uint by exact bound_8.
      rewrite decode_encode_uint by exact bound_9.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End UnderlyingIndexMappingMessage.

  Module SeriesIndexMappingMessage.

    (** On system startup, each multicast channel sends all the symbols on its channel. Underlying Index Mapping messages are published first, followed by all Series Index Mapping messages, and for the Complex feed, Complex Symbol Definitions last of all. *)
    Record t := {
      series_index : N;
      channel_id : N;
      reserved_a_1 : N;
      market_id : N;
      system_id : N;
      reserved_b_1 : N;
      stream_id : N;
      underlying_index : N;
      contract_multiplier : N;
      maturity_date : list byte;
      put_or_call : N;
      strike_price : list byte;
      price_scale_code : N;
      underlying_symbol : list byte;
      option_symbol_root : list byte;
      group_id : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (series_index record < 256 ^ N.of_nat 4)%N /\
      (channel_id record < 256 ^ N.of_nat 1)%N /\
      (reserved_a_1 record < 256 ^ N.of_nat 1)%N /\
      (market_id record < 256 ^ N.of_nat 2)%N /\
      (system_id record < 256 ^ N.of_nat 1)%N /\
      (reserved_b_1 record < 256 ^ N.of_nat 1)%N /\
      (stream_id record < 256 ^ N.of_nat 2)%N /\
      (underlying_index record < 256 ^ N.of_nat 4)%N /\
      (contract_multiplier record < 256 ^ N.of_nat 2)%N /\
      Datatypes.length (maturity_date record) = 6 /\
      (put_or_call record < 256 ^ N.of_nat 1)%N /\
      Datatypes.length (strike_price record) = 10 /\
      (price_scale_code record < 256 ^ N.of_nat 1)%N /\
      Datatypes.length (underlying_symbol record) = 11 /\
      Datatypes.length (option_symbol_root record) = 5 /\
      (group_id record < 256 ^ N.of_nat 4)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 4 (series_index record) ++
      encode_uint 1 (channel_id record) ++
      encode_uint 1 (reserved_a_1 record) ++
      encode_uint 2 (market_id record) ++
      encode_uint 1 (system_id record) ++
      encode_uint 1 (reserved_b_1 record) ++
      encode_uint 2 (stream_id record) ++
      encode_uint 4 (underlying_index record) ++
      encode_uint 2 (contract_multiplier record) ++
      encode_bytes 6 (maturity_date record) ++
      encode_uint 1 (put_or_call record) ++
      encode_bytes 10 (strike_price record) ++
      encode_uint 1 (price_scale_code record) ++
      encode_bytes 11 (underlying_symbol record) ++
      encode_bytes 5 (option_symbol_root record) ++
      encode_uint 4 (group_id record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 4 bytes with
      | None => None
      | Some (series_index_value, bytes) =>
          match decode_uint 1 bytes with
          | None => None
          | Some (channel_id_value, bytes) =>
              match decode_uint 1 bytes with
              | None => None
              | Some (reserved_a_1_value, bytes) =>
                  match decode_uint 2 bytes with
                  | None => None
                  | Some (market_id_value, bytes) =>
                      match decode_uint 1 bytes with
                      | None => None
                      | Some (system_id_value, bytes) =>
                          match decode_uint 1 bytes with
                          | None => None
                          | Some (reserved_b_1_value, bytes) =>
                              match decode_uint 2 bytes with
                              | None => None
                              | Some (stream_id_value, bytes) =>
                                  match decode_uint 4 bytes with
                                  | None => None
                                  | Some (underlying_index_value, bytes) =>
                                      match decode_uint 2 bytes with
                                      | None => None
                                      | Some (contract_multiplier_value, bytes) =>
                                          match decode_bytes 6 bytes with
                                          | None => None
                                          | Some (maturity_date_value, bytes) =>
                                              match decode_uint 1 bytes with
                                              | None => None
                                              | Some (put_or_call_value, bytes) =>
                                                  match decode_bytes 10 bytes with
                                                  | None => None
                                                  | Some (strike_price_value, bytes) =>
                                                      match decode_uint 1 bytes with
                                                      | None => None
                                                      | Some (price_scale_code_value, bytes) =>
                                                          match decode_bytes 11 bytes with
                                                          | None => None
                                                          | Some (underlying_symbol_value, bytes) =>
                                                              match decode_bytes 5 bytes with
                                                              | None => None
                                                              | Some (option_symbol_root_value, bytes) =>
                                                                  match decode_uint 4 bytes with
                                                                  | None => None
                                                                  | Some (group_id_value, bytes) =>
                                                                      Some ({| series_index := series_index_value; channel_id := channel_id_value; reserved_a_1 := reserved_a_1_value; market_id := market_id_value; system_id := system_id_value; reserved_b_1 := reserved_b_1_value; stream_id := stream_id_value; underlying_index := underlying_index_value; contract_multiplier := contract_multiplier_value; maturity_date := maturity_date_value; put_or_call := put_or_call_value; strike_price := strike_price_value; price_scale_code := price_scale_code_value; underlying_symbol := underlying_symbol_value; option_symbol_root := option_symbol_root_value; group_id := group_id_value |}, bytes)
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

    Theorem encode_length : forall record, Datatypes.length (encode record) = 56.
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
      rewrite decode_encode_uint by exact bound_4.
      rewrite decode_encode_uint by exact bound_5.
      rewrite decode_encode_uint by exact bound_6.
      rewrite decode_encode_uint by exact bound_7.
      rewrite decode_encode_uint by exact bound_8.
      rewrite decode_encode_bytes by exact bound_9.
      rewrite decode_encode_uint by exact bound_10.
      rewrite decode_encode_bytes by exact bound_11.
      rewrite decode_encode_uint by exact bound_12.
      rewrite decode_encode_bytes by exact bound_13.
      rewrite decode_encode_bytes by exact bound_14.
      rewrite decode_encode_uint by exact bound_15.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End SeriesIndexMappingMessage.

  Module StreamIdMessage.

    (** In all multicast channels, a Stream ID Message is sent immediately after each packet header to uniquely identify the source or Stream ID of the data in the packet. *)
    Record t := {
      stream_id : N;
      reserved_2 : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (stream_id record < 256 ^ N.of_nat 2)%N /\
      (reserved_2 record < 256 ^ N.of_nat 2)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 2 (stream_id record) ++
      encode_uint 2 (reserved_2 record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 2 bytes with
      | None => None
      | Some (stream_id_value, bytes) =>
          match decode_uint 2 bytes with
          | None => None
          | Some (reserved_2_value, bytes) =>
              Some ({| stream_id := stream_id_value; reserved_2 := reserved_2_value |}, bytes)
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

  End StreamIdMessage.

  Module SequenceNumberResetMessage.

    (** This message is sent to reset the Message Sequence Number at start of day, or in response to failures. *)
    Record t := {
      source_time : N;
      source_time_ns : N;
      product_id : N;
      channel_id : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (source_time record < 256 ^ N.of_nat 4)%N /\
      (source_time_ns record < 256 ^ N.of_nat 4)%N /\
      (product_id record < 256 ^ N.of_nat 1)%N /\
      (channel_id record < 256 ^ N.of_nat 1)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 4 (source_time record) ++
      encode_uint 4 (source_time_ns record) ++
      encode_uint 1 (product_id record) ++
      encode_uint 1 (channel_id record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 4 bytes with
      | None => None
      | Some (source_time_value, bytes) =>
          match decode_uint 4 bytes with
          | None => None
          | Some (source_time_ns_value, bytes) =>
              match decode_uint 1 bytes with
              | None => None
              | Some (product_id_value, bytes) =>
                  match decode_uint 1 bytes with
                  | None => None
                  | Some (channel_id_value, bytes) =>
                      Some ({| source_time := source_time_value; source_time_ns := source_time_ns_value; product_id := product_id_value; channel_id := channel_id_value |}, bytes)
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 10.
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

  End SequenceNumberResetMessage.

End NyseOptionsDeepFeedV13A.
