From Stdlib Require Import List.
From Stdlib Require Import NArith.
From Stdlib Require Import Lia.
From Stdlib Require Import Strings.Byte.
From Omi Require Import Wire.

Import ListNotations.

(** * New York Stock Exchange Complex Feed

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
      - a run counted by a field
  *)

Module ArcaOptionsComplexFeedV13A.

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

  Module ComplexQuoteMessage.

    (** The Complex Quote message is a two-sided message providing best bid and offer limits of orders on complex symbols with aggregated volumes at each limit. *)
    Record t := {
      source_time : N;
      source_time_ns : N;
      complex_index : N;
      symbol_seq_num : N;
      ask_price : N;
      bid_price : N;
      ask_volume : N;
      bid_volume : N;
      ask_customer_volume : N;
      bid_customer_volume : N;
      quote_condition : list byte;
      reserved_1 : N;
      reserved_2 : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (source_time record < 256 ^ N.of_nat 4)%N /\
      (source_time_ns record < 256 ^ N.of_nat 4)%N /\
      (complex_index record < 256 ^ N.of_nat 4)%N /\
      (symbol_seq_num record < 256 ^ N.of_nat 4)%N /\
      (ask_price record < 256 ^ N.of_nat 4)%N /\
      (bid_price record < 256 ^ N.of_nat 4)%N /\
      (ask_volume record < 256 ^ N.of_nat 2)%N /\
      (bid_volume record < 256 ^ N.of_nat 2)%N /\
      (ask_customer_volume record < 256 ^ N.of_nat 2)%N /\
      (bid_customer_volume record < 256 ^ N.of_nat 2)%N /\
      Datatypes.length (quote_condition record) = 1 /\
      (reserved_1 record < 256 ^ N.of_nat 1)%N /\
      (reserved_2 record < 256 ^ N.of_nat 2)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 4 (source_time record) ++
      encode_uint 4 (source_time_ns record) ++
      encode_uint 4 (complex_index record) ++
      encode_uint 4 (symbol_seq_num record) ++
      encode_uint 4 (ask_price record) ++
      encode_uint 4 (bid_price record) ++
      encode_uint 2 (ask_volume record) ++
      encode_uint 2 (bid_volume record) ++
      encode_uint 2 (ask_customer_volume record) ++
      encode_uint 2 (bid_customer_volume record) ++
      encode_bytes 1 (quote_condition record) ++
      encode_uint 1 (reserved_1 record) ++
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
              | Some (complex_index_value, bytes) =>
                  match decode_uint 4 bytes with
                  | None => None
                  | Some (symbol_seq_num_value, bytes) =>
                      match decode_uint 4 bytes with
                      | None => None
                      | Some (ask_price_value, bytes) =>
                          match decode_uint 4 bytes with
                          | None => None
                          | Some (bid_price_value, bytes) =>
                              match decode_uint 2 bytes with
                              | None => None
                              | Some (ask_volume_value, bytes) =>
                                  match decode_uint 2 bytes with
                                  | None => None
                                  | Some (bid_volume_value, bytes) =>
                                      match decode_uint 2 bytes with
                                      | None => None
                                      | Some (ask_customer_volume_value, bytes) =>
                                          match decode_uint 2 bytes with
                                          | None => None
                                          | Some (bid_customer_volume_value, bytes) =>
                                              match decode_bytes 1 bytes with
                                              | None => None
                                              | Some (quote_condition_value, bytes) =>
                                                  match decode_uint 1 bytes with
                                                  | None => None
                                                  | Some (reserved_1_value, bytes) =>
                                                      match decode_uint 2 bytes with
                                                      | None => None
                                                      | Some (reserved_2_value, bytes) =>
                                                          Some ({| source_time := source_time_value; source_time_ns := source_time_ns_value; complex_index := complex_index_value; symbol_seq_num := symbol_seq_num_value; ask_price := ask_price_value; bid_price := bid_price_value; ask_volume := ask_volume_value; bid_volume := bid_volume_value; ask_customer_volume := ask_customer_volume_value; bid_customer_volume := bid_customer_volume_value; quote_condition := quote_condition_value; reserved_1 := reserved_1_value; reserved_2 := reserved_2_value |}, bytes)
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

    Theorem encode_length : forall record, Datatypes.length (encode record) = 36.
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
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End ComplexQuoteMessage.

  Module ComplexTradeMessage.

    (** The Complex Trade message is used to publish all complex Last Sales. *)
    Record t := {
      source_time : N;
      source_time_ns : N;
      complex_index : N;
      symbol_seq_num : N;
      trade_id : N;
      price : N;
      volume_4 : N;
      trade_cond_1 : list byte;
      trade_cond_2 : list byte;
      reserved_2 : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (source_time record < 256 ^ N.of_nat 4)%N /\
      (source_time_ns record < 256 ^ N.of_nat 4)%N /\
      (complex_index record < 256 ^ N.of_nat 4)%N /\
      (symbol_seq_num record < 256 ^ N.of_nat 4)%N /\
      (trade_id record < 256 ^ N.of_nat 4)%N /\
      (price record < 256 ^ N.of_nat 4)%N /\
      (volume_4 record < 256 ^ N.of_nat 4)%N /\
      Datatypes.length (trade_cond_1 record) = 1 /\
      Datatypes.length (trade_cond_2 record) = 1 /\
      (reserved_2 record < 256 ^ N.of_nat 2)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 4 (source_time record) ++
      encode_uint 4 (source_time_ns record) ++
      encode_uint 4 (complex_index record) ++
      encode_uint 4 (symbol_seq_num record) ++
      encode_uint 4 (trade_id record) ++
      encode_uint 4 (price record) ++
      encode_uint 4 (volume_4 record) ++
      encode_bytes 1 (trade_cond_1 record) ++
      encode_bytes 1 (trade_cond_2 record) ++
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
              | Some (complex_index_value, bytes) =>
                  match decode_uint 4 bytes with
                  | None => None
                  | Some (symbol_seq_num_value, bytes) =>
                      match decode_uint 4 bytes with
                      | None => None
                      | Some (trade_id_value, bytes) =>
                          match decode_uint 4 bytes with
                          | None => None
                          | Some (price_value, bytes) =>
                              match decode_uint 4 bytes with
                              | None => None
                              | Some (volume_4_value, bytes) =>
                                  match decode_bytes 1 bytes with
                                  | None => None
                                  | Some (trade_cond_1_value, bytes) =>
                                      match decode_bytes 1 bytes with
                                      | None => None
                                      | Some (trade_cond_2_value, bytes) =>
                                          match decode_uint 2 bytes with
                                          | None => None
                                          | Some (reserved_2_value, bytes) =>
                                              Some ({| source_time := source_time_value; source_time_ns := source_time_ns_value; complex_index := complex_index_value; symbol_seq_num := symbol_seq_num_value; trade_id := trade_id_value; price := price_value; volume_4 := volume_4_value; trade_cond_1 := trade_cond_1_value; trade_cond_2 := trade_cond_2_value; reserved_2 := reserved_2_value |}, bytes)
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

    Theorem encode_length : forall record, Datatypes.length (encode record) = 32.
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
      rewrite decode_encode_uint by exact bound_1.
      rewrite decode_encode_uint by exact bound_2.
      rewrite decode_encode_uint by exact bound_3.
      rewrite decode_encode_uint by exact bound_4.
      rewrite decode_encode_uint by exact bound_5.
      rewrite decode_encode_uint by exact bound_6.
      rewrite decode_encode_bytes by exact bound_7.
      rewrite decode_encode_bytes by exact bound_8.
      rewrite decode_encode_uint by exact bound_9.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End ComplexTradeMessage.

  Module ComplexCrossingRfqMessage.

    (** The Complex Crossing RFQ (Request for Quote) message is sent out in the event of a COA auction on a complex order. *)
    Record t := {
      source_time : N;
      source_ns : N;
      complex_index : N;
      symbol_seq_num : N;
      side : list byte;
      reserved_1 : N;
      volume_2 : N;
      price : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (source_time record < 256 ^ N.of_nat 4)%N /\
      (source_ns record < 256 ^ N.of_nat 4)%N /\
      (complex_index record < 256 ^ N.of_nat 4)%N /\
      (symbol_seq_num record < 256 ^ N.of_nat 4)%N /\
      Datatypes.length (side record) = 1 /\
      (reserved_1 record < 256 ^ N.of_nat 1)%N /\
      (volume_2 record < 256 ^ N.of_nat 2)%N /\
      (price record < 256 ^ N.of_nat 4)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 4 (source_time record) ++
      encode_uint 4 (source_ns record) ++
      encode_uint 4 (complex_index record) ++
      encode_uint 4 (symbol_seq_num record) ++
      encode_bytes 1 (side record) ++
      encode_uint 1 (reserved_1 record) ++
      encode_uint 2 (volume_2 record) ++
      encode_uint 4 (price record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 4 bytes with
      | None => None
      | Some (source_time_value, bytes) =>
          match decode_uint 4 bytes with
          | None => None
          | Some (source_ns_value, bytes) =>
              match decode_uint 4 bytes with
              | None => None
              | Some (complex_index_value, bytes) =>
                  match decode_uint 4 bytes with
                  | None => None
                  | Some (symbol_seq_num_value, bytes) =>
                      match decode_bytes 1 bytes with
                      | None => None
                      | Some (side_value, bytes) =>
                          match decode_uint 1 bytes with
                          | None => None
                          | Some (reserved_1_value, bytes) =>
                              match decode_uint 2 bytes with
                              | None => None
                              | Some (volume_2_value, bytes) =>
                                  match decode_uint 4 bytes with
                                  | None => None
                                  | Some (price_value, bytes) =>
                                      Some ({| source_time := source_time_value; source_ns := source_ns_value; complex_index := complex_index_value; symbol_seq_num := symbol_seq_num_value; side := side_value; reserved_1 := reserved_1_value; volume_2 := volume_2_value; price := price_value |}, bytes)
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
      destruct bound as [bound_0 [bound_1 [bound_2 [bound_3 [bound_4 [bound_5 [bound_6 bound_7]]]]]]].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_uint by exact bound_0.
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

  End ComplexCrossingRfqMessage.

  Module ComplexCubeRfqMessage.

    Record t := {
      source_time : N;
      source_ns : N;
      complex_index : N;
      symbol_seq_num : N;
      side : list byte;
      reserved_1 : N;
      volume_2 : N;
      price : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (source_time record < 256 ^ N.of_nat 4)%N /\
      (source_ns record < 256 ^ N.of_nat 4)%N /\
      (complex_index record < 256 ^ N.of_nat 4)%N /\
      (symbol_seq_num record < 256 ^ N.of_nat 4)%N /\
      Datatypes.length (side record) = 1 /\
      (reserved_1 record < 256 ^ N.of_nat 1)%N /\
      (volume_2 record < 256 ^ N.of_nat 2)%N /\
      (price record < 256 ^ N.of_nat 4)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 4 (source_time record) ++
      encode_uint 4 (source_ns record) ++
      encode_uint 4 (complex_index record) ++
      encode_uint 4 (symbol_seq_num record) ++
      encode_bytes 1 (side record) ++
      encode_uint 1 (reserved_1 record) ++
      encode_uint 2 (volume_2 record) ++
      encode_uint 4 (price record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 4 bytes with
      | None => None
      | Some (source_time_value, bytes) =>
          match decode_uint 4 bytes with
          | None => None
          | Some (source_ns_value, bytes) =>
              match decode_uint 4 bytes with
              | None => None
              | Some (complex_index_value, bytes) =>
                  match decode_uint 4 bytes with
                  | None => None
                  | Some (symbol_seq_num_value, bytes) =>
                      match decode_bytes 1 bytes with
                      | None => None
                      | Some (side_value, bytes) =>
                          match decode_uint 1 bytes with
                          | None => None
                          | Some (reserved_1_value, bytes) =>
                              match decode_uint 2 bytes with
                              | None => None
                              | Some (volume_2_value, bytes) =>
                                  match decode_uint 4 bytes with
                                  | None => None
                                  | Some (price_value, bytes) =>
                                      Some ({| source_time := source_time_value; source_ns := source_ns_value; complex_index := complex_index_value; symbol_seq_num := symbol_seq_num_value; side := side_value; reserved_1 := reserved_1_value; volume_2 := volume_2_value; price := price_value |}, bytes)
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
      destruct bound as [bound_0 [bound_1 [bound_2 [bound_3 [bound_4 [bound_5 [bound_6 bound_7]]]]]]].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_uint by exact bound_0.
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

  End ComplexCubeRfqMessage.

  Module ComplexStatusMessage.

    (** The Complex Status message is used to inform the subscribers of changes in symbol status of a complex symbol. *)
    Record t := {
      source_time : N;
      source_time_ns : N;
      complex_index : N;
      symbol_seq_num : N;
      security_status : list byte;
      halt_condition : list byte;
      reserved_2 : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (source_time record < 256 ^ N.of_nat 4)%N /\
      (source_time_ns record < 256 ^ N.of_nat 4)%N /\
      (complex_index record < 256 ^ N.of_nat 4)%N /\
      (symbol_seq_num record < 256 ^ N.of_nat 4)%N /\
      Datatypes.length (security_status record) = 1 /\
      Datatypes.length (halt_condition record) = 1 /\
      (reserved_2 record < 256 ^ N.of_nat 2)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 4 (source_time record) ++
      encode_uint 4 (source_time_ns record) ++
      encode_uint 4 (complex_index record) ++
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
              | Some (complex_index_value, bytes) =>
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
                                  Some ({| source_time := source_time_value; source_time_ns := source_time_ns_value; complex_index := complex_index_value; symbol_seq_num := symbol_seq_num_value; security_status := security_status_value; halt_condition := halt_condition_value; reserved_2 := reserved_2_value |}, bytes)
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

  End ComplexStatusMessage.

  Module RefreshComplexQuoteMessage.

    (** The Refresh Complex Quote message is sent in the event no quote messages are published for the symbol for 2 consecutive minutes. *)
    Record t := {
      source_time : N;
      source_time_ns : N;
      complex_index : N;
      symbol_seq_num : N;
      ask_price : N;
      bid_price : N;
      ask_volume : N;
      bid_volume : N;
      ask_customer_volume : N;
      bid_customer_volume : N;
      quote_condition : list byte;
      reserved_1 : N;
      reserved_2 : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (source_time record < 256 ^ N.of_nat 4)%N /\
      (source_time_ns record < 256 ^ N.of_nat 4)%N /\
      (complex_index record < 256 ^ N.of_nat 4)%N /\
      (symbol_seq_num record < 256 ^ N.of_nat 4)%N /\
      (ask_price record < 256 ^ N.of_nat 4)%N /\
      (bid_price record < 256 ^ N.of_nat 4)%N /\
      (ask_volume record < 256 ^ N.of_nat 2)%N /\
      (bid_volume record < 256 ^ N.of_nat 2)%N /\
      (ask_customer_volume record < 256 ^ N.of_nat 2)%N /\
      (bid_customer_volume record < 256 ^ N.of_nat 2)%N /\
      Datatypes.length (quote_condition record) = 1 /\
      (reserved_1 record < 256 ^ N.of_nat 1)%N /\
      (reserved_2 record < 256 ^ N.of_nat 2)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 4 (source_time record) ++
      encode_uint 4 (source_time_ns record) ++
      encode_uint 4 (complex_index record) ++
      encode_uint 4 (symbol_seq_num record) ++
      encode_uint 4 (ask_price record) ++
      encode_uint 4 (bid_price record) ++
      encode_uint 2 (ask_volume record) ++
      encode_uint 2 (bid_volume record) ++
      encode_uint 2 (ask_customer_volume record) ++
      encode_uint 2 (bid_customer_volume record) ++
      encode_bytes 1 (quote_condition record) ++
      encode_uint 1 (reserved_1 record) ++
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
              | Some (complex_index_value, bytes) =>
                  match decode_uint 4 bytes with
                  | None => None
                  | Some (symbol_seq_num_value, bytes) =>
                      match decode_uint 4 bytes with
                      | None => None
                      | Some (ask_price_value, bytes) =>
                          match decode_uint 4 bytes with
                          | None => None
                          | Some (bid_price_value, bytes) =>
                              match decode_uint 2 bytes with
                              | None => None
                              | Some (ask_volume_value, bytes) =>
                                  match decode_uint 2 bytes with
                                  | None => None
                                  | Some (bid_volume_value, bytes) =>
                                      match decode_uint 2 bytes with
                                      | None => None
                                      | Some (ask_customer_volume_value, bytes) =>
                                          match decode_uint 2 bytes with
                                          | None => None
                                          | Some (bid_customer_volume_value, bytes) =>
                                              match decode_bytes 1 bytes with
                                              | None => None
                                              | Some (quote_condition_value, bytes) =>
                                                  match decode_uint 1 bytes with
                                                  | None => None
                                                  | Some (reserved_1_value, bytes) =>
                                                      match decode_uint 2 bytes with
                                                      | None => None
                                                      | Some (reserved_2_value, bytes) =>
                                                          Some ({| source_time := source_time_value; source_time_ns := source_time_ns_value; complex_index := complex_index_value; symbol_seq_num := symbol_seq_num_value; ask_price := ask_price_value; bid_price := bid_price_value; ask_volume := ask_volume_value; bid_volume := bid_volume_value; ask_customer_volume := ask_customer_volume_value; bid_customer_volume := bid_customer_volume_value; quote_condition := quote_condition_value; reserved_1 := reserved_1_value; reserved_2 := reserved_2_value |}, bytes)
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

    Theorem encode_length : forall record, Datatypes.length (encode record) = 36.
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
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End RefreshComplexQuoteMessage.

  Module RefreshComplexTradeMessage.

    (** The Refresh Complex Trade message is sent in the event no Complex Trade messages are published for the symbol for 2 consecutive minutes. *)
    Record t := {
      source_time : N;
      source_time_ns : N;
      complex_index : N;
      symbol_seq_num : N;
      trade_id : N;
      price : N;
      volume_4 : N;
      trade_cond_1 : list byte;
      trade_cond_2 : list byte;
      reserved_2 : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (source_time record < 256 ^ N.of_nat 4)%N /\
      (source_time_ns record < 256 ^ N.of_nat 4)%N /\
      (complex_index record < 256 ^ N.of_nat 4)%N /\
      (symbol_seq_num record < 256 ^ N.of_nat 4)%N /\
      (trade_id record < 256 ^ N.of_nat 4)%N /\
      (price record < 256 ^ N.of_nat 4)%N /\
      (volume_4 record < 256 ^ N.of_nat 4)%N /\
      Datatypes.length (trade_cond_1 record) = 1 /\
      Datatypes.length (trade_cond_2 record) = 1 /\
      (reserved_2 record < 256 ^ N.of_nat 2)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 4 (source_time record) ++
      encode_uint 4 (source_time_ns record) ++
      encode_uint 4 (complex_index record) ++
      encode_uint 4 (symbol_seq_num record) ++
      encode_uint 4 (trade_id record) ++
      encode_uint 4 (price record) ++
      encode_uint 4 (volume_4 record) ++
      encode_bytes 1 (trade_cond_1 record) ++
      encode_bytes 1 (trade_cond_2 record) ++
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
              | Some (complex_index_value, bytes) =>
                  match decode_uint 4 bytes with
                  | None => None
                  | Some (symbol_seq_num_value, bytes) =>
                      match decode_uint 4 bytes with
                      | None => None
                      | Some (trade_id_value, bytes) =>
                          match decode_uint 4 bytes with
                          | None => None
                          | Some (price_value, bytes) =>
                              match decode_uint 4 bytes with
                              | None => None
                              | Some (volume_4_value, bytes) =>
                                  match decode_bytes 1 bytes with
                                  | None => None
                                  | Some (trade_cond_1_value, bytes) =>
                                      match decode_bytes 1 bytes with
                                      | None => None
                                      | Some (trade_cond_2_value, bytes) =>
                                          match decode_uint 2 bytes with
                                          | None => None
                                          | Some (reserved_2_value, bytes) =>
                                              Some ({| source_time := source_time_value; source_time_ns := source_time_ns_value; complex_index := complex_index_value; symbol_seq_num := symbol_seq_num_value; trade_id := trade_id_value; price := price_value; volume_4 := volume_4_value; trade_cond_1 := trade_cond_1_value; trade_cond_2 := trade_cond_2_value; reserved_2 := reserved_2_value |}, bytes)
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

    Theorem encode_length : forall record, Datatypes.length (encode record) = 32.
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
      rewrite decode_encode_uint by exact bound_1.
      rewrite decode_encode_uint by exact bound_2.
      rewrite decode_encode_uint by exact bound_3.
      rewrite decode_encode_uint by exact bound_4.
      rewrite decode_encode_uint by exact bound_5.
      rewrite decode_encode_uint by exact bound_6.
      rewrite decode_encode_bytes by exact bound_7.
      rewrite decode_encode_bytes by exact bound_8.
      rewrite decode_encode_uint by exact bound_9.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End RefreshComplexTradeMessage.

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

End ArcaOptionsComplexFeedV13A.
