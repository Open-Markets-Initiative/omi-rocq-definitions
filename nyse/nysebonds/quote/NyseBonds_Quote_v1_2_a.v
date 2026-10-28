From Stdlib Require Import List.
From Stdlib Require Import NArith.
From Stdlib Require Import Lia.
From Stdlib Require Import Strings.Byte.
From Omi Require Import Wire.

Import ListNotations.

(** * New York Stock Exchange Quote

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
  *)

Module NyseBondsQuoteV12A.

  Module MessageHeader.

    (** Nyse Pdp common message header *)
    Record t := {
      msg_size : N;
      msg_type : N;
      msg_seq_num : N;
      send_time : N;
      product_id : N;
      retrans_flag : N;
      num_body_entries : N;
      filler : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (msg_size record < 256 ^ N.of_nat 2)%N /\
      (msg_type record < 256 ^ N.of_nat 2)%N /\
      (msg_seq_num record < 256 ^ N.of_nat 4)%N /\
      (send_time record < 256 ^ N.of_nat 4)%N /\
      (product_id record < 256 ^ N.of_nat 1)%N /\
      (retrans_flag record < 256 ^ N.of_nat 1)%N /\
      (num_body_entries record < 256 ^ N.of_nat 1)%N /\
      Datatypes.length (filler record) = 1.

    Definition encode (record : t) : list byte :=
      encode_uint 2 (msg_size record) ++
      encode_uint 2 (msg_type record) ++
      encode_uint 4 (msg_seq_num record) ++
      encode_uint 4 (send_time record) ++
      encode_uint 1 (product_id record) ++
      encode_uint 1 (retrans_flag record) ++
      encode_uint 1 (num_body_entries record) ++
      encode_bytes 1 (filler record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 2 bytes with
      | None => None
      | Some (msg_size_value, bytes) =>
          match decode_uint 2 bytes with
          | None => None
          | Some (msg_type_value, bytes) =>
              match decode_uint 4 bytes with
              | None => None
              | Some (msg_seq_num_value, bytes) =>
                  match decode_uint 4 bytes with
                  | None => None
                  | Some (send_time_value, bytes) =>
                      match decode_uint 1 bytes with
                      | None => None
                      | Some (product_id_value, bytes) =>
                          match decode_uint 1 bytes with
                          | None => None
                          | Some (retrans_flag_value, bytes) =>
                              match decode_uint 1 bytes with
                              | None => None
                              | Some (num_body_entries_value, bytes) =>
                                  match decode_bytes 1 bytes with
                                  | None => None
                                  | Some (filler_value, bytes) =>
                                      Some ({| msg_size := msg_size_value; msg_type := msg_type_value; msg_seq_num := msg_seq_num_value; send_time := send_time_value; product_id := product_id_value; retrans_flag := retrans_flag_value; num_body_entries := num_body_entries_value; filler := filler_value |}, bytes)
                                  end
                              end
                          end
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
      destruct bound as [bound_0 [bound_1 [bound_2 [bound_3 [bound_4 [bound_5 [bound_6 bound_7]]]]]]].
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
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End MessageHeader.

  Module SequenceNumberResetMessage.

    (** Sent to reset the sequence number at start of day and in response to failures. The message carries its own valid sequence number in the header. *)
    Record t := {
      next_seq_number : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (next_seq_number record < 256 ^ N.of_nat 4)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 4 (next_seq_number record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 4 bytes with
      | None => None
      | Some (next_seq_number_value, bytes) =>
          Some ({| next_seq_number := next_seq_number_value |}, bytes)
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

  End SequenceNumberResetMessage.

  Module MessageUnavailableMessage.

    (** Sent when the requested messages cannot be retransmitted. *)
    Record t := {
      begin_seq_num : N;
      end_seq_num : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (begin_seq_num record < 256 ^ N.of_nat 4)%N /\
      (end_seq_num record < 256 ^ N.of_nat 4)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 4 (begin_seq_num record) ++
      encode_uint 4 (end_seq_num record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 4 bytes with
      | None => None
      | Some (begin_seq_num_value, bytes) =>
          match decode_uint 4 bytes with
          | None => None
          | Some (end_seq_num_value, bytes) =>
              Some ({| begin_seq_num := begin_seq_num_value; end_seq_num := end_seq_num_value |}, bytes)
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

  End MessageUnavailableMessage.

  Module RefreshQuoteMessage.

    (** Sent in response to a Refresh Quote Request, and automatically when there are intraday symbol additions. The same body as a Quote message with the symbol and Cusip appended. *)
    Record t := {
      symbol_index : N;
      source_time : N;
      quote_link_id : N;
      ask_price_numerator : N;
      ask_size : N;
      bid_price_numerator : N;
      bid_size : N;
      price_scale_code : N;
      exchange_id : list byte;
      security_type : list byte;
      quote_condition : list byte;
      flat_pricing : list byte;
      trading_action : N;
      filler_ascii_2 : list byte;
      symbol : list byte;
      cusip : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (symbol_index record < 256 ^ N.of_nat 4)%N /\
      (source_time record < 256 ^ N.of_nat 4)%N /\
      (quote_link_id record < 256 ^ N.of_nat 4)%N /\
      (ask_price_numerator record < 256 ^ N.of_nat 4)%N /\
      (ask_size record < 256 ^ N.of_nat 4)%N /\
      (bid_price_numerator record < 256 ^ N.of_nat 4)%N /\
      (bid_size record < 256 ^ N.of_nat 4)%N /\
      (price_scale_code record < 256 ^ N.of_nat 1)%N /\
      Datatypes.length (exchange_id record) = 1 /\
      Datatypes.length (security_type record) = 1 /\
      Datatypes.length (quote_condition record) = 1 /\
      Datatypes.length (flat_pricing record) = 1 /\
      (trading_action record < 256 ^ N.of_nat 1)%N /\
      Datatypes.length (filler_ascii_2 record) = 2 /\
      Datatypes.length (symbol record) = 22 /\
      Datatypes.length (cusip record) = 14.

    Definition encode (record : t) : list byte :=
      encode_uint 4 (symbol_index record) ++
      encode_uint 4 (source_time record) ++
      encode_uint 4 (quote_link_id record) ++
      encode_uint 4 (ask_price_numerator record) ++
      encode_uint 4 (ask_size record) ++
      encode_uint 4 (bid_price_numerator record) ++
      encode_uint 4 (bid_size record) ++
      encode_uint 1 (price_scale_code record) ++
      encode_bytes 1 (exchange_id record) ++
      encode_bytes 1 (security_type record) ++
      encode_bytes 1 (quote_condition record) ++
      encode_bytes 1 (flat_pricing record) ++
      encode_uint 1 (trading_action record) ++
      encode_bytes 2 (filler_ascii_2 record) ++
      encode_bytes 22 (symbol record) ++
      encode_bytes 14 (cusip record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 4 bytes with
      | None => None
      | Some (symbol_index_value, bytes) =>
          match decode_uint 4 bytes with
          | None => None
          | Some (source_time_value, bytes) =>
              match decode_uint 4 bytes with
              | None => None
              | Some (quote_link_id_value, bytes) =>
                  match decode_uint 4 bytes with
                  | None => None
                  | Some (ask_price_numerator_value, bytes) =>
                      match decode_uint 4 bytes with
                      | None => None
                      | Some (ask_size_value, bytes) =>
                          match decode_uint 4 bytes with
                          | None => None
                          | Some (bid_price_numerator_value, bytes) =>
                              match decode_uint 4 bytes with
                              | None => None
                              | Some (bid_size_value, bytes) =>
                                  match decode_uint 1 bytes with
                                  | None => None
                                  | Some (price_scale_code_value, bytes) =>
                                      match decode_bytes 1 bytes with
                                      | None => None
                                      | Some (exchange_id_value, bytes) =>
                                          match decode_bytes 1 bytes with
                                          | None => None
                                          | Some (security_type_value, bytes) =>
                                              match decode_bytes 1 bytes with
                                              | None => None
                                              | Some (quote_condition_value, bytes) =>
                                                  match decode_bytes 1 bytes with
                                                  | None => None
                                                  | Some (flat_pricing_value, bytes) =>
                                                      match decode_uint 1 bytes with
                                                      | None => None
                                                      | Some (trading_action_value, bytes) =>
                                                          match decode_bytes 2 bytes with
                                                          | None => None
                                                          | Some (filler_ascii_2_value, bytes) =>
                                                              match decode_bytes 22 bytes with
                                                              | None => None
                                                              | Some (symbol_value, bytes) =>
                                                                  match decode_bytes 14 bytes with
                                                                  | None => None
                                                                  | Some (cusip_value, bytes) =>
                                                                      Some ({| symbol_index := symbol_index_value; source_time := source_time_value; quote_link_id := quote_link_id_value; ask_price_numerator := ask_price_numerator_value; ask_size := ask_size_value; bid_price_numerator := bid_price_numerator_value; bid_size := bid_size_value; price_scale_code := price_scale_code_value; exchange_id := exchange_id_value; security_type := security_type_value; quote_condition := quote_condition_value; flat_pricing := flat_pricing_value; trading_action := trading_action_value; filler_ascii_2 := filler_ascii_2_value; symbol := symbol_value; cusip := cusip_value |}, bytes)
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

    Theorem encode_length : forall record, Datatypes.length (encode record) = 72.
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
      rewrite decode_encode_bytes by exact bound_8.
      rewrite decode_encode_bytes by exact bound_9.
      rewrite decode_encode_bytes by exact bound_10.
      rewrite decode_encode_bytes by exact bound_11.
      rewrite decode_encode_uint by exact bound_12.
      rewrite decode_encode_bytes by exact bound_13.
      rewrite decode_encode_bytes by exact bound_14.
      rewrite decode_encode_bytes by exact bound_15.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End RefreshQuoteMessage.

  Module SymbolIndexMappingMessage.

    (** Maps a symbol index to its bond symbol and Cusip. *)
    Record t := {
      symbol_index : N;
      symbol : list byte;
      cusip : list byte;
      filler_ascii_4 : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (symbol_index record < 256 ^ N.of_nat 4)%N /\
      Datatypes.length (symbol record) = 22 /\
      Datatypes.length (cusip record) = 14 /\
      Datatypes.length (filler_ascii_4 record) = 4.

    Definition encode (record : t) : list byte :=
      encode_uint 4 (symbol_index record) ++
      encode_bytes 22 (symbol record) ++
      encode_bytes 14 (cusip record) ++
      encode_bytes 4 (filler_ascii_4 record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 4 bytes with
      | None => None
      | Some (symbol_index_value, bytes) =>
          match decode_bytes 22 bytes with
          | None => None
          | Some (symbol_value, bytes) =>
              match decode_bytes 14 bytes with
              | None => None
              | Some (cusip_value, bytes) =>
                  match decode_bytes 4 bytes with
                  | None => None
                  | Some (filler_ascii_4_value, bytes) =>
                      Some ({| symbol_index := symbol_index_value; symbol := symbol_value; cusip := cusip_value; filler_ascii_4 := filler_ascii_4_value |}, bytes)
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
      destruct bound as [bound_0 [bound_1 [bound_2 bound_3]]].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_uint by exact bound_0.
      rewrite decode_encode_bytes by exact bound_1.
      rewrite decode_encode_bytes by exact bound_2.
      rewrite decode_encode_bytes by exact bound_3.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End SymbolIndexMappingMessage.

  Module QuoteMessage.

    (** The L1 top of book quote for a bond. *)
    Record t := {
      symbol_index : N;
      source_time : N;
      quote_link_id : N;
      ask_price_numerator : N;
      ask_size : N;
      bid_price_numerator : N;
      bid_size : N;
      price_scale_code : N;
      exchange_id : list byte;
      security_type : list byte;
      quote_condition : list byte;
      flat_pricing : list byte;
      trading_action : N;
      filler_ascii_2 : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (symbol_index record < 256 ^ N.of_nat 4)%N /\
      (source_time record < 256 ^ N.of_nat 4)%N /\
      (quote_link_id record < 256 ^ N.of_nat 4)%N /\
      (ask_price_numerator record < 256 ^ N.of_nat 4)%N /\
      (ask_size record < 256 ^ N.of_nat 4)%N /\
      (bid_price_numerator record < 256 ^ N.of_nat 4)%N /\
      (bid_size record < 256 ^ N.of_nat 4)%N /\
      (price_scale_code record < 256 ^ N.of_nat 1)%N /\
      Datatypes.length (exchange_id record) = 1 /\
      Datatypes.length (security_type record) = 1 /\
      Datatypes.length (quote_condition record) = 1 /\
      Datatypes.length (flat_pricing record) = 1 /\
      (trading_action record < 256 ^ N.of_nat 1)%N /\
      Datatypes.length (filler_ascii_2 record) = 2.

    Definition encode (record : t) : list byte :=
      encode_uint 4 (symbol_index record) ++
      encode_uint 4 (source_time record) ++
      encode_uint 4 (quote_link_id record) ++
      encode_uint 4 (ask_price_numerator record) ++
      encode_uint 4 (ask_size record) ++
      encode_uint 4 (bid_price_numerator record) ++
      encode_uint 4 (bid_size record) ++
      encode_uint 1 (price_scale_code record) ++
      encode_bytes 1 (exchange_id record) ++
      encode_bytes 1 (security_type record) ++
      encode_bytes 1 (quote_condition record) ++
      encode_bytes 1 (flat_pricing record) ++
      encode_uint 1 (trading_action record) ++
      encode_bytes 2 (filler_ascii_2 record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 4 bytes with
      | None => None
      | Some (symbol_index_value, bytes) =>
          match decode_uint 4 bytes with
          | None => None
          | Some (source_time_value, bytes) =>
              match decode_uint 4 bytes with
              | None => None
              | Some (quote_link_id_value, bytes) =>
                  match decode_uint 4 bytes with
                  | None => None
                  | Some (ask_price_numerator_value, bytes) =>
                      match decode_uint 4 bytes with
                      | None => None
                      | Some (ask_size_value, bytes) =>
                          match decode_uint 4 bytes with
                          | None => None
                          | Some (bid_price_numerator_value, bytes) =>
                              match decode_uint 4 bytes with
                              | None => None
                              | Some (bid_size_value, bytes) =>
                                  match decode_uint 1 bytes with
                                  | None => None
                                  | Some (price_scale_code_value, bytes) =>
                                      match decode_bytes 1 bytes with
                                      | None => None
                                      | Some (exchange_id_value, bytes) =>
                                          match decode_bytes 1 bytes with
                                          | None => None
                                          | Some (security_type_value, bytes) =>
                                              match decode_bytes 1 bytes with
                                              | None => None
                                              | Some (quote_condition_value, bytes) =>
                                                  match decode_bytes 1 bytes with
                                                  | None => None
                                                  | Some (flat_pricing_value, bytes) =>
                                                      match decode_uint 1 bytes with
                                                      | None => None
                                                      | Some (trading_action_value, bytes) =>
                                                          match decode_bytes 2 bytes with
                                                          | None => None
                                                          | Some (filler_ascii_2_value, bytes) =>
                                                              Some ({| symbol_index := symbol_index_value; source_time := source_time_value; quote_link_id := quote_link_id_value; ask_price_numerator := ask_price_numerator_value; ask_size := ask_size_value; bid_price_numerator := bid_price_numerator_value; bid_size := bid_size_value; price_scale_code := price_scale_code_value; exchange_id := exchange_id_value; security_type := security_type_value; quote_condition := quote_condition_value; flat_pricing := flat_pricing_value; trading_action := trading_action_value; filler_ascii_2 := filler_ascii_2_value |}, bytes)
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

    Theorem encode_length : forall record, Datatypes.length (encode record) = 36.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_uint_length, !encode_bytes_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 [bound_1 [bound_2 [bound_3 [bound_4 [bound_5 [bound_6 [bound_7 [bound_8 [bound_9 [bound_10 [bound_11 [bound_12 bound_13]]]]]]]]]]]]].
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
      rewrite decode_encode_bytes by exact bound_8.
      rewrite decode_encode_bytes by exact bound_9.
      rewrite decode_encode_bytes by exact bound_10.
      rewrite decode_encode_bytes by exact bound_11.
      rewrite decode_encode_uint by exact bound_12.
      rewrite decode_encode_bytes by exact bound_13.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End QuoteMessage.

End NyseBondsQuoteV12A.
