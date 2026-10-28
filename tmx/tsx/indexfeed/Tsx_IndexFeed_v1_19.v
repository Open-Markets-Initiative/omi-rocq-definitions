From Stdlib Require Import List.
From Stdlib Require Import NArith.
From Stdlib Require Import Lia.
From Stdlib Require Import Strings.Byte.
From Omi Require Import Wire.

Import ListNotations.

(** * TMX Group Index Feed

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
  *)

Module TsxIndexFeedV119.

  Module MessageHeader.

    (** Twenty two byte ascii header carried on every Qrtmd message *)
    Record t := {
      message_length : list byte;
      sequence_number : list byte;
      service_identifier : list byte;
      retransmission_identifier : list byte;
      continuation_identifier : list byte;
      message_type : list byte;
      exchange_identifier : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (message_length record) = 4 /\
      Datatypes.length (sequence_number record) = 9 /\
      Datatypes.length (service_identifier record) = 3 /\
      Datatypes.length (retransmission_identifier record) = 1 /\
      Datatypes.length (continuation_identifier record) = 1 /\
      Datatypes.length (message_type record) = 2 /\
      Datatypes.length (exchange_identifier record) = 2.

    Definition encode (record : t) : list byte :=
      encode_bytes 4 (message_length record) ++
      encode_bytes 9 (sequence_number record) ++
      encode_bytes 3 (service_identifier record) ++
      encode_bytes 1 (retransmission_identifier record) ++
      encode_bytes 1 (continuation_identifier record) ++
      encode_bytes 2 (message_type record) ++
      encode_bytes 2 (exchange_identifier record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 4 bytes with
      | None => None
      | Some (message_length_value, bytes) =>
          match decode_bytes 9 bytes with
          | None => None
          | Some (sequence_number_value, bytes) =>
              match decode_bytes 3 bytes with
              | None => None
              | Some (service_identifier_value, bytes) =>
                  match decode_bytes 1 bytes with
                  | None => None
                  | Some (retransmission_identifier_value, bytes) =>
                      match decode_bytes 1 bytes with
                      | None => None
                      | Some (continuation_identifier_value, bytes) =>
                          match decode_bytes 2 bytes with
                          | None => None
                          | Some (message_type_value, bytes) =>
                              match decode_bytes 2 bytes with
                              | None => None
                              | Some (exchange_identifier_value, bytes) =>
                                  Some ({| message_length := message_length_value; sequence_number := sequence_number_value; service_identifier := service_identifier_value; retransmission_identifier := retransmission_identifier_value; continuation_identifier := continuation_identifier_value; message_type := message_type_value; exchange_identifier := exchange_identifier_value |}, bytes)
                              end
                          end
                      end
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 22.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_bytes_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 [bound_1 [bound_2 [bound_3 [bound_4 [bound_5 bound_6]]]]]].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_bytes by exact bound_0.
      rewrite decode_encode_bytes by exact bound_1.
      rewrite decode_encode_bytes by exact bound_2.
      rewrite decode_encode_bytes by exact bound_3.
      rewrite decode_encode_bytes by exact bound_4.
      rewrite decode_encode_bytes by exact bound_5.
      rewrite decode_encode_bytes by exact bound_6.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End MessageHeader.

  Module SAndPTsxOfficialIndexLevelMessage.

    (** Level of an index as of the time of the calculation. *)
    Record t := {
      time : list byte;
      index_id : list byte;
      last_level : list byte;
      net_change : list byte;
      volume : list byte;
      value : list byte;
      open_level : list byte;
      settlement_value : list byte;
      special_opening_quote : list byte;
      percent_trading : list byte;
      high_level : list byte;
      low_level : list byte;
      pe : list byte;
      yield : list byte;
      markers : list byte;
      bid_price : list byte;
      ask_price : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (time record) = 6 /\
      Datatypes.length (index_id record) = 4 /\
      Datatypes.length (last_level record) = 8 /\
      Datatypes.length (net_change record) = 7 /\
      Datatypes.length (volume record) = 11 /\
      Datatypes.length (value record) = 12 /\
      Datatypes.length (open_level record) = 8 /\
      Datatypes.length (settlement_value record) = 8 /\
      Datatypes.length (special_opening_quote record) = 8 /\
      Datatypes.length (percent_trading record) = 7 /\
      Datatypes.length (high_level record) = 8 /\
      Datatypes.length (low_level record) = 8 /\
      Datatypes.length (pe record) = 7 /\
      Datatypes.length (yield record) = 5 /\
      Datatypes.length (markers record) = 1 /\
      Datatypes.length (bid_price record) = 7 /\
      Datatypes.length (ask_price record) = 7.

    Definition encode (record : t) : list byte :=
      encode_bytes 6 (time record) ++
      encode_bytes 4 (index_id record) ++
      encode_bytes 8 (last_level record) ++
      encode_bytes 7 (net_change record) ++
      encode_bytes 11 (volume record) ++
      encode_bytes 12 (value record) ++
      encode_bytes 8 (open_level record) ++
      encode_bytes 8 (settlement_value record) ++
      encode_bytes 8 (special_opening_quote record) ++
      encode_bytes 7 (percent_trading record) ++
      encode_bytes 8 (high_level record) ++
      encode_bytes 8 (low_level record) ++
      encode_bytes 7 (pe record) ++
      encode_bytes 5 (yield record) ++
      encode_bytes 1 (markers record) ++
      encode_bytes 7 (bid_price record) ++
      encode_bytes 7 (ask_price record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 6 bytes with
      | None => None
      | Some (time_value, bytes) =>
          match decode_bytes 4 bytes with
          | None => None
          | Some (index_id_value, bytes) =>
              match decode_bytes 8 bytes with
              | None => None
              | Some (last_level_value, bytes) =>
                  match decode_bytes 7 bytes with
                  | None => None
                  | Some (net_change_value, bytes) =>
                      match decode_bytes 11 bytes with
                      | None => None
                      | Some (volume_value, bytes) =>
                          match decode_bytes 12 bytes with
                          | None => None
                          | Some (value_value, bytes) =>
                              match decode_bytes 8 bytes with
                              | None => None
                              | Some (open_level_value, bytes) =>
                                  match decode_bytes 8 bytes with
                                  | None => None
                                  | Some (settlement_value_value, bytes) =>
                                      match decode_bytes 8 bytes with
                                      | None => None
                                      | Some (special_opening_quote_value, bytes) =>
                                          match decode_bytes 7 bytes with
                                          | None => None
                                          | Some (percent_trading_value, bytes) =>
                                              match decode_bytes 8 bytes with
                                              | None => None
                                              | Some (high_level_value, bytes) =>
                                                  match decode_bytes 8 bytes with
                                                  | None => None
                                                  | Some (low_level_value, bytes) =>
                                                      match decode_bytes 7 bytes with
                                                      | None => None
                                                      | Some (pe_value, bytes) =>
                                                          match decode_bytes 5 bytes with
                                                          | None => None
                                                          | Some (yield_value, bytes) =>
                                                              match decode_bytes 1 bytes with
                                                              | None => None
                                                              | Some (markers_value, bytes) =>
                                                                  match decode_bytes 7 bytes with
                                                                  | None => None
                                                                  | Some (bid_price_value, bytes) =>
                                                                      match decode_bytes 7 bytes with
                                                                      | None => None
                                                                      | Some (ask_price_value, bytes) =>
                                                                          Some ({| time := time_value; index_id := index_id_value; last_level := last_level_value; net_change := net_change_value; volume := volume_value; value := value_value; open_level := open_level_value; settlement_value := settlement_value_value; special_opening_quote := special_opening_quote_value; percent_trading := percent_trading_value; high_level := high_level_value; low_level := low_level_value; pe := pe_value; yield := yield_value; markers := markers_value; bid_price := bid_price_value; ask_price := ask_price_value |}, bytes)
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

    Theorem encode_length : forall record, Datatypes.length (encode record) = 122.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_bytes_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 [bound_1 [bound_2 [bound_3 [bound_4 [bound_5 [bound_6 [bound_7 [bound_8 [bound_9 [bound_10 [bound_11 [bound_12 [bound_13 [bound_14 [bound_15 bound_16]]]]]]]]]]]]]]]].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_bytes by exact bound_0.
      rewrite decode_encode_bytes by exact bound_1.
      rewrite decode_encode_bytes by exact bound_2.
      rewrite decode_encode_bytes by exact bound_3.
      rewrite decode_encode_bytes by exact bound_4.
      rewrite decode_encode_bytes by exact bound_5.
      rewrite decode_encode_bytes by exact bound_6.
      rewrite decode_encode_bytes by exact bound_7.
      rewrite decode_encode_bytes by exact bound_8.
      rewrite decode_encode_bytes by exact bound_9.
      rewrite decode_encode_bytes by exact bound_10.
      rewrite decode_encode_bytes by exact bound_11.
      rewrite decode_encode_bytes by exact bound_12.
      rewrite decode_encode_bytes by exact bound_13.
      rewrite decode_encode_bytes by exact bound_14.
      rewrite decode_encode_bytes by exact bound_15.
      rewrite decode_encode_bytes by exact bound_16.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End SAndPTsxOfficialIndexLevelMessage.

End TsxIndexFeedV119.
