From Stdlib Require Import List.
From Stdlib Require Import NArith.
From Stdlib Require Import Lia.
From Stdlib Require Import Strings.Byte.
From Omi Require Import Wire.

Import ListNotations.

(** * Bolsa Mexicana de Valores Bmv Market Data Product 37

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

    License: MIT No Attribution
  *)

Module BmvMarketDataProduct37V11.

  Module INTRAMulticastHeader.

    (** BMV INTRA Multicast Header *)
    Record t := {
      length_ : N;
      total_messages : N;
      market_data_group : N;
      session : N;
      sequence_number : N;
      datetime : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (length_ record < 256 ^ N.of_nat 2)%N /\
      (total_messages record < 256 ^ N.of_nat 1)%N /\
      (market_data_group record < 256 ^ N.of_nat 1)%N /\
      (session record < 256 ^ N.of_nat 1)%N /\
      (sequence_number record < 256 ^ N.of_nat 4)%N /\
      (datetime record < 256 ^ N.of_nat 8)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 2 (length_ record) ++
      encode_uint 1 (total_messages record) ++
      encode_uint 1 (market_data_group record) ++
      encode_uint 1 (session record) ++
      encode_uint 4 (sequence_number record) ++
      encode_uint 8 (datetime record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 2 bytes with
      | None => None
      | Some (length__value, bytes) =>
          match decode_uint 1 bytes with
          | None => None
          | Some (total_messages_value, bytes) =>
              match decode_uint 1 bytes with
              | None => None
              | Some (market_data_group_value, bytes) =>
                  match decode_uint 1 bytes with
                  | None => None
                  | Some (session_value, bytes) =>
                      match decode_uint 4 bytes with
                      | None => None
                      | Some (sequence_number_value, bytes) =>
                          match decode_uint 8 bytes with
                          | None => None
                          | Some (datetime_value, bytes) =>
                              Some ({| length_ := length__value; total_messages := total_messages_value; market_data_group := market_data_group_value; session := session_value; sequence_number := sequence_number_value; datetime := datetime_value |}, bytes)
                          end
                      end
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 17.
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

  End INTRAMulticastHeader.

  Module MessageHeader.

    (** Message length and message type *)
    Record t := {
      message_length : N;
      message_type : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (message_length record < 256 ^ N.of_nat 2)%N /\
      (message_type record < 256 ^ N.of_nat 2)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 2 (message_length record) ++
      encode_uint 2 (message_type record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 2 bytes with
      | None => None
      | Some (message_length_value, bytes) =>
          match decode_uint 2 bytes with
          | None => None
          | Some (message_type_value, bytes) =>
              Some ({| message_length := message_length_value; message_type := message_type_value |}, bytes)
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

  Module OrderAditionMessage.

    (** When the order is accepted by the BMV central system, this message is disseminated to the relevant media. *)
    Record t := {
      id_instrument : N;
      date_and_hour : N;
      folio : N;
      direction : list byte;
      volume : N;
      price : N;
      participant : list byte;
      operation_type : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (id_instrument record < 256 ^ N.of_nat 4)%N /\
      (date_and_hour record < 256 ^ N.of_nat 8)%N /\
      (folio record < 256 ^ N.of_nat 4)%N /\
      Datatypes.length (direction record) = 1 /\
      (volume record < 256 ^ N.of_nat 4)%N /\
      (price record < 256 ^ N.of_nat 8)%N /\
      Datatypes.length (participant record) = 5 /\
      Datatypes.length (operation_type record) = 1.

    Definition encode (record : t) : list byte :=
      encode_uint 4 (id_instrument record) ++
      encode_uint 8 (date_and_hour record) ++
      encode_uint 4 (folio record) ++
      encode_bytes 1 (direction record) ++
      encode_uint 4 (volume record) ++
      encode_uint 8 (price record) ++
      encode_bytes 5 (participant record) ++
      encode_bytes 1 (operation_type record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 4 bytes with
      | None => None
      | Some (id_instrument_value, bytes) =>
          match decode_uint 8 bytes with
          | None => None
          | Some (date_and_hour_value, bytes) =>
              match decode_uint 4 bytes with
              | None => None
              | Some (folio_value, bytes) =>
                  match decode_bytes 1 bytes with
                  | None => None
                  | Some (direction_value, bytes) =>
                      match decode_uint 4 bytes with
                      | None => None
                      | Some (volume_value, bytes) =>
                          match decode_uint 8 bytes with
                          | None => None
                          | Some (price_value, bytes) =>
                              match decode_bytes 5 bytes with
                              | None => None
                              | Some (participant_value, bytes) =>
                                  match decode_bytes 1 bytes with
                                  | None => None
                                  | Some (operation_type_value, bytes) =>
                                      Some ({| id_instrument := id_instrument_value; date_and_hour := date_and_hour_value; folio := folio_value; direction := direction_value; volume := volume_value; price := price_value; participant := participant_value; operation_type := operation_type_value |}, bytes)
                                  end
                              end
                          end
                      end
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 35.
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
      rewrite decode_encode_bytes by exact bound_3.
      rewrite decode_encode_uint by exact bound_4.
      rewrite decode_encode_uint by exact bound_5.
      rewrite decode_encode_bytes by exact bound_6.
      rewrite decode_encode_bytes by exact bound_7.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End OrderAditionMessage.

  Module ExecutionOfOrdersMessage.

    (** The message is disseminated as soon as there is a match in the BMV's electronic system. *)
    Record t := {
      id_instrument : N;
      date : N;
      folio : N;
      volume : N;
      trade_number : N;
      execution_price : N;
      operation_type : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (id_instrument record < 256 ^ N.of_nat 4)%N /\
      (date record < 256 ^ N.of_nat 8)%N /\
      (folio record < 256 ^ N.of_nat 4)%N /\
      (volume record < 256 ^ N.of_nat 4)%N /\
      (trade_number record < 256 ^ N.of_nat 4)%N /\
      (execution_price record < 256 ^ N.of_nat 8)%N /\
      Datatypes.length (operation_type record) = 1.

    Definition encode (record : t) : list byte :=
      encode_uint 4 (id_instrument record) ++
      encode_uint 8 (date record) ++
      encode_uint 4 (folio record) ++
      encode_uint 4 (volume record) ++
      encode_uint 4 (trade_number record) ++
      encode_uint 8 (execution_price record) ++
      encode_bytes 1 (operation_type record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 4 bytes with
      | None => None
      | Some (id_instrument_value, bytes) =>
          match decode_uint 8 bytes with
          | None => None
          | Some (date_value, bytes) =>
              match decode_uint 4 bytes with
              | None => None
              | Some (folio_value, bytes) =>
                  match decode_uint 4 bytes with
                  | None => None
                  | Some (volume_value, bytes) =>
                      match decode_uint 4 bytes with
                      | None => None
                      | Some (trade_number_value, bytes) =>
                          match decode_uint 8 bytes with
                          | None => None
                          | Some (execution_price_value, bytes) =>
                              match decode_bytes 1 bytes with
                              | None => None
                              | Some (operation_type_value, bytes) =>
                                  Some ({| id_instrument := id_instrument_value; date := date_value; folio := folio_value; volume := volume_value; trade_number := trade_number_value; execution_price := execution_price_value; operation_type := operation_type_value |}, bytes)
                              end
                          end
                      end
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 33.
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
      rewrite decode_encode_uint by exact bound_4.
      rewrite decode_encode_uint by exact bound_5.
      rewrite decode_encode_bytes by exact bound_6.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End ExecutionOfOrdersMessage.

  Module OrderCancellationMessage.

    (** This message indicates the fully elimination of an order in the trading floor *)
    Record t := {
      id_instrument : N;
      date : N;
      folio : N;
      operation_type : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (id_instrument record < 256 ^ N.of_nat 4)%N /\
      (date record < 256 ^ N.of_nat 8)%N /\
      (folio record < 256 ^ N.of_nat 4)%N /\
      Datatypes.length (operation_type record) = 1.

    Definition encode (record : t) : list byte :=
      encode_uint 4 (id_instrument record) ++
      encode_uint 8 (date record) ++
      encode_uint 4 (folio record) ++
      encode_bytes 1 (operation_type record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 4 bytes with
      | None => None
      | Some (id_instrument_value, bytes) =>
          match decode_uint 8 bytes with
          | None => None
          | Some (date_value, bytes) =>
              match decode_uint 4 bytes with
              | None => None
              | Some (folio_value, bytes) =>
                  match decode_bytes 1 bytes with
                  | None => None
                  | Some (operation_type_value, bytes) =>
                      Some ({| id_instrument := id_instrument_value; date := date_value; folio := folio_value; operation_type := operation_type_value |}, bytes)
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

  End OrderCancellationMessage.

  Module OrderChangeMessage.

    (** Message sent when the order modifies any of its data, the system assigns it a new priority in the electronic book, the order to be replaced is identified with the original Instrument, Date, and Folio, and the new priority assignment in the electronic book appears in the New Date and Folio fields. *)
    Record t := {
      id_instrument : N;
      original_date : N;
      original_folio : N;
      new_date : N;
      new_folio : N;
      direction : list byte;
      volume : N;
      price : N;
      operation_type : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (id_instrument record < 256 ^ N.of_nat 4)%N /\
      (original_date record < 256 ^ N.of_nat 8)%N /\
      (original_folio record < 256 ^ N.of_nat 4)%N /\
      (new_date record < 256 ^ N.of_nat 8)%N /\
      (new_folio record < 256 ^ N.of_nat 4)%N /\
      Datatypes.length (direction record) = 1 /\
      (volume record < 256 ^ N.of_nat 4)%N /\
      (price record < 256 ^ N.of_nat 8)%N /\
      Datatypes.length (operation_type record) = 1.

    Definition encode (record : t) : list byte :=
      encode_uint 4 (id_instrument record) ++
      encode_uint 8 (original_date record) ++
      encode_uint 4 (original_folio record) ++
      encode_uint 8 (new_date record) ++
      encode_uint 4 (new_folio record) ++
      encode_bytes 1 (direction record) ++
      encode_uint 4 (volume record) ++
      encode_uint 8 (price record) ++
      encode_bytes 1 (operation_type record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 4 bytes with
      | None => None
      | Some (id_instrument_value, bytes) =>
          match decode_uint 8 bytes with
          | None => None
          | Some (original_date_value, bytes) =>
              match decode_uint 4 bytes with
              | None => None
              | Some (original_folio_value, bytes) =>
                  match decode_uint 8 bytes with
                  | None => None
                  | Some (new_date_value, bytes) =>
                      match decode_uint 4 bytes with
                      | None => None
                      | Some (new_folio_value, bytes) =>
                          match decode_bytes 1 bytes with
                          | None => None
                          | Some (direction_value, bytes) =>
                              match decode_uint 4 bytes with
                              | None => None
                              | Some (volume_value, bytes) =>
                                  match decode_uint 8 bytes with
                                  | None => None
                                  | Some (price_value, bytes) =>
                                      match decode_bytes 1 bytes with
                                      | None => None
                                      | Some (operation_type_value, bytes) =>
                                          Some ({| id_instrument := id_instrument_value; original_date := original_date_value; original_folio := original_folio_value; new_date := new_date_value; new_folio := new_folio_value; direction := direction_value; volume := volume_value; price := price_value; operation_type := operation_type_value |}, bytes)
                                      end
                                  end
                              end
                          end
                      end
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 42.
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
      rewrite decode_encode_uint by exact bound_3.
      rewrite decode_encode_uint by exact bound_4.
      rewrite decode_encode_bytes by exact bound_5.
      rewrite decode_encode_uint by exact bound_6.
      rewrite decode_encode_uint by exact bound_7.
      rewrite decode_encode_bytes by exact bound_8.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End OrderChangeMessage.

End BmvMarketDataProduct37V11.
