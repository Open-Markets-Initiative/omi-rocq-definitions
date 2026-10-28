From Stdlib Require Import List.
From Stdlib Require Import NArith.
From Stdlib Require Import Lia.
From Stdlib Require Import Strings.Byte.
From Omi Require Import Wire.

Import ListNotations.

(** * Box Options Market Sola Trade Reporting

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

Module BoxOptionsSolaTradeReportingV45Client.

  Module MessageHeader.

    (** Atr message header, twenty eight bytes opening every message either way *)
    Record t := {
      source : list byte;
      destination : list byte;
      message_type : list byte;
      message_flag : list byte;
      control_byte : list byte;
      sequence_number : list byte;
      acknowledgement_sequence_number : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (source record) = 4 /\
      Datatypes.length (destination record) = 4 /\
      Datatypes.length (message_type record) = 2 /\
      Datatypes.length (message_flag record) = 1 /\
      Datatypes.length (control_byte record) = 1 /\
      Datatypes.length (sequence_number record) = 8 /\
      Datatypes.length (acknowledgement_sequence_number record) = 8.

    Definition encode (record : t) : list byte :=
      encode_bytes 4 (source record) ++
      encode_bytes 4 (destination record) ++
      encode_bytes 2 (message_type record) ++
      encode_bytes 1 (message_flag record) ++
      encode_bytes 1 (control_byte record) ++
      encode_bytes 8 (sequence_number record) ++
      encode_bytes 8 (acknowledgement_sequence_number record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 4 bytes with
      | None => None
      | Some (source_value, bytes) =>
          match decode_bytes 4 bytes with
          | None => None
          | Some (destination_value, bytes) =>
              match decode_bytes 2 bytes with
              | None => None
              | Some (message_type_value, bytes) =>
                  match decode_bytes 1 bytes with
                  | None => None
                  | Some (message_flag_value, bytes) =>
                      match decode_bytes 1 bytes with
                      | None => None
                      | Some (control_byte_value, bytes) =>
                          match decode_bytes 8 bytes with
                          | None => None
                          | Some (sequence_number_value, bytes) =>
                              match decode_bytes 8 bytes with
                              | None => None
                              | Some (acknowledgement_sequence_number_value, bytes) =>
                                  Some ({| source := source_value; destination := destination_value; message_type := message_type_value; message_flag := message_flag_value; control_byte := control_byte_value; sequence_number := sequence_number_value; acknowledgement_sequence_number := acknowledgement_sequence_number_value |}, bytes)
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

  Module RestartRequest.

    Record t := {
      sequence_number : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (sequence_number record) = 8.

    Definition encode (record : t) : list byte :=
      encode_bytes 8 (sequence_number record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 8 bytes with
      | None => None
      | Some (sequence_number_value, bytes) =>
          Some ({| sequence_number := sequence_number_value |}, bytes)
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 8.
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

  End RestartRequest.

  Module ClientSignon.

    Record t := {
      member_number : list byte;
      initial_sequence_number : list byte;
      protocol_version : list byte;
      time : list byte;
      username : list byte;
      password_md_5_encryption : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (member_number record) = 4 /\
      Datatypes.length (initial_sequence_number record) = 8 /\
      Datatypes.length (protocol_version record) = 2 /\
      Datatypes.length (time record) = 6 /\
      Datatypes.length (username record) = 8 /\
      Datatypes.length (password_md_5_encryption record) = 8.

    Definition encode (record : t) : list byte :=
      encode_bytes 4 (member_number record) ++
      encode_bytes 8 (initial_sequence_number record) ++
      encode_bytes 2 (protocol_version record) ++
      encode_bytes 6 (time record) ++
      encode_bytes 8 (username record) ++
      encode_bytes 8 (password_md_5_encryption record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 4 bytes with
      | None => None
      | Some (member_number_value, bytes) =>
          match decode_bytes 8 bytes with
          | None => None
          | Some (initial_sequence_number_value, bytes) =>
              match decode_bytes 2 bytes with
              | None => None
              | Some (protocol_version_value, bytes) =>
                  match decode_bytes 6 bytes with
                  | None => None
                  | Some (time_value, bytes) =>
                      match decode_bytes 8 bytes with
                      | None => None
                      | Some (username_value, bytes) =>
                          match decode_bytes 8 bytes with
                          | None => None
                          | Some (password_md_5_encryption_value, bytes) =>
                              Some ({| member_number := member_number_value; initial_sequence_number := initial_sequence_number_value; protocol_version := protocol_version_value; time := time_value; username := username_value; password_md_5_encryption := password_md_5_encryption_value |}, bytes)
                          end
                      end
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 36.
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

  End ClientSignon.

  Module NewAllocation.

    (** The guide heads this message 106 bytes, while the fields it states measure 122 including the 28 byte header. *)
    Record t := {
      reference_transaction_id : list byte;
      reference_trade_number : list byte;
      give_up_firm : list byte;
      volume : list byte;
      account_type : list byte;
      open_close : list byte;
      client_account_number : list byte;
      sub_trader_id : list byte;
      cmta_broker : list byte;
      client_memo : list byte;
      additional_firm : list byte;
      additional_client_memo : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (reference_transaction_id record) = 10 /\
      Datatypes.length (reference_trade_number record) = 15 /\
      Datatypes.length (give_up_firm record) = 4 /\
      Datatypes.length (volume record) = 8 /\
      Datatypes.length (account_type record) = 1 /\
      Datatypes.length (open_close record) = 1 /\
      Datatypes.length (client_account_number record) = 12 /\
      Datatypes.length (sub_trader_id record) = 3 /\
      Datatypes.length (cmta_broker record) = 4 /\
      Datatypes.length (client_memo record) = 16 /\
      Datatypes.length (additional_firm record) = 4 /\
      Datatypes.length (additional_client_memo record) = 16.

    Definition encode (record : t) : list byte :=
      encode_bytes 10 (reference_transaction_id record) ++
      encode_bytes 15 (reference_trade_number record) ++
      encode_bytes 4 (give_up_firm record) ++
      encode_bytes 8 (volume record) ++
      encode_bytes 1 (account_type record) ++
      encode_bytes 1 (open_close record) ++
      encode_bytes 12 (client_account_number record) ++
      encode_bytes 3 (sub_trader_id record) ++
      encode_bytes 4 (cmta_broker record) ++
      encode_bytes 16 (client_memo record) ++
      encode_bytes 4 (additional_firm record) ++
      encode_bytes 16 (additional_client_memo record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 10 bytes with
      | None => None
      | Some (reference_transaction_id_value, bytes) =>
          match decode_bytes 15 bytes with
          | None => None
          | Some (reference_trade_number_value, bytes) =>
              match decode_bytes 4 bytes with
              | None => None
              | Some (give_up_firm_value, bytes) =>
                  match decode_bytes 8 bytes with
                  | None => None
                  | Some (volume_value, bytes) =>
                      match decode_bytes 1 bytes with
                      | None => None
                      | Some (account_type_value, bytes) =>
                          match decode_bytes 1 bytes with
                          | None => None
                          | Some (open_close_value, bytes) =>
                              match decode_bytes 12 bytes with
                              | None => None
                              | Some (client_account_number_value, bytes) =>
                                  match decode_bytes 3 bytes with
                                  | None => None
                                  | Some (sub_trader_id_value, bytes) =>
                                      match decode_bytes 4 bytes with
                                      | None => None
                                      | Some (cmta_broker_value, bytes) =>
                                          match decode_bytes 16 bytes with
                                          | None => None
                                          | Some (client_memo_value, bytes) =>
                                              match decode_bytes 4 bytes with
                                              | None => None
                                              | Some (additional_firm_value, bytes) =>
                                                  match decode_bytes 16 bytes with
                                                  | None => None
                                                  | Some (additional_client_memo_value, bytes) =>
                                                      Some ({| reference_transaction_id := reference_transaction_id_value; reference_trade_number := reference_trade_number_value; give_up_firm := give_up_firm_value; volume := volume_value; account_type := account_type_value; open_close := open_close_value; client_account_number := client_account_number_value; sub_trader_id := sub_trader_id_value; cmta_broker := cmta_broker_value; client_memo := client_memo_value; additional_firm := additional_firm_value; additional_client_memo := additional_client_memo_value |}, bytes)
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

    Theorem encode_length : forall record, Datatypes.length (encode record) = 94.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_bytes_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 [bound_1 [bound_2 [bound_3 [bound_4 [bound_5 [bound_6 [bound_7 [bound_8 [bound_9 [bound_10 bound_11]]]]]]]]]]].
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
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End NewAllocation.

  Module ModifyAllocation.

    (** The guide states this message as having the same structure as message type 42, whose fields are written out here. The guide heads this message 106 bytes, while the fields it states measure 122 including the 28 byte header. *)
    Record t := {
      reference_transaction_id : list byte;
      reference_trade_number : list byte;
      give_up_firm : list byte;
      volume : list byte;
      account_type : list byte;
      open_close : list byte;
      client_account_number : list byte;
      sub_trader_id : list byte;
      cmta_broker : list byte;
      client_memo : list byte;
      additional_firm : list byte;
      additional_client_memo : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (reference_transaction_id record) = 10 /\
      Datatypes.length (reference_trade_number record) = 15 /\
      Datatypes.length (give_up_firm record) = 4 /\
      Datatypes.length (volume record) = 8 /\
      Datatypes.length (account_type record) = 1 /\
      Datatypes.length (open_close record) = 1 /\
      Datatypes.length (client_account_number record) = 12 /\
      Datatypes.length (sub_trader_id record) = 3 /\
      Datatypes.length (cmta_broker record) = 4 /\
      Datatypes.length (client_memo record) = 16 /\
      Datatypes.length (additional_firm record) = 4 /\
      Datatypes.length (additional_client_memo record) = 16.

    Definition encode (record : t) : list byte :=
      encode_bytes 10 (reference_transaction_id record) ++
      encode_bytes 15 (reference_trade_number record) ++
      encode_bytes 4 (give_up_firm record) ++
      encode_bytes 8 (volume record) ++
      encode_bytes 1 (account_type record) ++
      encode_bytes 1 (open_close record) ++
      encode_bytes 12 (client_account_number record) ++
      encode_bytes 3 (sub_trader_id record) ++
      encode_bytes 4 (cmta_broker record) ++
      encode_bytes 16 (client_memo record) ++
      encode_bytes 4 (additional_firm record) ++
      encode_bytes 16 (additional_client_memo record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 10 bytes with
      | None => None
      | Some (reference_transaction_id_value, bytes) =>
          match decode_bytes 15 bytes with
          | None => None
          | Some (reference_trade_number_value, bytes) =>
              match decode_bytes 4 bytes with
              | None => None
              | Some (give_up_firm_value, bytes) =>
                  match decode_bytes 8 bytes with
                  | None => None
                  | Some (volume_value, bytes) =>
                      match decode_bytes 1 bytes with
                      | None => None
                      | Some (account_type_value, bytes) =>
                          match decode_bytes 1 bytes with
                          | None => None
                          | Some (open_close_value, bytes) =>
                              match decode_bytes 12 bytes with
                              | None => None
                              | Some (client_account_number_value, bytes) =>
                                  match decode_bytes 3 bytes with
                                  | None => None
                                  | Some (sub_trader_id_value, bytes) =>
                                      match decode_bytes 4 bytes with
                                      | None => None
                                      | Some (cmta_broker_value, bytes) =>
                                          match decode_bytes 16 bytes with
                                          | None => None
                                          | Some (client_memo_value, bytes) =>
                                              match decode_bytes 4 bytes with
                                              | None => None
                                              | Some (additional_firm_value, bytes) =>
                                                  match decode_bytes 16 bytes with
                                                  | None => None
                                                  | Some (additional_client_memo_value, bytes) =>
                                                      Some ({| reference_transaction_id := reference_transaction_id_value; reference_trade_number := reference_trade_number_value; give_up_firm := give_up_firm_value; volume := volume_value; account_type := account_type_value; open_close := open_close_value; client_account_number := client_account_number_value; sub_trader_id := sub_trader_id_value; cmta_broker := cmta_broker_value; client_memo := client_memo_value; additional_firm := additional_firm_value; additional_client_memo := additional_client_memo_value |}, bytes)
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

    Theorem encode_length : forall record, Datatypes.length (encode record) = 94.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_bytes_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 [bound_1 [bound_2 [bound_3 [bound_4 [bound_5 [bound_6 [bound_7 [bound_8 [bound_9 [bound_10 bound_11]]]]]]]]]]].
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
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End ModifyAllocation.

  Module DeleteAllocation.

    Record t := {
      reference_transaction_id : list byte;
      reference_trade_number : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (reference_transaction_id record) = 10 /\
      Datatypes.length (reference_trade_number record) = 15.

    Definition encode (record : t) : list byte :=
      encode_bytes 10 (reference_transaction_id record) ++
      encode_bytes 15 (reference_trade_number record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 10 bytes with
      | None => None
      | Some (reference_transaction_id_value, bytes) =>
          match decode_bytes 15 bytes with
          | None => None
          | Some (reference_trade_number_value, bytes) =>
              Some ({| reference_transaction_id := reference_transaction_id_value; reference_trade_number := reference_trade_number_value |}, bytes)
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 25.
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

  End DeleteAllocation.

  Module NewGiveUp.

    (** The guide states this message as having the same structure as message type 42, whose fields are written out here. The guide heads this message 106 bytes, while the fields it states measure 122 including the 28 byte header. *)
    Record t := {
      reference_transaction_id : list byte;
      reference_trade_number : list byte;
      give_up_firm : list byte;
      volume : list byte;
      account_type : list byte;
      open_close : list byte;
      client_account_number : list byte;
      sub_trader_id : list byte;
      cmta_broker : list byte;
      client_memo : list byte;
      additional_firm : list byte;
      additional_client_memo : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (reference_transaction_id record) = 10 /\
      Datatypes.length (reference_trade_number record) = 15 /\
      Datatypes.length (give_up_firm record) = 4 /\
      Datatypes.length (volume record) = 8 /\
      Datatypes.length (account_type record) = 1 /\
      Datatypes.length (open_close record) = 1 /\
      Datatypes.length (client_account_number record) = 12 /\
      Datatypes.length (sub_trader_id record) = 3 /\
      Datatypes.length (cmta_broker record) = 4 /\
      Datatypes.length (client_memo record) = 16 /\
      Datatypes.length (additional_firm record) = 4 /\
      Datatypes.length (additional_client_memo record) = 16.

    Definition encode (record : t) : list byte :=
      encode_bytes 10 (reference_transaction_id record) ++
      encode_bytes 15 (reference_trade_number record) ++
      encode_bytes 4 (give_up_firm record) ++
      encode_bytes 8 (volume record) ++
      encode_bytes 1 (account_type record) ++
      encode_bytes 1 (open_close record) ++
      encode_bytes 12 (client_account_number record) ++
      encode_bytes 3 (sub_trader_id record) ++
      encode_bytes 4 (cmta_broker record) ++
      encode_bytes 16 (client_memo record) ++
      encode_bytes 4 (additional_firm record) ++
      encode_bytes 16 (additional_client_memo record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 10 bytes with
      | None => None
      | Some (reference_transaction_id_value, bytes) =>
          match decode_bytes 15 bytes with
          | None => None
          | Some (reference_trade_number_value, bytes) =>
              match decode_bytes 4 bytes with
              | None => None
              | Some (give_up_firm_value, bytes) =>
                  match decode_bytes 8 bytes with
                  | None => None
                  | Some (volume_value, bytes) =>
                      match decode_bytes 1 bytes with
                      | None => None
                      | Some (account_type_value, bytes) =>
                          match decode_bytes 1 bytes with
                          | None => None
                          | Some (open_close_value, bytes) =>
                              match decode_bytes 12 bytes with
                              | None => None
                              | Some (client_account_number_value, bytes) =>
                                  match decode_bytes 3 bytes with
                                  | None => None
                                  | Some (sub_trader_id_value, bytes) =>
                                      match decode_bytes 4 bytes with
                                      | None => None
                                      | Some (cmta_broker_value, bytes) =>
                                          match decode_bytes 16 bytes with
                                          | None => None
                                          | Some (client_memo_value, bytes) =>
                                              match decode_bytes 4 bytes with
                                              | None => None
                                              | Some (additional_firm_value, bytes) =>
                                                  match decode_bytes 16 bytes with
                                                  | None => None
                                                  | Some (additional_client_memo_value, bytes) =>
                                                      Some ({| reference_transaction_id := reference_transaction_id_value; reference_trade_number := reference_trade_number_value; give_up_firm := give_up_firm_value; volume := volume_value; account_type := account_type_value; open_close := open_close_value; client_account_number := client_account_number_value; sub_trader_id := sub_trader_id_value; cmta_broker := cmta_broker_value; client_memo := client_memo_value; additional_firm := additional_firm_value; additional_client_memo := additional_client_memo_value |}, bytes)
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

    Theorem encode_length : forall record, Datatypes.length (encode record) = 94.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_bytes_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 [bound_1 [bound_2 [bound_3 [bound_4 [bound_5 [bound_6 [bound_7 [bound_8 [bound_9 [bound_10 bound_11]]]]]]]]]]].
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
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End NewGiveUp.

  Module ModifyGiveUp.

    (** The guide states this message as having the same structure as message type 42, whose fields are written out here. The guide heads this message 106 bytes, while the fields it states measure 122 including the 28 byte header. *)
    Record t := {
      reference_transaction_id : list byte;
      reference_trade_number : list byte;
      give_up_firm : list byte;
      volume : list byte;
      account_type : list byte;
      open_close : list byte;
      client_account_number : list byte;
      sub_trader_id : list byte;
      cmta_broker : list byte;
      client_memo : list byte;
      additional_firm : list byte;
      additional_client_memo : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (reference_transaction_id record) = 10 /\
      Datatypes.length (reference_trade_number record) = 15 /\
      Datatypes.length (give_up_firm record) = 4 /\
      Datatypes.length (volume record) = 8 /\
      Datatypes.length (account_type record) = 1 /\
      Datatypes.length (open_close record) = 1 /\
      Datatypes.length (client_account_number record) = 12 /\
      Datatypes.length (sub_trader_id record) = 3 /\
      Datatypes.length (cmta_broker record) = 4 /\
      Datatypes.length (client_memo record) = 16 /\
      Datatypes.length (additional_firm record) = 4 /\
      Datatypes.length (additional_client_memo record) = 16.

    Definition encode (record : t) : list byte :=
      encode_bytes 10 (reference_transaction_id record) ++
      encode_bytes 15 (reference_trade_number record) ++
      encode_bytes 4 (give_up_firm record) ++
      encode_bytes 8 (volume record) ++
      encode_bytes 1 (account_type record) ++
      encode_bytes 1 (open_close record) ++
      encode_bytes 12 (client_account_number record) ++
      encode_bytes 3 (sub_trader_id record) ++
      encode_bytes 4 (cmta_broker record) ++
      encode_bytes 16 (client_memo record) ++
      encode_bytes 4 (additional_firm record) ++
      encode_bytes 16 (additional_client_memo record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 10 bytes with
      | None => None
      | Some (reference_transaction_id_value, bytes) =>
          match decode_bytes 15 bytes with
          | None => None
          | Some (reference_trade_number_value, bytes) =>
              match decode_bytes 4 bytes with
              | None => None
              | Some (give_up_firm_value, bytes) =>
                  match decode_bytes 8 bytes with
                  | None => None
                  | Some (volume_value, bytes) =>
                      match decode_bytes 1 bytes with
                      | None => None
                      | Some (account_type_value, bytes) =>
                          match decode_bytes 1 bytes with
                          | None => None
                          | Some (open_close_value, bytes) =>
                              match decode_bytes 12 bytes with
                              | None => None
                              | Some (client_account_number_value, bytes) =>
                                  match decode_bytes 3 bytes with
                                  | None => None
                                  | Some (sub_trader_id_value, bytes) =>
                                      match decode_bytes 4 bytes with
                                      | None => None
                                      | Some (cmta_broker_value, bytes) =>
                                          match decode_bytes 16 bytes with
                                          | None => None
                                          | Some (client_memo_value, bytes) =>
                                              match decode_bytes 4 bytes with
                                              | None => None
                                              | Some (additional_firm_value, bytes) =>
                                                  match decode_bytes 16 bytes with
                                                  | None => None
                                                  | Some (additional_client_memo_value, bytes) =>
                                                      Some ({| reference_transaction_id := reference_transaction_id_value; reference_trade_number := reference_trade_number_value; give_up_firm := give_up_firm_value; volume := volume_value; account_type := account_type_value; open_close := open_close_value; client_account_number := client_account_number_value; sub_trader_id := sub_trader_id_value; cmta_broker := cmta_broker_value; client_memo := client_memo_value; additional_firm := additional_firm_value; additional_client_memo := additional_client_memo_value |}, bytes)
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

    Theorem encode_length : forall record, Datatypes.length (encode record) = 94.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_bytes_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 [bound_1 [bound_2 [bound_3 [bound_4 [bound_5 [bound_6 [bound_7 [bound_8 [bound_9 [bound_10 bound_11]]]]]]]]]]].
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
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End ModifyGiveUp.

  Module DeleteGiveUp.

    (** The guide states this message as having the same structure as message type 44, whose fields are written out here. *)
    Record t := {
      reference_transaction_id : list byte;
      reference_trade_number : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (reference_transaction_id record) = 10 /\
      Datatypes.length (reference_trade_number record) = 15.

    Definition encode (record : t) : list byte :=
      encode_bytes 10 (reference_transaction_id record) ++
      encode_bytes 15 (reference_trade_number record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 10 bytes with
      | None => None
      | Some (reference_transaction_id_value, bytes) =>
          match decode_bytes 15 bytes with
          | None => None
          | Some (reference_trade_number_value, bytes) =>
              Some ({| reference_transaction_id := reference_transaction_id_value; reference_trade_number := reference_trade_number_value |}, bytes)
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 25.
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

  End DeleteGiveUp.

End BoxOptionsSolaTradeReportingV45Client.
