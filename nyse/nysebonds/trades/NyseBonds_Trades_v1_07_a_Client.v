From Stdlib Require Import List.
From Stdlib Require Import NArith.
From Stdlib Require Import Lia.
From Stdlib Require Import Strings.Byte.
From Omi Require Import Wire.

Import ListNotations.

(** * New York Stock Exchange Trades

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

Module NyseBondsTradesV107AClient.

  Module ClientMessageHeader.

    (** The single Ascii type code that opens every client message *)
    Record t := {
      client_message_type : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (client_message_type record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 1 (client_message_type record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 1 bytes with
      | None => None
      | Some (client_message_type_value, bytes) =>
          Some ({| client_message_type := client_message_type_value |}, bytes)
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

  End ClientMessageHeader.

  Module LoginMessage.

    (** Authenticates the subscriber and names which trade data the session subscribes to.
      A starting sequence number of 0 requests current data; a greater number than the exchange holds
      is treated as 0, and a negative one is rejected *)
    Record t := {
      username : list byte;
      password : list byte;
      login_sequence_number : list byte;
      listed_subscription : list byte;
      etf_subscription : list byte;
      otc_subscription : list byte;
      arca_edge_subscription : list byte;
      bond_subscription : list byte;
      options_subscription : list byte;
      client_padding : list byte;
      etx : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (username record) = 8 /\
      Datatypes.length (password record) = 10 /\
      Datatypes.length (login_sequence_number record) = 10 /\
      Datatypes.length (listed_subscription record) = 1 /\
      Datatypes.length (etf_subscription record) = 1 /\
      Datatypes.length (otc_subscription record) = 1 /\
      Datatypes.length (arca_edge_subscription record) = 1 /\
      Datatypes.length (bond_subscription record) = 1 /\
      Datatypes.length (options_subscription record) = 1 /\
      Datatypes.length (client_padding record) = 5 /\
      (etx record < 256 ^ N.of_nat 1)%N.

    Definition encode (record : t) : list byte :=
      encode_bytes 8 (username record) ++
      encode_bytes 10 (password record) ++
      encode_bytes 10 (login_sequence_number record) ++
      encode_bytes 1 (listed_subscription record) ++
      encode_bytes 1 (etf_subscription record) ++
      encode_bytes 1 (otc_subscription record) ++
      encode_bytes 1 (arca_edge_subscription record) ++
      encode_bytes 1 (bond_subscription record) ++
      encode_bytes 1 (options_subscription record) ++
      encode_bytes 5 (client_padding record) ++
      encode_uint 1 (etx record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 8 bytes with
      | None => None
      | Some (username_value, bytes) =>
          match decode_bytes 10 bytes with
          | None => None
          | Some (password_value, bytes) =>
              match decode_bytes 10 bytes with
              | None => None
              | Some (login_sequence_number_value, bytes) =>
                  match decode_bytes 1 bytes with
                  | None => None
                  | Some (listed_subscription_value, bytes) =>
                      match decode_bytes 1 bytes with
                      | None => None
                      | Some (etf_subscription_value, bytes) =>
                          match decode_bytes 1 bytes with
                          | None => None
                          | Some (otc_subscription_value, bytes) =>
                              match decode_bytes 1 bytes with
                              | None => None
                              | Some (arca_edge_subscription_value, bytes) =>
                                  match decode_bytes 1 bytes with
                                  | None => None
                                  | Some (bond_subscription_value, bytes) =>
                                      match decode_bytes 1 bytes with
                                      | None => None
                                      | Some (options_subscription_value, bytes) =>
                                          match decode_bytes 5 bytes with
                                          | None => None
                                          | Some (client_padding_value, bytes) =>
                                              match decode_uint 1 bytes with
                                              | None => None
                                              | Some (etx_value, bytes) =>
                                                  Some ({| username := username_value; password := password_value; login_sequence_number := login_sequence_number_value; listed_subscription := listed_subscription_value; etf_subscription := etf_subscription_value; otc_subscription := otc_subscription_value; arca_edge_subscription := arca_edge_subscription_value; bond_subscription := bond_subscription_value; options_subscription := options_subscription_value; client_padding := client_padding_value; etx := etx_value |}, bytes)
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
      rewrite !length_app, !encode_bytes_length, !encode_uint_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 [bound_1 [bound_2 [bound_3 [bound_4 [bound_5 [bound_6 [bound_7 [bound_8 [bound_9 bound_10]]]]]]]]]].
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
      rewrite decode_encode_uint by exact bound_10.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End LoginMessage.

  Module LogoffMessage.

    (** Closes the session. Carries only its type code and the terminator *)
    Record t := {
      etx : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (etx record < 256 ^ N.of_nat 1)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 1 (etx record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 1 bytes with
      | None => None
      | Some (etx_value, bytes) =>
          Some ({| etx := etx_value |}, bytes)
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

  End LogoffMessage.

  Module HeartbeatResponseMessage.

    (** Answers a Heartbeat Request. The exchange closes the connection if no response
      arrives within 60 seconds. Table 9 of the specification labels the second field "Username",
      which is a copy and paste slip - its own description reads "Message Terminating Character" *)
    Record t := {
      etx : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (etx record < 256 ^ N.of_nat 1)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 1 (etx record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 1 bytes with
      | None => None
      | Some (etx_value, bytes) =>
          Some ({| etx := etx_value |}, bytes)
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

  End HeartbeatResponseMessage.

  Module TestRequestMessage.

    (** Signals or tests that the Tcp connection is open. Any text given is echoed back
      in a Test Response *)
    Record t := {
      test_request_text : list byte;
      etx : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (test_request_text record) = 20 /\
      (etx record < 256 ^ N.of_nat 1)%N.

    Definition encode (record : t) : list byte :=
      encode_bytes 20 (test_request_text record) ++
      encode_uint 1 (etx record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 20 bytes with
      | None => None
      | Some (test_request_text_value, bytes) =>
          match decode_uint 1 bytes with
          | None => None
          | Some (etx_value, bytes) =>
              Some ({| test_request_text := test_request_text_value; etx := etx_value |}, bytes)
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 21.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_bytes_length, !encode_uint_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 bound_1].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_bytes by exact bound_0.
      rewrite decode_encode_uint by exact bound_1.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End TestRequestMessage.

End NyseBondsTradesV107AClient.
