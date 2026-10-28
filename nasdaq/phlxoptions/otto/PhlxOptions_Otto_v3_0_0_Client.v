From Stdlib Require Import List.
From Stdlib Require Import NArith.
From Stdlib Require Import Lia.
From Stdlib Require Import Strings.Byte.
From Omi Require Import Wire.

Import ListNotations.

(** * National Association of Securities Dealers Automated Quotations (Nasdaq) Ouch to Trade Options

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
      - a length prefix framing what follows
      - a run counted by a field
  *)

Module PhlxOptionsOttoV300Client.

  Module ClientPacketHeader.

    (** Packet header of a packet sent by the client *)
    Record t := {
      packet_length : N;
      client_packet_type : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (packet_length record < 256 ^ N.of_nat 2)%N /\
      Datatypes.length (client_packet_type record) = 1.

    Definition encode (record : t) : list byte :=
      encode_uint 2 (packet_length record) ++
      encode_bytes 1 (client_packet_type record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 2 bytes with
      | None => None
      | Some (packet_length_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (client_packet_type_value, bytes) =>
              Some ({| packet_length := packet_length_value; client_packet_type := client_packet_type_value |}, bytes)
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

  End ClientPacketHeader.

  Module LoginRequestPacket.

    (** The SoupBinTCP client must send a Login Request Packet immediately upon establishing a new TCP/IP socket connection to the server *)
    Record t := {
      username : list byte;
      password : list byte;
      requested_session : list byte;
      requested_sequence_number : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (username record) = 6 /\
      Datatypes.length (password record) = 10 /\
      Datatypes.length (requested_session record) = 10 /\
      Datatypes.length (requested_sequence_number record) = 20.

    Definition encode (record : t) : list byte :=
      encode_bytes 6 (username record) ++
      encode_bytes 10 (password record) ++
      encode_bytes 10 (requested_session record) ++
      encode_bytes 20 (requested_sequence_number record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 6 bytes with
      | None => None
      | Some (username_value, bytes) =>
          match decode_bytes 10 bytes with
          | None => None
          | Some (password_value, bytes) =>
              match decode_bytes 10 bytes with
              | None => None
              | Some (requested_session_value, bytes) =>
                  match decode_bytes 20 bytes with
                  | None => None
                  | Some (requested_sequence_number_value, bytes) =>
                      Some ({| username := username_value; password := password_value; requested_session := requested_session_value; requested_sequence_number := requested_sequence_number_value |}, bytes)
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 46.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_bytes_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 [bound_1 [bound_2 bound_3]]].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_bytes by exact bound_0.
      rewrite decode_encode_bytes by exact bound_1.
      rewrite decode_encode_bytes by exact bound_2.
      rewrite decode_encode_bytes by exact bound_3.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End LoginRequestPacket.

  Module NewOrderShortFormMessage.

    (** Short format of the New Order request is a compact message (50 bytes) with limited flexibility: simple and multi-leg instruments, quantity up to 65535, auction responses, default clearing configuration for the Firm. Acknowledged by Order Accepted (Short Form). *)
    Record t := {
      firm_id : list byte;
      instrument_id : N;
      cl_ord_id : list byte;
      alo_inst : list byte;
      iso : list byte;
      side : list byte;
      order_type : list byte;
      price : N;
      quantity_short : N;
      tif : list byte;
      capacity : list byte;
      auction_type : list byte;
      auction_id : N;
      price_protection : list byte;
      position_effect_mask : N;
      stock_capacity : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (firm_id record) = 4 /\
      (instrument_id record < 256 ^ N.of_nat 4)%N /\
      Datatypes.length (cl_ord_id record) = 16 /\
      Datatypes.length (alo_inst record) = 1 /\
      Datatypes.length (iso record) = 1 /\
      Datatypes.length (side record) = 1 /\
      Datatypes.length (order_type record) = 1 /\
      (price record < 256 ^ N.of_nat 8)%N /\
      (quantity_short record < 256 ^ N.of_nat 2)%N /\
      Datatypes.length (tif record) = 1 /\
      Datatypes.length (capacity record) = 1 /\
      Datatypes.length (auction_type record) = 1 /\
      (auction_id record < 256 ^ N.of_nat 4)%N /\
      Datatypes.length (price_protection record) = 1 /\
      (position_effect_mask record < 256 ^ N.of_nat 2)%N /\
      Datatypes.length (stock_capacity record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 4 (firm_id record) ++
      encode_uint 4 (instrument_id record) ++
      encode_bytes 16 (cl_ord_id record) ++
      encode_bytes 1 (alo_inst record) ++
      encode_bytes 1 (iso record) ++
      encode_bytes 1 (side record) ++
      encode_bytes 1 (order_type record) ++
      encode_uint 8 (price record) ++
      encode_uint 2 (quantity_short record) ++
      encode_bytes 1 (tif record) ++
      encode_bytes 1 (capacity record) ++
      encode_bytes 1 (auction_type record) ++
      encode_uint 4 (auction_id record) ++
      encode_bytes 1 (price_protection record) ++
      encode_uint 2 (position_effect_mask record) ++
      encode_bytes 1 (stock_capacity record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 4 bytes with
      | None => None
      | Some (firm_id_value, bytes) =>
          match decode_uint 4 bytes with
          | None => None
          | Some (instrument_id_value, bytes) =>
              match decode_bytes 16 bytes with
              | None => None
              | Some (cl_ord_id_value, bytes) =>
                  match decode_bytes 1 bytes with
                  | None => None
                  | Some (alo_inst_value, bytes) =>
                      match decode_bytes 1 bytes with
                      | None => None
                      | Some (iso_value, bytes) =>
                          match decode_bytes 1 bytes with
                          | None => None
                          | Some (side_value, bytes) =>
                              match decode_bytes 1 bytes with
                              | None => None
                              | Some (order_type_value, bytes) =>
                                  match decode_uint 8 bytes with
                                  | None => None
                                  | Some (price_value, bytes) =>
                                      match decode_uint 2 bytes with
                                      | None => None
                                      | Some (quantity_short_value, bytes) =>
                                          match decode_bytes 1 bytes with
                                          | None => None
                                          | Some (tif_value, bytes) =>
                                              match decode_bytes 1 bytes with
                                              | None => None
                                              | Some (capacity_value, bytes) =>
                                                  match decode_bytes 1 bytes with
                                                  | None => None
                                                  | Some (auction_type_value, bytes) =>
                                                      match decode_uint 4 bytes with
                                                      | None => None
                                                      | Some (auction_id_value, bytes) =>
                                                          match decode_bytes 1 bytes with
                                                          | None => None
                                                          | Some (price_protection_value, bytes) =>
                                                              match decode_uint 2 bytes with
                                                              | None => None
                                                              | Some (position_effect_mask_value, bytes) =>
                                                                  match decode_bytes 1 bytes with
                                                                  | None => None
                                                                  | Some (stock_capacity_value, bytes) =>
                                                                      Some ({| firm_id := firm_id_value; instrument_id := instrument_id_value; cl_ord_id := cl_ord_id_value; alo_inst := alo_inst_value; iso := iso_value; side := side_value; order_type := order_type_value; price := price_value; quantity_short := quantity_short_value; tif := tif_value; capacity := capacity_value; auction_type := auction_type_value; auction_id := auction_id_value; price_protection := price_protection_value; position_effect_mask := position_effect_mask_value; stock_capacity := stock_capacity_value |}, bytes)
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
      rewrite !length_app, !encode_bytes_length, !encode_uint_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 [bound_1 [bound_2 [bound_3 [bound_4 [bound_5 [bound_6 [bound_7 [bound_8 [bound_9 [bound_10 [bound_11 [bound_12 [bound_13 [bound_14 bound_15]]]]]]]]]]]]]]].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_bytes by exact bound_0.
      rewrite decode_encode_uint by exact bound_1.
      rewrite decode_encode_bytes by exact bound_2.
      rewrite decode_encode_bytes by exact bound_3.
      rewrite decode_encode_bytes by exact bound_4.
      rewrite decode_encode_bytes by exact bound_5.
      rewrite decode_encode_bytes by exact bound_6.
      rewrite decode_encode_uint by exact bound_7.
      rewrite decode_encode_uint by exact bound_8.
      rewrite decode_encode_bytes by exact bound_9.
      rewrite decode_encode_bytes by exact bound_10.
      rewrite decode_encode_bytes by exact bound_11.
      rewrite decode_encode_uint by exact bound_12.
      rewrite decode_encode_bytes by exact bound_13.
      rewrite decode_encode_uint by exact bound_14.
      rewrite decode_encode_bytes by exact bound_15.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End NewOrderShortFormMessage.

  Module ReplaceOrderMessage.

    (** Replace Order message is used to modify an existing order for both simple and complex instruments. It can also be used to alter price of the contra side of Cross Orders. The order to be replaced is identified by OrigClOrdId. *)
    Record t := {
      firm_id : list byte;
      orig_cl_ord_id : list byte;
      cl_ord_id : list byte;
      quantity : N;
      order_type : list byte;
      price : N;
      tif : list byte;
      cust_acct : list byte;
      price_protection : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (firm_id record) = 4 /\
      Datatypes.length (orig_cl_ord_id record) = 16 /\
      Datatypes.length (cl_ord_id record) = 16 /\
      (quantity record < 256 ^ N.of_nat 4)%N /\
      Datatypes.length (order_type record) = 1 /\
      (price record < 256 ^ N.of_nat 8)%N /\
      Datatypes.length (tif record) = 1 /\
      Datatypes.length (cust_acct record) = 10 /\
      Datatypes.length (price_protection record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 4 (firm_id record) ++
      encode_bytes 16 (orig_cl_ord_id record) ++
      encode_bytes 16 (cl_ord_id record) ++
      encode_uint 4 (quantity record) ++
      encode_bytes 1 (order_type record) ++
      encode_uint 8 (price record) ++
      encode_bytes 1 (tif record) ++
      encode_bytes 10 (cust_acct record) ++
      encode_bytes 1 (price_protection record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 4 bytes with
      | None => None
      | Some (firm_id_value, bytes) =>
          match decode_bytes 16 bytes with
          | None => None
          | Some (orig_cl_ord_id_value, bytes) =>
              match decode_bytes 16 bytes with
              | None => None
              | Some (cl_ord_id_value, bytes) =>
                  match decode_uint 4 bytes with
                  | None => None
                  | Some (quantity_value, bytes) =>
                      match decode_bytes 1 bytes with
                      | None => None
                      | Some (order_type_value, bytes) =>
                          match decode_uint 8 bytes with
                          | None => None
                          | Some (price_value, bytes) =>
                              match decode_bytes 1 bytes with
                              | None => None
                              | Some (tif_value, bytes) =>
                                  match decode_bytes 10 bytes with
                                  | None => None
                                  | Some (cust_acct_value, bytes) =>
                                      match decode_bytes 1 bytes with
                                      | None => None
                                      | Some (price_protection_value, bytes) =>
                                          Some ({| firm_id := firm_id_value; orig_cl_ord_id := orig_cl_ord_id_value; cl_ord_id := cl_ord_id_value; quantity := quantity_value; order_type := order_type_value; price := price_value; tif := tif_value; cust_acct := cust_acct_value; price_protection := price_protection_value |}, bytes)
                                      end
                                  end
                              end
                          end
                      end
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 61.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_bytes_length, !encode_uint_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 [bound_1 [bound_2 [bound_3 [bound_4 [bound_5 [bound_6 [bound_7 bound_8]]]]]]]].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_bytes by exact bound_0.
      rewrite decode_encode_bytes by exact bound_1.
      rewrite decode_encode_bytes by exact bound_2.
      rewrite decode_encode_uint by exact bound_3.
      rewrite decode_encode_bytes by exact bound_4.
      rewrite decode_encode_uint by exact bound_5.
      rewrite decode_encode_bytes by exact bound_6.
      rewrite decode_encode_bytes by exact bound_7.
      rewrite decode_encode_bytes by exact bound_8.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End ReplaceOrderMessage.

  Module CancelOrderMessage.

    (** Cancel Order by Client ID. Deletes a single simple order, a single complex order, or a Cross Order (terminating an ongoing auction). The order to be deleted is identified by the ClOrdId field. *)
    Record t := {
      firm_id : list byte;
      cl_ord_id : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (firm_id record) = 4 /\
      Datatypes.length (cl_ord_id record) = 16.

    Definition encode (record : t) : list byte :=
      encode_bytes 4 (firm_id record) ++
      encode_bytes 16 (cl_ord_id record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 4 bytes with
      | None => None
      | Some (firm_id_value, bytes) =>
          match decode_bytes 16 bytes with
          | None => None
          | Some (cl_ord_id_value, bytes) =>
              Some ({| firm_id := firm_id_value; cl_ord_id := cl_ord_id_value |}, bytes)
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 20.
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

  End CancelOrderMessage.

  Module MassCancelMessage.

    (** This message is used to mass-delete multiple open orders based on the specified Scope. The sequence of Order Canceled messages is terminated with a single Mass Cancel Response. *)
    Record t := {
      firm_id : list byte;
      cl_request_id : list byte;
      instrument_type : list byte;
      scope : list byte;
      product_id : N;
      instrument_id : N;
      underlying_symbol : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (firm_id record) = 4 /\
      Datatypes.length (cl_request_id record) = 16 /\
      Datatypes.length (instrument_type record) = 1 /\
      Datatypes.length (scope record) = 1 /\
      (product_id record < 256 ^ N.of_nat 2)%N /\
      (instrument_id record < 256 ^ N.of_nat 4)%N /\
      Datatypes.length (underlying_symbol record) = 13.

    Definition encode (record : t) : list byte :=
      encode_bytes 4 (firm_id record) ++
      encode_bytes 16 (cl_request_id record) ++
      encode_bytes 1 (instrument_type record) ++
      encode_bytes 1 (scope record) ++
      encode_uint 2 (product_id record) ++
      encode_uint 4 (instrument_id record) ++
      encode_bytes 13 (underlying_symbol record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 4 bytes with
      | None => None
      | Some (firm_id_value, bytes) =>
          match decode_bytes 16 bytes with
          | None => None
          | Some (cl_request_id_value, bytes) =>
              match decode_bytes 1 bytes with
              | None => None
              | Some (instrument_type_value, bytes) =>
                  match decode_bytes 1 bytes with
                  | None => None
                  | Some (scope_value, bytes) =>
                      match decode_uint 2 bytes with
                      | None => None
                      | Some (product_id_value, bytes) =>
                          match decode_uint 4 bytes with
                          | None => None
                          | Some (instrument_id_value, bytes) =>
                              match decode_bytes 13 bytes with
                              | None => None
                              | Some (underlying_symbol_value, bytes) =>
                                  Some ({| firm_id := firm_id_value; cl_request_id := cl_request_id_value; instrument_type := instrument_type_value; scope := scope_value; product_id := product_id_value; instrument_id := instrument_id_value; underlying_symbol := underlying_symbol_value |}, bytes)
                              end
                          end
                      end
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 41.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_bytes_length, !encode_uint_length. reflexivity.
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
      rewrite decode_encode_uint by exact bound_4.
      rewrite decode_encode_uint by exact bound_5.
      rewrite decode_encode_bytes by exact bound_6.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End MassCancelMessage.

  Module MemberKillSwitchRequestMessage.

    (** The Member Kill Switch Request is used to block ability to enter new orders, alter existing orders, delete orders, and create complex instruments. Scope of the Kill Switch Request is one firm per request. Answered by Member Kill Switch Notification or Reject. *)
    Record t := {
      firm_id : list byte;
      cl_request_id : list byte;
      target_firm_id : list byte;
      kill_action : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (firm_id record) = 4 /\
      Datatypes.length (cl_request_id record) = 16 /\
      Datatypes.length (target_firm_id record) = 4 /\
      Datatypes.length (kill_action record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 4 (firm_id record) ++
      encode_bytes 16 (cl_request_id record) ++
      encode_bytes 4 (target_firm_id record) ++
      encode_bytes 1 (kill_action record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 4 bytes with
      | None => None
      | Some (firm_id_value, bytes) =>
          match decode_bytes 16 bytes with
          | None => None
          | Some (cl_request_id_value, bytes) =>
              match decode_bytes 4 bytes with
              | None => None
              | Some (target_firm_id_value, bytes) =>
                  match decode_bytes 1 bytes with
                  | None => None
                  | Some (kill_action_value, bytes) =>
                      Some ({| firm_id := firm_id_value; cl_request_id := cl_request_id_value; target_firm_id := target_firm_id_value; kill_action := kill_action_value |}, bytes)
                  end
              end
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
      destruct bound as [bound_0 [bound_1 [bound_2 bound_3]]].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_bytes by exact bound_0.
      rewrite decode_encode_bytes by exact bound_1.
      rewrite decode_encode_bytes by exact bound_2.
      rewrite decode_encode_bytes by exact bound_3.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End MemberKillSwitchRequestMessage.

  Module SubscriptionRequestMessage.

    (** Subscription Request message allows client to modify the set of optional notification types it receives on the OTTO connection for the current session. Supported on PHLX, ISE, GEMX and MRX. Answered by Subscription Response or Reject. *)
    Record t := {
      firm_id : list byte;
      cl_request_id : list byte;
      subscription : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (firm_id record) = 4 /\
      Datatypes.length (cl_request_id record) = 16 /\
      Datatypes.length (subscription record) = 16.

    Definition encode (record : t) : list byte :=
      encode_bytes 4 (firm_id record) ++
      encode_bytes 16 (cl_request_id record) ++
      encode_bytes 16 (subscription record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 4 bytes with
      | None => None
      | Some (firm_id_value, bytes) =>
          match decode_bytes 16 bytes with
          | None => None
          | Some (cl_request_id_value, bytes) =>
              match decode_bytes 16 bytes with
              | None => None
              | Some (subscription_value, bytes) =>
                  Some ({| firm_id := firm_id_value; cl_request_id := cl_request_id_value; subscription := subscription_value |}, bytes)
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
      destruct bound as [bound_0 [bound_1 bound_2]].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_bytes by exact bound_0.
      rewrite decode_encode_bytes by exact bound_1.
      rewrite decode_encode_bytes by exact bound_2.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End SubscriptionRequestMessage.

End PhlxOptionsOttoV300Client.
