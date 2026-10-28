From Stdlib Require Import List.
From Stdlib Require Import NArith.
From Stdlib Require Import Lia.
From Stdlib Require Import Strings.Byte.
From Omi Require Import Wire.

Import ListNotations.

(** * The Securities Industry Automation Corporation Output

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
      - a run counted by a field
      - the dispatch that chooses a message by its type
      - a field present only on a condition
      - a length prefix framing what follows
  *)

Module SiacOpraOutputV40.

  Module MessageHeader.

    (** Opra Message Header first level dispatch *)
    Record t := {
      participant_id : list byte;
      message_category : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (participant_id record) = 1 /\
      Datatypes.length (message_category record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 1 (participant_id record) ++
      encode_bytes 1 (message_category record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 1 bytes with
      | None => None
      | Some (participant_id_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (message_category_value, bytes) =>
              Some ({| participant_id := participant_id_value; message_category := message_category_value |}, bytes)
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 2.
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

  End MessageHeader.

  Module ExpirationBlock.

    (** Expiration Block *)
    Record t := {
      expiration_month : list byte;
      expiration_day : N;
      expiration_year : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (expiration_month record) = 1 /\
      (expiration_day record < 256 ^ N.of_nat 1)%N /\
      (expiration_year record < 256 ^ N.of_nat 1)%N.

    Definition encode (record : t) : list byte :=
      encode_bytes 1 (expiration_month record) ++
      encode_uint 1 (expiration_day record) ++
      encode_uint 1 (expiration_year record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 1 bytes with
      | None => None
      | Some (expiration_month_value, bytes) =>
          match decode_uint 1 bytes with
          | None => None
          | Some (expiration_day_value, bytes) =>
              match decode_uint 1 bytes with
              | None => None
              | Some (expiration_year_value, bytes) =>
                  Some ({| expiration_month := expiration_month_value; expiration_day := expiration_day_value; expiration_year := expiration_year_value |}, bytes)
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 3.
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

  End ExpirationBlock.

  Module EquityAndIndexLastSaleMessage.

    (** The Equity and Index Last Sale message is used to report equity and index options last sale information. *)
    Record t := {
      message_indicator : list byte;
      transaction_id : N;
      security_symbol : list byte;
      reserved_1 : N;
      expiration_block : ExpirationBlock.t;
      strike_price_denominator_code : list byte;
      strike_price : N;
      volume : N;
      premium_price_denominator_code : list byte;
      premium_price : N;
      trade_identifier : N;
      reserved_4 : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (message_indicator record) = 1 /\
      (transaction_id record < 256 ^ N.of_nat 8)%N /\
      Datatypes.length (security_symbol record) = 5 /\
      (reserved_1 record < 256 ^ N.of_nat 1)%N /\
      ExpirationBlock.bounded (expiration_block record) /\
      Datatypes.length (strike_price_denominator_code record) = 1 /\
      (strike_price record < 256 ^ N.of_nat 4)%N /\
      (volume record < 256 ^ N.of_nat 4)%N /\
      Datatypes.length (premium_price_denominator_code record) = 1 /\
      (premium_price record < 256 ^ N.of_nat 4)%N /\
      (trade_identifier record < 256 ^ N.of_nat 4)%N /\
      (reserved_4 record < 256 ^ N.of_nat 4)%N.

    Definition encode (record : t) : list byte :=
      encode_bytes 1 (message_indicator record) ++
      encode_uint 8 (transaction_id record) ++
      encode_bytes 5 (security_symbol record) ++
      encode_uint 1 (reserved_1 record) ++
      ExpirationBlock.encode (expiration_block record) ++
      encode_bytes 1 (strike_price_denominator_code record) ++
      encode_uint 4 (strike_price record) ++
      encode_uint 4 (volume record) ++
      encode_bytes 1 (premium_price_denominator_code record) ++
      encode_uint 4 (premium_price record) ++
      encode_uint 4 (trade_identifier record) ++
      encode_uint 4 (reserved_4 record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 1 bytes with
      | None => None
      | Some (message_indicator_value, bytes) =>
          match decode_uint 8 bytes with
          | None => None
          | Some (transaction_id_value, bytes) =>
              match decode_bytes 5 bytes with
              | None => None
              | Some (security_symbol_value, bytes) =>
                  match decode_uint 1 bytes with
                  | None => None
                  | Some (reserved_1_value, bytes) =>
                      match ExpirationBlock.decode bytes with
                      | None => None
                      | Some (expiration_block_value, bytes) =>
                          match decode_bytes 1 bytes with
                          | None => None
                          | Some (strike_price_denominator_code_value, bytes) =>
                              match decode_uint 4 bytes with
                              | None => None
                              | Some (strike_price_value, bytes) =>
                                  match decode_uint 4 bytes with
                                  | None => None
                                  | Some (volume_value, bytes) =>
                                      match decode_bytes 1 bytes with
                                      | None => None
                                      | Some (premium_price_denominator_code_value, bytes) =>
                                          match decode_uint 4 bytes with
                                          | None => None
                                          | Some (premium_price_value, bytes) =>
                                              match decode_uint 4 bytes with
                                              | None => None
                                              | Some (trade_identifier_value, bytes) =>
                                                  match decode_uint 4 bytes with
                                                  | None => None
                                                  | Some (reserved_4_value, bytes) =>
                                                      Some ({| message_indicator := message_indicator_value; transaction_id := transaction_id_value; security_symbol := security_symbol_value; reserved_1 := reserved_1_value; expiration_block := expiration_block_value; strike_price_denominator_code := strike_price_denominator_code_value; strike_price := strike_price_value; volume := volume_value; premium_price_denominator_code := premium_price_denominator_code_value; premium_price := premium_price_value; trade_identifier := trade_identifier_value; reserved_4 := reserved_4_value |}, bytes)
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

    Theorem encode_length : forall record, Datatypes.length (encode record) = 40.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_bytes_length, !encode_uint_length, !ExpirationBlock.encode_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 [bound_1 [bound_2 [bound_3 [bound_4 [bound_5 [bound_6 [bound_7 [bound_8 [bound_9 [bound_10 bound_11]]]]]]]]]]].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_bytes by exact bound_0.
      rewrite decode_encode_uint by exact bound_1.
      rewrite decode_encode_bytes by exact bound_2.
      rewrite decode_encode_uint by exact bound_3.
      rewrite ExpirationBlock.decode_encode by exact bound_4.
      rewrite decode_encode_bytes by exact bound_5.
      rewrite decode_encode_uint by exact bound_6.
      rewrite decode_encode_uint by exact bound_7.
      rewrite decode_encode_bytes by exact bound_8.
      rewrite decode_encode_uint by exact bound_9.
      rewrite decode_encode_uint by exact bound_10.
      rewrite decode_encode_uint by exact bound_11.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec) | apply ExpirationBlock.eq_dec]. Defined.

  End EquityAndIndexLastSaleMessage.

  Module ExpirationBlock2.

    (** Expiration Block *)
    Record t := {
      expiration_month : list byte;
      expiration_day : N;
      expiration_year : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (expiration_month record) = 1 /\
      (expiration_day record < 256 ^ N.of_nat 1)%N /\
      (expiration_year record < 256 ^ N.of_nat 1)%N.

    Definition encode (record : t) : list byte :=
      encode_bytes 1 (expiration_month record) ++
      encode_uint 1 (expiration_day record) ++
      encode_uint 1 (expiration_year record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 1 bytes with
      | None => None
      | Some (expiration_month_value, bytes) =>
          match decode_uint 1 bytes with
          | None => None
          | Some (expiration_day_value, bytes) =>
              match decode_uint 1 bytes with
              | None => None
              | Some (expiration_year_value, bytes) =>
                  Some ({| expiration_month := expiration_month_value; expiration_day := expiration_day_value; expiration_year := expiration_year_value |}, bytes)
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 3.
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

  End ExpirationBlock2.

  Module OpenInterestMessage.

    (** The Open Interest message is used to report contract volume on current options that have not been exercised and have not yet reached expiration. *)
    Record t := {
      message_indicator : list byte;
      transaction_id : N;
      security_symbol : list byte;
      reserved_1 : N;
      expiration_block : ExpirationBlock2.t;
      strike_price_denominator_code : list byte;
      strike_price : N;
      open_interest_volume : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (message_indicator record) = 1 /\
      (transaction_id record < 256 ^ N.of_nat 8)%N /\
      Datatypes.length (security_symbol record) = 5 /\
      (reserved_1 record < 256 ^ N.of_nat 1)%N /\
      ExpirationBlock2.bounded (expiration_block record) /\
      Datatypes.length (strike_price_denominator_code record) = 1 /\
      (strike_price record < 256 ^ N.of_nat 4)%N /\
      (open_interest_volume record < 256 ^ N.of_nat 4)%N.

    Definition encode (record : t) : list byte :=
      encode_bytes 1 (message_indicator record) ++
      encode_uint 8 (transaction_id record) ++
      encode_bytes 5 (security_symbol record) ++
      encode_uint 1 (reserved_1 record) ++
      ExpirationBlock2.encode (expiration_block record) ++
      encode_bytes 1 (strike_price_denominator_code record) ++
      encode_uint 4 (strike_price record) ++
      encode_uint 4 (open_interest_volume record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 1 bytes with
      | None => None
      | Some (message_indicator_value, bytes) =>
          match decode_uint 8 bytes with
          | None => None
          | Some (transaction_id_value, bytes) =>
              match decode_bytes 5 bytes with
              | None => None
              | Some (security_symbol_value, bytes) =>
                  match decode_uint 1 bytes with
                  | None => None
                  | Some (reserved_1_value, bytes) =>
                      match ExpirationBlock2.decode bytes with
                      | None => None
                      | Some (expiration_block_value, bytes) =>
                          match decode_bytes 1 bytes with
                          | None => None
                          | Some (strike_price_denominator_code_value, bytes) =>
                              match decode_uint 4 bytes with
                              | None => None
                              | Some (strike_price_value, bytes) =>
                                  match decode_uint 4 bytes with
                                  | None => None
                                  | Some (open_interest_volume_value, bytes) =>
                                      Some ({| message_indicator := message_indicator_value; transaction_id := transaction_id_value; security_symbol := security_symbol_value; reserved_1 := reserved_1_value; expiration_block := expiration_block_value; strike_price_denominator_code := strike_price_denominator_code_value; strike_price := strike_price_value; open_interest_volume := open_interest_volume_value |}, bytes)
                                  end
                              end
                          end
                      end
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 27.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_bytes_length, !encode_uint_length, !ExpirationBlock2.encode_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 [bound_1 [bound_2 [bound_3 [bound_4 [bound_5 [bound_6 bound_7]]]]]]].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_bytes by exact bound_0.
      rewrite decode_encode_uint by exact bound_1.
      rewrite decode_encode_bytes by exact bound_2.
      rewrite decode_encode_uint by exact bound_3.
      rewrite ExpirationBlock2.decode_encode by exact bound_4.
      rewrite decode_encode_bytes by exact bound_5.
      rewrite decode_encode_uint by exact bound_6.
      rewrite decode_encode_uint by exact bound_7.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec) | apply ExpirationBlock2.eq_dec]. Defined.

  End OpenInterestMessage.

  Module ExpirationBlock3.

    (** Expiration Block *)
    Record t := {
      expiration_month : list byte;
      expiration_day : N;
      expiration_year : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (expiration_month record) = 1 /\
      (expiration_day record < 256 ^ N.of_nat 1)%N /\
      (expiration_year record < 256 ^ N.of_nat 1)%N.

    Definition encode (record : t) : list byte :=
      encode_bytes 1 (expiration_month record) ++
      encode_uint 1 (expiration_day record) ++
      encode_uint 1 (expiration_year record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 1 bytes with
      | None => None
      | Some (expiration_month_value, bytes) =>
          match decode_uint 1 bytes with
          | None => None
          | Some (expiration_day_value, bytes) =>
              match decode_uint 1 bytes with
              | None => None
              | Some (expiration_year_value, bytes) =>
                  Some ({| expiration_month := expiration_month_value; expiration_day := expiration_day_value; expiration_year := expiration_year_value |}, bytes)
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 3.
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

  End ExpirationBlock3.

  Module EquityAndIndexEndOfDaySummaryMessage.

    (** The Equity and Index End of Day Summary messages are transmitted shortly before the Good Night messages. *)
    Record t := {
      message_indicator : list byte;
      transaction_id : N;
      security_symbol : list byte;
      reserved_1 : N;
      expiration_block : ExpirationBlock3.t;
      strike_price_denominator_code : list byte;
      strike_price : N;
      volume : N;
      open_interest_volume : N;
      premium_price_denominator_code : list byte;
      open_price : N;
      high_price : N;
      low_price : N;
      last_price : N;
      net_change : N;
      underlying_price_denominator_code : list byte;
      underlying_price : N;
      bid_price : N;
      offer_price : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (message_indicator record) = 1 /\
      (transaction_id record < 256 ^ N.of_nat 8)%N /\
      Datatypes.length (security_symbol record) = 5 /\
      (reserved_1 record < 256 ^ N.of_nat 1)%N /\
      ExpirationBlock3.bounded (expiration_block record) /\
      Datatypes.length (strike_price_denominator_code record) = 1 /\
      (strike_price record < 256 ^ N.of_nat 4)%N /\
      (volume record < 256 ^ N.of_nat 4)%N /\
      (open_interest_volume record < 256 ^ N.of_nat 4)%N /\
      Datatypes.length (premium_price_denominator_code record) = 1 /\
      (open_price record < 256 ^ N.of_nat 4)%N /\
      (high_price record < 256 ^ N.of_nat 4)%N /\
      (low_price record < 256 ^ N.of_nat 4)%N /\
      (last_price record < 256 ^ N.of_nat 4)%N /\
      (net_change record < 256 ^ N.of_nat 4)%N /\
      Datatypes.length (underlying_price_denominator_code record) = 1 /\
      (underlying_price record < 256 ^ N.of_nat 8)%N /\
      (bid_price record < 256 ^ N.of_nat 4)%N /\
      (offer_price record < 256 ^ N.of_nat 4)%N.

    Definition encode (record : t) : list byte :=
      encode_bytes 1 (message_indicator record) ++
      encode_uint 8 (transaction_id record) ++
      encode_bytes 5 (security_symbol record) ++
      encode_uint 1 (reserved_1 record) ++
      ExpirationBlock3.encode (expiration_block record) ++
      encode_bytes 1 (strike_price_denominator_code record) ++
      encode_uint 4 (strike_price record) ++
      encode_uint 4 (volume record) ++
      encode_uint 4 (open_interest_volume record) ++
      encode_bytes 1 (premium_price_denominator_code record) ++
      encode_uint 4 (open_price record) ++
      encode_uint 4 (high_price record) ++
      encode_uint 4 (low_price record) ++
      encode_uint 4 (last_price record) ++
      encode_uint 4 (net_change record) ++
      encode_bytes 1 (underlying_price_denominator_code record) ++
      encode_uint 8 (underlying_price record) ++
      encode_uint 4 (bid_price record) ++
      encode_uint 4 (offer_price record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 1 bytes with
      | None => None
      | Some (message_indicator_value, bytes) =>
          match decode_uint 8 bytes with
          | None => None
          | Some (transaction_id_value, bytes) =>
              match decode_bytes 5 bytes with
              | None => None
              | Some (security_symbol_value, bytes) =>
                  match decode_uint 1 bytes with
                  | None => None
                  | Some (reserved_1_value, bytes) =>
                      match ExpirationBlock3.decode bytes with
                      | None => None
                      | Some (expiration_block_value, bytes) =>
                          match decode_bytes 1 bytes with
                          | None => None
                          | Some (strike_price_denominator_code_value, bytes) =>
                              match decode_uint 4 bytes with
                              | None => None
                              | Some (strike_price_value, bytes) =>
                                  match decode_uint 4 bytes with
                                  | None => None
                                  | Some (volume_value, bytes) =>
                                      match decode_uint 4 bytes with
                                      | None => None
                                      | Some (open_interest_volume_value, bytes) =>
                                          match decode_bytes 1 bytes with
                                          | None => None
                                          | Some (premium_price_denominator_code_value, bytes) =>
                                              match decode_uint 4 bytes with
                                              | None => None
                                              | Some (open_price_value, bytes) =>
                                                  match decode_uint 4 bytes with
                                                  | None => None
                                                  | Some (high_price_value, bytes) =>
                                                      match decode_uint 4 bytes with
                                                      | None => None
                                                      | Some (low_price_value, bytes) =>
                                                          match decode_uint 4 bytes with
                                                          | None => None
                                                          | Some (last_price_value, bytes) =>
                                                              match decode_uint 4 bytes with
                                                              | None => None
                                                              | Some (net_change_value, bytes) =>
                                                                  match decode_bytes 1 bytes with
                                                                  | None => None
                                                                  | Some (underlying_price_denominator_code_value, bytes) =>
                                                                      match decode_uint 8 bytes with
                                                                      | None => None
                                                                      | Some (underlying_price_value, bytes) =>
                                                                          match decode_uint 4 bytes with
                                                                          | None => None
                                                                          | Some (bid_price_value, bytes) =>
                                                                              match decode_uint 4 bytes with
                                                                              | None => None
                                                                              | Some (offer_price_value, bytes) =>
                                                                                  Some ({| message_indicator := message_indicator_value; transaction_id := transaction_id_value; security_symbol := security_symbol_value; reserved_1 := reserved_1_value; expiration_block := expiration_block_value; strike_price_denominator_code := strike_price_denominator_code_value; strike_price := strike_price_value; volume := volume_value; open_interest_volume := open_interest_volume_value; premium_price_denominator_code := premium_price_denominator_code_value; open_price := open_price_value; high_price := high_price_value; low_price := low_price_value; last_price := last_price_value; net_change := net_change_value; underlying_price_denominator_code := underlying_price_denominator_code_value; underlying_price := underlying_price_value; bid_price := bid_price_value; offer_price := offer_price_value |}, bytes)
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
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 69.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_bytes_length, !encode_uint_length, !ExpirationBlock3.encode_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 [bound_1 [bound_2 [bound_3 [bound_4 [bound_5 [bound_6 [bound_7 [bound_8 [bound_9 [bound_10 [bound_11 [bound_12 [bound_13 [bound_14 [bound_15 [bound_16 [bound_17 bound_18]]]]]]]]]]]]]]]]]].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_bytes by exact bound_0.
      rewrite decode_encode_uint by exact bound_1.
      rewrite decode_encode_bytes by exact bound_2.
      rewrite decode_encode_uint by exact bound_3.
      rewrite ExpirationBlock3.decode_encode by exact bound_4.
      rewrite decode_encode_bytes by exact bound_5.
      rewrite decode_encode_uint by exact bound_6.
      rewrite decode_encode_uint by exact bound_7.
      rewrite decode_encode_uint by exact bound_8.
      rewrite decode_encode_bytes by exact bound_9.
      rewrite decode_encode_uint by exact bound_10.
      rewrite decode_encode_uint by exact bound_11.
      rewrite decode_encode_uint by exact bound_12.
      rewrite decode_encode_uint by exact bound_13.
      rewrite decode_encode_uint by exact bound_14.
      rewrite decode_encode_bytes by exact bound_15.
      rewrite decode_encode_uint by exact bound_16.
      rewrite decode_encode_uint by exact bound_17.
      rewrite decode_encode_uint by exact bound_18.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec) | apply ExpirationBlock3.eq_dec]. Defined.

  End EquityAndIndexEndOfDaySummaryMessage.

  Module ExpirationBlock4.

    (** Expiration Block *)
    Record t := {
      expiration_month : list byte;
      expiration_day : N;
      expiration_year : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (expiration_month record) = 1 /\
      (expiration_day record < 256 ^ N.of_nat 1)%N /\
      (expiration_year record < 256 ^ N.of_nat 1)%N.

    Definition encode (record : t) : list byte :=
      encode_bytes 1 (expiration_month record) ++
      encode_uint 1 (expiration_day record) ++
      encode_uint 1 (expiration_year record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 1 bytes with
      | None => None
      | Some (expiration_month_value, bytes) =>
          match decode_uint 1 bytes with
          | None => None
          | Some (expiration_day_value, bytes) =>
              match decode_uint 1 bytes with
              | None => None
              | Some (expiration_year_value, bytes) =>
                  Some ({| expiration_month := expiration_month_value; expiration_day := expiration_day_value; expiration_year := expiration_year_value |}, bytes)
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 3.
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

  End ExpirationBlock4.

  Module ExpirationBlock5.

    (** Expiration Block *)
    Record t := {
      expiration_month : list byte;
      expiration_day : N;
      expiration_year : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (expiration_month record) = 1 /\
      (expiration_day record < 256 ^ N.of_nat 1)%N /\
      (expiration_year record < 256 ^ N.of_nat 1)%N.

    Definition encode (record : t) : list byte :=
      encode_bytes 1 (expiration_month record) ++
      encode_uint 1 (expiration_day record) ++
      encode_uint 1 (expiration_year record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 1 bytes with
      | None => None
      | Some (expiration_month_value, bytes) =>
          match decode_uint 1 bytes with
          | None => None
          | Some (expiration_day_value, bytes) =>
              match decode_uint 1 bytes with
              | None => None
              | Some (expiration_year_value, bytes) =>
                  Some ({| expiration_month := expiration_month_value; expiration_day := expiration_day_value; expiration_year := expiration_year_value |}, bytes)
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 3.
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

  End ExpirationBlock5.

  Module UnderlyingValueLastSaleMessage.

    (** Underlying Value last sale Message *)
    Record t := {
      message_indicator : list byte;
      transaction_id : N;
      security_symbol : list byte;
      reserved_1 : N;
      index_value_denominator_code : list byte;
      index_value : N;
      reserved_4 : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (message_indicator record) = 1 /\
      (transaction_id record < 256 ^ N.of_nat 8)%N /\
      Datatypes.length (security_symbol record) = 5 /\
      (reserved_1 record < 256 ^ N.of_nat 1)%N /\
      Datatypes.length (index_value_denominator_code record) = 1 /\
      (index_value record < 256 ^ N.of_nat 4)%N /\
      (reserved_4 record < 256 ^ N.of_nat 4)%N.

    Definition encode (record : t) : list byte :=
      encode_bytes 1 (message_indicator record) ++
      encode_uint 8 (transaction_id record) ++
      encode_bytes 5 (security_symbol record) ++
      encode_uint 1 (reserved_1 record) ++
      encode_bytes 1 (index_value_denominator_code record) ++
      encode_uint 4 (index_value record) ++
      encode_uint 4 (reserved_4 record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 1 bytes with
      | None => None
      | Some (message_indicator_value, bytes) =>
          match decode_uint 8 bytes with
          | None => None
          | Some (transaction_id_value, bytes) =>
              match decode_bytes 5 bytes with
              | None => None
              | Some (security_symbol_value, bytes) =>
                  match decode_uint 1 bytes with
                  | None => None
                  | Some (reserved_1_value, bytes) =>
                      match decode_bytes 1 bytes with
                      | None => None
                      | Some (index_value_denominator_code_value, bytes) =>
                          match decode_uint 4 bytes with
                          | None => None
                          | Some (index_value_value, bytes) =>
                              match decode_uint 4 bytes with
                              | None => None
                              | Some (reserved_4_value, bytes) =>
                                  Some ({| message_indicator := message_indicator_value; transaction_id := transaction_id_value; security_symbol := security_symbol_value; reserved_1 := reserved_1_value; index_value_denominator_code := index_value_denominator_code_value; index_value := index_value_value; reserved_4 := reserved_4_value |}, bytes)
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
      rewrite decode_encode_uint by exact bound_1.
      rewrite decode_encode_bytes by exact bound_2.
      rewrite decode_encode_uint by exact bound_3.
      rewrite decode_encode_bytes by exact bound_4.
      rewrite decode_encode_uint by exact bound_5.
      rewrite decode_encode_uint by exact bound_6.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End UnderlyingValueLastSaleMessage.

  Module UnderlyingValueBidAndOfferMessage.

    (** Underlying value bid and offer message *)
    Record t := {
      message_indicator : list byte;
      transaction_id : N;
      security_symbol : list byte;
      reserved_1 : N;
      index_value_denominator_code : list byte;
      bid_index_value : N;
      offer_index_value : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (message_indicator record) = 1 /\
      (transaction_id record < 256 ^ N.of_nat 8)%N /\
      Datatypes.length (security_symbol record) = 5 /\
      (reserved_1 record < 256 ^ N.of_nat 1)%N /\
      Datatypes.length (index_value_denominator_code record) = 1 /\
      (bid_index_value record < 256 ^ N.of_nat 4)%N /\
      (offer_index_value record < 256 ^ N.of_nat 8)%N.

    Definition encode (record : t) : list byte :=
      encode_bytes 1 (message_indicator record) ++
      encode_uint 8 (transaction_id record) ++
      encode_bytes 5 (security_symbol record) ++
      encode_uint 1 (reserved_1 record) ++
      encode_bytes 1 (index_value_denominator_code record) ++
      encode_uint 4 (bid_index_value record) ++
      encode_uint 8 (offer_index_value record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 1 bytes with
      | None => None
      | Some (message_indicator_value, bytes) =>
          match decode_uint 8 bytes with
          | None => None
          | Some (transaction_id_value, bytes) =>
              match decode_bytes 5 bytes with
              | None => None
              | Some (security_symbol_value, bytes) =>
                  match decode_uint 1 bytes with
                  | None => None
                  | Some (reserved_1_value, bytes) =>
                      match decode_bytes 1 bytes with
                      | None => None
                      | Some (index_value_denominator_code_value, bytes) =>
                          match decode_uint 4 bytes with
                          | None => None
                          | Some (bid_index_value_value, bytes) =>
                              match decode_uint 8 bytes with
                              | None => None
                              | Some (offer_index_value_value, bytes) =>
                                  Some ({| message_indicator := message_indicator_value; transaction_id := transaction_id_value; security_symbol := security_symbol_value; reserved_1 := reserved_1_value; index_value_denominator_code := index_value_denominator_code_value; bid_index_value := bid_index_value_value; offer_index_value := offer_index_value_value |}, bytes)
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
      rewrite decode_encode_uint by exact bound_1.
      rewrite decode_encode_bytes by exact bound_2.
      rewrite decode_encode_uint by exact bound_3.
      rewrite decode_encode_bytes by exact bound_4.
      rewrite decode_encode_uint by exact bound_5.
      rewrite decode_encode_uint by exact bound_6.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End UnderlyingValueBidAndOfferMessage.

End SiacOpraOutputV40.
