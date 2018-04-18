Set Implicit Arguments.

Require Import
        Ascii
        String
        List.

Definition name : Set := string.

Definition eq_name_dec := string_dec.

Class Nameable (A : Type) : Type
  :={
      name_of : A -> name
    }.

Definition names {A : Type}`{Nameable A} (v : list A) : list name :=
  map name_of v.
