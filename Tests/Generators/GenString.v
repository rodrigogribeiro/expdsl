From QuickChick Require Import QuickChick.

Import QcDefaultNotation. Open Scope qc_scope.

Require Import
        List
        ListDec
        String
        Ascii.

Import ListNotations.

(* simple instances for strings *)

Section STRING.
  Instance string_show : Show string
    := {|
        show x := x
      |}.

  Instance show_ascii : Show ascii
    := {|
        show c := String c EmptyString
      |}.

  Definition gen_ascii : G ascii
    := liftGen ascii_of_nat (choose (97,122)).

  Fixpoint build_string (xs : list ascii) : string
    := fold_right (fun a ac => String a ac) EmptyString xs. 

  Definition gen_string_of_size : nat -> G string
    := fun n => liftGen build_string (vectorOf n gen_ascii).

  Definition gen_string : G string
    := bindGen (choose (1,3)) gen_string_of_size.

  Fixpoint gen_string_list (n : nat)(ls : list string) : G (list string) :=
    match n with
    | O => returnGen ls
    | S n' => bindGen gen_string (fun s => if in_dec string_dec s ls
                                       then gen_string_list n' ls
                                       else gen_string_list n' (s :: ls))
    end.

  Definition gen_string_nodup : G (list string)
    := bindGen (choose (1,3)) (fun n => gen_string_list n []).

  Definition gen_string_nodup_noempty : G (string * list string)%type
    := bindGen (choose (1,3))
               (fun n => bindGen (gen_string_list (1 + n) [])
                              (fun ls => match ls with
                                      | [] => returnGen ("" , [])
                                      | (x :: ls) => returnGen (x , ls)
                                      end)).
End STRING.