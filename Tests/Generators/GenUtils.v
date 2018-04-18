From QuickChick Require Import QuickChick.

Import QcDefaultNotation. Open Scope qc_scope.

Require Import
        List
        ListDec.

Import ListNotations.


(** generating non empty lists *)

Definition gen_list {A : Type} : G A -> G (A * (list A)%type)
  := fun genA => bindGen (choose (1,5)) (fun n => genPair genA (vectorOf n genA)).

Definition gen_from_list {A : Type} (xs : (A * (list A))%type) : G A :=
  match xs with
  | (y , ys) => elements y ys
  end.

Module DoNotation.
  Import ssrfun.
  Notation "'do!' X <- A ; B" :=
    (bindGen A (fun X => B))
      (at level 200, X ident, A at level 100, B at level 200).
End DoNotation.
