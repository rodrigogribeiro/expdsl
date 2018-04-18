Set Implicit Arguments.

Require Import
        Syntax.Syntax
        Utils.ListUtils.

(** since Coq doesn't support side effects,
    execution results are specified as a list
    of natural numbers *)

Definition execute (scp : execution_script)(res : list nat) : list nat :=
  zipWith (fun _ n => n) scp res.
