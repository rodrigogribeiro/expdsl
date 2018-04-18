Set Implicit Arguments.

Require Import
        List
        ListDec
        Tactics.Tactics.

Import ListNotations.

Fixpoint zipWith
         {A B C : Type}
         (f : A -> B -> C)
         (ls : list A)
         (ls' : list B) : list C :=
  match ls, ls' with
  | [] , _ => []
  | _  , [] => []
  | (x :: xs), (y :: ys) => f x y :: zipWith f xs ys
  end.

Fixpoint replicate {A : Type}(n : nat)(xs : list A) : list A :=
  match n with
  | O => []
  | S n' => xs ++ replicate n' xs
  end.

Lemma replicate_nil {A : Type} :
  forall n, replicate n (@nil A) = (@nil A).
Proof.
  induction n ; crush.
Qed.

Lemma Forall_app {A : Type}
  : forall (P : A -> Prop)
      (xs ys : list A), (Forall P xs /\ Forall P ys) <-> (Forall P (xs ++ ys)).
Proof.
  induction xs ; destruct ys ; splits ; intros H ; crush.
  +
    rewrite <- app_nil_end ; auto.
  +
    rewrite <- app_nil_end in H ; auto.
  +
    inverts* H0.
    constructor ; auto.
    destruct (IHxs (a0 :: ys)).
    apply H.
    splits*.
  +
    destruct (IHxs (a0 :: ys)).
    inverts* H.
    lets* J : H1 H5.
  +
    constructor.
    inverts* H.
    destruct (IHxs (a0 :: ys)).
    lets* J : H0 H3.
    destruct* J.
    inverts* H4.
    inverts* H.
    destruct (IHxs (a0 :: ys)).
    lets* J : H0 H3.
    destruct* J.
    inverts* H4.
Qed.

Lemma replicate_cons {A : Type}
  : forall n x (xs : list A), replicate (S n) (x :: xs) = (x :: xs) ++ replicate n (x :: xs).
Proof.
  induction n ; crush.
Qed.

Lemma replicate_forall
      {A : Type}{P : A -> Prop} :
  forall xs, Forall P xs -> forall n, Forall P (replicate n xs).
Proof.
  induction xs ; intros H n ; destruct* n ; crush.
  +
    rewrite replicate_nil ; auto.
  +
    inverts* H.
    constructor ; eauto.
    apply Forall_app ; splits*.
    destruct n ; simpl in * ; eauto.
    constructor ; auto.
    apply Forall_app ; splits*.
    induction n ; crush.
    -
      constructor ; auto.
      apply Forall_app ; crush.
Qed.

Lemma count_occ_app {A : Type}
      (eqA : forall (x y : A), {x = y} + {x <> y})
  : forall (xs ys : list A) x, count_occ eqA (xs ++ ys) x = count_occ eqA xs x + count_occ eqA ys x.
Proof.
  induction xs ; crush.
  destruct* (eqA a x) ; crush.
Qed.

Lemma replicate_count_occ_not_in
      {A : Type}(eqA : forall (x y : A), {x = y} + {x <> y})
  : forall (xs : list A) x, ~ In x xs -> forall n, count_occ eqA (replicate n xs) x = 0.
Proof.
  induction xs ; intros ; crush.
  +
    rewrite replicate_nil ; crush.
  +
    lets J : IHxs H1.
    induction n ; crush.
    destruct* (eqA a x) ; crush.
    eapply (count_occ_not_In eqA) in H1.
    rewrite count_occ_app.
    crush.
Qed.

Lemma replicate_count_occ {A : Type}
      (eqA : forall (x y : A), {x = y} + {x <> y})
  : forall (xs : list A), NoDup xs -> (forall x, In x xs ->
                                      forall n, count_occ eqA (replicate n xs) x = n).
Proof.
  Hint Constructors NoDup.
  induction xs ; crush.
  + 
    inverts* H.
    eapply (replicate_count_occ_not_in eqA) with (n := n) in H2.
    induction n ; crush.
    destruct (eqA x x) ; crush.
    rewrite count_occ_app in *.
    assert (Lem : forall (n m : nat), n + m = 0 -> n = 0 /\ m = 0) by (induction n ; crush).  
    apply Lem in H2.
    destruct* H2. rewrite H1 in *.
    crush.
  + 
    inverts* H.
    induction n ; crush.
    destruct (eqA a x) ; crush.
    rewrite count_occ_app.
    apply (count_occ_In eqA) in  H1.
    eapply (NoDup_count_occ eqA) with (x := x) in H4.
    crush.
Qed.


Lemma flat_map_In {A B : Type} :
  forall (f : A -> list B)(xs : list A) x y,
    In y (f x) -> 
    In x xs    ->
    In y (flat_map f xs).
Proof.
  inductions xs ; crush.
  apply in_app_iff ; right*.
Qed.