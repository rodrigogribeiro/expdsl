Set Implicit Arguments.

Require Import
        List
        Semantics.WellFormedness.WellFormedness
        Syntax.Syntax
        Tactics.Tactics
        Utils.ListUtils.

Definition compile_from_hypothesis
           (hyps : list research_hypothesis)
           (p : treatment * experimental_object)
          : list application
  := map (fun hyp => MkApplication (dep_instrument (hyp_variable hyp))
                                (tr_command (fst p))
                                (obj_argument (snd p))) hyps.

Definition compile_execution_script (e : experiment) : execution_script :=
  replicate (des_runs (exp_design e))
            (nodup eq_application_dec
                   (flat_map (fun p => compile_from_hypothesis (exp_hypothesis e) p)
                             (des_function (exp_design e)))).

Lemma compile_hypothesis_sound
  : forall hyps hyp p tr obj app,
    p = (tr,obj) ->
    In hyp hyps ->
    app = MkApplication (dep_instrument (hyp_variable hyp))
                        (tr_command tr)
                        (obj_argument obj) ->
    In app (compile_from_hypothesis hyps p).
Proof.
  induction hyps ; intros ; try solve [simpl in * ; contradiction].
  rewrite H. simpl in H0. destruct H0 ; substs. crush. right*.
Qed.

Hint Resolve compile_hypothesis_sound.

Lemma compile_execution_sound
  : forall fs hyps hyp tr obj app,
    In (tr,obj) fs ->
    In hyp hyps -> 
    app = MkApplication (dep_instrument (hyp_variable hyp))
                        (tr_command tr)
                        (obj_argument obj) ->
    In app
    (nodup eq_application_dec
       (flat_map
          (fun p => compile_from_hypothesis hyps p) fs)).
Proof.
  induction fs ; intros ; apply nodup_In.
  +
    crush.
  +
    simpl in *.
    destruct H. rewrite H in *.
    apply in_app_iff.
    left*.
    apply in_app_iff.
    right*.
    eapply flat_map_In with (x := (tr, obj)) ; crush.
    eapply compile_hypothesis_sound ; eauto.
Qed.

Theorem compilation_sound
  : forall e, wf_experiment e ->
    forall hyp, In hyp (exp_hypothesis e) ->
           forall p tr obj, In p (des_function (exp_design e)) ->
                       p = (tr , obj) ->
                       forall app, app = MkApplication (dep_instrument (hyp_variable hyp))
                                                  (tr_command tr)
                                                  (obj_argument obj) ->
                     (count_occ
                        eq_application_dec
                        (compile_execution_script e) app) = (des_runs (exp_design e)).
Proof.
  intros ;
    unfold compile_execution_script.
  assert (Hd : NoDup (nodup eq_application_dec
                     (flat_map (fun p => compile_from_hypothesis (exp_hypothesis e)
                                                              p)
                               (des_function (exp_design e))))) by
      apply NoDup_nodup.
  eapply (replicate_count_occ eq_application_dec)
    with (x := app)(n := des_runs (exp_design e))
    in Hd ; eauto.
  inverts* H.
  inverts* H13.
  eapply compile_execution_sound ; eauto ; crush.
Qed.
