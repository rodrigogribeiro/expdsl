Set Implicit Arguments.

Require Import
        List
        ListDec

        Syntax.Experiment
        Syntax.Name
        Semantics.WellFormedness.Spec.WF_experiment
        Tactics.Tactics.

Ltac dec_finisher :=
  try solve [left *] ;
  try (let H := fresh "H" in solve [right ; intro H ; inverts* H]).

Definition wf_treatment_dec : forall e t, {wf_treatment e t} + {~ wf_treatment e t}.
  intros e t ;
    destruct (In_dec eq_treatment_dec t (exp_treatments e)) ;
    dec_finisher. 
Defined.    

Definition wf_experimental_object_dec
  : forall e obj, {wf_experimental_object e obj} + {~ wf_experimental_object e obj}.
  intros e obj ;
    destruct (In_dec eq_experimental_object_dec obj (exp_objects e)) ;
    dec_finisher.
Defined.

Definition wf_dependent_variable_dec
  : forall e v, {wf_dependent_variable e v} + {~ wf_dependent_variable e v}.
  intros e v ;
    destruct (In_dec eq_dependent_variable_dec v (exp_variables e)) ;
    dec_finisher.
Defined.


Definition eq_tr_obj_dec :
  forall (p p' : (treatment * experimental_object)),
    {p = p'} + {p <> p'}.
  pose eq_experimental_object_dec ;
    pose eq_treatment_dec ;
    decide equality.
Defined.

Remark exp_in_prop
  : forall (os : list experimental_object)
      (f : list (treatment * experimental_object))
      (t : treatment)
      (o : experimental_object),
    {In o os /\ In (t,o) f} +
    {~ (In o os /\ In (t,o) f)}.
Proof.
  intros os f t o;
    destruct (in_dec eq_experimental_object_dec o os) ;
    destruct (in_dec eq_tr_obj_dec (t,o) f) ;
    dec_finisher.
Qed.

Lemma exp_design_prop
  : forall (os : list experimental_object)
      (f : list (treatment * experimental_object))
      (t : treatment),
     {Exists (fun o => In o os /\ In (t , o) f) os} +
     {~ Exists (fun o => In o os /\ In (t , o) f) os}.
Proof.
  intros os f t ; 
    destruct(Exists_dec _ os (exp_in_prop os f t)) ;
    dec_finisher.
Qed.


Definition wf_experimental_design_dec
  : forall e, {wf_experimental_design e (exp_design e)} +
         {~ wf_experimental_design e (exp_design e)}.
  Hint Resolve exp_design_prop.
  intros e ; 
  destruct (Forall_dec _ (exp_design_prop (exp_objects e)
                                          (des_function (exp_design e)))
                         (exp_treatments e)) ; dec_finisher.
Defined.


Definition wf_research_hypothesis_dec
  : forall e h, {wf_research_hypothesis e h} + {~ wf_research_hypothesis e h}.
  intros e h ;
    destruct (In_dec eq_research_hypothesis_dec h (exp_hypothesis e)) ;
    destruct (wf_treatment_dec e (hyp_treatment1 h)) ;
    destruct (wf_treatment_dec e (hyp_treatment2 h)) ;
    destruct (wf_dependent_variable_dec e (hyp_variable h)) ;
    destruct (eq_treatment_dec (hyp_treatment1 h) (hyp_treatment2 h)) ;
    dec_finisher.
Defined.

Definition wf_experiment_dec
  : forall e, {wf_experiment e} + {~ wf_experiment e}.
  intros e ;
    destruct (Forall_dec _ (wf_research_hypothesis_dec e) (exp_hypothesis e)) ;
    destruct (Forall_dec _ (wf_treatment_dec e) (exp_treatments e)) ;
    destruct (Forall_dec _ (wf_experimental_object_dec e) (exp_objects e)) ;
    destruct (Forall_dec _ (wf_dependent_variable_dec e) (exp_variables e)) ;
    destruct (wf_experimental_design_dec e) ;
    destruct (NoDup_dec eq_treatment_dec (exp_treatments e)) ;
    destruct (NoDup_dec eq_dependent_variable_dec (exp_variables e)) ;
    destruct (NoDup_dec eq_experimental_object_dec (exp_objects e)) ;
    destruct (NoDup_dec eq_name_dec (names (exp_hypothesis e))) ; dec_finisher.
Defined.  