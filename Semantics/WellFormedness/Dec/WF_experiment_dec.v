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

Definition wf_experimental_design_dec
  : forall e, {wf_experimental_design e (exp_design e)} +
         {~ wf_experimental_design e (exp_design e)}.
  intros e; 
     assert (Hdec : forall (p : treatment * experimental_object),
             {In (fst p) (exp_treatments e) /\ In (snd p) (exp_objects e)} +
             {~ (In (fst p) (exp_treatments e) /\ In (snd p) (exp_objects e))})
        by 
          (intros p ;
            destruct (In_dec eq_treatment_dec (fst p) (exp_treatments e)) ;
            destruct (In_dec eq_experimental_object_dec (snd p) (exp_objects e)) ;
            dec_finisher) ;
     destruct (Forall_dec _ Hdec (des_function (exp_design e))) ; dec_finisher.
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