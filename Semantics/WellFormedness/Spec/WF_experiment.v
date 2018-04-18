Set Implicit Arguments.

Require Import
        List
        Syntax.Experiment
        Syntax.Name
        Tactics.Tactics.

Inductive wf_treatment : experiment -> treatment -> Prop :=
| WF_treatment
  : forall e t ts,
      ts = exp_treatments e ->
      In t ts               ->
      wf_treatment e t.

Hint Constructors wf_treatment.

Inductive wf_experimental_object : experiment -> experimental_object -> Prop :=
| WF_object
  : forall e o os,
    os = exp_objects e ->
    In o os ->
    wf_experimental_object e o.

Hint Constructors wf_experimental_object.

Inductive wf_dependent_variable : experiment -> dependent_variable -> Prop :=
| WF_variable
  : forall e v vs,
    vs = exp_variables e ->
    In v vs              ->
    wf_dependent_variable e v.

Hint Constructors wf_dependent_variable.

Inductive wf_experimental_design : experiment -> experimental_design -> Prop :=
| WF_design
  : forall e d ts os f,
    ts = exp_treatments e ->
    d  = exp_design e     ->
    os = exp_objects e    -> 
    f = des_function d    ->
    Forall (fun t => In (fst t) ts /\ In (snd t) os) f ->
    wf_experimental_design e d.

Hint Constructors wf_experimental_design.
   
Inductive wf_research_hypothesis : experiment -> research_hypothesis -> Prop :=
| WF_hypothesis
  : forall e n rh rhs t1 t2 op dv,
    n = hyp_name rh -> 
    rhs = exp_hypothesis e ->
    t1 = hyp_treatment1 rh ->
    t2 = hyp_treatment2 rh ->
    op = hyp_operator rh ->
    dv = hyp_variable rh -> 
    In rh rhs -> 
    wf_treatment e t1 ->
    wf_treatment e t2 ->
    wf_dependent_variable e dv ->
    t1 <> t2 ->
    wf_research_hypothesis e rh.

Hint Constructors wf_research_hypothesis.


Inductive wf_experiment : experiment -> Prop :=
| WF_experiment
  : forall e rhs d ts os vs,
    rhs = exp_hypothesis e ->
    d = exp_design e ->
    ts = exp_treatments e ->
    os = exp_objects e ->
    vs = exp_variables e -> 
    Forall (fun rh => wf_research_hypothesis e rh) rhs ->
    Forall (fun t => wf_treatment e t) ts ->
    Forall (fun o => wf_experimental_object e o) os ->
    Forall (fun v => wf_dependent_variable e v) vs ->
    wf_experimental_design e d ->
    NoDup ts ->
    NoDup vs ->
    NoDup os ->
    NoDup (names rhs) ->
    wf_experiment e.

Hint Constructors wf_experiment.
