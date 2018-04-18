Set Implicit Arguments.

Require Import
        Arith_base
        Syntax.Name
        Tactics.Tactics.

Record treatment : Set
  := MkTreatment {
         tr_name     : name
     ;   tr_command  : name 
     }.

Definition eq_treatment_dec : forall (t t' : treatment), {t = t'} + {t <> t'}.
  pose eq_name_dec ; decide equality.
Defined.

Instance treatmentName : Nameable treatment
  :={
      name_of := tr_name
    }.

Record experimental_object : Set
  := MkObject {
         obj_name     : name
     ;   obj_argument : name
     }.

Definition eq_experimental_object_dec
  : forall (o o' : experimental_object), {o = o'} + {o <> o'}.
  pose eq_name_dec ; decide equality.
Defined.

Instance objectName : Nameable experimental_object
  :={
      name_of := obj_name
    }.

Record dependent_variable : Set
  := MkDependentVar {
         dep_name       : name
     ;   dep_instrument : name 
     }.

Definition eq_dependent_variable_dec
  : forall (v v' : dependent_variable), {v = v'} + {v <> v'}.
  pose eq_name_dec ; decide equality.
Defined.

Instance variableName : Nameable dependent_variable
  :={
      name_of := dep_name
    }.

Record experimental_design : Set
  := MkDesign {
        des_runs     : nat
     ;  des_function : list (treatment * experimental_object)  
     }.

Record research_hypothesis : Set
  := MkHypothesis {
       hyp_name       : name
     ; hyp_variable   : dependent_variable
     ; hyp_treatment1 : treatment
     ; hyp_operator   : name 
     ; hyp_treatment2 : treatment
     }.

Definition eq_research_hypothesis_dec
  : forall (r r' : research_hypothesis), {r = r'} + {r <> r'}.
    pose eq_name_dec ;
    pose eq_dependent_variable_dec ;
    pose eq_treatment_dec ; decide equality.
Defined.

Instance hypothesisName : Nameable research_hypothesis
  :={
      name_of := hyp_name
    }.

Record experiment : Set
  := MkExperiment {
        exp_hypothesis : list research_hypothesis
     ;  exp_design     : experimental_design
     ;  exp_treatments : list treatment
     ;  exp_objects    : list experimental_object
     ;  exp_variables  : list dependent_variable
     }.
