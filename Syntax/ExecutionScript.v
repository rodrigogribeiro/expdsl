Set Implicit Arguments.

Require Import
        List
        Syntax.Name.

Record application : Set
  := MkApplication {
         app_instrument : name
     ;   app_command    : name
     ;   app_argument   : name 
     }.

Definition eq_application_dec :
  forall (app app' : application), {app = app'} + {app <> app'}.
  pose eq_name_dec ; decide equality.
Defined.

Definition execution_script := list application.