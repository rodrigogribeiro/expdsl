Set Warnings "-extraction-opaque-accessed,-extraction".
Set Warnings "-notation-overridden,-parsing".
Set Implicit Arguments.

From QuickChick Require Import QuickChick.

Import QcDefaultNotation. Open Scope qc_scope.
Import GenLow GenHigh.


Require Import
        List
        ListDec
        String
        Syntax.Syntax
        Semantics.WellFormedness.Dec.WF_experiment_dec
        Tests.Generators.GenExperiment.

Require Import mathcomp.ssreflect.ssreflect.
From mathcomp Require Import seq ssreflect ssrbool ssrnat eqtype.

Definition wf_experiment_bool (e : experiment) : bool
  := if wf_experiment_dec e then true else false.

Definition gen_experiment_wf
           (e : experiment) :=  wf_experiment_bool e == true.

QuickChick (forAll gen_experiment gen_experiment_wf).
