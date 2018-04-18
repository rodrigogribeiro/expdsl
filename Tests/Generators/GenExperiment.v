From QuickChick Require Import QuickChick.

Import QcDefaultNotation. Open Scope qc_scope.

Require Import
        List
        ListDec
        String
        Ascii
        Syntax.Syntax
        Tests.Generators.GenString
        Tests.Generators.GenUtils
        Utils.ListUtils.

Import ListNotations.

Definition sizeConst := 3.

Import DoNotation.

Definition non_empty_list (A : Type) : Type
  := (A * list A)%type.

Definition from_non_empty_list {A : Type}(xs : non_empty_list A) : list A :=
  fst xs :: snd xs.

(** treatment *)

Section TREATMENT.
  Derive Show for treatment.

  Definition gen_treatments : G (non_empty_list treatment) :=
    bindGen gen_string_nodup_noempty
            (fun inp1 => bindGen gen_string_nodup_noempty
                              (fun inp2 =>
                  match inp1 , inp2 with
                  | (x , xs) , (y , ys) =>
                    returnGen (MkTreatment x y , zipWith MkTreatment xs ys)
                  end)).
End TREATMENT.

(** experimental object *)

Section EXPERIMENTAL_OBJECT.
  Derive Show for experimental_object.

  Definition gen_experimental_objects : G (non_empty_list experimental_object)
    := bindGen gen_string_nodup_noempty
            (fun inp1 => bindGen gen_string_nodup_noempty
                              (fun inp2 =>
                  match inp1 , inp2 with
                  | (x , xs) , (y , ys) =>
                    returnGen ( MkObject x y
                              , zipWith MkObject xs ys)
                  end)).
End EXPERIMENTAL_OBJECT.

(** dependent variable *)


Section DEPENDENT_VARIABLE.
  Derive Show for dependent_variable.

  Definition gen_dependent_variables : G (non_empty_list dependent_variable)
    := bindGen gen_string_nodup_noempty
            (fun inp1 => bindGen gen_string_nodup_noempty
                              (fun inp2 =>
                  match inp1 , inp2 with
                  | (x , xs) , (y , ys) =>
                    returnGen ( MkDependentVar x y
                              , zipWith MkDependentVar xs ys)
                  end)).
End DEPENDENT_VARIABLE.

(** research hypothesis *)

Section RESEARCH_HYPOTHESIS.
  Derive Show for research_hypothesis.

  Definition gen_research_hypothesis
             (ts : non_empty_list treatment)
             (dvs : non_empty_list dependent_variable)
     : G research_hypothesis
    := do! n <- gen_string ;
       do! dv <- gen_from_list dvs ;
       do! t1 <- gen_from_list ts ;
       do! op <- gen_string ;
       do! t2 <- gen_from_list ts ; 
       returnGen (MkHypothesis n dv t1 op t2).

Fixpoint remove_hypothesis1 (xs ac : list research_hypothesis)
    := match xs with
       | [] => ac
       | (h :: hs) =>
         match in_dec eq_research_hypothesis_dec h ac ,
               eq_treatment_dec (hyp_treatment1 h) (hyp_treatment2 h) ,
               in_dec string_dec (hyp_name h)
                      (map hyp_name ac) with
         | left _ , _ , _ => remove_hypothesis1 hs ac
         | _      , left _ , _  => remove_hypothesis1 hs ac
         | _  , _ , left _ => remove_hypothesis1 hs ac
         | right _ , right _ , right _ => remove_hypothesis1 hs (h :: ac)
         end
       end.

  Definition remove_hypothesis (xs : list research_hypothesis)
    := remove_hypothesis1 xs [].

  Definition gen_research_hypothesis_list
             (ts : non_empty_list treatment)
             (dvs : non_empty_list dependent_variable)
    : G (list research_hypothesis)
    := bindGen (choose (1,sizeConst))
               (fun n => liftGen remove_hypothesis
                              (vectorOf n (gen_research_hypothesis ts dvs))).  
End RESEARCH_HYPOTHESIS.

Section EXPERIMENTAL_DESIGN.
  Derive Show for experimental_design.
  Definition gen_experimental_design
             (ts : non_empty_list treatment)
             (os : non_empty_list experimental_object)
        : G experimental_design
    := liftGen2 MkDesign (choose (1,sizeConst))
                (mapGen (fun t => liftGen (fun o => (t, o))
                                       (elements (fst os)
                                                 (snd os))) (fst ts :: snd ts)).
End EXPERIMENTAL_DESIGN.

Section EXPERIMENT.
  Derive Show for experiment.

  Definition gen_experiment : G experiment
    := do! dvs <- gen_dependent_variables ;
       do! ts  <- gen_treatments ;
       do! objs <- gen_experimental_objects ;
       do! dsn <- gen_experimental_design ts objs ;
       do! rhs <- gen_research_hypothesis_list ts dvs ;
       returnGen (MkExperiment rhs
                               dsn
                               (from_non_empty_list ts)
                               (from_non_empty_list objs)
                               (from_non_empty_list dvs)).
End EXPERIMENT.