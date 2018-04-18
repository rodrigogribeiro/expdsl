Set Implicit Arguments.

Require Import
        List
        Syntax.Name.

Record analysis_result : Set
  := MkAnalysisResult {
       anres_result : name 
     }.


Record test_result : Set
  := MkTestResult {
       tres_name : name
     ; tres_result : analysis_result
     }.

Record hypothesis_result : Set
  := MkHypResult {
       hypr_name : name
     ; hypr_results : list test_result 
     }.


