Require Import ssreflect ssrbool. 
Require Export Lists.List.

Require Export GenReflect SetSpecs.

Require Export Sorting MinMax.
Require Export BidAsk.
Require Export DecList.
Require Export Matching.
Require Export AuctionInvar.

Require Export Fair.

Section MM.

Fixpoint produce_MM (B:list Bid) (A: list Ask): (list fill_type) :=
  match (B, A) with
  |(nil, _) => nil
  |(b::B', nil) => nil              
  |(b::B', a::A') => match (Nat.leb (sp a) (bp b)) with
                    |true => ({|bid_of:= b ; ask_of:= a ; tp:=(bp b) |})::(produce_MM B' A')
                    |false => produce_MM B A'
                    end
  end.

(*------------ Sorting by decreasing ask prices and their properties --------------*)

Definition by_dsp := fun a1 a2 : Ask => a2 <=? a1.
Lemma by_dsp_P : transitive by_dsp /\ comparable by_dsp.
Proof.  { split.
          { unfold transitive. unfold by_dsp.  
            intros y x z H H1. move /leP in H1. move /leP in H.
            apply /leP. omega. }
          { unfold comparable.  unfold by_dsp. intros.
            move /leP in H. apply /leP. omega. } } Qed.

Hint Resolve by_dsp_P: core.


 Lemma nil_is_MM_forB (B: list Bid): MM_in B nil nil.
 Proof. Admitted.
 
 Lemma nil_is_MM_forA (A: list Ask): MM_in nil A nil.
 Proof. Admitted.

 Hint Resolve nil_is_MM_forB nil_is_MM_forA: core.
           
Lemma produce_MM_is_MM (B: list Bid)(A: list Ask): Sorted by_dbp B -> Sorted by_dsp A->
                                                   MM_in B A (produce_MM B A).
Proof. revert B. induction A as [|a A'].
       { (* base case: when A is nil *)
         intros B H H0.  case B. simpl.
         { eauto. }
         { intros b l. simpl. eauto. } }
       { (* induction step: when A is a::A' *)
         intros B h h0. case B as [| b B'].
         { simpl. eauto. }
         { (*----- induction step : b::B'   and a:: A' ---------*)
           assert (Case: b < a \/ b >= a ). omega.
           destruct Case as [C1 | C2].
           { (*------C1:  when b and a are not matchable then produce_MM (b::B') A' *)
             simpl. replace (a <=? b) with false.
             Focus 2. symmetry. apply /leP. omega.
             assert (h1: MM_in (b::B') A' (produce_MM (b::B') A')).
             { apply IHA'. all: eauto. }
             unfold MM_in. split.
             { (*-- matching_in (b :: B') (a :: A') (produce_MM (b :: B') A') ---*)
               destruct h1 as [h1a h1]. eauto. }
             { intros M' h2. destruct h1 as [h1a h1].
               apply h1.
               (* --- Goal: matching_in (b :: B') A' M'---- trivial proof ---*)
               admit. } }
           
           { (*-- C2: when b and a are matchable then Output is (b,a):: produce_MM B' A'----*)
             admit. } } } Admitted.
               

          
 

(*
Definition B2:= ({|b_id:= 1 ; bp:= 125 |}) ::({|b_id:= 2 ; bp:= 120 |}) ::({|b_id:= 3 ; bp:= 112 |}) ::({|b_id:= 4 ; bp:= 91 |}) ::({|b_id:= 5 ; bp:= 82 |}) ::({|b_id:= 6 ; bp:= 82 |}) ::({|b_id:= 7 ; bp:= 69 |}) ::({|b_id:= 8 ; bp:= 37 |}) :: nil.

Definition A2:= ({|s_id:= 1 ; sp:= 121 |}) ::({|s_id:= 3 ; sp:= 113 |}) ::({|s_id:= 5 ; sp:= 98 |}) ::({|s_id:= 9 ; sp:= 94 |}) ::({|s_id:= 90 ; sp:= 90 |}) ::({|s_id:= 78 ; sp:= 85 |}) ::({|s_id:= 67 ; sp:= 79 |}) ::({|s_id:= 45 ; sp:= 53 |}) ::nil.

*)


End MM.
