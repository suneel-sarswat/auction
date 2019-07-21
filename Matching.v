
(* -----------------Description----------------------------------------------------------

This file contains useful definitions and basic properties of fundamental concepts 
about auctions such as matching, maximum matching (MM), individual rational matching (IR), 
uniform matching, fair matching etc. This file also contains results on matchings, 
IR matchings, uniform matchings.


    Terms          <==>     Explanations
    -----------------------------------------------------
    All_matchable M        Every bid-ask pair in M are matchable
    matching M             All_matchable M && NoDup B_M && NoDup A_M              
    matching_in B A M      matching M && B_M [<=] B && A_M [<=] A
    Is_MM M B A            M is maximal matching for B and A
    rational m             bid_of m  >= tp m >= ask_of m
    Is_IR M                forall m, In n M -> rational m    
    Uniform M              all bid-ask pairs in M is traded at single price        
    fair_on_bids B M       M is fair on all bids (i.e. B)
    fair_on_asks A M       M is fair on all asks (i.e. A) 
    Is_fair M B A          M is fair on B and A

Most of the results in this file contains the introduction and elimination rules 
for all the above defined notions.

-----------------------------------------------------------------------------*)

Require Import ssreflect ssrbool.
Require Export Lists.List.
Require Export GenReflect SetSpecs.

Require Export BidAsk.
Require Export DecList.
Require Export Sorting.

Section Matching.

  
(*----------------- Notion of matching and  Maximal Matching (MM) ------------------------*)

(* Definition matchable (b: Bid)(a: Ask):=  (sp (a)) <= (bp (b)). *)

  Definition All_matchable (M: list fill_type):= forall m, In m M -> (ask_of m) <= (bid_of m).


Definition all_matchable (M:list fill_type) := forallb (fun m => 
 (ask_of m) <=? (bid_of m)) M.

Lemma all_matchableP (M:list fill_type): reflect (All_matchable M) (all_matchable M).
Proof. {  apply reflect_intro.  unfold Prop_bool_eq. split.
          { induction M. intros. simpl. auto. intros. simpl. apply /andP. split.
            apply /leP. unfold All_matchable in H. apply H. auto.
            assert (H1: All_matchable M).
            revert H. unfold All_matchable. simpl. auto.  apply IHM in H1. eauto. }
          { induction M. intros. unfold All_matchable. intros. destruct H0.
            simpl. intros. move /andP in H. destruct H. unfold All_matchable. intros. 
            destruct H1. move /leP in H. subst a. exact. eapply IHM in H0. 
            unfold All_matchable in H0. eapply H0 in H1. exact. } } Qed.

Definition matching (M: list fill_type):=
  (All_matchable M) /\ (NoDup (bids_of M)) /\ (NoDup (asks_of M)).


  
Definition matching_in (B:list Bid) (A:list Ask) (M:list fill_type):=
(matching M) /\ ((bids_of M) [<=] B) /\ ((asks_of M) [<=] A).

Definition Is_MM (M : list fill_type)(B: list Bid)(A: list Ask) :=
  matching_in B A M /\ 
  (forall M': list fill_type, matching_in B A M'-> |M'| <= |M|).


Lemma All_matchable_elim (m: fill_type)(M: list fill_type):
  All_matchable (m::M) -> (ask_of m) <= (bid_of m).
Proof.  intros H.  unfold All_matchable in H. simpl in H. auto.  Qed.   
 

Lemma All_matchable_elim1 (m: fill_type)(M: list fill_type):
  All_matchable (m::M) -> All_matchable M.
Proof.  unfold All_matchable. intros.  simpl in H. auto. Qed.

Lemma All_matchable_elim2  (m: fill_type)(M: list fill_type):
  All_matchable M -> All_matchable (delete m M).
Proof. unfold All_matchable. intros. apply H. eapply delete_elim1. eauto. Qed.  

Definition empty_fill: list fill_type:= nil.

Lemma All_matchable_nil: All_matchable nil.
Proof. unfold All_matchable. intros. inversion H. Qed.  

Lemma All_matchable_intro (m: fill_type)(M: list fill_type):
  (ask_of m) <= (bid_of m) -> All_matchable M -> All_matchable (m::M).
Proof. { intros H1 H2. unfold All_matchable. simpl. intros m0 H3. destruct H3.
         subst m0. exact. eauto. } Qed. 


Hint Immediate All_matchable_intro All_matchable_nil: core.
Hint Resolve All_matchable_elim All_matchable_elim1 All_matchable_elim2 : core.

Lemma nill_is_matching (B: list Bid)(A: list Ask) : matching_in B A nil.
Proof. { unfold matching_in. split. unfold matching.
         split. apply All_matchable_nil.
         split. simpl. constructor. simpl. constructor.
         split. simpl. auto. simpl. auto. } Qed.
Hint Resolve nill_is_matching: core.

(*-------------introduction and elimination for matching ------------------------*)

(*-------    Definition matching (M: list fill_type):=
             (All_matchable M) /\ (NoDup (bids_of M)) /\ (NoDup (asks_of M)).    *)

Lemma matching_elim0 (m: fill_type) (M: list fill_type): matching M -> In m M ->
                                                         (ask_of m) <= (bid_of m).
Proof. intros. unfold matching in H.  destruct H. unfold All_matchable in H.
apply H in H0. exact. Qed.

Lemma matching_elim1 (M: list fill_type): matching M -> NoDup (bids_of M).
Proof.  intro H. unfold matching in H. destruct H. destruct H0. exact. Qed.

Lemma matching_elim2 (M: list fill_type): matching M -> NoDup (asks_of M).
Proof. intro H. unfold matching in H. destruct H. destruct H0. exact. Qed.

Lemma matching_elim3 (M: list fill_type): matching M -> NoDup M.
Proof. { intro H. destruct H. destruct H0.
         induction M as [|m].
         { auto. }
         { constructor. intro H2. assert (H4: In (bid_of m) (bids_of M)). eauto.
           simpl in H0. assert (H5: ~In (bid_of m) (bids_of M)). eauto. contradiction.
           apply IHM. all: eauto. } } Qed.


Lemma matching_elim4 (m: fill_type) (M: list fill_type): matching (m::M) ->
                                                         ~ In (ask_of m) (asks_of M).
Proof. { intros. unfold matching in H. destruct H. destruct H0. simpl in H1.
         eapply nodup_elim2 in H1. exact. } Qed.

Lemma matching_elim5 (m: fill_type) (M: list fill_type): matching (m::M) ->
                                                         ~ In (bid_of m) (bids_of M).
Proof. { intros. unfold matching in H. destruct H. destruct H0. simpl in H0.
         eapply nodup_elim2 in H0. exact. } Qed.

Lemma matching_elim6 (m: fill_type) (M: list fill_type): matching (m::M) -> matching M.
Proof. { intros. unfold matching in H. destruct H. destruct H0. unfold matching.
         split. eapply All_matchable_elim1. eauto. split. eauto. eauto. } Qed.

Lemma matching_elim14 (m1 m2: fill_type) (M: list fill_type): matching M -> In m1 M -> In m2 M ->
                                                              m1 <> m2 -> bid_of m1 <> bid_of m2.
Proof. { induction M.
         { intros. destruct H0. }
         { intros.  destruct H. destruct H3. destruct H1;destruct H0.
           { subst m1. subst m2. destruct H2. exact. }
           { subst a. simpl in H4.
             assert (H5: In (bid_of m1) (bids_of M)). eauto. 
             assert (H6: ~ In (bid_of m2) (bids_of M)). eauto.
             intro h7. rewrite h7 in H5. contradiction. } 
           { subst a. simpl in H4.
             assert (H5: In (bid_of m2) (bids_of M)). eauto. 
             assert (H6: ~ In (bid_of m1) (bids_of M)). eauto.
             intro h7. rewrite h7 in H6. contradiction. }
           { apply IHM. unfold matching;eauto. all: exact. } } } Qed.

Lemma matching_elim15 (m1 m2: fill_type) (M: list fill_type): matching M -> In m1 M -> In m2 M ->
                                                              m1 <> m2 -> ask_of m1 <> ask_of m2.
Proof.  { induction M.
          { intros. destruct H0. } 
          { intros.  destruct H. destruct H3. destruct H1;destruct H0. 
            { subst m1. subst m2. destruct H2. exact. }
            { subst a. simpl in H4.
              assert (H5: In (ask_of m1) (asks_of M)). eauto. 
              assert (H6: ~ In (ask_of m2) (asks_of M)). eauto.
              intro h7. rewrite h7 in H5. contradiction. } 
            { subst a. simpl in H4.
              assert (H5: In (ask_of m2) (asks_of M)). eauto. 
              assert (H6: ~ In (ask_of m1) (asks_of M)). eauto.
              intro h7. rewrite h7 in H6. contradiction. }
            { apply IHM. unfold matching;eauto. all: exact. } } } Qed.



Lemma matching_elim7 (m: fill_type) (M: list fill_type): In m M -> matching M ->
                                                         ~ In (ask_of m) (asks_of (delete m M)).
Proof.  { intros H1 H2. unfold matching in H2.
          destruct H2. destruct H0.
          intro H3.
          assert (H4: exists m', (In m' (delete m M))/\ (ask_of m = ask_of m')).
          eauto. destruct H4 as [m' H4]. destruct H4 as [H4 H5].
          assert (H6: In m' M). eapply included_elim2. eapply included_elim4.
          apply included_intro2. exact H1. apply included_intro2. exact H4.
          apply included_refl. assert (H7: m'<>m).
          cut (NoDup M).
          { intro. eapply delete_elim2. exact H7. exact H4. }
          apply matching_elim3. unfold matching. auto.
          eapply matching_elim15 in H7. symmetry in H5.
          contradiction. instantiate (1:=M).
          unfold matching. auto. exact. exact. } Qed.
 
  

Lemma matching_elim8 (m: fill_type) (M: list fill_type): In m M -> matching M ->
                                                         ~ In (bid_of m) (bids_of (delete m M)).
Proof.  { intros H1 H2. unfold matching in H2. destruct H2. destruct H0.
          intro H3.
          assert (H4: exists m', (In m' (delete m M))/\ (bid_of m = bid_of m')). eauto.
          destruct H4 as [m' H4]. destruct H4 as [H4 H5].
          assert (H6: In m' M). eauto. assert (H7: m'<>m).
          cut (NoDup M). eauto. apply matching_elim3.
          unfold matching. auto. eapply matching_elim14 in H7.
          symmetry in H5. contradiction. instantiate (1:=M).
          unfold matching. auto. exact. exact. } Qed.



Lemma matching_elim9 (m: fill_type) (M: list fill_type): matching M ->  matching (delete m M).
Proof. { intros H. unfold matching in H. destruct H. destruct H0.
         unfold matching. split. 
         { eauto. }
         split.
         {  assert (H2: included (delete m M) (M)).
            eapply included_elim4a. eapply included_M_imp_included_bids in H2.
            eapply nodup_included_nodup in H2.
            all: exact. }
         { assert (H2: included (delete m M) (M)).
           eapply included_elim4a. eapply included_M_imp_included_asks in H2.
           eapply nodup_included_nodup in H2.
           all: exact. } } Qed.

Lemma matching_elim10 (m: fill_type) (M: list fill_type): matching M -> In m M ->
                                                          ~ In (bid_of m) (bids_of (delete m M)).
Proof. intros. eapply  matching_elim8. exact. exact. Qed.

Lemma matching_elim11 (m: fill_type) (M: list fill_type): matching M -> In m M ->
                                                          ~ In (ask_of m) (asks_of (delete m M)).
Proof. intros. eapply  matching_elim7. all: exact. Qed.

Lemma matching_elim12 (m: fill_type) (M: list fill_type): matching (m::M) ->
                                                          ~ In (bid_of m) (bids_of M).
Proof. { intros. intro. destruct H. destruct H1.  simpl in H1.
         eapply nodup_elim2 in H1. contradiction. } Qed.

Lemma matching_elim13 (m: fill_type) (M: list fill_type): matching (m::M) ->
                                                          ~ In (ask_of m) (asks_of M).
Proof. { intros. intro. destruct H. destruct H1.  simpl in H2. eapply nodup_elim2 in H2.
         contradiction. } Qed.




Hint Resolve matching_elim0 matching_elim1 matching_elim2 matching_elim3: core.
Hint Resolve matching_elim4 matching_elim5 matching_elim6 matching_elim7: core.
Hint Resolve matching_elim8 matching_elim9 matching_elim10 matching_elim11: core.
Hint Resolve matching_elim12 matching_elim13: core.
Hint Resolve matching_elim14 matching_elim15: core.


(*-----------------introduction and elimination for matching_in -----------------*)                                                         
Lemma matching_in_intro (m: fill_type) (M: list fill_type)(B: list Bid)(A: list Ask):
  (ask_of m) <= (bid_of m) -> matching_in B A M -> ~ In (bid_of m) (bids_of M) ->
  ~ In (ask_of m) (asks_of M) -> In (bid_of m) B -> In (ask_of m) A -> matching_in B A (m::M).

Proof.  { intros H1 H2 H3 H4 H5 H6. unfold matching_in. split.
          unfold matching in H2. destruct H2. destruct H. destruct H2.
          destruct H0. unfold matching.
          split. eauto. split. simpl. eapply nodup_intro in H3. exact. exact.
          eapply nodup_intro in H4. exact. exact. destruct H2. destruct H0. split.
          simpl. unfold "[<=]". intros. destruct H7. subst a. exact. eauto.
          simpl. unfold "[<=]". intros. destruct H7. subst a. exact. eauto. } Qed.

  Lemma matching_in_elim0 (M: list fill_type)(B: list Bid)(A: list Ask): matching_in B A M ->
                                                                         matching M.
  Proof. intros. unfold matching_in in H. destruct H. exact. Qed.
  
  
Lemma matching_in_elim (m: fill_type) (M: list fill_type)(B: list Bid)(A: list Ask):
  matching_in B A (m::M) -> matching_in B A M.
Proof. { intros. unfold matching_in in H. destruct H. destruct H0. 
         unfold matching_in. split. eauto. split. eauto. eauto. } Qed.

Lemma matching_in_elim1 (m: fill_type) (M: list fill_type) (B: list Bid)(A: list Ask):
  matching_in B A (m::M) ->  (ask_of m) <= (bid_of m).
Proof. { unfold matching_in. intros H. destruct H as [H1 H].
         destruct H1 as [H1 H2]. eauto. } Qed.
 

Lemma matching_in_elim2 (m: fill_type) (M: list fill_type) (B: list Bid)(A: list Ask):
  matching_in B A (m::M) ->   ~ In (bid_of m) (bids_of M).
Proof. { unfold matching_in;unfold matching. intros H.
         destruct H as [H1 H]. destruct H as [H2 H]. destruct H1 as [H1 H3].
         destruct H3 as [H3 H4]. eauto. } Qed.


Lemma matching_in_elim3 (m: fill_type) (M: list fill_type) (B: list Bid)(A: list Ask):
  matching_in B A (m::M) ->   ~ In (ask_of m) (asks_of M).
Proof. { unfold matching_in;unfold matching. intros H.
         destruct H as [H1 H]. destruct H as [H2 H]. destruct H1 as [H1 H3].
         destruct H3 as [H3 H4]. eauto. } Qed.



Lemma matching_in_elim4 (m: fill_type) (M: list fill_type) (B: list Bid)(A: list Ask):
  matching_in B A (m::M) ->   In (bid_of m) B.
Proof. { unfold matching_in;unfold matching. intros H.
         destruct H as [H1 H]. destruct H as [H2 H]. destruct H1 as [H1 H3].
         destruct H3 as [H3 H4]. eauto. } Qed.

Lemma matching_in_elim4a (m: fill_type) (M: list fill_type) (B: list Bid)(A: list Ask):
  matching_in B A M -> In m M ->  In (bid_of m) B.
Proof. intros. destruct H. destruct H1. eauto. Qed.


Lemma matching_in_elim5 (m: fill_type) (M: list fill_type) (B: list Bid)(A: list Ask):
  matching_in B A (m::M) ->   In (ask_of m) A.
Proof. { unfold matching_in;unfold matching. intros H.
         destruct H as [H1 H]. destruct H as [H2 H]. destruct H1 as [H1 H3].
         destruct H3 as [H3 H4]. eauto. } Qed.

Lemma matching_in_elim5a (m: fill_type) (M: list fill_type) (B: list Bid)(A: list Ask):
  matching_in B A M ->  In m M -> In (ask_of m) A.
Proof. intros. unfold matching_in in H. destruct H. destruct H1. eauto. Qed.


Lemma matching_in_elim6 (a: Ask)(B: list Bid)(A: list Ask)(M: list fill_type):
  matching_in B A M -> matching_in B (a::A) M.
Proof. { unfold matching_in. intros. destruct H. destruct H0. split. exact.
         split. exact. eauto. } Qed.

Lemma matching_in_elim7 (b: Bid)(B: list Bid)(A: list Ask)(M: list fill_type):
  matching_in B A M -> matching_in (b::B) A M.
Proof. { unfold matching_in. intros. destruct H. destruct H0. split. exact.
         split. eauto. exact. } Qed.


 Lemma matching_in_elim8 (B: list Bid)(A: list Ask)(b: Bid)(a: Ask)(M: list fill_type):
   matching_in (b::B) (a::A) M -> ~ In b (bids_of M) -> ~ In a (asks_of M) -> matching_in B A M.
 Proof. { unfold matching_in. intros. destruct H. destruct H2. destruct H.
          destruct H4. unfold matching. split.
          { split. { exact. } { eauto. } }
          split.
          { eapply subset_nodup_subset in H2. all: exact. }
          { eapply subset_nodup_subset in H3. all: exact. } } Qed.

Hint Resolve matching_in_elim4a matching_in_elim5a: core. 
Hint Immediate matching_in_intro: auction.
Hint Resolve matching_in_elim0 matching_in_elim matching_in_elim1 matching_in_elim2
     matching_in_elim3 matching_in_elim4 matching_in_elim5 : auction.

Hint Resolve matching_in_elim6 matching_in_elim7 matching_in_elim8: core.

(*----------------- Individual rational and  Fair matching--------------------------*)

Definition rational (m: fill_type):=
  ((bid_of m) >= tp m) /\ (tp m >= (ask_of m)).
Definition Is_IR (M: list fill_type):= forall m, In m M -> rational m.

Lemma Is_IR_elim (m: fill_type)(M: list fill_type): Is_IR (m::M) -> rational m.
Proof. { unfold Is_IR. intros H.  specialize H with m. simpl in H.
         destruct H. left. exact. unfold rational. eauto. } Qed.

Lemma Is_IR_elim1 (m: fill_type)(M: list fill_type): Is_IR (m::M)-> Is_IR M.
Proof. unfold Is_IR. simpl. intros. eauto. Qed.

Lemma Is_IR_elim2 (m: fill_type)(M: list fill_type): Is_IR M -> Is_IR (delete m M).
Proof. unfold Is_IR. intros. eauto. Qed.

Lemma Is_IR_intro (m: fill_type)(M: list fill_type): rational m -> Is_IR M -> Is_IR (m::M).
Proof.  unfold Is_IR. intros. destruct H1. subst m0. exact. auto. Qed.  

Hint Immediate Is_IR_intro: auction.
Hint Resolve Is_IR_elim Is_IR_elim1: auction.

Definition fair_on_bids (M: list fill_type)(B: list Bid):=
  (forall b b', In b B /\ In b' B -> b > b' -> In b' (bids_of M) -> In b (bids_of M)).

Definition fair_on_asks (M: list fill_type) (A: list Ask):=
  (forall s s', In s A /\ In s' A -> s < s' -> In s' (asks_of M) -> In s (asks_of M)).

Definition Is_fair (M: list fill_type) (B: list Bid) (A: list Ask) 
  :=  fair_on_asks M A /\ fair_on_bids M B.


(*------------------Uniform matching------------------------------*)


Definition Uniform (M : list fill_type) := uniform (trade_prices_of M).


Lemma Uniform_intro (M:list fill_type) (m:fill_type) : Uniform M -> Uniform (delete m M).
Proof. { unfold Uniform. induction M. simpl. auto. intros H.
         simpl.  case (m_eqb m a) eqn: H1.
         assert (H2:uniform (trade_prices_of M)).
         assert (H2: uniform (trade_prices_of (a :: M))).
         exact H. revert H2. eapply uniform_elim2. exact H2.
         simpl in H. eapply uniform_elim2 in H as H2.  eapply IHM in H2. simpl.  Admitted.

Lemma Uniform_intro1 (M:list fill_type) (m:fill_type) : Uniform (m::M) -> Uniform M.
Proof. unfold Uniform.  simpl.  eapply uniform_elim2. Qed.

Lemma Uniform_elim (M:list fill_type) (m1 m2:fill_type) :
  Uniform M -> In m1 M -> In m2 M -> tp m1= tp m2.
Proof. Admitted.

Lemma Uniform_intro2 (M:list fill_type) (m m':fill_type) : Uniform M -> 
In m M -> tp m = tp m' -> Uniform (m'::M).
Proof. Admitted.

Hint Resolve Uniform_intro Uniform_elim Uniform_intro1 : core.
Hint Immediate Uniform_intro2 : core.


End Matching.


Hint Unfold All_matchable.
Hint Immediate All_matchable_intro All_matchable_nil: core.
Hint Resolve All_matchable_elim All_matchable_elim1 All_matchable_elim2 : core.

Hint Resolve matching_elim0 matching_elim1 matching_elim2 matching_elim3: core.
Hint Resolve matching_elim4 matching_elim5 matching_elim6 matching_elim7: core.
Hint Resolve matching_elim8 matching_elim9: core.
Hint Resolve matching_elim10 matching_elim11: core.
Hint Resolve matching_elim12 matching_elim13: core.
Hint Resolve matching_elim14 matching_elim15: core.

Hint Resolve nill_is_matching: core.
Hint Immediate matching_in_intro: core.
Hint Resolve matching_in_elim0 matching_in_elim matching_in_elim1: core.
Hint Resolve matching_in_elim2 matching_in_elim3 matching_in_elim4: core.
Hint Resolve matching_in_elim4a matching_in_elim5a: core. 
Hint Resolve matching_in_elim5 matching_in_elim6 matching_in_elim7 matching_in_elim8: core.
Hint Immediate Is_IR_intro: core.
Hint Resolve Is_IR_elim Is_IR_elim1: core.
Hint Resolve Uniform_intro Uniform_elim Uniform_intro1 : core.
Hint Immediate Uniform_intro2 : core.

