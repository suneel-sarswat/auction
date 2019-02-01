
(* -----------------Description----------------------------------------------------------

This file contains useful definitions and basic properties of fundamental concepts 
about auctions such as matching, fair matching, individual rational matching, uniform 
matching, maximum matching etc. This file also contains come counting results about 
matching for example number of buyers above a price in matching etc.

----------------------------------------------------------------------------------------*)

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
 (bid_of m) <=? (ask_of m)) M.

Lemma all_matchableP (M:list fill_type): reflect (All_matchable M) (all_matchable M).
Proof.  Admitted.

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

Definition empty_fill: list fill_type:= nil.

Lemma All_matchable_nil: All_matchable nil.
Proof. unfold All_matchable. intros. inversion H. Qed.  

Lemma All_matchable_intro (m: fill_type)(M: list fill_type):
  (ask_of m) <= (bid_of m) -> All_matchable M -> All_matchable (m::M).
Proof. { intros H1 H2. unfold All_matchable. simpl. intros m0 H3. destruct H3.
         subst m0. exact. eauto. } Qed. 


Hint Immediate All_matchable_intro All_matchable_nil: auction.
Hint Resolve All_matchable_elim All_matchable_elim1 : auction.

Lemma nill_is_matching (B: list Bid)(A: list Ask) : matching_in B A nil.
Proof. { unfold matching_in. split. unfold matching.
         split. apply All_matchable_nil.
         split. simpl. constructor. simpl. constructor.
         split. simpl. auto. simpl. auto. } Qed.
Hint Resolve nill_is_matching: auction.

(*-------------introduction and elimination for matching ------------------------*)

(*-------    Definition matching (M: list fill_type):=
             (All_matchable M) /\ (NoDup (bids_of M)) /\ (NoDup (asks_of M)).    *)

Lemma matching_elim0 (m: fill_type) (M: list fill_type): matching M -> In m M ->
                                                         (ask_of m) <= (bid_of m).
Proof. Admitted.

Lemma matching_elim1 (M: list fill_type): matching M -> NoDup (bids_of M).
Proof. Admitted.

Lemma matching_elim2 (M: list fill_type): matching M -> NoDup (asks_of M).
Proof. Admitted.

Lemma matching_elim3 (M: list fill_type): matching M -> NoDup M.
Proof. Admitted.

Lemma matching_elim4 (m: fill_type) (M: list fill_type): matching (m::M) ->
                                                         ~ In (ask_of m) (asks_of M).
Proof. Admitted.

Lemma matching_elim5 (m: fill_type) (M: list fill_type): matching (m::M) ->
                                                         ~ In (bid_of m) (bids_of M).
Proof. Admitted.

Lemma matching_elim6 (m: fill_type) (M: list fill_type): matching (m::M) -> matching M.
Proof. Admitted.

Lemma matching_elim7 (m: fill_type) (M: list fill_type): In m M -> matching M ->
                                                         ~ In (ask_of m) (asks_of (delete m M)).
Proof. Admitted.

Lemma matching_elim8 (m: fill_type) (M: list fill_type): In m M -> matching M ->
                                                         ~ In (bid_of m) (bids_of (delete m M)).
Proof. Admitted.

Lemma matching_elim9 (m: fill_type) (M: list fill_type): matching M ->  matching (delete m M).
Proof. Admitted.

Lemma matching_elim10 (m: fill_type) (M: list fill_type): matching M -> In m M ->
                                                          ~ In (bid_of m) (bids_of (delete m M)).
Proof. Admitted.

Lemma matching_elim11 (m: fill_type) (M: list fill_type): matching M -> In m M ->
                                                          ~ In (ask_of m) (asks_of (delete m M)).
Proof. Admitted.

Lemma matching_elim12 (m: fill_type) (M: list fill_type): matching (m::M) ->
                                                          ~ In (bid_of m) (bids_of M).
Proof. Admitted.

Lemma matching_elim13 (m: fill_type) (M: list fill_type): matching (m::M) ->
                                                          ~ In (ask_of m) (asks_of M).
Proof. Admitted.




Hint Resolve matching_elim0 matching_elim1 matching_elim2 matching_elim3: core.
Hint Resolve matching_elim4 matching_elim5 matching_elim6 matching_elim7: core.
Hint Resolve matching_elim8 matching_elim9 matching_elim10 matching_elim11: core.
Hint Resolve matching_elim12 matching_elim13: core.


(*-----------------introduction and elimination for matching_in -----------------*)                                                         
Lemma matching_in_intro (m: fill_type) (M: list fill_type)(B: list Bid)(A: list Ask):
  (ask_of m) <= (bid_of m) -> matching_in B A M -> ~ In (bid_of m) (bids_of M) ->
  ~ In (ask_of m) (asks_of M) -> In (bid_of m) B -> In (ask_of m) A -> matching_in B A (m::M).
  Proof. Admitted.

  (*
Proof.  intros H1 H2 H3 H4 H5 H6. unfold Is_a_matching. split. unfold Is_a_matching in H2. destruct H2. eauto with auction. split. unfold Is_a_matching in H2. destruct H2 as [H7 H2]. destruct H2 as [H8 H2]. destruct H2 as [H9 H2]. destruct H2 as [H10 H2]. simpl. eauto. split. destruct H2 as [H7 H2]. destruct H2 as [H8 H2]. destruct H2 as [H9 H2]. destruct H2 as [H10 H2]. simpl. eauto. split. destruct H2 as [H7 H2]. destruct H2 as [H8 H2]. destruct H2 as [H9 H2]. destruct H2 as [H10 H2]. simpl. unfold "[<=]". simpl. intros a H. destruct H.  subst a. exact. eauto. destruct H2 as [H7 H2]. destruct H2 as [H8 H2]. destruct H2 as [H9 H2]. destruct H2 as [H10 H2]. simpl. unfold "[<=]". simpl. intros a H. destruct H.  subst a. exact. eauto. Qed.

*)

  Lemma matching_in_elim0 (M: list fill_type)(B: list Bid)(A: list Ask): matching_in B A M ->
                                                                         matching M.
  Proof. Admitted.
  
  
Lemma matching_in_elim (m: fill_type) (M: list fill_type)(B: list Bid)(A: list Ask):
  matching_in B A (m::M) -> matching_in B A M.
  Proof. Admitted.

Lemma matching_in_elim1 (m: fill_type) (M: list fill_type) (B: list Bid)(A: list Ask):
  matching_in B A (m::M) ->  (ask_of m) <= (bid_of m).
Proof. unfold matching_in. intros H. destruct H as [H1 H]. destruct H1 as [H1 H2]. eauto. Qed.
 

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

Lemma matching_in_elim5 (m: fill_type) (M: list fill_type) (B: list Bid)(A: list Ask):
  matching_in B A (m::M) ->   In (ask_of m) A.
Proof. { unfold matching_in;unfold matching. intros H.
         destruct H as [H1 H]. destruct H as [H2 H]. destruct H1 as [H1 H3].
         destruct H3 as [H3 H4]. eauto. } Qed.

Lemma matching_in_elim6 (a: Ask)(B: list Bid)(A: list Ask)(M: list fill_type):
  matching_in B A M -> matching_in B (a::A) M.
Proof. Admitted.

Lemma matching_in_elim7 (b: Bid)(B: list Bid)(A: list Ask)(M: list fill_type):
  matching_in B A M -> matching_in (b::B) A M.
Proof. Admitted.

 Lemma matching_in_elim8 (B: list Bid)(A: list Ask)(b: Bid)(a: Ask)(M: list fill_type):
   matching_in (b::B) (a::A) M -> ~ In b (bids_of M) -> ~ In a (asks_of M) -> matching_in B A M.
 Proof. Admitted.


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


Definition Is_uniform (M : list fill_type) := uniform (trade_prices_of M).


(*-------------- buyers_above and sellers_above relationship and results------------------*)

Definition buyers_above (p: nat)(B: list Bid): list Bid :=
  filter (fun x:Bid => Nat.leb p x)  B.

Lemma buyers_above_elim (p:nat)(B: list Bid)(x:Bid):
  In x (buyers_above p B)-> x >= p.
Proof.   Admitted.
         
Lemma buyers_above_intro (p:nat)(B: list Bid)(x:Bid):
 ( In x B /\ x >= p ) -> In x (buyers_above p B).
Proof. Admitted.

Definition sellers_above (p: nat)(A: list Ask): list Ask :=
  filter (fun x:Ask => Nat.leb p x) (A).

Lemma sellers_above_elim (p:nat)(A: list Ask)(x:Ask):
  In x (sellers_above p A)-> x >= p.
Proof. Admitted.
Lemma sellers_above_intro (p:nat)(A: list Ask)(x:Ask):
 ( In x A /\ x >= p ) -> In x (sellers_above p A).
Proof. Admitted.

Definition buyers_below (p: nat)(B: list Bid): list Bid :=
  filter (fun x:Bid => Nat.leb x p) (B).

Lemma buyers_below_intro (p:nat)(B: list Bid)(x:Bid):
 ( In x B /\ x <= p ) -> In x (buyers_below p B).
Proof. Admitted.
Lemma buyers_below_elim (p:nat)(B: list Bid)(x:Bid):
  In x (buyers_below p B)-> x <= p.
Proof. Admitted.

Definition sellers_below (p: nat)(A: list Ask): list Ask :=
  filter (fun x:Ask => Nat.leb x p) (A).

Lemma sellers_below_intro (p:nat)(A: list Ask)(x:Ask):
 ( In x A /\ x <= p ) -> In x (sellers_below p A).
Proof. Admitted.
Lemma sellers_below_elim (p:nat)(A: list Ask)(x:Ask):
  In x (sellers_below p A)-> x <= p.
Proof. Admitted.

Hint Resolve buyers_above_elim buyers_above_intro: auction.
Hint Resolve sellers_above_elim sellers_above_intro: auction.

Hint Resolve buyers_below_elim buyers_below_intro: auction.
Hint Resolve sellers_below_elim sellers_below_intro: auction.


Theorem buyers_above_ge_sellers (p:nat)(M: list fill_type) (B: list Bid) (A: list Ask):
  matching_in B A M -> | buyers_above p (bids_of M)| >= | sellers_above p (asks_of M)|.
Proof. Admitted.

Theorem sellers_below_ge_buyers (p:nat)(M: list fill_type) (B: list Bid) (A: list Ask):
  matching_in B A M -> | buyers_below p (bids_of M)| <= | sellers_below p (asks_of M)|.
Proof. Admitted.

End Matching.


Hint Unfold All_matchable.
Hint Immediate All_matchable_intro All_matchable_nil: core.
Hint Resolve All_matchable_elim All_matchable_elim1 : core.

Hint Resolve matching_elim0 matching_elim1 matching_elim2 matching_elim3: core.
Hint Resolve matching_elim4 matching_elim5 matching_elim6 matching_elim7: core.
Hint Resolve matching_elim8 matching_elim9: core.
Hint Resolve matching_elim10 matching_elim11: core.
Hint Resolve matching_elim12 matching_elim13: core.

Hint Resolve nill_is_matching: core.
Hint Immediate matching_in_intro: core.
Hint Resolve matching_in_elim0 matching_in_elim matching_in_elim1: core.
Hint Resolve matching_in_elim2 matching_in_elim3 matching_in_elim4: core.
Hint Resolve matching_in_elim5 matching_in_elim6 matching_in_elim7 matching_in_elim8: core.

Hint Immediate Is_IR_intro: core.
Hint Resolve Is_IR_elim Is_IR_elim1: core.

