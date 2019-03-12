

Require Export Lists.List.
Require Export GenReflect SetSpecs.
Require Export Sorting.
Require Export DecType SetReflect.
Require Export DecList MoreDecList.

Require Export BidAsk Matching.

Set Implicit Arguments.

Section InvariancePerm.



(******************Matching Invariance*****************)
  
Lemma match_inv (M M': list fill_type) (B B': list Bid) (A A' : list Ask):
perm M  M' -> perm B B' -> perm A A' -> matching_in B A M -> matching_in B' A' M'.
Proof. { intros. destruct H2. destruct H3. destruct H2. destruct H5.
 unfold matching_in. unfold matching. split. { split. {
 unfold All_matchable. unfold All_matchable in H2. 
 unfold perm in H. move /andP in H. destruct H. eapply included_elim5 in H7.
 eauto. } split.  { eauto. } { eauto. } } split. { eapply bids_of_perm in H. unfold perm in H. move /andP in H. destruct H.  eapply included_elim5 in H7.
 unfold perm in H0. move /andP in H0. destruct H0.  eapply included_elim5 in H0. eauto. }
 {  eapply asks_of_perm in H. unfold perm in H. move /andP in H.  destruct H.   eapply included_elim5 in H7.
 unfold perm in H1. move /andP in H1. destruct H1.  eapply included_elim5 in H1. eauto.  } } Qed.
 
  
(******************Fainess Invariance******************)



Lemma fair_on_bid_inv (M M': list fill_type) (B B': list Bid) :
perm M  M' -> perm B B' -> fair_on_bids M B -> fair_on_bids M' B'.
Proof. Admitted.


Lemma fair_on_ask_inv (M M': list fill_type) (A A' : list Ask):
perm M M' -> perm A A' -> fair_on_asks M A -> fair_on_asks M' A'.
Proof. Admitted.

Lemma fair_inv (M M': list fill_type) (B B': list Bid) (A A' : list Ask):
 perm M M' -> perm B B' -> perm A A' -> Is_fair M B A -> Is_fair M' B' A'.
Proof. Admitted.


(*********************IR Invariance********************)



(*******************Uniform Invariance*****************)


(*******************Maximum Invariance*****************)



End InvariancePerm.

Hint Resolve bids_of_perm asks_of_perm: auction.    
Hint Resolve  match_inv fair_inv fair_on_bid_inv fair_on_ask_inv : auction.

