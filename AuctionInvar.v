

Require Export Lists.List.
Require Export GenReflect SetSpecs.
Require Export DecSort.
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





End InvariancePerm.
Hint Resolve  match_inv : auction.

