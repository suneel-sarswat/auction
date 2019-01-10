

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
perm M  M' -> perm B B' -> perm A A' ->
matching_in B A M -> matching_in B' A' M'.
Proof.  Admitted.
  


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

    
Hint Resolve  match_inv fair_inv fair_on_bid_inv fair_on_ask_inv : auction.

