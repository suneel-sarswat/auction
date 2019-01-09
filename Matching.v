Require Import ssreflect ssrbool.
Require Export Lists.List.
Require Export GenReflect SetSpecs OrdType.

Require Export BidAsk.
Require Export DecList.
Require Export Sorting.

Section Matching.

  
(*----------------- Notion of matching and  Maximal Matching (MM) ------------------------*)

Definition matchable (b: Bid)(a: Ask):=  (sp (a)) <= (bp (b)).

Definition All_matchable(M: list fill_type):= forall m, In m M -> matchable (bid_of m) (ask_of m).

Hint Unfold All_matchable.

Definition Is_a_matching (M: list fill_type) (B: list Bid) (A: list Ask):=
  (All_matchable M) /\ (NoDup (bids_of M)) /\ (NoDup (asks_of M)) /\
  (bids_of M [<=] B) /\ (asks_of M [<=] A).

Definition Is_MM (M : list fill_type) (B: list Bid) (A: list Ask):=
  Is_a_matching M B A /\ 
  (forall M': list fill_type, Is_a_matching M' B A -> |M'| <= |M|).


Lemma All_matchable_elim (m: fill_type)(M: list fill_type):
  All_matchable (m::M) -> matchable (bid_of m) (ask_of m).
Proof.  intros H.  unfold All_matchable in H. simpl in H. specialize H with m. auto. Qed.   
 

Lemma All_matchable_elim1 (m: fill_type)(M: list fill_type):
  All_matchable (m::M) -> All_matchable M.
Proof.  unfold All_matchable. intros.  simpl in H. auto. Qed.

Definition empty_fill: list fill_type:= nil.

Lemma All_matchable_nil: All_matchable nil.
Proof. Admitted.


Lemma All_matchable_intro (m: fill_type)(M: list fill_type):
  matchable (bid_of m) (ask_of m) -> All_matchable M -> All_matchable (m::M).
Proof. intros H1 H2. unfold All_matchable. simpl. intros m0 H3. destruct H3. subst m0. exact. eauto. Qed. 


Hint Immediate All_matchable_intro All_matchable_nil: auction.
Hint Resolve All_matchable_elim All_matchable_elim1 : auction.

Lemma Is_a_matching_nil (B: list Bid)(A: list Ask) : Is_a_matching nil B A.
Proof. Admitted.

Hint Resolve Is_a_matching_nil: auction.



Lemma Is_a_matching_intro (m: fill_type) (M: list fill_type)(B: list Bid)(A: list Ask):
  matchable (bid_of m)(ask_of m) -> Is_a_matching M B A -> ~ In (bid_of m) (bids_of M) ->
  ~ In (ask_of m) (asks_of M) -> In (bid_of m) B -> In (ask_of m) A -> Is_a_matching (m::M) B A.
Proof.  intros H1 H2 H3 H4 H5 H6. unfold Is_a_matching. split. unfold Is_a_matching in H2. destruct H2. eauto with auction. split. unfold Is_a_matching in H2. destruct H2 as [H7 H2]. destruct H2 as [H8 H2]. destruct H2 as [H9 H2]. destruct H2 as [H10 H2]. simpl. eauto. split. destruct H2 as [H7 H2]. destruct H2 as [H8 H2]. destruct H2 as [H9 H2]. destruct H2 as [H10 H2]. simpl. eauto. split. destruct H2 as [H7 H2]. destruct H2 as [H8 H2]. destruct H2 as [H9 H2]. destruct H2 as [H10 H2]. simpl. unfold "[<=]". simpl. intros a H. destruct H.  subst a. exact. eauto. destruct H2 as [H7 H2]. destruct H2 as [H8 H2]. destruct H2 as [H9 H2]. destruct H2 as [H10 H2]. simpl. unfold "[<=]". simpl. intros a H. destruct H.  subst a. exact. eauto. Qed.



Lemma Is_a_matching_elim (m: fill_type) (M: list fill_type)(B: list Bid)(A: list Ask):
  Is_a_matching (m::M) B A -> Is_a_matching M B A.
Proof. unfold Is_a_matching. simpl. intros H. destruct H as [H1 H]. destruct H as [H2 H]. destruct H as [H3 H]. destruct H as [H4 H]. split. eauto with auction. split. eauto. split. eauto. split. unfold "[<=]".  eauto. unfold "[<=]". eauto. Qed.


Lemma Is_a_matching_elim1 (m: fill_type) (M: list fill_type) (B: list Bid)(A: list Ask):
  Is_a_matching (m::M) B A ->  matchable (bid_of m )(ask_of m).
Proof. unfold Is_a_matching. intros H. destruct H as [H1 H].  eauto with auction. Qed.
 

Lemma Is_a_matching_elim2 (m: fill_type) (M: list fill_type) (B: list Bid)(A: list Ask):
  Is_a_matching (m::M) B A ->   ~ In (bid_of m) (bids_of M).
Proof. unfold Is_a_matching. intros H. destruct H as [H1 H]. destruct H as [H2 H]. destruct H as [H3 H]. destruct H as [H4 H]. simpl in H2. eauto. Qed.


Lemma Is_a_matching_elim3 (m: fill_type) (M: list fill_type) (B: list Bid)(A: list Ask):
  Is_a_matching (m::M) B A ->   ~ In (ask_of m) (asks_of M).
Proof. unfold Is_a_matching. intros H. destruct H as [H1 H]. destruct H as [H2 H]. destruct H as [H3 H]. destruct H as [H4 H]. simpl in H3. eauto. Qed.

Lemma Is_a_matching_elim4 (m: fill_type) (M: list fill_type) (B: list Bid)(A: list Ask):
  Is_a_matching (m::M) B A ->   In (bid_of m) B.
Proof. unfold Is_a_matching. intros H. destruct H as [H1 H]. destruct H as [H2 H]. destruct H as [H3 H]. destruct H as [H4 H]. simpl in H4. eauto. Qed.

Lemma Is_a_matching_elim5 (m: fill_type) (M: list fill_type) (B: list Bid)(A: list Ask):
  Is_a_matching (m::M) B A ->   In (ask_of m) A.
Proof. unfold Is_a_matching. intros H. destruct H as [H1 H]. destruct H as [H2 H]. destruct H as [H3 H]. destruct H as [H4 H]. simpl in H. eauto. Qed.

Variable m_by_bp m_by_sp : fill_type->fill_type-> bool.
Variable b_by_bp : Bid -> Bid->bool.
Variable a_by_sp : Ask -> Ask->bool.




Lemma sorted_mbp_is_matching (M:list fill_type)(B:list Bid)(A:list Ask):
Is_a_matching M B A -> Is_a_matching (sort m_by_bp M) B A.
Proof. Admitted.

Lemma sorted_msp_is_matching (M:list fill_type)(B:list Bid)(A:list Ask):
Is_a_matching M B A -> Is_a_matching (sort m_by_sp M) B A.
Proof. Admitted.

Lemma sorted_bid_is_matching (M:list fill_type)(B:list Bid)(A:list Ask):
Is_a_matching M B A -> Is_a_matching M (sort b_by_bp B) A.
Proof. Admitted.

Lemma sorted_ask_is_matching (M:list fill_type)(B:list Bid)(A:list Ask):
Is_a_matching M B A -> Is_a_matching M B (sort a_by_sp A).
Proof. Admitted.

Hint Immediate Is_a_matching_intro: auction.
Hint Resolve Is_a_matching_elim Is_a_matching_elim1 Is_a_matching_elim2
     Is_a_matching_elim3 Is_a_matching_elim4 Is_a_matching_elim5: auction.
Hint Resolve sorted_mbp_is_matching sorted_msp_is_matching sorted_bid_is_matching sorted_ask_is_matching : auction.

(*----------------- Individual rational and  Fair matching--------------------------*)

Definition rational (m: fill_type):=
  (bp (bid_of m)  >= tp m) /\ (tp m >= sp (ask_of m)).
Definition Is_IR (M: list fill_type):= forall m, In m M -> rational m.

Lemma Is_IR_elim (m: fill_type)(M: list fill_type): Is_IR (m::M) -> rational m.
Proof. unfold Is_IR. intros H.  specialize H with m. simpl in H. destruct H. left. exact. unfold rational. eauto. Qed.

Lemma Is_IR_elim1 (m: fill_type)(M: list fill_type): Is_IR (m::M)-> Is_IR M.
Proof. unfold Is_IR. simpl. intros. eauto. Qed.

Lemma Is_IR_intro (m: fill_type)(M: list fill_type): rational m -> Is_IR M -> Is_IR (m::M).
Proof.  unfold Is_IR. intros. case (m==m0) eqn: H3. move /eqP in H3. subst m0. exact. destruct H1. subst m0. exact. specialize H0 with m0. apply H0 in H1. exact. Qed.  

Hint Immediate Is_IR_intro: auction.
Hint Resolve Is_IR_elim Is_IR_elim1: auction.

Definition fair_on_bids (M: list fill_type)(B: list Bid)(A: list Ask):=
  (forall b b', In b B /\ In b' B -> (bp b) > (bp b') -> In b' (bids_of M) -> In b (bids_of M)).


Definition fair_on_asks (M: list fill_type)(B: list Bid)(A: list Ask):=
  (forall s s', In s A /\ In s' A -> (sp s) < (sp s') -> In s' (asks_of M) -> In s (asks_of M)).



  
Definition Is_fair (M: list fill_type) (B: list Bid) (A: list Ask) 
  :=  fair_on_asks M B A /\ fair_on_bids M B A.




Lemma sorted_mbp_is_fair (M:list fill_type)(B:list Bid)(A:list Ask):
Is_fair M B A -> Is_fair (sort m_by_bp M) B A.
Proof. Admitted.


Lemma sorted_msp_is_fair (M:list fill_type)(B:list Bid)(A:list Ask):
Is_fair M B A -> Is_fair (sort m_by_sp M) B A.
Proof. Admitted.


Lemma sorted_bid_is_fair (M:list fill_type)(B:list Bid)(A:list Ask):
Is_fair M B A -> Is_fair M (sort b_by_bp B) A.
Proof. Admitted.


Lemma sorted_ask_is_fair (M:list fill_type)(B:list Bid)(A:list Ask):
Is_fair M B A -> Is_fair M B (sort a_by_sp A).
Proof. Admitted.


(*------------------Uniform matching------------------------------*)


Definition Is_uniform (M : list fill_type) := uniform (trade_prices_of M).


(*-------------- buyers_above and sellers_above relationship and results------------------*)

Definition buyers_above (p: nat)(B: list Bid): list Bid :=
  filter (fun x:Bid => Nat.leb p (bp x))  B.

Lemma buyers_above_elim (p:nat)(B: list Bid)(x:Bid):
  In x (buyers_above p B)-> bp(x) >= p.
Proof.   Admitted.
        

  
Lemma buyers_above_intro (p:nat)(B: list Bid)(x:Bid):
 ( In x B /\ bp(x) >= p ) -> In x (buyers_above p B).
Proof. Admitted.

Definition sellers_above (p: nat)(A: list Ask): list Ask :=
  filter (fun x:Ask => Nat.leb p (sp x)) (A).

Lemma sellers_above_elim (p:nat)(A: list Ask)(x:Ask):
  In x (sellers_above p A)-> sp(x) >= p.
Proof. Admitted.
Lemma sellers_above_intro (p:nat)(A: list Ask)(x:Ask):
 ( In x A /\ sp(x) >= p ) -> In x (sellers_above p A).
Proof. Admitted.

Definition buyers_below (p: nat)(B: list Bid): list Bid :=
  filter (fun x:Bid => Nat.leb (bp x) p) (B).

Lemma buyers_below_intro (p:nat)(B: list Bid)(x:Bid):
 ( In x B /\ bp(x) <= p ) -> In x (buyers_below p B).
Proof. Admitted.
Lemma buyers_below_elim (p:nat)(B: list Bid)(x:Bid):
  In x (buyers_below p B)-> bp(x) <= p.
Proof. Admitted.

Definition sellers_below (p: nat)(A: list Ask): list Ask :=
  filter (fun x:Ask => Nat.leb (sp x) p) (A).

Lemma sellers_below_intro (p:nat)(A: list Ask)(x:Ask):
 ( In x A /\ sp(x) <= p ) -> In x (sellers_below p A).
Proof. Admitted.
Lemma sellers_below_elim (p:nat)(A: list Ask)(x:Ask):
  In x (sellers_below p A)-> sp(x) <= p.
Proof. Admitted.

Hint Resolve buyers_above_elim buyers_above_intro: auction.
Hint Resolve sellers_above_elim sellers_above_intro: auction.

Hint Resolve buyers_below_elim buyers_below_intro: auction.
Hint Resolve sellers_below_elim sellers_below_intro: auction.


Theorem buyers_above_ge_sellers (p:nat)(M: list fill_type) (B: list Bid) (A: list Ask):
  Is_a_matching M B A -> | buyers_above p (bids_of M)| >= | sellers_above p (asks_of M)|.
Proof. Admitted.

Theorem sellers_below_ge_buyers (p:nat)(M: list fill_type) (B: list Bid) (A: list Ask):
  Is_a_matching M B A -> | buyers_below p (bids_of M)| <= | sellers_below p (asks_of M)|.
Proof. Admitted.

End Matching.


Hint Unfold All_matchable.
Hint Immediate All_matchable_intro All_matchable_nil: auction.
Hint Resolve All_matchable_elim All_matchable_elim1 : auction.

Hint Resolve Is_a_matching_nil: auction.
Hint Immediate Is_a_matching_intro: auction.
Hint Resolve Is_a_matching_elim Is_a_matching_elim1 Is_a_matching_elim2
     Is_a_matching_elim3 Is_a_matching_elim4 Is_a_matching_elim5: auction.

Hint Immediate Is_IR_intro: auction.
Hint Resolve Is_IR_elim Is_IR_elim1: auction.
Hint Resolve sorted_mbp_is_matching sorted_msp_is_matching  sorted_bid_is_matching sorted_ask_is_matching : auction.
Hint Resolve sorted_mbp_is_fair sorted_msp_is_fair sorted_bid_is_fair sorted_ask_is_fair : auction.
