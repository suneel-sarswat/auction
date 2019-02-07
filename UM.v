Require Import ssreflect ssrbool. 
Require Export Lists.List.

Require Export GenReflect SetSpecs.

Require Export Sorting MinMax.
Require Export BidAsk.
Require Export DecList.
Require Export Matching.
Require Export AuctionInvar.

Require Export Fair.

Section UM.



Fixpoint produce_UM (B:list Bid) (A:list Ask)  :=
  match (B,A) with
  |(nil, _) => nil
  |(_,nil)=> nil
  |(b::B',a::A') => match Nat.leb (sp a) (bp b) with
                        |false =>nil
                        |true  => ({|bid_of:= b ; ask_of:= a ; tp:=(bp b) |})::produce_UM B' A'
  end
  end.
  

Lemma UM_correct (B:list Bid) (A:list Ask) : forall m, In m (produce_UM B A) ->
                                (bp (bid_of m)) >= (sp (ask_of m)).
Proof.  intros m. revert A. induction B. simpl. auto. intro A.
        induction A. simpl. auto. simpl. intro H1. 
        destruct (a0 <=? a) eqn: H2. destruct H1.
        subst m. unfold bid_of. unfold ask_of. move /eqP in H2.  
        move /eqP in H2.  move /leP in H2. auto. 
        move /leP in H2. eauto.  inversion H1. Qed.
   

(*
Lemma bids_of_UM_sorted (B: list Bid) (A: list Ask) :
  ((IsOrd (rev B)) /\ (IsOrd A)) -> (IsOrd (rev (bids_of (UM_matching B A)))).
Proof.  induction B. intro H.  simpl. constructor. induction A.
 intros H1. simpl. constructor. intros H2. destruct H2 as [H2 H3]. simpl. destruct (sp a1 <=? bp a). simpl. Admitted.


Lemma asks_of_UM_sorted (B: list Bid) (A: list Ask) :
  ((IsOrd (rev B)) /\ (IsOrd A)) -> (IsOrd (asks_of (UM_matching B A))).
Proof. Admitted.


Definition uniform_price (B: list Bid) (A: list Ask):=
  (bp (bid_of (last (UM_matching B A) ((b0,a0),0)))).
  



(*------------------------------------------------------------------ *)
(* move the general version of the following lemmas to the OrdList file
 ------------------ *)
 
Lemma last_in_tail (A:Type): forall l:list A, forall a b d:A, 
(last (a::b::l) d) = (last (b::l) d).
Admitted.
 
Lemma last_is_smallest (l: list Bid): IsOrd (rev l)-> forall m, In m l -> ((last l b0) <=b m).
Proof. intros H m H1.   induction l. 

 auto.  destruct H1. subst m. 
  eauto with hint_auction. Admitted.
 
Lemma last_is_largest (l: list Ask): IsOrd l-> forall m, In m l -> (m <=b (last l a0)).
Proof. Admitted.

Lemma last_in_list (T:Type)(l:list T)(p:T)(d:T) : In (last (p :: l) d)  (p :: l).
Proof.  revert p. induction l. eauto with hint_list.
intros. Admitted.  

(*--------------------------------------------------------*)


Lemma bid_of_last_and_last_of_bids (F: list fill_type):
  (bid_of (last F ((b0,a0),0))) = (last (bids_of F) b0).

Proof. induction F.  simpl. unfold bid_of. simpl. exact. {
case F eqn:H1. simpl. auto. replace (last (a :: f :: l) (b0, a0, 0)) with (last (f :: l) (b0, a0, 0)). unfold bids_of;fold bids_of. replace
 (last (bid_of a :: bid_of f :: bids_of l) b0) with
 (last (bid_of f :: bids_of l) b0). exact. symmetry.
 eapply last_in_tail. symmetry. eapply last_in_tail. } Qed.

Lemma ask_of_last_and_last_of_asks (F: list fill_type):
  (ask_of (last F ((b0,a0),0))) = (last (asks_of F) a0).
Proof.
induction F.  simpl. unfold ask_of. simpl. exact. {
case F eqn:H1. simpl. auto. replace (last (a :: f :: l) (b0, a0, 0)) with (last (f :: l) (b0, a0, 0)). unfold asks_of;fold asks_of. replace
 (last (ask_of a :: ask_of f :: asks_of l) a0) with
 (last (ask_of f :: asks_of l) a0). exact. symmetry.
 eapply last_in_tail. symmetry. eapply last_in_tail. } Qed.

*)
Lemma UP_is_matching (B: list Bid) (A: list Ask) (NDB: NoDup B) (NDA: NoDup A):
 Sorted by_dbp B -> Sorted by_sp A -> matching_in B A (produce_UM B A).
 Proof. revert NDA. revert A. induction B. simpl. eauto. intros. simpl.
 case A eqn: H1. eauto. destruct (a0 <=? a) eqn: H2. simpl. unfold matching_in. split. unfold matching. split. unfold All_matchable. simpl. intros. eauto. destruct H3. move /leP in H2. subst m. simpl. exact. eapply IHB in H3. exact. eauto. eauto. eauto. eauto. split. simpl. eauto. Admitted.

Lemma UM_returns_IR (B: list Bid) (A: list Ask) (NDB: NoDup B) (NDA: NoDup A):
 Sorted by_dbp B -> Sorted by_sp A -> forall m, In m (produce_UM B A) ->
   (bp (bid_of m))>= (tp m)  /\ (sp (ask_of m)) <= (tp m).
  
Proof.   { revert NDA. revert A. induction B. intros. split. simpl in H1.
destruct H1. simpl in H1. destruct H1. intros.  case A eqn: Ha. simpl in H1. destruct H1. simpl in H1.  case (a0 <=? a) eqn: Ha0. simpl in H1.
destruct H1. subst m. move /leP in Ha0. simpl. eauto. eapply IHB in H1.
 exact. eauto. eauto. eauto. eauto. destruct H1. } Qed.
 


Definition UM (B:list Bid) (A:list Ask) : (list fill_type) :=
  replace_column (UM_matching B A)
                (uniform_price B A).



Theorem UM_is_fair(B: list Bid) (A:list Ask): Is_fair ( UM B A) B A.
Proof. Admitted.

Theorem UM_is_Ind_Rat (B: list Bid) (A:list Ask):
  (IsOrd (rev B)) -> (IsOrd A) -> Is_ind_rational (UM B A).
Proof. { intros HB HA. unfold Is_ind_rational. intros m H. unfold rational. unfold UM in H.
       replace (trade_price_of m) with (uniform_price B A).
       assert (H0: exists m', In m' (UM_matching B A) /\ bid_of m' = bid_of m /\ ask_of m' = ask_of m).
       apply replace_column_elim with (n:= uniform_price B A). auto.
       destruct H0 as [m' H0]. destruct H0 as [H1 H0]. destruct H0 as [H2 H0].
       rewrite <- H2. rewrite <- H0. split; apply UP_returns_IR; auto.
       symmetry; eapply last_column_is_trade_price;eauto.  } Qed.

Theorem UM_is_Uniform (B: list Bid) (A:list Ask) : Is_uniform ( UM B A).
Proof.  unfold Is_uniform. unfold UM. apply replace_column_is_uniform. Qed.

Theorem UM_is_maximal_Uniform (B: list Bid) (A:list Ask): forall M: list fill_type, Is_uniform M -> |M| <= | (UM B A ) |.
Proof. Admitted.

End UM.
