Require Import ssreflect ssrbool. 
Require Export Lists.List.

Require Export GenReflect SetSpecs.

Require Export Sorting MinMax.
Require Export BidAsk.
Require Export DecList.
Require Export Matching.
Require Export AuctionInvar.

Section Fair.
 
Lemma same_ask_is_fair (M M': list fill_type)(A: list Ask):
  fair_on_asks M A -> (asks_of M [=] asks_of M')-> fair_on_asks M' A.
Proof.  { intros H1 H2. unfold fair_on_asks. unfold fair_on_asks in H1.
          intros s s' H3 H4 H5. destruct H2 as [H2a H2].
          apply H2a; eapply H1 with (s':=s');auto. } Qed.
       
 

Lemma same_bid_is_fair (M M': list fill_type)(B: list Bid):
  fair_on_bids M B -> (bids_of M [=] bids_of M')-> fair_on_bids M' B.
Proof. { intros H1 H2. unfold fair_on_bids. unfold fair_on_bids in H1.
         intros s s' H3 H4 H5. destruct H2 as [H2a H2].
         apply H2a; eapply H1 with (b':=s');auto.  }  Qed.

Hint Resolve same_ask_is_fair same_bid_is_fair.

(*------------ Sorting by decreasing bid prices and their properties --------------*)

Definition by_bp (b1:Bid) (b2:Bid) := (b2 <=? b1).

Lemma by_bp_P : transitive by_bp /\ comparable by_bp.
Proof.  { split.
          { unfold transitive. unfold by_bp.  
            intros y x z H H1. move /leP in H1. move /leP in H.
            apply /leP. omega. }
          { unfold comparable.  unfold by_bp. intros.
           move /leP in H. apply /leP. omega. } } Qed.
            
 
Definition m_bp (m1:fill_type) (m2:fill_type) := by_bp (bid_of m1) (bid_of m2).

Lemma m_bp_P : transitive m_bp /\ comparable m_bp.
Proof. { split.
         { unfold transitive. unfold m_bp. 
           intros. cut (transitive by_bp). intros. eauto using by_bp_P. 
            apply by_bp_P. }
         { unfold comparable.  unfold m_bp. intros x y H. eapply by_bp_P. 
           exact.  } } Qed.

(*------------- Sorting by increasing ask prices and their properties -------------*)

Definition by_sp (a1:Ask) (a2:Ask) := a1 <=? a2.

Lemma by_sp_P : transitive by_sp /\ comparable by_sp.
Proof. { split.
         { unfold transitive. unfold by_sp.  
            intros y x z H H1. move /leP in H1. move /leP in H.
            apply /leP. omega. }
          { unfold comparable.  unfold by_sp. intros.
           move /leP in H. apply /leP. omega. } } Qed.

Definition m_sp (m1:fill_type) (m2:fill_type) :=  by_sp (ask_of m1) (ask_of m2).

Lemma m_sp_P : transitive m_sp /\ comparable m_sp.
Proof. { split.
         { unfold transitive. unfold m_sp. 
           intros. cut (transitive by_sp). intros. eauto using by_sp_P. 
            apply by_sp_P. }
         { unfold comparable.  unfold m_sp. intros x y H. eapply by_sp_P. 
           exact.  } } Qed. 

Hint Resolve m_bp_P m_sp_P by_bp_P by_sp_P.

Definition geb := fun a b => Nat.leb b a.

Lemma sorted_B_imply_sorted_p (B: list Bid): Sorted by_bp B -> Sorted geb (bid_prices B).
  Proof. Admitted.

Lemma top_prices_mb (m: fill_type)(b: Bid) (M: list fill_type)(B: list Bid):
  Sorted m_bp (m::M)-> Sorted by_bp (b::B) ->
  bid_prices (bids_of (m::M)) [<=] bid_prices (b::B) -> (bid_of m) <= b.
Proof. { intros H1 H2 H3. simpl in H3.
       assert (H4: Sorted geb (bid_prices (b::B))).
       { apply sorted_B_imply_sorted_p;auto. } 
       cut (In (bp (bid_of m)) ((bp b)::bid_prices B)).
       Print Sorted. inversion H4. intro H7. destruct H7. omega.
       apply H6 in H7 as H8. unfold geb in H8. apply /leP. exact. auto. } Qed.
       
Lemma sorted_nodup_is_sublist (B1 B2: list Bid): Sorted by_bp B1 -> Sorted by_bp B2 ->
                                                 NoDup B1 -> NoDup B2 -> B1 [<=] B2 ->
                                                 sublist (bid_prices B1) (bid_prices B2).
Proof. Admitted.

Lemma sorted_m_imply_sorted_b (M: list fill_type): Sorted m_bp M -> Sorted by_bp (bids_of M).
Proof. { induction M.
       { simpl. intro H. constructor. }
       { simpl. intro H. inversion H. constructor. auto.
         intros b H4. unfold by_bp.
         assert (H5: exists m, In m M /\ b = bid_of m). eauto.
         destruct H5 as [m H5]. destruct H5 as [H5 H6].
         apply H3 in H5 as H7. unfold m_bp in H7. unfold by_bp in H7.
         subst b. exact. } } Qed.

Hint Resolve sorted_m_imply_sorted_b.

(* Lemma tail_is_matching (m: fill_type)(b: Bid) (M: list fill_type)(B: list Bid)(A: list Ask):
  Sorted m_bp (m::M)-> Sorted by_bp (b::B) -> matching_in (b::B) A (m::M)-> matching_in B A M.
Proof. Admitted. *)

  
(*----------------  Function to make a matching fair on bids -----------------*)

Fixpoint Make_FOB (M:list fill_type) (B: list Bid):=
match (M,B) with 
|(nil,_) => nil
|(m::M',nil) => nil
|(m::M',b::B') => (Mk_fill b (ask_of m) (tp m))::(Make_FOB M' B')
end.


Lemma mfob_subB (M:list fill_type) (B:list Bid): bids_of (Make_FOB M B) [<=] B.
Proof. { revert B. induction M. simpl. auto. intro B.
         case B.
         { simpl. auto. }
         { intros b l. simpl. intro x. intro H1.
           destruct H1. subst x. auto. cut (In x l). auto. eapply IHM. auto. } } Qed.

Lemma mfob_ask_sub_M (M: list fill_type)(B: list Bid): asks_of (Make_FOB M B) [<=] asks_of M.
Proof. { revert B. induction M.
       { simpl. auto. }
       { intro B. case B.
         { simpl. auto. }
         { intros b l. simpl.  auto. } } } Qed.
  
Lemma mfob_subA (M:list fill_type)(B:list Bid)(A:list Ask):
  (asks_of M [<=] A)->(asks_of(Make_FOB M B)) [<=] A.
Proof. eauto using mfob_ask_sub_M. Qed.

Lemma mfob_nodup_asks (M: list fill_type)(B: list Bid): NoDup (asks_of M)->
                                                        NoDup (asks_of (Make_FOB M B)).
Proof. { revert B. induction M.
       { simpl. auto. }
       { intro B. case B.
         { simpl. auto. }
         { intros b l. simpl. intro H. cut (NoDup (asks_of (Make_FOB M l))).
           cut(~ In (ask_of a) (asks_of (Make_FOB M l))). eauto.
           Focus 2. eauto.
           intro H1. absurd (In (ask_of a) (asks_of M)). auto.
           eapply mfob_ask_sub_M. eauto. } } } Qed.

Lemma mfob_nodup_bids (M: list fill_type)(B:list Bid): NoDup B -> NoDup (bids_of (Make_FOB M B)).
Proof. { revert B. induction M. simpl. auto.
         intro B. case B.
         { simpl. auto. }
         { intros b l. simpl. intro h1.
           cut (~In b (bids_of (Make_FOB M l))). cut (NoDup (bids_of (Make_FOB M l))).
           auto. eauto. intro h2. absurd (In b l). eauto. eapply mfob_subB. apply h2. } } Qed.

Lemma mfob_matchable (M:list fill_type)(B:list Bid)(NDB: NoDup B):
  (Sorted m_bp M) -> (Sorted by_bp B) -> All_matchable M ->
   sublist (bid_prices (bids_of M)) (bid_prices B) ->
   NoDup (bids_of M) -> All_matchable (Make_FOB M B).
Proof. { revert B NDB. induction M. 
         { intros B H1 H2 H3 H4 H5 H6. simpl. eauto. }
         { intros B H1 H2 H3 H4 H5 H6. 
           destruct B. 
           { simpl. apply All_matchable_nil.  }
           { simpl. apply All_matchable_intro. 
             { simpl.
               assert (H7: b >= (bid_of a)). 
               { eapply top_prices_mb.   eauto. apply H3. auto. } 
               assert (H8: bid_of a >= ask_of a). 
               { unfold All_matchable in H4. simpl in H4. eapply H4. left;auto. }
               omega. } 
             { eapply IHM. 
               { eauto. } 
               { eauto. }
               { eauto. } 
               { eapply All_matchable_elim1. apply H4. }
               { simpl in H5. destruct (bid_of a =? b).
                 auto.  eauto. } 
               { simpl in H6. eauto.  } } } } } Qed.          

(*

Lemma mfob_matchable (M:list fill_type) (B:list Bid) (A:list Ask) (NDB: NoDup B):
(Sorted m_by_bp M) -> (Sorted b_by_bp B) -> (matching_in B A M) -> All_matchable (Make_FOB M B).

Proof. 

*)

Lemma mfob_matching (M:list fill_type) (B:list Bid) (A:list Ask) (NDB: NoDup B):
(Sorted m_bp M) -> (Sorted by_bp B) -> (matching_in B A M) -> matching (Make_FOB M B).
Proof. { intros h1 h2 h3. unfold matching.
       split.
       { (*-------- All_matchable (Make_FOB M B)---------*)
         apply mfob_matchable. all: auto. apply h3.
         eapply sorted_nodup_is_sublist. all: auto. all: apply h3. }
       split.
       { (*-------NoDup (bids_of (Make_FOB M B))---------*)
        auto using mfob_nodup_bids. }
       { (*------ NoDup (asks_of (Make_FOB M B))---------*)
        eapply mfob_nodup_asks. apply h3. } } Qed.
 



Lemma mfob_matching_in (M: list fill_type)(B: list Bid)(A: list Ask)(NDB: NoDup B):
(Sorted m_bp M) -> (Sorted by_bp B) -> matching_in B A M -> matching_in B A (Make_FOB M B).
Proof.  { intros H1 H2 H3. unfold matching_in. 
          split. { eapply mfob_matching. all: auto. eapply H3.  }
                 split. { eapply mfob_subB. }
                        { eapply mfob_subA. apply H3.  } } Qed.



Lemma mfob_asks_is_perm (M: list fill_type) (B:list Bid):
perm (asks_of M) (asks_of (Make_FOB M B)). 
Proof. Admitted. 

Lemma mfob_is_same_size (M: list fill_type) (B:list Bid):
|M| = |(Make_FOB M B)|. 
Proof. Admitted.

Lemma mfob_fair_on_bid (M: list fill_type) (B:list Bid) (A:list Ask):
 (Sorted m_bp M) -> (Sorted by_bp B) -> matching_in B A M -> fair_on_bids (Make_FOB M B) B. 
Proof. Admitted.  

Hint Resolve mfob_matching mfob_asks_is_perm mfob_is_same_size mfob_fair_on_bid.

Theorem exists_fair_on_bids (M: list fill_type) (B: list Bid)(A:list Ask)(NDB: NoDup B):
  matching_in B A M->
  (exists M':list fill_type, matching_in B A M'  /\ (|M| = |M'|) /\ perm (asks_of M) (asks_of M')
   /\ fair_on_bids M' B).
Proof. { assert (HmP: transitive m_bp /\ comparable m_bp). apply m_bp_P.  
        assert (HbP: transitive by_bp /\ comparable by_bp). apply by_bp_P.
        destruct HmP as [Hmp1 Hmp2]. destruct HbP as [Hbp1 Hbp2].
        intro H. exists (Make_FOB (sort m_bp M) (sort by_bp B)).
        split. 
        { assert (HM: matching_in (sort by_bp B) A (Make_FOB (sort m_bp M) (sort by_bp B))).
          apply mfob_matching_in. all:auto. 
          apply match_inv with (M:=M)(B:=B)(A:=A);auto.
          eapply match_inv with
              (B:= (sort by_bp B)) (M:=(Make_FOB (sort m_bp M) (sort by_bp B))) (A:=A).
          all: auto. } split.
        { replace (|M|) with (|sort m_bp M|); auto. } split.
        {  assert(HA: perm (asks_of (sort m_bp M))
                          (asks_of (Make_FOB (sort m_bp M) (sort by_bp B)))).
          auto. eauto with auction.  }
        {  assert (HBid: fair_on_bids
                           (Make_FOB (sort m_bp M) (sort by_bp B)) (sort by_bp B)).
           eapply mfob_fair_on_bid. all:auto. eapply match_inv with (M:=M)(B:=B)(A:=A);auto.
           eauto with auction. } } Qed.

(* -------------- function to make a matching fair on asks --------------------- *)
Fixpoint Make_FOA (M:list fill_type) (A: list Ask):=
match (M,A) with 
|(nil,_) => nil
|(m::M',nil) => nil
|(m::M',a::A') => (Mk_fill (bid_of m) a (tp m))::(Make_FOA M' A')
end.

Theorem exists_fair_on_asks (M: list fill_type) (B: list Bid) (A:list Ask):
  matching_in B A M->
  (exists M':list fill_type, matching_in B A M' /\  (|M| = |M'|) /\ perm (bids_of M) (bids_of M')
   /\ fair_on_asks M' A).
Proof. Admitted.

Theorem exists_fair_matching (M: list fill_type) (B: list Bid) (A:list Ask) (NDB: NoDup B):
  matching_in B A M-> (exists M':list fill_type, matching_in B A M' /\ Is_fair M' B A /\ |M|= |M'|).
Proof. { intros H0. apply exists_fair_on_bids in H0 as H1.
       destruct H1 as [M' H1].
       destruct H1 as [H1a H1]. destruct H1 as [H1b H1]. destruct H1 as [H1c H1d].
       apply exists_fair_on_asks in H1a as H2.
       destruct H2 as [M'' H2].
       destruct H2 as [H2a H2]. destruct H2 as [H2b H2]. destruct H2 as [H2c H2d].
       exists M''. split.
       { auto. }
       split.
       { split. auto. eauto. }
       {eauto. } auto. } Qed.
         
End Fair.