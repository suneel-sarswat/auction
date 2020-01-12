
(* ------------   Work to be done : organise the hints properly ------------- *)



(* -------------------------------------------------------------------------------------

      This file contains all the important results about fair matching.
      The main result is existance of a fair matching without compromize of it's size.

       by_sp                 <===>   order by increasing sp
       by_dbp                <===>   order by decreasing bp
       Make_FOA M A          <===>   makes M fair on asks A
       Make_FOB M B          <===>   makes M fair on bids B


Some important results:

Lemma mfob_matching :
(Sorted m_dbp M) -> (Sorted by_dbp B) -> (matching_in B A M) -> matching (Make_FOB M B).

Lemma mfob_fair_on_bid : (Sorted m_dbp M) -> (Sorted by_dbp B) -> 
 sublist (bid_prices (bids_of M)) (bid_prices B) -> fair_on_bids (Make_FOB M B) B. 

Theorem exists_fair_on_bids :
   matching_in B A M-> (exists M':list fill_type, matching_in B A M'  /\ 
   (|M| = |M'|) /\ perm (asks_of M) (asks_of M') /\ fair_on_bids M' B).

Lemma mfoa_fair_on_ask : (Sorted m_sp M) -> (Sorted by_sp A) -> 
sublist (ask_prices (asks_of M)) (ask_prices A) -> fair_on_asks (Make_FOA M A) A. 

Theorem exists_fair_on_asks :
  matching_in B A M-> (exists M':list fill_type, matching_in B A M' /\  
(|M| = |M'|) /\ perm (bids_of M) (bids_of M') /\ fair_on_asks M' A).


Theorem exists_fair_matching :
  matching_in B A M-> 
  (exists M':list fill_type, matching_in B A M' /\ Is_fair M' B A /\ |M|= |M'|).

------------------------------------------------------------------------------------------*)







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

Definition by_dbp (b1:Bid) (b2:Bid) := (b2 <=? b1).

Lemma by_dbp_P : transitive by_dbp /\ comparable by_dbp.
Proof.  { split.
          { unfold transitive. unfold by_dbp.  
            intros y x z H H1. move /leP in H1. move /leP in H.
            apply /leP. omega. }
          { unfold comparable.  unfold by_dbp. intros.
           move /leP in H. apply /leP. omega. } } Qed.
            
Lemma by_dbp_refl: reflexive by_dbp.
Proof. unfold reflexive. intros. eauto. Qed.



Definition m_dbp (m1:fill_type) (m2:fill_type) := by_dbp (bid_of m1) (bid_of m2).

Lemma m_dbp_P : transitive m_dbp /\ comparable m_dbp.
Proof. { split.
         { unfold transitive. unfold m_dbp. 
           intros. cut (transitive by_dbp). intros. eauto using by_dbp_P. 
            apply by_dbp_P. }
         { unfold comparable.  unfold m_dbp. intros x y H. eapply by_dbp_P. 
           exact.  } } Qed.

Lemma m_dbp_refl: reflexive m_dbp.
Proof. unfold reflexive. intros. unfold m_dbp. eauto. Qed.


(*------------- Sorting by increasing ask prices and their properties -------------*)

Definition by_sp (a1:Ask) (a2:Ask) := a1 <=? a2.

Lemma by_sp_P : transitive by_sp /\ comparable by_sp.
Proof. { split.
         { unfold transitive. unfold by_sp.  
            intros y x z H H1. move /leP in H1. move /leP in H.
            apply /leP. omega. }
          { unfold comparable.  unfold by_sp. intros.
            move /leP in H. apply /leP. omega. } } Qed.

Lemma by_sp_refl: reflexive by_sp.
Proof. unfold reflexive.  intros. eauto. Qed.


Definition m_sp (m1:fill_type) (m2:fill_type) :=  by_sp (ask_of m1) (ask_of m2).

Lemma m_sp_P : transitive m_sp /\ comparable m_sp.
Proof. { split.
         { unfold transitive. unfold m_sp. 
           intros. cut (transitive by_sp). intros. eauto using by_sp_P. 
            apply by_sp_P. }
         { unfold comparable.  unfold m_sp. intros x y H. eapply by_sp_P. 
           exact.  } } Qed.

Lemma m_sp_refl: reflexive m_sp.
Proof. unfold reflexive. intros. eauto. Qed.


Hint Resolve m_dbp_P m_sp_P by_dbp_P by_sp_P.
Hint Resolve by_dbp_refl by_sp_refl m_dbp_refl m_sp_refl.

Definition geb := fun a b => Nat.leb b a.
Lemma geb_anti: antisymmetric geb.
Proof. { unfold geb. unfold antisymmetric.  intros ax ay ah10. 
            move /andP in ah10. destruct ah10 as [ah10 ah11].
            move /leP in ah10. move /leP in ah11. omega. } Qed.

Lemma leb_anti: antisymmetric leb.
Proof. {   unfold antisymmetric.  intros ax ay ah10. 
            move /andP in ah10. destruct ah10 as [ah10 ah11].
            move /leP in ah10. move /leP in ah11. omega. } Qed.
            
Hint Resolve geb_anti leb_anti: core.

Lemma sorted_B_imply_sorted_p (B: list Bid): Sorted by_dbp B -> Sorted geb (bid_prices B).
  Proof. { induction B.
       { simpl. intro H. constructor. }
       { simpl. intro H. inversion H. constructor. auto.
         intros b H4. unfold geb.
         apply IHB in H2. assert (H5: exists b1, In b1 B /\ b = bp b1).
         eauto. destruct H5 as [b1 H5]. destruct H5 as [H5 H6].
         apply H3 in H5 as H7. unfold by_dbp in H7. subst b. exact. } } Qed. 

Lemma top_prices_mb (m: fill_type)(b: Bid) (M: list fill_type)(B: list Bid):
  Sorted m_dbp (m::M)-> Sorted by_dbp (b::B) ->
  bid_prices (bids_of (m::M)) [<=] bid_prices (b::B) -> (bid_of m) <= b.
Proof. { intros H1 H2 H3. simpl in H3.
       assert (H4: Sorted geb (bid_prices (b::B))).
       { apply sorted_B_imply_sorted_p;auto. } 
       cut (In (bp (bid_of m)) ((bp b)::bid_prices B)).
       inversion H4. intro H7. destruct H7. omega.
       apply H6 in H7 as H8. unfold geb in H8. apply /leP. exact. auto. } Qed.

Lemma nodup_sub_is_includedB (B1 B2: list Bid):  NoDup B1 -> NoDup B2 -> B1 [<=] B2 ->
                                                  included B1 B2.
Proof. eauto. Qed.

(*--------------- following lemma important : need a mention in the paper ------------*)

Lemma count_in_deleted_B (b: Bid)(B: list Bid):
  In b B -> count (bp b)(bid_prices B) = S (count (bp b) (bid_prices (delete b B))).
Proof. { induction B.
       { simpl. auto. }
       { intro h1. destruct (b == a) eqn: h2.
         { simpl. rewrite h2. move /eqP in h2.
           subst a. simpl. replace (b =? b) with true. auto. auto. }
         { assert (h1a: In b B).
           { move /eqP in h2; eauto. }
           replace (delete b (a :: B)) with (a :: (delete b B)).
           { simpl. destruct (b =? a) eqn: h3.
             { apply IHB in h1a as h1b. rewrite h1b. auto. }
             { auto. } }
           { simpl. rewrite h2. auto. } } } } Qed.


Lemma included_B_imp_included_BP (B1 B2: list Bid): included B1 B2 ->
                                                    included (bid_prices B1) (bid_prices B2).
Proof. { revert B2. induction B1 as [| b1].
       { simpl. auto. }
       { intros B2 h1.
         assert (h2: In b1 B2). eauto.
         assert (h3: included B1 (delete b1 B2)). eauto.
         assert (h3a: included (bid_prices B1) (bid_prices (delete b1 B2))).
         { auto. }
         assert(h4:count (bp b1)(bid_prices B2)= S (count (bp b1) (bid_prices (delete b1 B2)))).
         { eauto using count_in_deleted_B. }
         eapply included_intro.
         intro x.  simpl. destruct (x =? b1) eqn: C1.
         { (* ---- C1: x = b1 ---- *)
           move /nat_eqP in C1. subst x.
           rewrite h4.
           eapply included_elim in h3a  as h3b. instantiate (1 := b1) in h3b.
           omega. }
         { (*----- C1: x <> b1 ---- *)
           assert (h3b: included B1 B2). eapply included_elim4; apply h1. 
           apply IHB1 in h3b as h3c. auto. } } } Qed.


Lemma sorted_nodup_is_sublistB (B1 B2: list Bid): Sorted by_dbp B1 -> Sorted by_dbp B2 ->
                                                 NoDup B1 -> NoDup B2 -> B1 [<=] B2 ->
                                                 sublist (bid_prices B1) (bid_prices B2). 
Proof. { intros h1 h2 h3 h4 h5.
         assert (h6: Sorted geb (bid_prices B1)).
         { auto using sorted_B_imply_sorted_p. }
         
         assert (h7: Sorted geb (bid_prices B2)).
         { auto using sorted_B_imply_sorted_p. }

         assert (h8: included B1 B2).
         { auto using nodup_sub_is_includedB. }
         
         assert (h9: included (bid_prices B1) (bid_prices B2)).
         { auto using included_B_imp_included_BP. }
          assert (Hanti: antisymmetric geb). 
          { unfold geb. unfold antisymmetric.  intros ax ay ah10. 
            move /andP in ah10. destruct ah10 as [ah10 ah11].
            move /leP in ah10. move /leP in ah11. omega. }
            eauto. }  Qed.

Lemma sorted_m_imply_sorted_b (M: list fill_type): Sorted m_dbp M -> Sorted by_dbp (bids_of M).
Proof. { induction M.
       { simpl. intro H. constructor. }
       { simpl. intro H. inversion H. constructor. auto.
         intros b H4. unfold by_dbp.
         assert (H5: exists m, In m M /\ b = bid_of m). eauto.
         destruct H5 as [m H5]. destruct H5 as [H5 H6].
         apply H3 in H5 as H7. unfold m_dbp in H7. unfold by_dbp in H7.
         subst b. exact. } } Qed.

Hint Resolve sorted_m_imply_sorted_b.


  
(*----------------  Function to make a matching fair on bids -----------------------*)

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
  (Sorted m_dbp M) -> (Sorted by_dbp B) -> All_matchable M ->
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


Lemma mfob_matching (M:list fill_type) (B:list Bid) (A:list Ask) (NDB: NoDup B):
(Sorted m_dbp M) -> (Sorted by_dbp B) -> (matching_in B A M) -> matching (Make_FOB M B).
Proof. { intros h1 h2 h3. unfold matching.
       split.
       { (*-------- All_matchable (Make_FOB M B)---------*)
         apply mfob_matchable. all: auto. apply h3.
         eapply sorted_nodup_is_sublistB. all: auto. all: apply h3. }
       split.
       { (*-------NoDup (bids_of (Make_FOB M B))---------*)
        auto using mfob_nodup_bids. }
       { (*------ NoDup (asks_of (Make_FOB M B))---------*)
        eapply mfob_nodup_asks. apply h3. } } Qed.
 



Lemma mfob_matching_in (M: list fill_type)(B: list Bid)(A: list Ask)(NDB: NoDup B):
(Sorted m_dbp M) -> (Sorted by_dbp B) -> matching_in B A M -> matching_in B A (Make_FOB M B).
Proof.  { intros H1 H2 H3. unfold matching_in. 
          split. { eapply mfob_matching. all: auto. eapply H3.  }
                 split. { eapply mfob_subB. }
                        { eapply mfob_subA. apply H3.  } } Qed.

Lemma mfob_fair_on_bid (M: list fill_type) (B:list Bid) (A:list Ask):
  (Sorted m_dbp M) -> (Sorted by_dbp B) -> sublist (bid_prices (bids_of M)) (bid_prices B) ->
  fair_on_bids (Make_FOB M B) B. 
Proof. { revert B. induction M as [|m]. 
        { intros; simpl; unfold fair_on_bids; intros; inversion H4. }
        { intros. unfold fair_on_bids. intros b b' H2 H3 H4.
          destruct B eqn: Hb. 
         { simpl. inversion H4. }
         { assert (case1: b' = b0 \/ b' <> b0). eauto.
           destruct H2 as [H2 H2a].
           assert  (case3: b0 = b' \/ In b' (bids_of ((Make_FOB M l)))).
           { simpl in H4. auto. }
           destruct case1 as [c1a | c1b]. 
           { (*-- c1a : b0 = b' -------------------------*)
             subst b'. (*H3 is not possible*) 
             assert (H5: b <= b0).
             { apply Sorted_elim2 with (x:= b) in H0 as H0a.
              apply /leP. auto.  unfold by_dbp.
              unfold reflexive. auto.  auto. } omega.  }
           
           { (*-- c1b : b' <> b0 ---*)             assert (H5: In b' l).
             { eauto. }
             assert (case2: b=b0 \/ In b l).
             { auto. }
             destruct case2 as [c2a | c2b]. 
             { subst b. simpl. left. auto. }
             { destruct case3 as [c3a | c3b].
               { subst b0. contradiction. }
               { simpl. right. eapply IHM with (b':= b').
                 { eauto. }
                 { eauto. }
                 { simpl in H1. destruct ( bid_of m =? b0) eqn: H6.  auto. eauto. }
                 { split;auto. }
                 { auto. }
                 { auto. }  } } } } } } Qed.


Lemma mfob_asks_is_perm (M: list fill_type) (B:list Bid) :
 (|M| <= |B|)  -> perm (asks_of M) (asks_of (Make_FOB M B)). 
Proof. { revert B.  induction M. 
         { simpl. auto. }
         { destruct B eqn: HB.
           { simpl. intro h1. inversion h1. } 
           { simpl. intro h1.
             assert (h2: |M| <= |l|). omega.
             apply IHM in h2 as h3.  simpl. auto. } } } Qed.

Lemma mfob_is_same_size (M: list fill_type) (B:list Bid):
 (|M| <= |B|)  -> |M| = |(Make_FOB M B)|. 
Proof.  { revert B.  induction M. 
         { simpl. auto. }
         { destruct B eqn: HB.
           { simpl. intro h1. inversion h1. } 
           { simpl. intro h1.
             assert (h2: |M| <= |l|). omega.
             apply IHM in h2 as h3.  simpl. auto. } } } Qed. 
             
Lemma bids_of_size (M: list fill_type):
|M|=|bids_of M|.
Proof. induction M. simpl. auto. simpl. omega. Qed.
     
Lemma asks_of_size (M:list fill_type):
|M|=|asks_of M|.
Proof. induction M. simpl. auto. simpl. omega. Qed.

Lemma M_is_smaller_than_B (M: list fill_type) (B: list Bid)(A: list Ask):
  matching_in B A M -> (|M| <= |B|).
Proof. { intro H. unfold matching_in in H. destruct H as [H H1]. 
destruct H1 as [H1 H2]. unfold matching in H. destruct H as [H H3].
destruct H3 as [H3 H4]. assert (H5: NoDup (bids_of M) -> bids_of M [<=] B). auto. eapply subset_cardinal_le in H5. assert (H6:|M| = |(bids_of M)|). apply bids_of_size. rewrite H6. exact. exact. exact. } Qed.   

Lemma M_is_smaller_than_A (M: list fill_type) (B: list Bid)(A: list Ask):
  matching_in B A M -> (|M| <= |A|).
Proof. { intro H. unfold matching_in in H. destruct H as [H H1]. 
destruct H1 as [H1 H2]. unfold matching in H. destruct H as [H H3].
destruct H3 as [H3 H4]. assert (H5: NoDup (asks_of M) -> asks_of M [<=] A). auto. eapply subset_cardinal_le in H5. assert (H6:|M| = |(asks_of M)|).
apply asks_of_size. rewrite H6. exact. exact. exact. } Qed.

Hint Resolve mfob_matching mfob_fair_on_bid mfob_asks_is_perm mfob_is_same_size: core.

Theorem exists_fair_on_bids (M: list fill_type) (B: list Bid)(A:list Ask)(NDB: NoDup B):
  matching_in B A M->
  (exists M':list fill_type, matching_in B A M'  /\ (|M| = |M'|) /\ perm (asks_of M) (asks_of M')
   /\ fair_on_bids M' B).
Proof. { assert (HmP: transitive m_dbp /\ comparable m_dbp). apply m_dbp_P.  
        assert (HbP: transitive by_dbp /\ comparable by_dbp). apply by_dbp_P.
        destruct HmP as [Hmp1 Hmp2]. destruct HbP as [Hbp1 Hbp2].
        intro H. exists (Make_FOB (sort m_dbp M) (sort by_dbp B)).
        split. 
        { assert (HM: matching_in (sort by_dbp B) A (Make_FOB (sort m_dbp M) (sort by_dbp B))).
          apply mfob_matching_in. unfold matching_in in H. unfold matching in H. auto. all:auto. 
          apply match_inv with (M:=M)(B:=B)(A:=A);auto.
          eapply match_inv with
              (B:= (sort by_dbp B)) (M:=(Make_FOB (sort m_dbp M) (sort by_dbp B))) (A:=A).
          all: auto. } split.
        { replace (|M|) with (|sort m_dbp M|). eapply mfob_is_same_size.
          apply M_is_smaller_than_B with (A:= A).
          eapply match_inv with (B:= B)(A:= A)(M:= M). all: eauto. } split.
        {  assert(HA: perm (asks_of (sort m_dbp M))
                           (asks_of (Make_FOB (sort m_dbp M) (sort by_dbp B)))).
           eapply  mfob_asks_is_perm. apply M_is_smaller_than_B with (A:=A).
           eapply match_inv with (B:= B)(A:= A)(M:= M). all: eauto.  }
        {  assert (HBid: fair_on_bids (Make_FOB (sort m_dbp M) (sort by_dbp B)) (sort by_dbp B)).
           { eapply mfob_fair_on_bid. all:auto. apply sorted_nodup_is_sublistB.
             all: auto. 
             { assert (H1: NoDup (bids_of M)). apply H.  eauto. }
             { assert (H2: bids_of M [<=] B). apply H.
               eapply perm_subset with (l1:= bids_of M)(s1:= B).
               auto. all: auto. } }
           unfold fair_on_bids.
           intros b b' h1 h2 h3.
           unfold fair_on_bids in HBid. apply HBid with (b':= b').
           { destruct h1 as [h1 h1a]. split; auto. }
           all: auto.  } } Qed.



(*-------------------------End of Fair On Bid Lemmas ---------------------*)







Lemma sorted_A_imply_sorted_p (A: list Ask): Sorted by_sp A -> Sorted leb (ask_prices A).
  Proof.  { induction A.
       { simpl. intro H. constructor. }
       { simpl. intro H. inversion H. constructor. auto.
         intros b H4. 
         apply IHA in H2. assert (H5: exists b1, In b1 A /\ b = sp b1).
         eauto. destruct H5 as [b1 H5]. destruct H5 as [H5 H6].
         apply H3 in H5 as H7. unfold by_dbp in H7. subst b. exact. } } Qed. 
 
Lemma top_prices_ma (m: fill_type)(a: Ask) (M: list fill_type)(A: list Ask):
  Sorted m_sp (m::M)-> Sorted by_sp (a::A) ->
  ask_prices (asks_of (m::M)) [<=] ask_prices (a::A) -> a<=(ask_of m).
Proof. { intros H1 H2 H3. simpl in H3.
       assert (H4: Sorted leb (ask_prices (a::A))).
       { apply sorted_A_imply_sorted_p;auto. } 
       cut (In (sp (ask_of m)) ((sp a)::ask_prices A)).
       inversion H4. intro H7. destruct H7. omega.
       apply H6 in H7 as H8.  apply /leP. exact. auto. } Qed.

Lemma nodup_sub_is_includedA (A1 A2: list Ask):  NoDup A1 -> NoDup A2 -> A1 [<=] A2 ->
                                                  included A1 A2.
Proof. eauto. Qed.

(*--------------- following lemma important : need a mention in the paper ------------*)

Lemma count_in_deletedA (a: Ask)(A: list Ask):
  In a A -> count (sp a)(ask_prices A) = S (count (sp a) (ask_prices (delete a A))).
Proof. { induction A as [|b].
       { simpl. auto. }
       { intro h1. destruct (a == b) eqn: h2.
         { simpl. rewrite h2. move /eqP in h2.
           subst a. simpl. replace (b =? b) with true. auto. auto. }
         { assert (h1a: In a A).
           { move /eqP in h2. eauto.   }
           replace (delete a (b :: A)) with (b :: (delete a A)).
           { simpl. destruct (a =? b) eqn: h3.
             { apply IHA in h1a as h1b. rewrite h1b. auto. }
             { auto. } }
           { simpl. rewrite h2. auto. } } } } Qed.


Lemma included_A_imp_included_AP (A1 A2: list Ask): included A1 A2 ->
                                                    included (ask_prices A1) (ask_prices A2).
Proof. { revert A2. induction A1 as [| a1].
       { simpl. auto. }
       { intros A2 h1.
         assert (h2: In a1 A2). eauto.
         assert (h3: included A1 (delete a1 A2)). eauto.
         assert (h3a: included (ask_prices A1) (ask_prices (delete a1 A2))).
         { auto. }
         assert(h4:count (sp a1)(ask_prices A2)= S (count (sp a1) (ask_prices (delete a1 A2)))).
         {eauto using count_in_deletedA. }
         eapply included_intro.
         intro x.  simpl. destruct (x =? a1) eqn: C1.
         { (* ---- C1: x = b1 ---- *)
           move /nat_eqP in C1. subst x.
           rewrite h4.
           eapply included_elim in h3a  as h3b. instantiate (1 := a1) in h3b.
           omega. }
         { (*----- C1: x <> b1 ---- *)
           assert (h3b: included A1 A2). eapply included_elim4; apply h1. 
           apply IHA1 in h3b as h3c. auto. } } } Qed.


Lemma sorted_nodup_is_sublistA (A1 A2: list Ask): Sorted by_sp A1 -> Sorted by_sp A2 ->
                                                 NoDup A1 -> NoDup A2 -> A1 [<=] A2 ->
                                                 sublist (ask_prices A1) (ask_prices A2). 
Proof. { intros h1 h2 h3 h4 h5.
         assert (h6: Sorted leb (ask_prices A1)).
         { auto using sorted_A_imply_sorted_p. }
         
         assert (h7: Sorted leb (ask_prices A2)).
         { auto using sorted_A_imply_sorted_p. }

         assert (h8: included A1 A2).
         { auto using nodup_sub_is_includedA. }
         
         assert (h9: included (ask_prices A1) (ask_prices A2)).
         { auto using included_A_imp_included_AP. } 
         assert (Hanti: antisymmetric leb). 
          { unfold antisymmetric.  intros ax ay ah10. 
            move /andP in ah10. destruct ah10 as [ah10 ah11].
            move /leP in ah10. move /leP in ah11. omega. } 
            eapply sorted_included_sublist. exact Hanti. all: auto. }  Qed.

Lemma sorted_m_imply_sorted_a (M: list fill_type): Sorted m_sp M -> Sorted by_sp (asks_of M).
Proof. { induction M.
       { simpl. intro H. constructor. }
       { simpl. intro H. inversion H. constructor. auto.
         intros a1 H4. unfold by_sp.
         assert (H5: exists m, In m M /\ a1 = ask_of m). eauto.
         destruct H5 as [m H5]. destruct H5 as [H5 H6].
         apply H3 in H5 as H7. unfold m_sp in H7. unfold by_sp in H7.
         subst a1. exact. } } Qed.

Hint Resolve sorted_m_imply_sorted_a.
















(* -------------- function to make a matching fair on asks --------------------- *)
Fixpoint Make_FOA (M:list fill_type) (A: list Ask):=
match (M,A) with 
|(nil,_) => nil
|(m::M',nil) => nil
|(m::M',a::A') => (Mk_fill (bid_of m) a (tp m))::(Make_FOA M' A')
end.


Lemma mfoa_subA (M:list fill_type) (A:list Ask): asks_of (Make_FOA M A) [<=] A.
Proof. { revert A. induction M. simpl. auto. intro A.
         case A.
         { simpl. auto. }
         { intros. simpl. intro x. intro H1.
           destruct H1. subst x. auto. cut (In x l). auto. eapply IHM. auto. } } Qed.

Lemma mfoa_bid_sub_M (M: list fill_type)(A: list Ask): bids_of (Make_FOA M A) [<=] bids_of M.
Proof. { revert A. induction M.
       { simpl. auto. }
       { intro A. case A.
         { simpl. auto. }
         { intros a0 l. simpl.  auto. } } } Qed.
  
Lemma mfoa_subB (M:list fill_type)(A:list Ask)(B:list Bid):
  (bids_of M [<=] B)->(bids_of(Make_FOA M A)) [<=] B.
Proof. eauto using mfoa_bid_sub_M. Qed.

Lemma mfoa_nodup_bids (M: list fill_type)(A: list Ask): NoDup (bids_of M)->
                                                        NoDup (bids_of (Make_FOA M A)).
Proof. { revert A. induction M.
       { simpl. auto. }
       { intro A. case A.
         { simpl. auto. }
         { intros a0 l. simpl. intro H. cut (NoDup (bids_of (Make_FOA M l))).
           cut(~ In (bid_of a) (bids_of (Make_FOA M l))). eauto.
           Focus 2. eauto.
           intro H1. absurd (In (bid_of a) (bids_of M)). auto.
           eapply mfoa_bid_sub_M. eauto. } } } Qed.

Lemma mfoa_nodup_asks (M: list fill_type)(A:list Ask): NoDup A -> NoDup (asks_of (Make_FOA M A)).
Proof. { revert A. induction M. simpl. auto.
         intro A. case A.
         { simpl. auto. }
         { intros a0 l. simpl. intro h1.
           cut (~In a0 (asks_of (Make_FOA M l))). cut (NoDup (asks_of (Make_FOA M l))).
           auto. eauto. intro h2. absurd (In a0 l). eauto. eapply mfoa_subA. apply h2. } } Qed.

Lemma mfoa_matchable (M:list fill_type)(A:list Ask)(NDA: NoDup A):
  (Sorted m_sp M) -> (Sorted by_sp A) -> All_matchable M ->
   sublist (ask_prices (asks_of M)) (ask_prices A) ->
   NoDup (asks_of M) -> All_matchable (Make_FOA M A).
Proof. { revert A NDA. induction M. 
         { intros A H1 H2 H3 H4 H5 H6. simpl. eauto. }
         { intros A H1 H2 H3 H4 H5 H6. 
           destruct A. 
           { simpl. apply All_matchable_nil.  }
           { simpl. apply All_matchable_intro. 
             { simpl.
               assert (H7: a0 <= (ask_of a)). 
               { eapply top_prices_ma.   eauto. apply H3. auto. } 
               assert (H8: ask_of a <= bid_of a). 
               { unfold All_matchable in H4. simpl in H4. eapply H4. left;auto. }
               omega. } 
             { eapply IHM. 
               { eauto. } 
               { eauto. }
               { eauto. } 
               { eapply All_matchable_elim1. apply H4. }
               { simpl in H5. destruct (ask_of a =? a0).
                 auto.  eauto. } 
               { simpl in H6. eauto.  } } } } } Qed.          


Lemma mfoa_matching (M:list fill_type) (A:list Ask) (B:list Bid) (NDA: NoDup A):
(Sorted m_sp M) -> (Sorted by_sp A) -> (matching_in B A M) -> matching (Make_FOA M A).
Proof. { intros h1 h2 h3. unfold matching.
       split.
       { (*-------- All_matchable (Make_FOA M B)---------*)
         apply mfoa_matchable. all: auto. apply h3.
         eapply sorted_nodup_is_sublistA. all: auto. all: apply h3. }
       split.
       { (*-------NoDup (bids_of (Make_FOA M B))---------*)
         unfold matching_in in h3. unfold matching in h3. 
         destruct h3. destruct H.  destruct H1. eauto using mfoa_nodup_bids. }
       { (*------ NoDup (asks_of (Make_FOB M B))---------*)
        eapply mfoa_nodup_asks. unfold matching_in in h3. unfold matching in h3. 
         destruct h3. destruct H.  destruct H1. eauto. } } Qed.
 



Lemma mfoa_matching_in (M: list fill_type)(A: list Ask)(B: list Bid)(NDA: NoDup A):
(Sorted m_sp M) -> (Sorted by_sp A) -> matching_in B A M -> matching_in B A (Make_FOA M A).
Proof.  { intros H1 H2 H3. unfold matching_in. 
          split. { eapply mfoa_matching. all: auto. eapply H3.  }
                 split. { eapply mfoa_subB. unfold matching_in in H3. unfold matching in H3. 
         destruct H3. destruct H.  destruct H0. exact. }
                        { eapply mfoa_subA. } } Qed.

Lemma mfoa_fair_on_ask (M: list fill_type) (B:list Bid) (A:list Ask):
  (Sorted m_sp M) -> (Sorted by_sp A) -> sublist (ask_prices (asks_of M)) (ask_prices A) ->
  fair_on_asks (Make_FOA M A) A. 
Proof. { revert A. induction M as [|m]. 
        { intros; simpl; unfold fair_on_asks; intros; inversion H4. }
        { intros. unfold fair_on_asks. intros a a' H2 H3 H4.
          destruct A eqn: Ha. 
         { simpl. inversion H4. }
         { assert (case1: a' = a0 \/ a' <> a0). eauto.
           destruct H2 as [H2 H2a].
           assert  (case3: a0 = a' \/ In a' (asks_of ((Make_FOA M l)))).
           { simpl in H4. auto. }
           destruct case1 as [c1a | c1b]. 
           { (*-- c1a : a0 = a' -------------------------*)
             subst a'. (*H3 is not possible*) 
             assert (H5: a >= a0).
             { apply Sorted_elim2 with (x:= a) in H0 as H0a.
              apply /leP. auto.  unfold by_sp.
              unfold reflexive. auto. exact. } omega.  }
           
           { (*-- c1b : a' <> a0 ---*)             assert (H5: In a' l).
             { eauto. }
             assert (case2: a=a0 \/ In a l).
             { auto. }
             destruct case2 as [c2a | c2b]. 
             { subst a. simpl. left. auto. }
             { destruct case3 as [c3a | c3b].
               { subst a0. contradiction. }
               { simpl. right. eapply IHM with (s':=a').
                 { eauto. }
                 { eauto. }
                 { simpl in H1. destruct ( ask_of m =? a0) eqn: H6.  auto. eauto. }
                 { split. exact. eauto. }
                 { exact.  }
                 { auto. }  } } } } } } Qed.


Lemma mfoa_bids_is_perm (M: list fill_type) (A:list Ask) :
 (|M| <= |A|)  -> perm (bids_of M) (bids_of (Make_FOA M A)). 
Proof. { revert A.  induction M. 
         { simpl. auto. }
         { destruct A eqn: HA.
           { simpl. intro h1. inversion h1. } 
           { simpl. intro h1.
             assert (h2: |M| <= |l|). omega.
             apply IHM in h2 as h3.  simpl. auto. } } } Qed.

Lemma mfoa_is_same_size (M: list fill_type) (A:list Ask):
 (|M| <= |A|)  -> |M| = |(Make_FOA M A)|. 
Proof.  { revert A.  induction M. 
         { simpl. auto. }
         { destruct A eqn: HA.
           { simpl. intro h1. inversion h1. } 
           { simpl. intro h1.
             assert (h2: |M| <= |l|). omega.
             apply IHM in h2 as h3.  simpl. auto. } } } Qed. 

Hint Resolve mfob_matching mfob_fair_on_bid mfob_asks_is_perm mfob_is_same_size: core.



Theorem exists_fair_on_asks (M: list fill_type) (B: list Bid) (A:list Ask)(NDA: NoDup A):
  matching_in B A M->
  (exists M':list fill_type, matching_in B A M' /\  (|M| = |M'|) /\ perm (bids_of M) (bids_of M')
   /\ fair_on_asks M' A).
Proof. { assert (HmP: transitive m_sp /\ comparable m_sp). apply m_sp_P.  
        assert (HaP: transitive by_sp /\ comparable by_sp). apply by_sp_P.
        destruct HmP as [Hmp1 Hmp2]. destruct HaP as [Hbp1 Hbp2].
        intro H. exists (Make_FOA (sort m_sp M) (sort by_sp A)).
        split. 
        { assert (HM: matching_in B (sort by_sp A) (Make_FOA (sort m_sp M) (sort by_sp A))).
          apply mfoa_matching_in. all:auto.   
          apply match_inv with (M:=M)(B:=B)(A:=A);auto.
          eapply match_inv with
              (B:= B) (M:=(Make_FOA (sort m_sp M) (sort by_sp A))) (A:=(sort by_sp A)).
          all:auto.  }
        split.
        { replace (|M|) with (|sort m_sp M|). eapply mfoa_is_same_size.
          apply M_is_smaller_than_A with (B:= B).
          eapply match_inv with (B:= B)(A:= A)(M:= M). all: auto. } split.
        {  assert(HB: perm (bids_of (sort m_sp M))
                           (bids_of (Make_FOA (sort m_sp M) (sort by_sp A)))).
           eapply  mfoa_bids_is_perm. apply M_is_smaller_than_A with (B:=B).
           eapply match_inv with (B:= B)(A:= A)(M:= M). all: auto.  }
        {  assert (HAsk: fair_on_asks (Make_FOA (sort m_sp M) (sort by_sp A)) (sort by_sp A)).
           { eapply mfoa_fair_on_ask. all:auto. apply sorted_nodup_is_sublistA.
             all: auto. 
             { assert (H1: NoDup (bids_of M)). apply H. unfold matching_in in H.
             unfold matching in H. destruct H. destruct H. destruct H2.
              eauto. }
             { assert (H2: bids_of M [<=] B). apply H.
               eapply perm_subset with (l1:= asks_of M)(s1:= A).
               auto. all: auto. apply H. } }
           unfold fair_on_asks.
           intros a a' h1 h2 h3.
           unfold fair_on_asks in HAsk. apply HAsk with (s':= a').
           { destruct h1 as [h1 h1a]. split; auto. }
           all: auto.  } } Qed.





Theorem exists_fair_matching(M: list fill_type)(B: list Bid)(A:list Ask)(NDB: NoDup B)
        (NDA: NoDup A): matching_in B A M->
                        (exists M':list fill_type, matching_in B A M' /\ Is_fair M' B A /\ |M|= |M'|).
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
       {eauto. } auto. auto. } Qed.
         
End Fair.


Hint Resolve m_dbp_P m_sp_P by_dbp_P by_sp_P.
Hint Resolve by_dbp_refl by_sp_refl m_dbp_refl m_sp_refl.
Hint Resolve geb_anti leb_anti: core.