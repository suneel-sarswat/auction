




(* ---------------------------------------------------------------------------------------

   This file contains results of bounds on Matchings. 
 -------------------------------------------------------------------------------------- *)





Require Import ssreflect ssrbool. 
Require Export Lists.List.

Require Export GenReflect SetSpecs.

Require Export DecSort MinMax.
Require Export BidAsk.
Require Export DecList.
Require Export Matching.
Require Export AuctionInvar.
Require Export Fair.
Require Export MM.
Require Export UM.

Section bounds.


Fixpoint bids_above (p:nat)(M:list fill_type) :=
match M with 
|nil => nil
|m::M' => match (Nat.leb p (bid_of m)) with
  |true => (bid_of m)::(bids_above p M')
  |false => (bids_above p M')
  end
end.

Fixpoint asks_below (p:nat)(M:list fill_type) :=
match M with 
|nil => nil
|m::M' => match (Nat.leb (ask_of m) p) with
  |true => (ask_of m)::(asks_below p M')
  |false => (asks_below p M')
  end
end.

Lemma matchable_buy_above_sell_below (b:Bid) (a: Ask) (B: list Bid) (A: list Ask) (p:nat): In b (buyers_above p B) -> In a (sellers_below p A)
-> a<=b.
Proof. intros. apply  buyers_above_elim in H. apply sellers_below_elim in H0. omega. Qed. 

Lemma buy_below_above_total (M: list fill_type) (B:list Bid) (A:list Ask) (p:nat):
(matching_in B A M) -> (|(buyers_above p (bids_of M))|) + (|(buyers_below p (bids_of M))|) >= |M|.
Proof. { intros H. destruct H as [H H0]. destruct H0 as [H0 H1]. 
          destruct H as [H H2]. destruct H2 as [H2 H3].
          induction M. { simpl. auto. }
           { simpl.  
            destruct (p <=? bid_of a) eqn: Hpb.
            { destruct (bid_of a <=? p) eqn: Hpa.
            { simpl. cut ((| buyers_above p (bids_of M) |) + (| buyers_below p (bids_of M) |) >= |M|). 
            omega. apply IHM. all:eauto. }
            { simpl. cut ((| buyers_above p (bids_of M) |) + (| buyers_below p (bids_of M) |) >= |M|). 
            omega. apply IHM. all:eauto. } }
            { destruct (bid_of a <=? p) eqn: Hpa.
            { simpl. cut ((| buyers_above p (bids_of M) |) + (| buyers_below p (bids_of M) |) >= |M|). omega. apply IHM. all:eauto. }
            { move /leP in Hpb. move /leP in Hpa. omega. } }}} Qed.
            
Lemma sell_below_above_total (M: list fill_type) (B:list Bid) (A:list Ask) (p:nat):
(matching_in B A M) -> (|(sellers_above p (asks_of M))|) + (|(sellers_below p (asks_of M))|) >= |M|.
Proof. { intros H. destruct H as [H H0]. destruct H0 as [H0 H1]. 
          destruct H as [H H2]. destruct H2 as [H2 H3].
          induction M. { simpl. auto. }
           { simpl.  
            destruct (p <=? ask_of a) eqn: Hpb.
            { destruct (ask_of a <=? p) eqn: Hpa.
            { simpl. cut ((|(sellers_above p (asks_of M))|) + (|(sellers_below p (asks_of M))|) >= |M|). 
            omega. apply IHM. all:eauto. }
            { simpl. cut ((|(sellers_above p (asks_of M))|) + (|(sellers_below p (asks_of M))|) >= |M|). 
            omega. apply IHM. all:eauto. } }
            { destruct (ask_of a <=? p) eqn: Hpa.
            { simpl. cut ((|(sellers_above p (asks_of M))|) + (|(sellers_below p (asks_of M))|) >= |M|). omega. apply IHM. all:eauto. }
            { move /leP in Hpb. move /leP in Hpa. omega. } }}} Qed.


Lemma maching_buyer_right_plus_seller_left 
(M: list fill_type) (B:list Bid) (A:list Ask) (p:nat):
(matching_in B A M) -> (|(buyers_above p (bids_of M))|) + (|(sellers_below p (asks_of M))|) >= |M|.
Proof.  intros H. apply sellers_below_ge_buyers with (p:=p) in H  as H1.
                  eapply buyers_above_ge_sellers with (p:=p) in H as H2.
                  eapply buy_below_above_total with (p:=p) in H as H3.
                  eapply sell_below_above_total with (p:=p) in H as H4.
                  omega. Qed.

Lemma buyers_above_delete_S (A : list Bid) (b:Bid) (p:nat):
In b A -> p<= b-> (| buyers_above p A |)=S((| buyers_above p (delete b A) |)).
Proof. { intros. induction A. destruct H. simpl. destruct (p <=? a) eqn: Hpa.
{ destruct (b_eqb b a) eqn:Hba. simpl. auto. simpl. destruct (p <=? a).
simpl. move /eqP in Hba. simpl in H. destruct H. subst a. destruct Hba.
auto. apply IHA in H. omega. inversion Hpa. }
{ destruct (b_eqb b a) eqn: Hba. move /eqP in Hba. subst. move /leP in H0.
  assert (p <=? a = true). eauto. rewrite H1 in Hpa. inversion Hpa.
  simpl. destruct (p <=? a) eqn: Hpa2. inversion Hpa. apply IHA. 
  move /eqP in Hba. simpl in H. destruct H. subst a. destruct Hba. auto. exact. }} Qed.

Lemma buyers_above_delete (A : list Bid) (b:Bid) (p:nat):
In b A -> (p <=? b) = false -> (| buyers_above p A |)=(| buyers_above p (delete b A) |).
Proof. { intros. induction A. destruct H. simpl. destruct (p <=? a) eqn: Hpa.
{ destruct (b_eqb b a) eqn:Hba. simpl. move /eqP in Hba. subst a.
rewrite H0 in Hpa. inversion Hpa. simpl. destruct (p <=? a).
simpl. move /eqP in Hba. simpl in H. destruct H. subst a. destruct Hba.
auto. apply IHA in H. omega. inversion Hpa. }
{ destruct (b_eqb b a) eqn: Hba. auto. simpl.
  destruct (p <=? a) eqn: Hpa2. inversion Hpa. apply IHA. 
  move /eqP in Hba. simpl in H. destruct H. subst a. destruct Hba. auto. exact. }} Qed.
  
Lemma sellers_below_delete_S (A : list Ask) (b:Ask) (p:nat):
In b A -> b<= p-> (| sellers_below p A |)=S((| sellers_below p (delete b A) |)).
Proof. { intros. induction A. destruct H. simpl. destruct (a <=? p) eqn: Hpa.
{ destruct (a_eqb b a) eqn:Hba. simpl. auto. simpl. destruct (a <=? p).
simpl. move /eqP in Hba. simpl in H. destruct H. subst a. destruct Hba.
auto. apply IHA in H. omega. inversion Hpa. }
{ destruct (a_eqb b a) eqn: Hba. move /eqP in Hba. subst. move /leP in H0.
  assert (a <=? p = true). eauto. rewrite H1 in Hpa. inversion Hpa.
  simpl. destruct (a <=? p) eqn: Hpa2. inversion Hpa. apply IHA. 
  move /eqP in Hba. simpl in H. destruct H. subst a. destruct Hba. auto. exact. }} Qed.

Lemma sellers_below_delete (A : list Ask) (b:Ask) (p:nat):
In b A -> (b <=? p) = false -> 
(| sellers_below p A |)=(| sellers_below p (delete b A) |).
Proof. { intros. induction A. destruct H. simpl. destruct (a <=? p) eqn: Hpa.
{ destruct (a_eqb b a) eqn:Hba. simpl. move /eqP in Hba. subst a.
rewrite H0 in Hpa. inversion Hpa. simpl. destruct (a <=? p).
simpl. move /eqP in Hba. simpl in H. destruct H. subst a. destruct Hba.
auto. apply IHA in H. omega. inversion Hpa. }
{ destruct (a_eqb b a) eqn: Hba. auto. simpl.
  destruct (a <=? p) eqn: Hpa2. inversion Hpa. apply IHA. 
  move /eqP in Hba. simpl in H. destruct H. subst a. destruct Hba. auto. exact. }} Qed.
  

Lemma buyers_above_bid_size (A B:list Bid) (p:nat):
A [<=] B -> NoDup A -> (|buyers_above p B|) >= (|buyers_above p A|).
Proof. { revert A. induction B as [| b]. intros. assert (A=nil). eauto. subst A.
simpl. omega. intros. assert (In b A \/ ~In b A). eauto. destruct H1.
{
simpl. destruct (p <=? b) eqn: Hpa. simpl.
assert ((| buyers_above p A |)=S((| buyers_above p (delete b A) |))).
{ eapply buyers_above_delete_S. exact. move /leP in Hpa. exact. } rewrite H2. cut (| buyers_above p B | >= | buyers_above p (delete b A) |).
omega. assert (delete b A [<=] delete b (b::B)). eapply delete_subset2. exact. exact.
simpl in H3. destruct (b_eqb b b) eqn:Hbb. apply IHB in H3. exact. eauto.
 move /eqP in Hbb. destruct Hbb. auto.
 assert ((| buyers_above p A |)=(| buyers_above p (delete b A) |)).
{ apply buyers_above_delete. exact. exact.  } rewrite H2.  assert (delete b A [<=] delete b (b::B)). eapply delete_subset2. exact. exact.
simpl in H3. destruct (b_eqb b b) eqn:Hbb. apply IHB in H3. exact. eauto.
 move /eqP in Hbb. destruct Hbb. auto. }
{ assert (A[<=]B). { assert (delete b A [<=] delete b (b::B)). eapply delete_subset2.
exact. exact. simpl in H2.  destruct (b_eqb b b) eqn: Hbb. assert (A=delete b A).
eapply delete_intro1. exact. rewrite <- H3 in H2. exact. move /eqP in Hbb. destruct Hbb. auto. } simpl. destruct (p <=? b) eqn: Hpa. simpl.
cut ((| buyers_above p B |) >= (| buyers_above p A |)). omega. apply IHB. eauto. eauto.
apply IHB. eauto. eauto. } } Qed.

Lemma sellers_below_ask_size 
(M: list fill_type) (A B:list Ask) (p:nat):
A [<=] B -> NoDup A -> (|sellers_below p B|) >= (|sellers_below p A|).
Proof. { revert A. induction B as [| b]. intros. assert (A=nil). eauto. subst A.
simpl. omega. intros. assert (In b A \/ ~In b A). eauto. destruct H1.
{
simpl. destruct (b <=? p) eqn: Hpa. simpl.
assert ((| sellers_below p A |)=S((| sellers_below p (delete b A) |))).
{ eapply sellers_below_delete_S. exact. move /leP in Hpa. exact. } rewrite H2. cut (| sellers_below p B | >= | sellers_below p (delete b A) |).
omega. assert (delete b A [<=] delete b (b::B)). eapply delete_subset2. exact. exact.
simpl in H3. destruct (a_eqb b b) eqn:Hbb. apply IHB in H3. exact. eauto.
 move /eqP in Hbb. destruct Hbb. auto.
 assert ((| sellers_below p A |)=(| sellers_below p (delete b A) |)).
{ apply sellers_below_delete. exact. exact.  } rewrite H2.  assert (delete b A [<=] delete b (b::B)). eapply delete_subset2. exact. exact.
simpl in H3. destruct (a_eqb b b) eqn:Hbb. apply IHB in H3. exact. eauto.
 move /eqP in Hbb. destruct Hbb. auto. }
{ assert (A[<=]B). { assert (delete b A [<=] delete b (b::B)). eapply delete_subset2.
exact. exact. simpl in H2.  destruct (a_eqb b b) eqn: Hbb. assert (A=delete b A).
eapply delete_intro1. exact. rewrite <- H3 in H2. exact. move /eqP in Hbb. destruct Hbb. auto. } simpl. destruct (b <=? p) eqn: Hpa. simpl.
cut ((| sellers_below p B |) >= (| sellers_below p A |)). omega. apply IHB. eauto. eauto.
apply IHB. eauto. eauto. } } Qed.





Lemma buyers_above_size 
(M: list fill_type) (B:list Bid) (A:list Ask) (p:nat):
(matching_in B A M) -> (|buyers_above p B|) >= (|buyers_above p (bids_of M)|).
Proof. intros H. destruct H as [H H0]. destruct H0 as [H0 H1]. 
          destruct H as [H H2]. destruct H2 as [H2 H3].
          apply buyers_above_bid_size. auto. auto.  Qed.
          

Lemma sellers_below_size 
(M: list fill_type) (B:list Bid) (A:list Ask) (p:nat):
(matching_in B A M) -> (|sellers_below p A|) >= (|sellers_below p (asks_of M)|).
Proof. intros H. destruct H as [H H0]. destruct H0 as [H0 H1]. 
          destruct H as [H H2]. destruct H2 as [H2 H3].
          apply sellers_below_ask_size. auto. auto. auto. Qed.

Theorem bound_on_M
(M: list fill_type) (B:list Bid) (A:list Ask) (p:nat):
(matching_in B A M) -> 
(|(buyers_above p B)|) + (|(sellers_below p A)|) >= |M|.
Proof. { intros H. apply sellers_below_ge_buyers with (p:=p) in H  as H1b.
                  eapply buyers_above_ge_sellers with (p:=p) in H as H2a.
                  eapply buy_below_above_total with (p:=p) in H as H3a.
                  eapply sell_below_above_total with (p:=p) in H as H3b.
                  eapply buyers_above_size with (p:=p) in H as H4a.
                  eapply sellers_below_size with (p:=p) in H as H4b.
                  omega. } Qed.
                  


Lemma buyers_above_nodup (B:list Bid) (Ndb: NoDup B) (p:nat):
NoDup (buyers_above p B).
Proof. induction B. simpl. constructor. simpl. 
destruct (p <=? a) eqn: Hpa. assert (H0:~In a B).
eauto. assert (H1:~In a (buyers_above p B)). eauto. 
assert (H2: NoDup B). eauto. eapply IHB in H2. eauto.
assert (H2: NoDup B). eauto. eapply IHB in H2. eauto. Qed.



Lemma sellers_below_nodup (A:list Ask) (Nda: NoDup A) (p:nat):
NoDup (sellers_below p A).
Proof. induction A. simpl. constructor. simpl. 
destruct (a <=? p) eqn: Hap. assert (H0:~In a A).
eauto. assert (H1:~In a (sellers_below p A)). eauto. 
assert (H2: NoDup A). eauto. eapply IHA in H2. eauto.
assert (H2: NoDup A). eauto. eapply IHA in H2. eauto. Qed.


Lemma uniform_halfBA (M: list fill_type) (B:list Bid) (A:list Ask)(no_dup_B: NoDup B)(no_dup_A: NoDup A)(n:nat) :
Sorted by_dbp B ->  Sorted by_sp A -> matching_in B A M -> |M|>=2*n ->
(|pair_uniform B A|)>=n.
Proof. revert A B no_dup_B no_dup_A M. induction n. intros. simpl. omega.
intros. case A as [| a1 A']. { case B as [| b1 B']. 
(* base case: when A is nil *)
         
          { apply matching_on_nilA in H1 as HA. rewrite HA in H2. subst M. simpl in H2.
          omega. }
          { apply matching_on_nilA in H1 as HA. rewrite HA in H2. subst M. simpl in H2.
          omega. } } 
          { case B as [| b1 B']. 
          { apply matching_on_nilB in H1 as HB. rewrite HB in H2. subst M. simpl in H2.
          omega. }          
         { (*----- induction step : b::B'   and a:: A' ---------*)
           assert (Case: b1 < a1 \/ b1 >= a1 ). omega.
           destruct Case as [C1 | C2].
                      { (*------C1:  when b and a are not matchable then produce_MM (b::B') A' *)
             simpl. replace (a1 <=? b1) with false.
             2:{ symmetry. apply /leP. omega. } 
             assert (HM:M=nil). eapply unmatchableAB_nil.
             eauto. eauto. eauto. exact. subst M. simpl in H2. omega. }
             { (*-- C2: when b and a are matchable then Output is (b,a):: produce_MM B' A'----*)
             assert (HBdel:B'=(delete b1 B')). { 
             eapply delete_intro1. assert (B'=(delete b1 (b1::B'))).
             simpl. destruct (b_eqb b1 b1) eqn:heq. auto. move /eqP in heq.
             destruct heq. auto. rewrite H3. eapply delete_intro2. exact. } 
             assert (HAdel:A'=(delete a1 A')). { 
             eapply delete_intro1. assert (A'=(delete a1 (a1::A'))).
             simpl. destruct (a_eqb a1 a1) eqn:heq. auto. move /eqP in heq.
             destruct heq. auto. rewrite H3. eapply delete_intro2. exact. }
               simpl.
              replace (a1 <=? b1) with true.
             
             2:{ symmetry. apply /leP. auto. } simpl.
             cut ( (| pair_uniform B' A' |) >= n). omega.
             assert (Hb: In b1 (bids_of M) \/ ~ In b1 (bids_of M)). eauto.
             assert (Ha: In a1 (asks_of M) \/ ~ In a1 (asks_of M)). eauto.
             destruct Hb as [Hb1 | Hb2]; destruct Ha as [Ha1 | Ha2].

              { (* Case_ab1: In b (bids_of M) and In a (asks_of M)------*)
               assert (h3: exists m1, In m1 M /\ a1 = ask_of m1). eauto.
               assert (h4: exists m2, In m2 M /\ b1 = bid_of m2). eauto.
               destruct h3 as [m1 h3]. destruct h3 as [h3a h3].
               destruct h4 as [m2 h4]. destruct h4 as [h4a h4].
               set (M'' := delete m1 (delete m2 M)).
               assert (HM_size: |M''|>=2*n).
{ assert (Hdeletem2: |delete m2 M|>=|M| - 1). eauto.
  assert (Hdeletem1: |delete m1 (delete m2 M)|>=|(delete m2 M)| - 1). eauto. subst M''.
  omega. }
assert (HM'B'A': matching_in (delete b1 B') (delete a1 A') M'').
{ destruct H1 as [ Hmatch1 Hmatch2]. destruct Hmatch1 as [Hmatch1 Hmatch3].
  destruct Hmatch3 as [Hmatch3 Hmatch4]. destruct Hmatch2 as [Hmatch2 Hmatch5].
  (*************************************************)
     assert (Hdbid: (bids_of (delete m1 (delete m2 M))) = 
     (delete (bid_of m1) (delete (bid_of m2) (bids_of M)))).  
     apply bids_of_delete_delete. exact. exact. exact.
     assert (Hdask: (asks_of (delete m1 (delete m2 M))) = 
     (delete (ask_of m1) (delete (ask_of m2) (asks_of M)))).  
     apply asks_of_delete_delete. exact. exact. exact.
   (**********************************************)
   unfold matching_in. split. 
   { unfold matching. split. 
   {
   { eauto. } } split. 
   { subst M''. rewrite Hdbid. eauto. }
   { subst M''. rewrite Hdask. eauto. }
   } split. 
{ subst M''. rewrite Hdbid. assert ((delete (bid_of m1) (bids_of M))
[<=] b1::B'). eauto. assert (delete (bid_of m2) (delete (bid_of m1) (bids_of M)) [<=] delete (bid_of m2) (b1 :: B')).  eapply delete_subset2. eapply delete_subset.  exact. eauto. rewrite<- h4 in H3. assert (delete (bid_of m1) (delete (bid_of m2) (bids_of M)) = delete (bid_of m2) (delete (bid_of m1) (bids_of M))). eapply delete_exchange.
rewrite H4.  rewrite <- h4. simpl in H3.
    destruct (b_eqb b1 b1) eqn: Hbb. assert ((delete b1 B')=B'). eauto. rewrite H5.
    exact. move /eqP in Hbb. destruct Hbb. auto. }    
     { subst M''. rewrite Hdask. assert ((delete (ask_of m2) (asks_of M))
[<=] a1::A'). eauto. 
    assert (delete (ask_of m1) (delete (ask_of m2) (asks_of M)) [<=] delete (ask_of m1) (a1 :: A')). eapply delete_subset2. exact. eauto. rewrite<- h3 in H3. simpl in H3.
    destruct (a_eqb a1 a1) eqn: Haa. assert ((delete a1 A')=A'). eauto. rewrite H4.
    rewrite<- h3. exact. move /eqP in Haa. destruct Haa. auto. } }
apply IHn in HM'B'A'. rewrite HBdel. rewrite HAdel. exact. {
assert ((delete b1 B')=B'). eauto. rewrite H3. eauto. }
{ assert ((delete a1 A')=A'). eauto. rewrite H3. eauto.  } rewrite <- HBdel. eauto.
rewrite <- HAdel. eauto. exact. }

{(* Case_ab2: In b (bids_of M) and ~ In a (asks_of M)----*)
               assert (h3: exists m, In m M /\ b1 = bid_of m). eauto.
               destruct h3 as [m h3]. destruct h3 as [h3a h3].
               set (M' := delete m M).
               assert (h4: matching_in B' A' M').
                 { unfold matching_in. split.
                 { (*------ matching M' -----------*)
                   unfold M'. eauto. } split.
                 { (*------bids_of M' [<=] B'------*)
                   intros x h4.
                   assert (h5: In x (bids_of M)).
                   { unfold M' in h4. eauto. }
                   assert (h5a: In x (b1::B')).
                   { destruct H1. destruct H3. apply H3. auto. }
                   assert (h6: x <> b1).
                   { intro h6. unfold M' in h4.
                     subst x;subst b1.
                     absurd (In (bid_of m) (bids_of (delete m M))).
                     { apply matching_elim10. eapply matching_in_elim0.
                      exact H1. exact h3a. } auto. }
                   eapply in_inv2. all: eauto. }
                 { (*------ asks_of M' [<=] A'-------*)
                   intros x h4.
                   assert (h5: In x (asks_of M)).
                   { unfold M' in h4. eauto. }
                   assert (h6: x <> a1).
                   { intro h6. subst x. contradiction. }
                   assert (h7: In x (a1::A')).
                   { apply H1. auto. }
                   eapply in_inv2. all: eauto.  } }
                   apply IHn in h4. exact. eauto. eauto. eauto. eauto. 
                   subst M'. assert ((| delete m M |)=|M| - 1).
                   eapply delete_size1. exact. rewrite H3. omega. }
                   
                   
{(* Case: ~In b (bids_of M) and In a (asks_of M)----*)
               assert (h3: exists m, In m M /\ a1 = ask_of m). eauto.
               destruct h3 as [m h3]. destruct h3 as [h3a h3].
               set (M' := delete m M).
               assert (h4: matching_in B' A' M').
                 { unfold matching_in. split.
                 { (*------ matching M' -----------*)
                   unfold M'. eauto. } split.
                 { (*------bids_of M' [<=] B'------*)
                   intros x h4.
                   assert (h5: In x (bids_of M)).
                   { unfold M' in h4. eauto. }
                   assert (h5a: In x (b1::B')).
                   { apply H1. auto. }
                   assert (h6: x <> b1).
                   { intro h6. unfold M' in h4.
                     subst x;subst a1.
                     absurd (In (bid_of m) (bids_of (delete m M))).
                     { apply matching_elim10. eapply matching_in_elim0.
                      exact H1. exact h3a. } auto. }
                   eapply in_inv2. all: eauto. }
                 { (*------ asks_of M' [<=] A'-------*)
                   intros x h4.
                   assert (h5: In x (asks_of M)).
                   { unfold M' in h4. eauto. }
                   assert (h6: x <> a1).
                   { intro h6. subst x. 
                   subst M'. assert (~In (ask_of m) (asks_of (delete m M))).
                   eapply matching_elim11. eapply matching_in_elim0.
                   exact H1. exact h3a. subst a1. contradiction. }
                   assert (h7: In x (a1::A')).
                   { apply H1. auto. }
                   eapply in_inv2. all: eauto.  } }
                   apply IHn in h4. exact. eauto. eauto. eauto. eauto.
                   subst M'. assert ((| delete m M |)=|M| - 1).
                   eapply delete_size1. exact. rewrite H3. omega. }
                   assert (h3: matching_in B' A' M). eauto using matching_in_elim8.
                   apply IHn in h3. exact. eauto. eauto. eauto. eauto. omega. } } } Qed. 

End bounds.


(*

Definition B2:= ({|b_id:= 1 ; bp:= 125 |}) ::({|b_id:= 2 ; bp:= 120 |}) ::({|b_id:= 3 ; bp:= 112 |}) ::({|b_id:= 4 ; bp:= 91 |}) ::({|b_id:= 5 ; bp:= 82 |}) ::({|b_id:= 6 ; bp:= 82 |}) ::({|b_id:= 7 ; bp:= 69 |}) ::({|b_id:= 8 ; bp:= 37 |}) :: nil.

Definition A2:= ({|s_id:= 1 ; sp:= 121 |}) ::({|s_id:= 3 ; sp:= 113 |}) ::({|s_id:= 5 ; sp:= 98 |}) ::({|s_id:= 9 ; sp:= 94 |}) ::({|s_id:= 90 ; sp:= 90 |}) ::({|s_id:= 78 ; sp:= 85 |}) ::({|s_id:= 67 ; sp:= 79 |}) ::({|s_id:= 45 ; sp:= 53 |}) ::nil.

 *)

