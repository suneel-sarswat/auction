




Require Import ssreflect ssrbool. 
Require Export Lists.List.

Require Export GenReflect SetSpecs.

Require Export Sorting MinMax.
Require Export BidAsk.
Require Export DecList.
Require Export Matching.
Require Export AuctionInvar.

Require Export Fair.

Section MM.

Fixpoint produce_MM (B:list Bid) (A: list Ask): (list fill_type) :=
  match (B, A) with
  |(nil, _) => nil
  |(b::B', nil) => nil              
  |(b::B', a::A') => match (Nat.leb (sp a) (bp b)) with
                    |true => ({|bid_of:= b ; ask_of:= a ; tp:=(bp b) |})::(produce_MM B' A')
                    |false => produce_MM B A'
                    end
  end. 

(*------------ Sorting by decreasing ask prices and their properties --------------*)

Definition by_dsp := fun a1 a2 : Ask => a2 <=? a1.
Lemma by_dsp_P : transitive by_dsp /\ comparable by_dsp.
Proof.  { split.
          { unfold transitive. unfold by_dsp.  
            intros y x z H H1. move /leP in H1. move /leP in H.
            apply /leP. omega. }
          { unfold comparable.  unfold by_dsp. intros.
            move /leP in H. apply /leP. omega. } } Qed.

Lemma by_dsp_refl: reflexive by_dsp.
Proof. eauto. Qed.


Hint Resolve by_dsp_P by_dsp_refl: core.


 Lemma nil_is_MM_forB (B: list Bid): Is_MM nil B nil.
 Proof. { unfold Is_MM. split.
          { eauto. }
          { intros. destruct H. destruct H0. 
            assert (H2: asks_of M'=nil). eauto.
            assert (H3: |M'|=|asks_of M'|). eapply asks_of_size.
            assert (H4: |asks_of M'| = 0). rewrite H2. auto. omega. } } Qed.
 
 Lemma nil_is_MM_forA (A: list Ask): Is_MM nil nil A.
 Proof. { unfold Is_MM. split.
          { eauto. }
          { intros. destruct H. destruct H0. 
            assert (H2: bids_of M'=nil). eauto.
            assert (H3: |M'|=|bids_of M'|). eapply bids_of_size.
            assert (H4: |bids_of M'| = 0). rewrite H2. auto. omega. } } Qed.

 Hint Resolve nil_is_MM_forB nil_is_MM_forA: core.

 
 Lemma produce_MM_is_matching(B: list Bid)(A: list Ask)(no_dup_B: NoDup B)(no_dup_A: NoDup A):
   Sorted by_dbp B -> Sorted by_dsp A -> matching_in B A (produce_MM B A).
 Proof. revert no_dup_A. induction B. intros. simpl. case A eqn: H1. simpl. eauto.
 simpl. eauto. intros. case A eqn: H2. simpl. eauto. simpl. 
 destruct (a0 <=? a) eqn: Ha. simpl. Admitted.
           
 Lemma produce_MM_is_MM (B: list Bid)(A: list Ask)(no_dup_B: NoDup B)(no_dup_A: NoDup A):
   Sorted by_dbp B -> Sorted by_dsp A-> Is_MM (produce_MM B A) B A.
Proof. revert B no_dup_B. induction A as [|a A'].
       { (* base case: when A is nil *)
         intros B hB H H0.  case B. simpl.
         { eauto. }
         { intros b l. simpl. eauto. } }
       { (* induction step: when A is a::A' *)
         intros B hB h h0. case B as [| b B'].
         { simpl. eauto. }
         { (*----- induction step : b::B'   and a:: A' ---------*)
           assert (Case: b < a \/ b >= a ). omega.
           destruct Case as [C1 | C2].
           { (*------C1:  when b and a are not matchable then produce_MM (b::B') A' *)
             simpl. replace (a <=? b) with false.
             Focus 2. symmetry. apply /leP. omega.
             assert (h1: Is_MM  (produce_MM (b::B') A') (b::B') A').
             { apply IHA'. all: eauto. }
             unfold Is_MM. split.
             { (*-- matching_in (b :: B') (a :: A') (produce_MM (b :: B') A') ---*)
               destruct h1 as [h1a h1]. eauto. }
             { intros M' h2. destruct h1 as [h1a h1].
               apply h1.
               (* --- Goal: matching_in (b :: B') A' M'---- trivial proof ---*)
               unfold matching_in. split.
               apply h2. split. apply h2.
               assert (h3: asks_of M' [<=] (a::A')). apply h2.
               intros x h4.
               assert (h5: In x (a::A')). auto. destruct h5.
               { subst x.
                 assert (h5: exists m, In m M' /\ a = ask_of m). auto.
                 destruct h5 as [m h5]. destruct h5 as [h5a h5].
                 assert (h6: a <= bid_of m).
                 { subst a. cut (matching M').
                   unfold matching. intro h6. destruct h6. auto.
                   apply h2. }
                 assert (h7:  In (bid_of m) (b::B')).
                 { cut (In (bid_of m) (bids_of M')).
                   cut ((bids_of M') [<=] (b::B')). auto.
                   apply h2. auto. } 
                 assert (h8: (bid_of m) <= b).
                 { assert (h9: by_dbp b (bid_of m)). eauto.
                   unfold by_dbp in h9. apply /leP. auto. }
                 omega. }
               { auto. }  } }
           
           { (*-- C2: when b and a are matchable then Output is (b,a):: produce_MM B' A'----*)
             assert (h1: matching_in (b::B') (a::A') (produce_MM (b::B') (a::A'))).
             { auto using produce_MM_is_matching. }
             unfold Is_MM. split. auto.
             simpl. replace (a <=? b) with true. Focus 2. symmetry. apply /leP. auto.
             intros M h2. simpl.
             assert (Hb: In b (bids_of M) \/ ~ In b (bids_of M)). eauto.
             assert (Ha: In a (asks_of M) \/ ~ In a (asks_of M)). eauto.
             assert (H0: Is_MM (produce_MM B' A') B' A').
             { apply IHA'. all: eauto. }
             destruct Hb as [Hb1 | Hb2]; destruct Ha as [Ha1 | Ha2].
             { (* Case_ab1: In b (bids_of M) and In a (asks_of M)------*)
               assert (h3: exists m1, In m1 M /\ a = ask_of m1). eauto.
               assert (h4: exists m2, In m2 M /\ b = bid_of m2). eauto.
               destruct h3 as [m1 h3]. destruct h3 as [h3a h3].
               destruct h4 as [m2 h4]. destruct h4 as [h4a h4].
               assert (h5: m1 = m2 \/ m1 <> m2). eauto.
               destruct h5 as [h5a | h5b].
               { (*-------- h5a : m1 = m2 ---------*)
                 subst m2. 
                 set (M' := delete m1 M). 
                 assert (h5: matching_in B' A' M').
                 { unfold matching_in. unfold M'. split.
                   { cut(matching M). auto.  apply h2. } split.
                   { intros x h5.
                     assert (h6: In x (b::B')).
                     { cut (In x (bids_of M)). apply h2.
                       cut ((delete m1 M) [<=] M). intro h6.
                       eapply bids_of_intro1. apply h6. all: auto. }
                     destruct h6 as [h6 | h6].
                     { absurd (In b (bids_of (delete m1 M))).
                       subst x. subst b. eauto. subst x;auto. }
                     { auto. } }
                    { intros x h5.
                     assert (h6: In x (a::A')).
                     { cut (In x (asks_of M)). apply h2.
                       cut ((delete m1 M) [<=] M). intro h6.
                       eapply asks_of_intro1. apply h6. all: auto. }
                     destruct h6 as [h6 | h6].
                     { absurd (In a (asks_of (delete m1 M))).
                       subst x. subst a. eauto. subst x;auto. }
                     { auto. } } }
                 assert (h6: |M| = S (|M'|)).
                 { unfold M'. eauto. }
                 assert (h7: |M'| <= |(produce_MM B' A')|). apply H0. exact.
                 omega. }
               
               { (*-------- h5b : m1 <> m2 ---------*)
                 set (M'' := delete m1 (delete m2 M)).
                 assert (h5: |M| = S (S (|M''|))).
                 { unfold M''.
                   assert (h3b: In m1 (delete m2 M)).
                   { auto. }
                   assert (h6: S (| delete m1 (delete m2 M) |) = |delete m2 M|).
                   { symmetry. auto. }
                   rewrite h6. auto. }  
                 set (m:= {|bid_of:= bid_of m1 ; ask_of:= ask_of m2 ; tp:=(bp (bid_of m1))|}).
                 set (M' := (m :: M'')).
                 
                 assert (h6: matching_in B' A' M').
                 { unfold matching_in. split.
                   { (*----- matching M' ---------------*)
                     unfold matching. split.
                     { unfold M'. cut (ask_of m <= bid_of m).
                       cut (All_matchable M''). auto.
                       unfold M''. cut (All_matchable M).
                       auto. eauto. simpl. cut (ask_of m2 <= ask_of m1).
                       cut (ask_of m1 <= bid_of m1). omega.
                       eauto. rewrite <- h3. cut (In (ask_of m2) (a::A')).
                       intro h6. assert(h7: by_dsp a (ask_of m2)). eauto.
                       unfold by_dsp in h7. apply /leP. auto.
                       eapply matching_in_elim5a. apply h2. auto. } split.
                     { (*---- NoDup (bids_of M') ----*)
                       unfold M'. simpl.
                       cut (~ In (bid_of m1) (bids_of M'')).
                       cut (NoDup (bids_of M'')). auto.
                       { (*--- NoDup (bids_of M'')---*)
                         cut (matching M''). auto.
                         unfold M''. eauto. }
                       { unfold M''. eauto. } }
                      { (*---- NoDup (asks_of M') ----*)
                       unfold M'. simpl.
                       cut (~ In (ask_of m2) (asks_of M'')).
                       cut (NoDup (asks_of M'')). auto.
                       { (*--- NoDup (asks_of M'')---*)
                         cut (matching M''). auto.
                         unfold M''. eauto. }
                       { unfold M''.
                         assert(h6:asks_of(delete m1 (delete m2 M))[<=]asks_of(delete m2 M)).
                         eauto. intro h7.
                         absurd (In (ask_of m2) (asks_of (delete m2 M))).
                         eauto. auto. } } } split. 
                   { (*----- bids_of M' [<=] B'-------------*)
                     unfold M'. simpl.
                     intros x h6. destruct h6 as [h6 | h6].
                     { cut (In x (b::B')). cut ( x <> b). eauto.
                       { subst x; subst b. eapply matching_elim14 with (M:= M).
                         all: auto. eauto. }
                       { subst x. eapply matching_in_elim4a. apply h2. auto. } }
                     { unfold M'' in h6.
                       assert (h7: In x (bids_of M)).
                       { eauto. }
                       assert (h8: x <> bid_of m2).
                       { intro h8. subst x.
                         assert (h9: In (bid_of m2) (bids_of (delete m2 M))).
                         eauto.
                         absurd (In (bid_of m2) (bids_of (delete m2 M))).
                         eauto. auto. } 
                       rewrite <- h4 in h8.
                       assert (h9: In x (b::B')).
                       { apply h2. auto. }
                       destruct h9. symmetry in H. contradiction. auto. } } 
                   { (*------ asks_of M' [<=] A' -------*)
                     unfold M'. simpl.
                     intros x h6. destruct h6 as [h6 | h6].
                     { cut (In x (a::A')). cut ( x <> a). eauto.
                       { subst x; subst a. eapply matching_elim15 with (M:= M).
                         all: auto. eauto. }
                       { subst x. eapply matching_in_elim5a. apply h2. auto. } }
                     { unfold M'' in h6.
                       assert (h7: In x (asks_of M)).
                       { eauto. } 
                       assert (h8: x <> ask_of m1).
                       { intro h8. subst x.
                         assert (h9: In (ask_of m1) (asks_of (delete m2 M))).
                         eauto.
                         absurd (In (ask_of m1) (asks_of (delete m1 (delete m2 M)))).
                         eauto. auto. }
                       rewrite <- h3 in h8.
                       assert (h9: In x (a::A')).
                       { apply h2. auto. }
                       destruct h9. symmetry in H. contradiction. auto. } } } 
                 
                 assert (h7: |M'| <= |(produce_MM B' A')|). apply H0. exact.
                 unfold M' in h7. simpl in h7. rewrite h5. simpl. omega. } }
             { (* Case_ab2: In b (bids_of M) and ~ In a (asks_of M)----*)
               assert (h3: exists m, In m M /\ b = bid_of m). eauto.
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
                   assert (h5a: In x (b::B')).
                   { apply h2. auto. }
                   assert (h6: x <> b).
                   { intro h6. unfold M' in h4.
                     subst x;subst b.
                     absurd (In (bid_of m) (bids_of (delete m M))).
                     eauto. auto. }
                   eapply in_inv2. all: eauto. }
                 { (*------ asks_of M' [<=] A'-------*)
                   intros x h4.
                   assert (h5: In x (asks_of M)).
                   { unfold M' in h4. eauto. }
                   assert (h6: x <> a).
                   { intro h6. subst x. contradiction. }
                   assert (h7: In x (a::A')).
                   { apply h2. auto. }
                   eapply in_inv2. all: eauto.  } }
               assert (h5: |M| = S (|M'|)).
               { unfold M'. eauto. }
               assert (h6: |M'| <= |(produce_MM B' A')|). apply H0. exact.
               omega. }
             { (* Case_ab3: ~ In b (bids_of M) and In a (asks_of M)----*)
               assert (h3: exists m, In m M /\ a = ask_of m). eauto.
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
                   assert (h6: x <> b).
                   { intro h6. subst x. contradiction. }
                   assert (h7: In x (b::B')).
                   { apply h2. auto. }
                   eapply in_inv2. all: eauto. }
                 { (*------ asks_of M' [<=] A'-------*)
                   intros x h4.
                   assert (h5: In x (asks_of M)).
                   { unfold M' in h4. eauto. }
                   assert (h5a: In x (a::A')).
                   { apply h2. auto. }
                   assert (h6: x <> a).
                   { intro h6. unfold M' in h4.
                     subst x;subst a.
                     absurd (In (ask_of m) (asks_of (delete m M))).
                     eauto. auto. }
                   eapply in_inv2. all: eauto. } } 
               assert (h5: |M| = S (|M'|)).
               { unfold M'. eauto. }
               assert (h6: |M'| <= |(produce_MM B' A')|). apply H0. exact.
               omega. }
             { (* Case_ab4: ~ In b (bids_of M) and ~ In a (asks_of M)---*)
               assert (h3: matching_in B' A' M). eauto using matching_in_elim8.
               cut (|M| <= | produce_MM B' A'|). omega. apply H0. exact. }   } } } Qed.
               

          
(*
Definition B2:= ({|b_id:= 1 ; bp:= 125 |}) ::({|b_id:= 2 ; bp:= 120 |}) ::({|b_id:= 3 ; bp:= 112 |}) ::({|b_id:= 4 ; bp:= 91 |}) ::({|b_id:= 5 ; bp:= 82 |}) ::({|b_id:= 6 ; bp:= 82 |}) ::({|b_id:= 7 ; bp:= 69 |}) ::({|b_id:= 8 ; bp:= 37 |}) :: nil.

Definition A2:= ({|s_id:= 1 ; sp:= 121 |}) ::({|s_id:= 3 ; sp:= 113 |}) ::({|s_id:= 5 ; sp:= 98 |}) ::({|s_id:= 9 ; sp:= 94 |}) ::({|s_id:= 90 ; sp:= 90 |}) ::({|s_id:= 78 ; sp:= 85 |}) ::({|s_id:= 67 ; sp:= 79 |}) ::({|s_id:= 45 ; sp:= 53 |}) ::nil.

*)

End MM.
