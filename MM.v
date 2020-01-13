




(* ---------------------------------------------------------------------------------------

   This file contains results of Maximum matchings. 
   The file contains a function produce_MM, which produces a maximum matching 
   from any list of bids B and list of asks A. We also prove that matching produced 
   by this function is largest in size as compared to any other possible matching
   on the same set of bids B and asks A.


Lemma produce_MM_is_MM: Sorted by_dbp B -> Sorted by_dsp A->  Is_MM (produce_MM B A) B A.

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

 Lemma produce_MM_bids_in_B(B: list Bid)(A: list Ask): bids_of (produce_MM B A) [<=] B.
 Proof. { revert B. induction A.
          { intros. simpl. case B eqn: H0. all:simpl;auto. }
          { intros. simpl. case B eqn: H0.
            { simpl;auto. }
            { destruct (a <=? b) eqn: Hab.
              { simpl. intros x H1.
                destruct H1 as [H1 | H1].
                subst b. auto. cut (In x l). auto.
                apply IHA. exact. }
              { apply IHA. } } } } Qed.

 Lemma produce_MM_asks_in_A (B: list Bid)(A: list Ask): asks_of (produce_MM B A) [<=] A.
 Proof. { revert B. induction A.
          { intros. simpl. case B eqn: H0. all:simpl;auto. }
          { intros. simpl. case B eqn: H0.
            { simpl;auto. }
            { destruct (a <=? b) eqn: Hab.
              { simpl. intros x H1.
                destruct H1 as [H1 | H1].
                subst a. auto. cut (In x A). auto.
                eapply IHA. exact H1. }
              { intros x H1. cut (In x A). auto. eapply IHA. exact H1. } } } } Qed.
 

 
 Lemma produce_MM_is_matching(B: list Bid)(A: list Ask)(no_dup_B: NoDup B)(no_dup_A: NoDup A):
   Sorted by_dbp B -> Sorted by_dsp A -> matching_in B A (produce_MM B A).
 Proof. { revert B no_dup_B. induction A as [| a].
          { intros. simpl.
            case B eqn: H1.
            { simpl. eauto. }
            { simpl. eauto. } }
          { intros.
            case B eqn: H2.
            { simpl. eauto. }
            { split.
              {(*--- matching (produce_MM (b :: l) (a :: A)) ----*)
                split.
                { (*--  All_matchable (produce_MM (b :: l) (a :: A))----*)
                  simpl.
                  destruct (a <=? b) eqn:Hab.
                  { apply All_matchable_intro. simpl. move /leP in Hab. exact.
                    cut (matching_in l A (produce_MM l A)).
                    intro H3. apply H3.
                    apply IHA. all: eauto. }
                  { cut (matching_in (b::l) A (produce_MM (b::l) A)).
                    intro H3. apply H3.
                    apply IHA. all: eauto. }  }
                split.
                { (*---- NoDup (bids_of (produce_MM (b :: l) (a :: A))) ---*)
                  simpl.
                  destruct (a <=? b) eqn:Hab.
                  { simpl. apply nodup_intro.
                    { intro H3.
                      assert (H4: In b l).  eapply produce_MM_bids_in_B. exact H3.
                      absurd (In b l). all: auto. }
                    { cut (matching_in l A (produce_MM l A)).
                      intro H3. apply H3.
                      apply IHA. all: eauto. } }
                  {  cut (matching_in (b::l) A (produce_MM (b::l) A)).
                      intro H3. apply H3.
                      apply IHA. all: eauto. }  }
                { (*-----  NoDup (asks_of (produce_MM (b :: B) (a :: l))) ----*)
                  simpl.
                  destruct (a <=? b) eqn:Hab.
                  { simpl. apply nodup_intro.
                    { intro H3.
                      assert (H4: In a A).  eapply produce_MM_asks_in_A. exact H3.
                      absurd (In a A). all: auto. }
                    { cut (matching_in l A (produce_MM l A)).
                      intro H3. apply H3.
                      apply IHA. all: eauto. } }
                  {  cut (matching_in (b::l) A (produce_MM (b::l) A)).
                      intro H3. apply H3.
                      apply IHA. all: eauto. }  } }
              split.
              { (*--- bids_of (produce_MM (b :: B) (a :: l)) [<=] b :: B  --*)
                  eapply produce_MM_bids_in_B. }
              { (*---- asks_of (produce_MM (b :: B) (a :: l)) [<=] a :: l--- *)
                eapply produce_MM_asks_in_A. } } } } Qed.
 
           
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
             2:{ symmetry. apply /leP. omega. }
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
                 { assert (h9: by_dbp b (bid_of m)). eapply Sorted_elim2. auto.
                   exact h. exact h7. 
                   unfold by_dbp in h9. apply /leP. auto. }
                 omega. }
               { auto. }  } }
           
           { (*-- C2: when b and a are matchable then Output is (b,a):: produce_MM B' A'----*)
             assert (h1: matching_in (b::B') (a::A') (produce_MM (b::B') (a::A'))).
             { auto using produce_MM_is_matching. }
             unfold Is_MM. split. auto.
             simpl. replace (a <=? b) with true. 2:{ symmetry. apply /leP. auto. }
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
                 { unfold M'.  eapply delete_size1a. exact. }
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
                       intro h6. assert(h7: by_dsp a (ask_of m2)). eapply Sorted_elim2.
                       auto. exact h0. exact h6.
                       unfold by_dsp in h7. apply /leP. auto.
                       eapply matching_in_elim5a. apply h2. auto. } split.
                     { (*---- NoDup (bids_of M') ----*)
                       unfold M'. simpl.
                       cut (~ In (bid_of m1) (bids_of M'')).
                       cut (NoDup (bids_of M'')). auto.
                       { (*--- NoDup (bids_of M'')---*)
                         cut (matching M''). auto.
                         unfold M''. eauto. }
                       { unfold M''. apply matching_elim10. apply matching_elim9. 
                       eapply matching_in_elim0. exact h2. apply delete_intro.
                       exact h3a. exact h5b. } }
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
                         apply matching_elim11. eapply matching_in_elim0. exact h2. 
                         exact h4a. auto. } } } split. 
                   { (*----- bids_of M' [<=] B'-------------*)
                     unfold M'. simpl.
                     intros x h6. destruct h6 as [h6 | h6].
                     { cut (In x (b::B')). cut ( x <> b). intros. apply element_list with
                     (b:=x)(a:=b). auto. exact.
                       { subst x; subst b. eapply matching_elim14 with (M:= M).
                         all: auto. eauto. }
                       { subst x. eapply matching_in_elim4a. apply h2. auto. } }
                     { unfold M'' in h6.
                       assert (h7: In x (bids_of M)).
                       { eauto. }
                       assert (h8: x <> bid_of m2).
                       { intro h8. subst x.
                         assert (h9: In (bid_of m2) (bids_of (delete m2 M))).
                         eapply bids_of_elim1. exact h6.
                         absurd (In (bid_of m2) (bids_of (delete m2 M))).
                         apply matching_elim10. eapply matching_in_elim0.
                         exact h2. exact h4a. auto. } 
                       rewrite <- h4 in h8.
                       assert (h9: In x (b::B')).
                       { apply h2. auto. }
                       destruct h9. symmetry in H. contradiction. auto. } } 
                   { (*------ asks_of M' [<=] A' -------*)
                     unfold M'. simpl.
                     intros x h6. destruct h6 as [h6 | h6].
                     { cut (In x (a::A')). cut ( x <> a). intros. eapply element_list.
                       apply not_eq_sym ; trivial. exact H. exact H1.
                       { subst x; subst a. eapply matching_elim15 with (M:= M).
                         all: auto. eauto. }
                       { subst x. eapply matching_in_elim5a. apply h2. auto. } }
                     { unfold M'' in h6.
                       assert (h7: In x (asks_of M)).
                       { eauto. } 
                       assert (h8: x <> ask_of m1).
                       { intro h8. subst x.
                         assert (h9: In (ask_of m1) (asks_of (delete m2 M))).
                         apply asks_of_intro. apply delete_intro. exact h3a. exact h5b.
                         absurd (In (ask_of m1) (asks_of (delete m1 (delete m2 M)))).
                         apply matching_elim11. apply matching_elim9. 
                         eapply matching_in_elim0. exact h2. apply delete_intro.
                         exact h3a. exact h5b. auto. }
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
                     apply matching_elim10. eapply matching_in_elim0. 
                     exact h2. exact h3a. auto. }
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
               { unfold M'. eapply delete_size1a. exact h3a. }
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
                     apply matching_elim11. eapply matching_in_elim0. 
                     exact h2. exact h3a. auto. }
                   eapply in_inv2. all: eauto. } } 
               assert (h5: |M| = S (|M'|)).
               { unfold M'. eapply delete_size1a.  exact h3a. }
               assert (h6: |M'| <= |(produce_MM B' A')|). apply H0. exact.
               omega. }
             { (* Case_ab4: ~ In b (bids_of M) and ~ In a (asks_of M)---*)
               assert (h3: matching_in B' A' M). eauto using matching_in_elim8.
               cut (|M| <= | produce_MM B' A'|). omega. apply H0. exact. }   } } } Qed.
               
Theorem exists_fair_maximum (B: list Bid)(A: list Ask) (Nb: NoDup B) (Na: NoDup A):
  exists M, (Is_fair M B A /\ Is_MM M B A).
Proof. { set (M:= produce_MM (sort by_dbp B) (sort by_dsp A)).
         assert (H1: Is_MM M (sort by_dbp B) (sort by_dsp A)).
         { apply produce_MM_is_MM. all: eauto. 
           apply sort_correct;eapply by_dbp_P. 
           apply sort_correct;eapply by_dsp_P. }
         assert (H2: Is_MM M B A).
         { destruct H1 as [H1 H2].
           split.
           { eapply match_inv with (M:= M)(B:= (sort by_dbp B)) (A:=(sort by_dsp A)).
             all: eauto. }
           { intros M' H3. apply H2.
             eapply match_inv with (M:= M')(B:= B) (A:= A). all: eauto. } }
         
         assert (H3: matching_in B A M). apply H2. 
         apply (exists_fair_matching M B A Nb Na) in H3 as H4.
         destruct H4 as [M' H4].
         exists M'.
         split.
         { apply H4. }
         { unfold Is_MM.
           destruct H4 as [H4a H4]. destruct H4 as [H4b H4].
           split.
           exact.
           intros M0 H5. rewrite <- H4.
           apply H2. exact. } } Qed.
         
        
          
(*
Definition B2:= ({|b_id:= 1 ; bp:= 125 |}) ::({|b_id:= 2 ; bp:= 120 |}) ::({|b_id:= 3 ; bp:= 112 |}) ::({|b_id:= 4 ; bp:= 91 |}) ::({|b_id:= 5 ; bp:= 82 |}) ::({|b_id:= 6 ; bp:= 82 |}) ::({|b_id:= 7 ; bp:= 69 |}) ::({|b_id:= 8 ; bp:= 37 |}) :: nil.

Definition A2:= ({|s_id:= 1 ; sp:= 121 |}) ::({|s_id:= 3 ; sp:= 113 |}) ::({|s_id:= 5 ; sp:= 98 |}) ::({|s_id:= 9 ; sp:= 94 |}) ::({|s_id:= 90 ; sp:= 90 |}) ::({|s_id:= 78 ; sp:= 85 |}) ::({|s_id:= 67 ; sp:= 79 |}) ::({|s_id:= 45 ; sp:= 53 |}) ::nil.

 *)



End MM.
