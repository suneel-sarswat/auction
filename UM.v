



(* ---------------------------------------------------------------------------------

     This file contains results of Uniform matchings. function produce_UM, which 
     produces a uniform matching from any list of bids B and list of aks A. 
     We prove that matching produced by this function is largest among 
     all possible uniform matching on B and A. We also prove that matching 
     produced is IR and uniform.

Important results:

Theorem UM_is_maximal_Uniform: Sorted by_dbp B -> Sorted by_sp A-> 
(forall M: list fill_type, Is_uniform M B A-> |M| <= | (produce_UM B A ) |).

------------------------------------------------------------------------------------*)



Require Import ssreflect ssrbool. 
Require Export Lists.List.

Require Export GenReflect SetSpecs.

Require Export Sorting MinMax.
Require Export BidAsk.
Require Export DecList.
Require Export MoreDecList.
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
Proof. { intros m. revert A. induction B. simpl. auto. intro A.
         induction A. simpl. auto. simpl. intro H1. 
         destruct (a0 <=? a) eqn: H2. destruct H1.
         subst m. unfold bid_of. unfold ask_of. move /eqP in H2.  
         move /eqP in H2.  move /leP in H2. auto. 
         move /leP in H2. eapply IHB. exact H. inversion H1. }  Qed.
   
Lemma UP_is_matching (B: list Bid) (A: list Ask) (NDB: NoDup B) (NDA: NoDup A):
  Sorted by_dbp B -> Sorted by_sp A -> matching_in B A (produce_UM B A).
 Proof. { revert B NDB. induction A. 
          { case B eqn: H1. simpl. auto. simpl. auto. }  
          { case B eqn:H1. simpl. auto. 
            intros H2 H3 H4. simpl. destruct (a <=? b) eqn:Hab. 
            assert (Hm:matching_in l A (produce_UM l A)). 
            { eapply IHA with (B:=l). eauto. subst B. eauto. subst B. eauto. eauto. }
            eapply matching_in_intro.
            { simpl. move /leP in Hab. exact Hab. }
            { eauto. }
            { simpl. intro H5. assert (Hl:In b l). subst B. unfold matching_in in Hm.
              destruct Hm as [Hm1 Hm]. destruct Hm as [Hm2 Hm].  eauto. absurd (In b l).
              all:auto.
            } 
            { simpl. intro H5. assert (Hl:In a A). unfold matching_in in Hm.
              destruct Hm as [Hm1 Hm]. destruct Hm as [Hm2 Hm].  eauto. absurd (In a A).
              all:auto.
            } simpl. left;auto. simpl. left;auto.
            auto. } } Qed.
 

 
Lemma produce_UM_bids_sublist_B(B: list Bid)(A: list Ask): sublist (bids_of (produce_UM B A)) B.
 Proof. { revert B. induction A.
          { intros. simpl. case B eqn: H0. all:simpl;auto. }
          { intros. simpl. case B eqn: H0.
            { simpl;auto. }
            { destruct (a <=? b) eqn: Hab.
              { simpl. rewrite Hab. simpl.
                case (b_eqb b b) eqn: Hbb. 
                 { apply IHA. }
                 { unfold b_eqb in Hbb. move /andP in Hbb. destruct Hbb. auto. } }
              { simpl. rewrite Hab. simpl. auto. } } } } Qed.

Lemma produce_UM_asks_sublist_A(B: list Bid)(A: list Ask): sublist (asks_of (produce_UM B A)) A.
 Proof. { revert B. induction A.
          { intros. simpl. case B eqn: H0. all:simpl;auto. }
          { intros. simpl. case B eqn: H0.
            { simpl;auto. }
            { destruct (a <=? b) eqn: Hab.
              { simpl. rewrite Hab. simpl.
                case (a_eqb a a) eqn: Haa. 
                 { apply IHA. }
                 { unfold b_eqb in Haa. move /andP in Haa. destruct Haa. auto. } }
              { simpl. rewrite Hab. simpl. auto. } } } } Qed.

Lemma bids_of_UM_sorted (B: list Bid) (A: list Ask) :
  (Sorted by_dbp B -> (Sorted by_dbp (bids_of (produce_UM B A)))).
Proof. { assert (H0:sublist (bids_of (produce_UM B A)) B). apply produce_UM_bids_sublist_B.
intros. eapply sublist_is_sorted with (lr:=by_dbp) (s:=B). exact. exact. } Qed.



Lemma asks_of_UM_sorted (B: list Bid) (A: list Ask) :
    (Sorted by_sp A -> (Sorted by_sp (asks_of (produce_UM B A)))).
Proof. { assert (H0:sublist (asks_of (produce_UM B A)) A). apply produce_UM_asks_sublist_A.
intros. eapply sublist_is_sorted with (lr:=by_sp) (s:=A). exact. exact. } Qed.


Lemma last_in_tail (A:Type): forall l:list A, forall a b d:A, 
(last (a::b::l) d) = (last (b::l) d).
Proof. intros. eauto. Qed.
 
 

(*--------------------------------------------------------*)

Lemma bid_of_last_and_last_of_bids (F: list fill_type)  (b : Bid):
(bid_of (last F m0)) = (last (bids_of F) b0).
Proof.  
induction F as [|m'].  simpl.  auto.  { 
case F eqn:H1. simpl. auto. replace (last (m' :: f :: l) m0) with (last (f :: l) m0). unfold asks_of;fold asks_of. replace
 (last (ask_of m' :: ask_of f :: asks_of l) a0) with
 (last (ask_of f :: asks_of l) a0). exact. symmetry.
 eapply last_in_tail. symmetry. eapply last_in_tail. } Qed.

 
Lemma ask_of_last_and_last_of_asks (F: list fill_type) (a: Ask):
  (ask_of (last F m0)) = (last (asks_of F) a0).
Proof. 

induction F as [|m'].  simpl.  auto.  {
case F eqn:H1. simpl. auto. replace (last (m' :: f :: l) m0) with (last (f :: l) m0). unfold asks_of;fold asks_of. replace
 (last (ask_of m' :: ask_of f :: asks_of l) a0) with
 (last (ask_of f :: asks_of l) a0). exact. symmetry.
 eapply last_in_tail. symmetry. eapply last_in_tail. } Qed.




Lemma UM_returns_IR (B: list Bid) (A: list Ask) (NDB: NoDup B) (NDA: NoDup A):
 Sorted by_dbp B -> Sorted by_sp A -> forall m, In m (produce_UM B A) ->
   (bp (bid_of m))>= (tp m)  /\ (sp (ask_of m)) <= (tp m).
Proof.  { revert NDA. revert A. induction B. intros. split. simpl in H1.
          destruct H1. simpl in H1. destruct H1. intros.
          case A eqn: Ha. simpl in H1. destruct H1.
          simpl in H1.  case (a0 <=? a) eqn: Ha0. simpl in H1.
          destruct H1. subst m. move /leP in Ha0. simpl. eauto. eapply IHB in H1.
          exact. eauto. eauto. eauto. eauto. destruct H1. } Qed.
 
Fixpoint replace_column (l:list fill_type)(n:nat):=
  match l with
  |nil=>nil
  |m::l'=> ({|bid_of:= bid_of m ; ask_of:= ask_of m ; tp:=n|})::(replace_column l' n)
  end.

Lemma replace_column_is_uniform (l: list fill_type)(n:nat):
  uniform (trade_prices_of (replace_column l n)).
Proof. { induction l. simpl.  constructor.
         case l eqn: H. simpl.  constructor. simpl. simpl in IHl. constructor;auto. } Qed.

Lemma last_column_is_trade_price (l:list fill_type)(m:fill_type)(n:nat): In m (replace_column l n)->
                                                                  (tp m = n).
Proof. { intro H. induction l. auto. inversion H as [H0 |].  
         inversion H0 as [H1 ]. simpl. exact. apply IHl in H0. exact. } Qed.

Lemma replace_column_elim (l: list fill_type)(n:nat): forall m', In m' (replace_column l n)-> exists m, In m l /\ bid_of m = bid_of m' 
/\ ask_of m = ask_of m'.
  Proof. { intros m' H. induction l. 
           { simpl in H. inversion H. }
           { simpl in H. destruct H.
             {  exists a. split. auto. split. subst m'. simpl. auto. subst m'. simpl. auto. }
             { apply IHl in H as H1. destruct H1 as [m H1]. exists m. 
               destruct H1 as [H2 H1]. destruct H1 as [H3 H1]. split.
               auto. split;auto. } } } Qed. 
  


Definition uniform_price B A := bp (bid_of (last (produce_UM B A) m0)).



Lemma uniform_price_bid (B: list Bid) (A:list Ask) (b: Bid)  : Sorted by_dbp (B) -> Sorted by_sp (A) -> In b (bids_of (produce_UM B A)) ->
  b >=(uniform_price B A).
Proof. { intros H1 H2 H3. unfold uniform_price.
         eapply bids_of_UM_sorted  with (A:=A) in H1 as H4 . 
         assert (H5: by_dbp b (bid_of (last (produce_UM B A) m0))).
         assert (Hlastb: last (bids_of (produce_UM B A)) b0 = bid_of (last (produce_UM B A) m0)).
         symmetry. eapply bid_of_last_and_last_of_bids with (F:= ((produce_UM B A))). auto. rewrite <- Hlastb.
         eapply last_in_Sorted. exact H4. auto.
         unfold by_dbp in H5. move /leP in H5. auto. } Qed.
  
Lemma produce_UM_bids_ge_asks (B: list Bid) (A:list Ask) (m: fill_type):
In m (produce_UM B A) -> (bid_of  m) >= (ask_of m).
Proof. { revert B m. induction A. 
{ intros. case B eqn: HB. 
 { simpl in H. destruct H. }
 { simpl in H. destruct H. } }
 { intros B m H0. case B eqn: HB.
 { simpl in H0. destruct H0. }
 { simpl in H0. case (a <=? b) eqn: Hab.
 { destruct H0. 
  { subst m. simpl. move /leP in Hab. auto. }
  { eapply IHA. exact H. } }
 { destruct H0. } } } }  Qed.

(*Move below lemma to DecList *)


Lemma last_in_list (T:Type)(l:list T)(x:T)(d:T) : In x l -> In (last l d) l.
Proof. { revert x d. 
         induction l as [| a l'].
         { (*------ l = nil ------*) 
           simpl. auto. }
         { (*------ l = a::l'-----*)
           destruct l' as [| b l'']. 
           { (*----- l = [a]------*)
            simpl. intros; left;auto. }
           { (*------ l = a ::b::l'' --------*) 
             intros x d H0.
             assert (H1: last (a::b::l'') d = last (b::l'') d).
             { simpl. destruct l'';auto. }
             rewrite H1.
             cut(In (last (b :: l'') d) (b :: l'')). auto.
             eapply IHl' with (x:=b). auto. } } } Qed.

Lemma uniform_price_ask (B: list Bid) (A:list Ask) (a: Ask):
  Sorted by_dbp B -> Sorted by_sp (A) -> In a (asks_of (produce_UM B A))-> a <= (uniform_price B A).
Proof. { intros H1 H2 H3. unfold uniform_price.
         eapply asks_of_UM_sorted  with (B:=B) in H2 as H4. 
         eapply bids_of_UM_sorted  with (A:=A) in H1 as H4b.
         assert (H5: by_sp a (ask_of (last (produce_UM B A) m0))).
         assert (Hlasta: last (asks_of (produce_UM B A)) a0 = ask_of (last (produce_UM B A) m0)).
         symmetry.  eapply ask_of_last_and_last_of_asks. auto. auto.
         rewrite <- Hlasta.
         eapply last_in_Sorted. exact H4. auto. unfold by_sp in H5. move /leP in H5. 
         assert (H6: bid_of (last (produce_UM B A) m0) >= ask_of (last (produce_UM B A) m0)). 
        { apply produce_UM_bids_ge_asks with (B:=B) (A:=A). 
          assert (Hma: exists m, In m (produce_UM B A) /\ a = ask_of m).
          eauto. destruct Hma as [m Hma].
          apply last_in_list with (x:=m). apply Hma. } 
          { assert (Hma: exists m, In m (produce_UM B A) /\ a = ask_of m).
          eauto. destruct Hma as [m Hma]. omega. } } Qed.

Definition UM (B:list Bid) (A:list Ask) : (list fill_type) :=
  replace_column (produce_UM B A)
                (uniform_price B A).


(*

Theorem UM_is_Ind_Rat (B: list Bid) (A:list Ask):
  Sorted by_dbp B -> Sorted by_sp A -> Is_IR (UM B A).
Proof. {  intros H1 H2. unfold UM. unfold Is_IR.
          intros m H3. unfold rational. split. 
          assert (H4: tp m = (uniform_price B A)).  
          eapply last_column_is_trade_price. exact H3.
          rewrite  H4. eapply replace_column_elim in H3 as H5. 
          eapply bids_of_UM_sorted with (A:=A) in H1  as H6. 
          unfold uniform_price. admit. admit. }  Admitted.
*)

(*
revert B. induction A. { case B eqn:HB. 
{ unfold UM. simpl. unfold Is_IR. intros H1 H2 H3 H4. inversion H4. }
{ unfold UM. simpl. unfold Is_IR. intros H1 H2 H3 H4. inversion H4. } }
{ case B eqn:HB. 
{ unfold UM. simpl. unfold Is_IR. intros H1 H2 H3 H4. inversion H4. }
{ unfold UM. simpl. intros H1 H2. destruct (a <=? b) eqn: Hab.
{ simpl. unfold Is_IR. intros m H3. destruct H3 eqn: Hm. subst m.
unfold rational. simpl. split.   unfold uniform_price.
*)
 
Theorem UM_is_Uniform (B: list Bid) (A:list Ask) : Uniform ( UM B A).
Proof.  unfold Uniform. unfold UM. apply replace_column_is_uniform. Qed.

Definition Is_uniform M B A := (Uniform M /\ matching_in B A M /\ Is_IR M).

Lemma matching_on_nilA (B:list Bid) (M:list fill_type) : matching_in B nil M -> M=nil.
Proof. { intros H1. unfold matching_in in H1. destruct H1 as [H1 H2].
         destruct H2 as [H2 H3]. unfold matching in H1. destruct H1 as [H1 H4]. 
         unfold All_matchable in H1. assert (HAMnil: (asks_of M) = nil). eauto.
         case M eqn: HM. auto. simpl in HAMnil. inversion HAMnil. } Qed.

Lemma matching_on_nilB (A: list Ask)(M:list fill_type) : matching_in nil A M -> M=nil.
Proof. { intros H1. unfold matching_in in H1. destruct H1 as [H1 H2].
         destruct H2 as [H2 H3]. unfold matching in H1. destruct H1 as [H1 H4]. 
         unfold All_matchable in H1. assert (HBMnil: (bids_of M) = nil). eauto.
         case M eqn: HM. auto. simpl in HBMnil. inversion HBMnil. } Qed.

Lemma unmatchableAB_nil (B:list Bid) (A:list Ask) (b:Bid)(a:Ask) (M:list fill_type): Sorted by_dbp (b::B) -> Sorted by_sp (a::A) ->matching_in (b::B) (a::A) M -> b<a-> M=nil.
Proof. { intros H1 H2 H3 H4.
         case M as [|f  M'] eqn:HM.
         { auto. }
         { set (b0:= bid_of f). set (a0:= ask_of f).
           assert (Hfask: In (ask_of f) (a::A)). 
           { eapply matching_in_elim5. exact H3. }
           assert (Hfbid: In (bid_of f) (b::B)). 
           { eapply matching_in_elim4.  exact H3. }
           assert (Hmatch: bid_of f >= ask_of f). eauto.
           assert (h1: by_dbp b b0). 
           { unfold b0. eauto. }
           move /leP in h1. unfold b0 in h1. 
           assert (h2: by_sp a a0). 
           { unfold a0. eauto. }
           move /leP in h2. unfold a0 in h2. omega. } } Qed.

Lemma delete_IR_is_IR (M : list fill_type) (m:fill_type): Is_IR M -> Is_IR (delete m M).
Proof. unfold Is_IR. eauto. Qed. 

Lemma IR_UM_matchable (M:list fill_type)(b:Bid)(a:Ask):
  Is_IR M -> Uniform M -> In a (asks_of M) -> In b (bids_of M)->b>=a.
Proof. { intros H1 H2 Ha Hb.
         assert (Hm1: exists m1, (In m1 M) /\ a=(ask_of m1)). 
         eauto. assert (Hm2: exists m2, (In m2 M) /\ b=(bid_of m2)). 
         eauto. destruct Hm1 as [m1 Hm1]. destruct Hm2 as [m2 Hm2]. 
         assert (Ht:tp m1 = tp m2).
         destruct Hm1 as [Hm1m Hm1a]. destruct Hm2 as [Hm2m Hm2b].
         eapply Uniform_elim. eauto. all: auto. assert (Hbm: b>= tp m2).
         { destruct Hm1 as [Hm1m Hm1a]. destruct Hm2 as [Hm2m Hm2b]. subst b.
           eapply H1. exact. } assert (Ham: a<= tp m1). 
         { destruct Hm1 as [Hm1m Hm1a]. destruct Hm2 as [Hm2m Hm2b]. subst a.
           eapply H1. exact. } omega. } Qed.



Lemma M'_unifom_ir (M : list fill_type) (m1 m2: fill_type):
(Is_IR M /\ Uniform M) -> In m1 M -> In m2 M -> 
Is_IR (({|bid_of:= bid_of m1 ; ask_of:= ask_of m2 ; tp:=(tp m1)|}::delete m1 (delete m2 M))) /\
Uniform (({|bid_of:= bid_of m1 ; ask_of:= ask_of m2 ; tp:=(tp m1)|}::delete m1 (delete m2 M))).
Proof. { intros H0 H1 H2.
         split.
         { destruct H0 as [H0ir H0uni].
           set (M'':= delete m1 (delete m2 M)). assert (H_irM'':Is_IR M'').
           { subst M''. unfold Is_IR. intros. apply H0ir. eapply delete_elim1.
             simple eapply delete_elim1. exact H. }
           { assert (Htp: tp m1 = tp m2).
             eauto.
             assert (Hrationalm2: rational m2).
             eauto. unfold rational in Hrationalm2. 
             assert (Htpm2: tp m2 >= ask_of m2). eapply Hrationalm2. 
             set (m:={| bid_of := bid_of m1; ask_of := ask_of m2; tp := tp m1 |}).
             assert (mrat:rational m).
             { unfold rational. subst m.  simpl.
               assert (Hrationalm1: rational m1). eauto.
               unfold rational in Hrationalm1. 
               assert (Htpm1: bid_of m1 >= tp m1). eapply Hrationalm1.
               split. eauto. omega. } eauto. } }
         { destruct H0 as [H0ir H0uni].  
           set (M'':= delete m1 (delete m2 M)). assert (H_uniM'':Uniform M'').
           subst M''. eauto. case M'' eqn: HM''. constructor. 
           assert (HeM'': In e M''). rewrite HM''. auto. assert (HeM: In e M).
           eapply delete_elim1. eapply delete_elim1. exact HeM''.
           assert (H_e: tp e = tp m1).
           eapply Uniform_elim. exact H0uni.
           exact HeM. exact H1. rewrite <- H_e. eauto. } } Qed. 

 
                 
                 

Lemma IR_UM_matchable_m (M:list fill_type)(m1 m2:fill_type):
  Is_IR M -> Uniform M -> In m1 M -> In m2 M-> bid_of m1 >=ask_of m2. 
Proof. { intros H1 H2 H3 H4. assert (Htp: tp m1 = tp m2). eauto.
         assert (Htpm1b: tp m1 <= bid_of m1). 
         { unfold Is_IR in H1. unfold rational in H1. eapply H1. exact. }
         assert (Htpm1a: tp m1 >= ask_of m1). 
         { unfold Is_IR in H1. unfold rational in H1. eapply H1. exact. }
         assert (Htpm2b: tp m2 <= bid_of m2). 
         { unfold Is_IR in H1. unfold rational in H1. eapply H1. exact. }
         assert (Htpm2a: tp m2 >= ask_of m2). 
         { unfold Is_IR in H1. unfold rational in H1. eapply H1. exact. }
         omega. } Qed. 

Theorem UM_is_maximal_Uniform (B: list Bid) (A:list Ask)(no_dup_B: NoDup B)(no_dup_A: NoDup A): Sorted by_dbp B -> Sorted by_sp A-> (forall M: list fill_type, Is_uniform M B A-> |M| <= | (produce_UM B A ) |).

Proof. revert B no_dup_B. induction A as [|a A'].
       { (* base case: when A is nil *)
         intros B hB H H0.  case B. simpl.
         { intros M H1. destruct H1 as [H1 H2].
           destruct H2 as [H2 H3]. apply matching_on_nilA in H2. subst M. auto. }
         { intros b l. simpl. intros M H1. destruct H1 as [H1 H2].
           destruct H2 as [H2 H3]. apply matching_on_nilA in H2. subst M. auto. } }
       { (* induction step: when A is a::A' *)
         intros B hB h h0. case B as [| b B'].
         { simpl. intros M H1.  destruct H1 as [H1 H2]. destruct H2 as [H2 H3].
           apply matching_on_nilB in H2. subst M. auto. }
         { (*----- induction step : b::B'   and a:: A' ---------*)
           assert (Case: b < a \/ b >= a ). omega.
           destruct Case as [C1 | C2].
                      { (*------C1:  when b and a are not matchable then produce_MM (b::B') A' *)
             simpl. replace (a <=? b) with false.
             Focus 2. symmetry. apply /leP. omega. intros M H1.
             destruct H1 as [H1 H2]. destruct H2 as [H2 H3]. 
             assert (HM:M=nil). eapply unmatchableAB_nil.
             eauto. eauto. eauto. exact. subst M. auto. }
             { (*-- C2: when b and a are matchable then Output is (b,a):: produce_MM B' A'----*)
               assert (h1: matching_in (b::B') (a::A') (produce_UM (b::B') (a::A'))).
               {eauto using UP_is_matching. }
             intros M h2. destruct h2 as [h2a h2]. destruct h2 as [h2 h2b]. 
              simpl. replace (a <=? b) with true.
             
             Focus 2. symmetry. apply /leP. auto.
             assert (Hb: In b (bids_of M) \/ ~ In b (bids_of M)). eauto.
             assert (Ha: In a (asks_of M) \/ ~ In a (asks_of M)). eauto.
             assert (H0: forall M, Is_uniform M B' A' -> |M| <= |(produce_UM B' A')|).
            
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
                     assert (h5_ir: Is_IR M'). 
                     {eapply delete_IR_is_IR. exact. }
                     assert (h5_unif: Uniform M').
                     { subst M'. eauto. }
                     assert (h5_is_uni:Is_uniform M' B' A').
                     {unfold Is_uniform. eauto. }
                 assert (h6: |M| = S (|M'|)).
                 { unfold M'. eauto. }
                 assert (h7: |M'| <= |(produce_UM B' A')|). apply H0. exact.
                 simpl. omega. }
                                { (*-------- h5b : m1 <> m2 ---------*)
                 set (M'' := delete m1 (delete m2 M)).
                 assert (h5: |M| = S (S (|M''|))).
                 { unfold M''.
                   assert (h3b: In m1 (delete m2 M)).
                   { auto. }
                   assert (h6: S (| delete m1 (delete m2 M) |) = |delete m2 M|).
                   { symmetry. auto. }
                   rewrite h6. auto. }  
                 set (m:= {|bid_of:= bid_of m1 ; ask_of:= ask_of m2 ; tp:=(tp m1)|}).
                 set (M' := (m :: M'')).
                 
                 assert (h6: matching_in B' A' M').
                  { unfold matching_in. split.
                   { (*----- matching M' ---------------*)
                     unfold matching. split.
                     { unfold M'. cut (ask_of m <= bid_of m).
                       cut (All_matchable M''). auto.
                       unfold M''. cut (All_matchable M).
                       auto. eauto. set t:=tp m1.
                       assert (h_t1:bid_of m1 >=t). 
                       { subst t. assert ( Hrationalm1:rational m1). eauto.
                       unfold rational in Hrationalm1. apply Hrationalm1. }
                       assert (h_t2: t>=ask_of m2).
                       { subst t. assert ( Hrationalm2:rational m2). eauto.
                         unfold rational in Hrationalm2.
                         assert (Htpm1m2: tp m1 = tp m2).
                         eauto. rewrite Htpm1m2. apply Hrationalm2. }
                       simpl. omega. } split.
                     { (*---- NoDup (bids_of M') ----*)
                       unfold M'. simpl.
                       cut (~ In (bid_of m1) (bids_of M'')).
                       cut (NoDup (bids_of M'')). auto.
                       { (*--- NoDup (bids_of M'')---*)
                         cut (matching M''). auto.
                         unfold M''. eauto. }
                       { unfold M''.
                         { apply matching_elim10. apply matching_elim9.
                           eapply matching_in_elim0. exact h2.
                           apply delete_intro. exact. exact. }  } }
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
                         simple apply matching_elim11. simple eapply matching_in_elim0.
                         exact h2. exact. auto. } } } split. 
                   { (*----- bids_of M' [<=] B'-------------*)
                     unfold M'. simpl.
                     intros x h6. destruct h6 as [h6 | h6].
                     { cut (In x (b::B')). cut ( x <> b). 
                     { intros H H1. eapply in_inv2. exact H1. exact H. }
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
                     { cut (In x (a::A')). cut ( x <> a). 
                      { intros H H1. eapply in_inv2. exact H1. exact H. }
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
                         { apply matching_elim11. apply matching_elim9. 
                         eapply matching_in_elim0. exact h2. 
                         apply delete_intro. exact h3a. exact h5b. } auto. }
                       rewrite <- h3 in h8.
                       assert (h9: In x (a::A')).
                       { apply h2. auto. }
                       destruct h9. symmetry in H. contradiction. auto. } } }          

                     assert (h5_is_uni: (Is_IR M') /\ (Uniform M')).
                     subst M'. subst M''. subst m. 
                     assert (h_temp1: (Is_IR M /\ Uniform M) ). auto. 
                     eapply M'_unifom_ir with 
                     (M:=M) (m1:=m1) (m2:=m2). exact. exact. exact.
                      
                       assert (h5_ir: Is_IR M'). 
                     { apply h5_is_uni.  }
                       assert (h5_unif: Uniform M'). 
                     { apply h5_is_uni.  }
                      (*continue from here*) 
                    
                     assert (h5_is_unif:Is_uniform M' B' A').
                     {unfold Is_uniform. eauto. }
                     
             assert (h7: |M'| <= |(produce_UM B' A')|). apply H0. exact.
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
                     { apply matching_elim10. eapply matching_in_elim0.
                      exact h2. exact h3a. } auto. }
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
                assert (h5_ir: Is_IR M'). 
                     { subst M'. eapply Is_IR_elim2. exact. }
                     assert (h5_unif: Uniform M').
                     { subst M'.  eauto. }
                     assert (h5_is_uni:Is_uniform M' B' A').
                     {unfold Is_uniform. eauto. }
               assert (h6: |M'| <= |(produce_UM B' A')|). apply H0. exact.
               simpl. omega. }
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
                     { apply matching_elim11. eapply matching_in_elim0. 
                     exact h2. exact h3a. } auto. }
                   eapply in_inv2. all: eauto. } } 
               assert (h5: |M| = S (|M'|)).
               { unfold M'. eauto. }
                assert (h5_ir: Is_IR M'). 
                     { subst M'. eapply Is_IR_elim2. exact. }
                     assert (h5_unif: Uniform M').
                     { subst M'. eauto. }
                     assert (h5_is_uni:Is_uniform M' B' A').
                     {unfold Is_uniform. eauto. }
               assert (h6: |M'| <= |(produce_UM B' A')|). apply H0. exact.
               simpl. omega. }
             { (* Case_ab4: ~ In b (bids_of M) and ~ In a (asks_of M)---*)
               assert (h3: matching_in B' A' M). eauto using matching_in_elim8.
                assert (h5_ir: Is_IR M). 
                     { exact. }
                     assert (h5_unif: Uniform M).
                     {exact. }
                     assert (h5_is_uni:Is_uniform M B' A').
                     {unfold Is_uniform. eauto. }
               cut (|M| <= | produce_UM B' A'|). simpl. omega. apply H0. exact. }   } } } Qed.  
               

End UM.
