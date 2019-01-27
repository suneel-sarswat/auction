

(* -----------------Description----------------------------------------------

This file contains basic definitions of Bids, Asks and Fill (trade between
Bid and Ask). They are also attached with eqType (i.e, domain with 
decidable Equality). This file also contains three functions to compute 
bids, asks and trade prices from a matching, and their specifications. ---- *)


Require Import ssreflect ssrbool.
Require Export Lists.List.
Require Export GenReflect SetSpecs.
Require Export DecList DecType MoreDecList.

Section Bid_Ask.
  


Record Bid:Type:= Mk_bid{
                        bp:> nat;
                        idb: nat}.



Definition b_eqb (x y:Bid): bool:= (idb x == idb y) && ( bp x == bp y).

 
Record Ask:Type:= Mk_ask{
                        sp:>nat;
                        ida: nat;}.

Definition a_eqb (x y: Ask): bool:= (ida x == ida y) && (  sp x ==  sp y).

(*
Hypothesis unique_idb : forall b1 b2:Bid, (idb(b1) = idb(b2))-> (b1 = b2).
Hypothesis unique_ida : forall a1 a2:Ask, (ida(a1) = ida(a2))-> (a1 = a2).
*)

(*----------------  Attaching Bid to the EqType ----------------------------------*)

Lemma b_eqb_ref (x:Bid): b_eqb x x = true.
Proof. unfold b_eqb. split_; apply /eqP;auto. Qed.

Hint Resolve b_eqb_ref: auction.
Lemma b_eqb_elim (x y:Bid):  b_eqb x y -> x = y.
Proof. unfold b_eqb. move /andP. intro H. destruct H as [H1 H2].
destruct x; destruct y. move /eqP in H1. auto.  Qed. 


Lemma b_eqb_intro (x y:Bid): x=y -> b_eqb x y = true.
Proof. unfold b_eqb. intros H. apply /andP. split. 
apply /eqP. subst x.  auto. apply /eqP. 
inversion H. auto.  Qed.  

Hint Immediate b_eqb_elim b_eqb_intro: auction.

Lemma b_eqP (x y:Bid): reflect (x=y)(b_eqb x y).
Proof. apply reflect_intro. split; auto with auction. Qed. 
Hint Resolve b_eqP: auction.


Canonical bid_eqType: eqType:= {| Decidable.E:= Bid; Decidable.eqb:= b_eqb; Decidable.eqP:= b_eqP |}.



(*------------------ Attaching Ask to EqType ------------------------------------ *)

Lemma a_eqb_ref (x: Ask): a_eqb x x = true.
Proof. unfold a_eqb. apply /andP. split. apply /eqP. auto. apply /eqP.
auto. Qed.


Hint Resolve a_eqb_ref: auction.
Lemma a_eqb_elim (x y: Ask):  a_eqb x y -> x = y.
Proof. unfold a_eqb. move /andP. intro H. destruct H as [H1 H2].
destruct x; destruct y. move /eqP in H1. auto. Qed. 


Lemma a_eqb_intro (x y: Ask): x=y -> a_eqb x y = true.
Proof. unfold a_eqb. intros H. apply /andP. split. 
apply /eqP. subst x.  auto. apply /eqP. 
inversion H. auto. Qed.  

Hint Immediate a_eqb_elim a_eqb_intro: auction.

Lemma a_eqP (x y: Ask): reflect (x=y)(a_eqb x y).
Proof. apply reflect_intro. split; auto with auction. Qed. 
Hint Resolve a_eqP: auction.

Canonical ask_eqType: eqType:= {| Decidable.E:= Ask; Decidable.eqb:= a_eqb; Decidable.eqP:= a_eqP |}.

(*------------- Price projections for list of Bids and Asks--------------------------*)

Fixpoint bid_prices (B: list Bid): (list nat):=
  match B with
  |nil => nil
  |b::B' => (bp b)::(bid_prices B')
  end.

Lemma bid_prices_intro (B: list Bid) (b: Bid):
  In b B -> (In (bp b) (bid_prices B)).
Proof. { intro H. induction B. simpl. simpl in H. contradiction.
         destruct  H. subst b. simpl. left. auto. simpl. right. auto. } Qed.


Lemma bid_prices_intro1 (B: list Bid) (B': list Bid):
  B [<=] B' -> ((bid_prices B)  [<=] (bid_prices B')).
Proof. Admitted.


Lemma bid_prices_elim (B: list Bid): forall p, In p (bid_prices B)->
                                             exists b, In b B /\ p = bp b.
Proof. { intros p H. induction B. simpl in H. contradiction. simpl in H.
       destruct  H as [H1 | H2].  exists a. split; auto.
       apply IHB in H2 as H0. destruct H0 as [b H0].
       exists b. destruct H0. split.
       eauto. auto. } Qed.

Fixpoint ask_prices (A: list Ask): (list nat):=
  match A with
  |nil => nil
  |a::A' => (sp a)::(ask_prices A')
  end.

Lemma ask_prices_intro (A: list Ask) (a: Ask):
  In a A -> (In (sp a) (ask_prices A)).
Proof. { intro H. induction A. simpl. simpl in H. contradiction.
         destruct  H. subst a. simpl. left. auto. simpl. right. auto. } Qed.


Lemma ask_prices_intro1 (A: list Ask) (A': list Ask):
  A [<=] A' -> ((ask_prices A)  [<=] (ask_prices A')).
Proof.  Admitted.


Lemma ask_prices_elim (A: list Ask): forall p, In p (ask_prices A)->
                                             exists a, In a A /\ p = sp a.
Proof. { intros p H. induction A. simpl in H. contradiction. simpl in H.
       destruct  H as [H1 | H2]. exists a. split; auto.
       apply IHA in H2 as H0. destruct H0 as [a0 H0].
       exists a0. destruct H0. split.
       eauto. auto. } Qed.


Hint Resolve bid_prices_elim bid_prices_intro bid_prices_intro1: core.
Hint Resolve ask_prices_elim ask_prices_intro ask_prices_intro1: core.


(* ------------definition of  fill_type as record---------------------------- *)

Record fill_type:Type:=  Mk_fill {
                             bid_of: Bid;
                             ask_of: Ask;
                             tp: nat }. 
                             
 Definition m_eqb (x y: fill_type): bool:= (bid_of x == bid_of y) && (  ask_of x ==  ask_of y) && (tp x == tp y).                            

(*------------------ Attaching fill_type to eqType ------------------------------------ *)

Lemma m_eqb_ref (x: fill_type): m_eqb x x = true.
Proof. unfold m_eqb. apply /andP. split. apply /andP. split. all: apply /eqP; auto. Qed.


Hint Resolve m_eqb_ref: auction.
Lemma m_eqb_elim (x y: fill_type):  m_eqb x y -> x = y.
Proof. unfold m_eqb. intros H. destruct x. destruct y. simpl in H. Admitted.


Lemma m_eqb_intro (x y: fill_type): x=y -> m_eqb x y = true.
Proof. unfold m_eqb. intros H. apply /andP. split. apply /andP. 
split. 
apply /eqP. subst x. exact. apply /eqP. subst x. exact. apply /eqP. 
subst x. exact. Qed.  

Hint Immediate m_eqb_elim m_eqb_intro: auction.

Lemma m_eqP (x y: fill_type): reflect (x=y)(m_eqb x y).
Proof. apply reflect_intro. split; auto with auction. Qed. 
Hint Resolve m_eqP: auction.

Canonical fill_eqType: eqType:= {| Decidable.E:= fill_type; Decidable.eqb:= m_eqb; Decidable.eqP:= m_eqP |}.




Fixpoint bids_of (F: list fill_type) : (list Bid) :=
  match F with
  |nil => nil
  |f::F'=> (bid_of f)::(bids_of F')
  end.

Lemma bids_of_intro (F: list fill_type) (m: fill_type):
  In m F -> (In (bid_of m) (bids_of F)).
Proof. { intro H. induction F. simpl. simpl in H. contradiction. destruct  H.
        subst m. simpl. left. auto. simpl. right. auto. } Qed.


Lemma bids_of_intro1 (M': list fill_type) (M: list fill_type):
  M [<=] M' -> ((bids_of M)  [<=] (bids_of M')).
Proof.  Admitted.

Lemma bids_of_elim (F: list fill_type): forall b, In b (bids_of F)->
                                             exists m, In m F /\ b = bid_of m.
Proof. { intros b H. induction F. simpl in H. contradiction. simpl in H.
       destruct  H as [H1 | H2]. exists a. split; auto.
       apply IHF in H2 as H0. destruct H0 as [m H0]. exists m. destruct H0. split.
       eauto. auto. } Qed.
       
Lemma bids_of_perm (M M': list fill_type): perm M M' -> perm (bids_of M) (bids_of M').
Proof.  Admitted.

Fixpoint asks_of (F: list fill_type) : (list Ask) :=
  match F with
  |nil => nil
  |f::F'=> (ask_of f)::(asks_of F')
  end.

Lemma asks_of_intro (F: list fill_type) (m: fill_type):
  In m F -> (In (ask_of m) (asks_of F)).
Proof. { intro H. induction F. simpl. simpl in H. contradiction. destruct  H.
        subst m. simpl. left. auto. simpl. right. auto. } Qed.
  
Lemma asks_of_elim (F: list fill_type): forall a, In a (asks_of F)->
                                            exists m, In m F /\ a = ask_of m.
Proof. { intros b H. induction F. simpl in H. contradiction. simpl in H. 
       destruct  H as [H1 | H2]. exists a. split; auto.
       apply IHF in H2 as H0. destruct H0 as [m H0]. exists m. destruct H0. split.
       eauto. auto. } Qed.

Lemma asks_of_perm (M M': list fill_type): perm M M' -> perm (asks_of M) (asks_of M').
Proof. Admitted.

Fixpoint trade_prices_of (F: list fill_type) : (list nat) :=
  match F with
  |nil => nil
  |f::F'=> (tp f)::(trade_prices_of F')
  end.

Lemma trade_prices_of_intro (F: list fill_type) (m: fill_type):
  In m F -> In (tp m) (trade_prices_of F).
Proof. { intro H. induction F. eauto. destruct H. subst m.
       simpl. left;auto. simpl. right;auto.
       } Qed.

                           
Lemma trade_prices_of_elim (F: list fill_type): forall p, In p (trade_prices_of F) ->
                                                     exists m, In m F /\ p = tp m.
Proof. { intros p H. induction F. simpl in H. contradiction. simpl in H. destruct H.
       exists a. split. eauto. auto. apply IHF in H as H0. destruct  H0 as [m H0].
       destruct H0 as [H1 H2]. exists m. split;eauto. } Qed.
Lemma tps_of_perm (M M': list fill_type):
 perm M M' -> perm (trade_prices_of M) (trade_prices_of M').
Proof. Admitted.

      
Hint Resolve bids_of_intro bids_of_elim asks_of_intro asks_of_elim: auction.
Hint Resolve trade_prices_of_intro trade_prices_of_elim: auction.


  
End Bid_Ask.


Hint Resolve b_eqb_ref b_eqP : auction.
Hint Immediate b_eqb_elim b_eqb_intro: auction.

Hint Resolve a_eqb_ref a_eqP : auction.
Hint Immediate a_eqb_intro a_eqb_elim: auction.


Hint Resolve bid_prices_elim bid_prices_intro bid_prices_intro1: core.
Hint Resolve ask_prices_elim ask_prices_intro ask_prices_intro1: core.


Hint Resolve m_eqb_ref m_eqP: auction.
Hint Immediate m_eqb_elim m_eqb_intro: auction.

      
Hint Resolve bids_of_intro bids_of_elim asks_of_intro asks_of_elim: core.
Hint Resolve trade_prices_of_intro trade_prices_of_elim: core.

Hint Resolve bids_of_perm asks_of_perm tps_of_perm: core.