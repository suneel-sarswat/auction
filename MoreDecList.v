



Require Export Lists.List.
Require Export GenReflect SetSpecs.
Require Export Sorting.
Require Export DecType SetReflect.
Require Export DecList.



Set Implicit Arguments.



Section MoreDecList.

Context { A: eqType}.
(*------------------ Uniform list -----------------------------------------------------*)

Inductive uniform : list A -> Prop:=
| Nil_uni: uniform nil
|Sing_uni(a:A): uniform (a::nil)
|Ind_uni(a b:A)(l:list A): a=b -> uniform (b::l)-> uniform (a::b::l).

Lemma uniform_elim (a:A)(l: list A): uniform (a::l)-> (forall x, In x l -> x=a).
Proof. Admitted.
Lemma uniform_elim1 (a:A)(l: list A): uniform (a::l)-> (forall x, In x (a::l)-> x=a).
Proof. Admitted.
Lemma uniform_elim2 (a:A) (l: list A): uniform (a::l)-> uniform l.
Proof. Admitted.
Lemma uniform_intro (a:A)(l: list A): (forall x, In x l -> x=a) -> uniform (a::l).
Proof. Admitted.

(* ----------------- delete_all operation ---------------------------------------------  *)

Fixpoint del_all (a:A)(l: list A): list A:=
    match l with
    |nil => nil
    | a1::l1 => match  (a == a1) with
               |true => del_all a l1
               |false => a1 :: del_all a l1
               end
    end.

(* This function deletes all occurences of a in the list l *)

  Lemma del_all_elim1 (a b:A)(l: list A): In a (del_all b l)-> In a l.
  Proof. Admitted.
  Lemma del_all_elim2 (a b:A)(l: list A): In a (del_all b l)-> (a<>b).
  Proof. Admitted.

  Lemma del_all_intro (a b: A)(l:list A): In a l -> a<>b -> In a (del_all b l).
  Proof. Admitted.
  Lemma del_all_iff (a b:A)(l: list A): (In a (del_all b l) <-> (In a l /\ a<>b)).
  Proof. Admitted.

  Hint Resolve del_all_elim1 del_all_elim2 del_all_intro: core.
  
  Lemma del_all_nodup (a:A)(l: list A): NoDup l -> NoDup (del_all a l).
  Proof. Admitted.

  Hint Resolve del_all_nodup: core.

 (* ------- count of an element a in the list l ----------------------------------------*)

 Fixpoint count (a:A) (l:list A) : nat:= match l with
                          | nil => 0
                          |a1::l1 => match a == a1 with
                                    |true => S (count a l1)
                                    |false => count a l1
                                    end
                                        end.
  Lemma countP1 (a:A) (l:list A): In a l -> (count a l >= 1).
  Proof. Admitted.
  Lemma countP2 (a:A)(l: list A): ~ In a l -> (count a l = 0).
  Proof. Admitted.
  Lemma countP3 (a:A)(l: list A): (count a l = 0) -> ~ In a l.
  Proof. Admitted.
  Lemma countP4 (a:A)(l: list A): count a (a::l) = S (count a l).
  Proof. Admitted.
  Lemma countP5 (a b:A)(l: list A): (count a l) <= count a (b::l).
  Proof. Admitted.
  Lemma countP6 (a: A)(l: list A): count a l <= |l|.
  Proof. Admitted.
  Lemma countP7 (a:A) (l:list A): In a l -> count a l = S(count a (delete a l)).
  Proof. Admitted.
  Lemma countP8 (a:A) (l:list A): forall x, x<>a-> count x (a::l) = count x l.
  Proof. Admitted.
  Lemma countP9 (a:A) (l:list A): forall x, x<>a -> count x l = count x (delete a l).
  Proof. Admitted.
  Lemma countP10 (a:A)(l s:list A): count a l <= count a s -> count a (a::l) <= count a (a::s).
  Proof. Admitted.
  Lemma countP11 (a:A)(l s: list A): count a l = count a s -> count a (a::l) = count a (a::s).
  Proof. Admitted.
  Lemma countP12 (a:A)(l s: list A): count a l < count a s -> count a (a::l) < count a (a::s).
  Proof. Admitted.
  
  Hint Immediate countP1 countP2 countP3: core.
  Hint Resolve countP4 countP5 countP6 countP7 countP8 countP9: core.
 
End MoreDecList.

 Hint Resolve del_all_elim1 del_all_elim2 del_all_intro: core.
 Hint Resolve del_all_nodup: core.

 Hint Immediate countP1 countP2 countP3: core.
 Hint Resolve countP4 countP5 countP6 countP7 countP8 countP9:  core.
 Hint Resolve countP10 countP11 countP12: core.


Section Permutation.

  Context { A: eqType }.
  
   Lemma EM:forall x y : A, x=y \/ x<>y.
   Proof. eauto. Qed.
   
   Definition empty: list A:= nil.

   Lemma count_in_putin1 (a: A)(l: list A)(lr: A-> A-> bool):
     count a (putin lr a l)= S (count a l).
   Proof. { induction l. simpl. destruct (a==a) eqn:H. auto. conflict_eq. 
           { simpl. case (lr a a0) eqn: H0.
             { destruct (a==a0) eqn:H1. move /eqP in H1.
               subst a0. assert (H: count a (a::a::l)=S(count a (a::l))). eauto.
               rewrite H. eauto.
               assert (H: count a (a :: a0 :: l) = S (count a (a0::l))).
               eauto.  move /eqP in H1. rewrite H. eauto. }
             { simpl. destruct (a==a0) eqn:H1. omega. auto. } } } Qed.
   
   Lemma count_in_putin2 (a b: A)(l: list A)(lr: A-> A-> bool):
     a<>b -> count a l = count a (putin lr b l).
   Proof. { induction l.
            { simpl; destruct (a==b) eqn:H. intros;conflict_eq. auto. }
            { intros.  simpl. case (lr b a0) eqn: H0.
              { destruct (a==a0) eqn:H1.
                move /eqP in H1. subst a0.
                replace (count a (b :: a :: l)) with (count a (a :: l)).
                eauto. symmetry; auto. move /eqP in H1.
                replace (count a (b :: a0 :: l)) with (count a (a0 :: l)).
                all: symmetry;eauto. }
              { destruct (a==a0) eqn: H1.
                move /eqP in H1. subst a0.
                replace (count a (a :: putin lr b l)) with (S(count a (putin lr b l))).
                 eauto. symmetry. auto. 
                replace (count a (a0 :: putin lr b l)) with (count a (putin lr b l)).
                auto. move /eqP in H1. symmetry;auto. }  } } Qed.
   
  Lemma count_in_sorted (a: A)(l: list A)(lr: A-> A-> bool): count a l = count a (sort lr l). 
  Proof. { induction l. simpl; auto.
           simpl. destruct  (a == a0) eqn:H0.
           move /eqP in H0. subst a.
           rewrite IHl. symmetry; apply count_in_putin1.
           move /eqP in H0. rewrite IHl.  apply count_in_putin2. auto. }  Qed.


  Hint Resolve count_in_putin1 count_in_putin2 count_in_sorted: core.
  
  (* ---------------  sublist of a list (subsequence)------------------------------------ *)

  Fixpoint sublist (l s: list A): bool := match (l, s) with
                                              |(nil , _) => true
                                              |(a::l1, nil) => false
                                              |(a::l1, b::s1) => match (a == b) with
                                                          |true => sublist l1 s1
                                                          |false => sublist l s1
                                                          end
                                       end.
  
  Lemma sublist_intro (l: list A): sublist nil l.
  Proof.   destruct l;simpl;auto. Qed.
  Lemma sublist_reflex (l: list A): sublist l l.
  Proof. induction l;simpl.
         auto. destruct (a==a) eqn:H; [auto | conflict_eq].  Qed.

 
  Lemma sublist_elim1 (l: list A): sublist l nil -> l=nil.
  Proof. destruct l; [auto | simpl; intro H; inversion H]. Qed.

  Lemma sublist_elim2 (a:A)(l s: list A): sublist (a::l) s -> In a s.
  Proof. induction s.  simpl; auto. simpl. destruct (a==a0) eqn:H. move /eqP in H.
         subst a0; auto. intro;right;auto. Qed.
  
  Lemma sublist_elim3 (a: A)(l s: list A): sublist (a::l) s -> sublist l s.
  Proof. { revert l; revert a. induction s.
         { auto. }
         { intros a0 l. 
           simpl. destruct (a0 == a) eqn:H.
           { destruct l. auto.  destruct (e == a) eqn:H1.
             apply IHs. auto.  }
           { destruct l. auto.  destruct (e == a) eqn:H1.
             { intro H2. assert (H2a: sublist (e::l) s). eapply IHs;exact H2.
               eapply IHs; exact H2a. }
             { apply IHs. }
         } } } Qed.
  
  Lemma sublist_elim3a (a e: A)(l s: list A): sublist (a::l)(e::s)-> sublist l s.
  Proof. simpl. destruct (a==e) eqn:H. auto.   eauto using sublist_elim3. Qed.
  
   Lemma sublist_intro1 (a:A)(l s: list A): sublist l s -> sublist l (a::s).
   Proof.  { revert s;revert a. induction l.
           { auto. }
           { intros a0 s.
             simpl. destruct (a == a0) eqn:H. apply sublist_elim3. auto. } } Qed.

   Lemma sublist_Subset (l s: list A): sublist l s -> Subset l s.
   Proof. { revert s. induction l.  eauto.
           intros s H. eauto. unfold "[<=]". intros x H1.
           destruct H1. subst x. eauto using  sublist_elim2. apply sublist_elim3 in H.
           apply IHl in H. eauto. } Qed.

  
   Lemma sublist_elim4 (l s: list A): sublist l s -> (forall a, count a l <= count a s).
   Proof. { revert l. induction s as [| e s'].
          { intro l. intro H. assert (H1: l=nil); auto using sublist_elim1.
            subst l; auto.  }
          { intros l H x. destruct l as [|a l'].
            simpl. omega. destruct (x==a) eqn:Hxa.
            { move /eqP in Hxa. subst x.
              simpl in H. destruct (a == e) eqn: Hae. move /eqP in Hae.
              subst e.
              cut (count a l' <= count a s'); auto.
              assert (H1: count a (a :: l') <= count a  s'). eauto.
              cut (count a s' <= count a (e::s')). omega. auto. }
            { assert (H1: count x (a::l')<= count x s').
              { simpl. rewrite Hxa. eauto using sublist_elim3a. }
              cut (count x s' <= count x (e::s')). omega. auto. } } } Qed.
   
   
  Lemma sublist_trans (l1 l2 l3: list A): sublist l1 l2 -> sublist l2 l3 -> sublist l1 l3.
  Proof. Admitted.

  Hint Extern 0 (is_true ( sublist ?x ?z) ) =>
  match goal with
  | H: is_true (sublist x  ?y) |- _ => apply (@sublist_trans  x y z)
  | H: is_true (sublist ?y  z) |- _ => apply (@sublist_trans  x y z) 
  end.

    
 
  Hint Resolve sublist_intro sublist_intro1 sublist_reflex sublist_Subset sublist_elim1: core.
  Hint Resolve sublist_elim2 sublist_elim3 sublist_elim4: core.


  (* -------------- list inclusion (subset in multiset) ----------------------------------*)

  Fixpoint included (l s: list A): bool := match l with
                                        |nil => true
                                        | a::l1 => match (memb a s) with
                                                  |true => included l1 (delete a s)
                                                  |false => false
                                                  end
                                        end.
  Lemma included_intro1 (l: list A): included nil l.
  Proof. Admitted.
   Lemma included_refl (l: list A): included l l.
  Proof. Admitted.
  Lemma included_intro2 (a:A)(l s: list A): In a s -> included l (delete a s)-> included (a::l) s.
  Proof. Admitted.
  Lemma included_intro3 (l s: list A): sublist l s -> included l s.
  Proof. Admitted. 
  Lemma included_intro (l s: list A): (forall a, count a l <= count a s)-> included l s.
  Proof. { revert s. induction l. intros;apply included_intro1;auto.
           { intros s H. simpl.  case (memb a s) eqn:Has;move /membP in Has.
             apply IHl. intro x. destruct (EM x a).
             Focus 2.  replace (count x l) with (count x (a::l)).
             replace (count x (delete a s)) with (count x s).
             all: eauto. subst x. 
             replace (count a l) with ((count a (a::l)) -1). 
             replace (count a (delete a s)) with ((count a s)-1).
             specialize (H a).  omega.
             replace (count a s) with (S (count a (delete a s))). omega.
             symmetry; eauto.
             replace (count a (a :: l)) with (S (count a l)). omega.
             symmetry; eauto.
             specialize (H a). rewrite countP4 in H.
             replace (count a s) with 0 in H. inversion H. symmetry; eauto. } } Qed. 

  Lemma included_elim1 (l: list A): included l nil -> l=nil.
  Proof. Admitted.
  Lemma included_elim2 (a:A)(l s: list A): included (a::l) s -> In a s.
  Proof. Admitted.
  Lemma included_elim3 (a:A)(l s: list A): included (a::l) s -> included l (delete a s).
  Proof. Admitted.
  Lemma included_elim4 (a:A)(l s: list A): included (a::l) s -> included l s.
  Proof. Admitted.
  Lemma included_elim5 (l s: list A): included l s -> Subset l s.
  Proof. Admitted.

  Lemma included_elim (l s: list A): included l s-> (forall a, count a l <= count a s).
  Proof. { revert s. induction l. simpl. intros;omega. 
           intros s H x. apply included_elim2 in H as H1. apply included_elim3 in H as H2.
           assert (H3: count a l <= count a (delete a s)).  eapply IHl with (s:= (delete a s)).
           auto.  destruct (EM x a).
           subst x. replace (count a (a::l)) with (S(count a l)).
           replace (count a s) with (S( count a (delete a s))).
           omega. symmetry; eauto.  eauto.  
           replace (count x (a::l)) with (count x l).
           replace (count x s) with  (count x (delete a s)).
           eauto. all: symmetry;eauto. } Qed. 
  

  Lemma included_trans (l1 l2 l3: list A): 
  included l1 l2-> included l2 l3 -> included l1 l3.
  Proof. Admitted.

   Hint Extern 0 (is_true ( included ?x ?z) ) =>
  match goal with
  | H: is_true (included x  ?y) |- _ => apply (@included_trans  x y z)
  | H: is_true (included ?y  z) |- _ => apply (@included_trans  x y z) 
  end.

 
  Hint Resolve included_intro1 included_intro2 included_intro3: core.
  Hint Resolve included_refl included_intro: core.
  Hint Resolve included_elim1 included_elim2 included_elim3: core.
  Hint Resolve included_elim4 included_elim5 included_elim: core.

  (* ----- Some Misc Lemmas on nodup, sorted, sublist, subset and included ---------------- *)

  Lemma nodup_subset_included (l s: list A): NoDup l -> l [<=] s -> included l s.
  Proof. Admitted.
  Lemma sorted_included_sublist (l s: list A)(lr: A->A-> bool):
    Sorted lr l-> Sorted lr s-> included l s-> sublist l s.
  Proof. Admitted.
  Lemma first_in_ordered_sublists (a e:A)(l s: list A)(lr: A->A-> bool):
    Sorted lr (a::l)-> Sorted lr (e::s)-> sublist (a::l)(e::s)-> lr e a.
  Proof. Admitted.


  Hint Resolve nodup_subset_included: core.
  Hint Immediate sorted_included_sublist first_in_ordered_sublists:core.
  

  (* --------------------  permuted lists (permutation) -------------------------------------*)

  Definition perm (l s: list A): bool:= included l s && included s l. 

  Lemma perm_intro  (l s: list A): (forall a, count a l = count a s)-> perm l s.
  Proof.  { intro H; split_; apply included_intro; intro a; specialize (H a); omega. } Qed.

  Lemma perm_intro0a (l: list A)(lr: A-> A-> bool): perm l (sort lr l).
  Proof. apply perm_intro. eauto. Qed.
  
  Lemma perm_intro0b (l: list A)(lr: A-> A-> bool): perm (sort lr l) l.
  Proof. apply perm_intro; eauto. Qed.
 
  Lemma perm_nil: perm nil nil.
  Proof. split_; eauto.  Qed.
  
  Lemma perm_refl (l: list A): perm l l.
  Proof. split_; eauto.  Qed.

  Lemma perm_intro3 (l s: list A): sublist l s -> sublist s l -> perm l s.
  Proof. intros; split_; eauto.  Qed.

  Lemma perm_elim   (l s: list A): perm l s -> (forall a, count a l = count a s).
  Proof.  { intros H a. move /andP in H. destruct H as [H1 H2].
          cut (count a l <= count a s). cut (count a s <= count a l). omega.
          all: eauto. } Qed.

  Lemma perm_elim1 (l: list A): perm l nil -> l = nil.
  Proof. intro H; move /andP in H; destruct H as [H1 H2]; eauto. Qed.
  Lemma perm_elim2 (l s: list A): perm l s -> l [=] s.
  Proof. move /andP;intro H; destruct H; split; eauto. Qed.
  Lemma perm_sym (l s: list A): perm l s -> perm s l.
  Proof. move /andP;intro H; apply /andP; tauto. Qed.

  Lemma perm_trans (x y z: list A): perm x y -> perm y z -> perm x z.
  Proof. intros H H1; move /andP in H; move /andP in H1; apply /andP.
         split;destruct H; destruct H1. all: auto. Qed.

  Hint Extern 0 (is_true ( perm ?x ?z) ) =>
  match goal with
  | H: is_true (perm x  ?y) |- _ => apply (@perm_trans x y z)
  | H: is_true (perm ?y  z) |- _ => apply (@perm_trans x y z) 
  end.

  Hint Resolve  perm_intro0a  perm_intro0b perm_refl perm_nil perm_elim1 : core.
  Hint Immediate perm_elim perm_intro perm_sym: core.
  
  Lemma perm_sort1 (l s: list A)(lr: A-> A-> bool): perm l s -> perm  l (sort lr s).
  Proof.  eauto. Qed.

   Lemma perm_sort2 (l s: list A)(lr: A-> A-> bool): perm l s -> perm  (sort lr l) s.
   Proof. eauto.  Qed.

   Lemma perm_sort3 (l s: list A)(lr: A-> A-> bool): perm l s -> perm (sort lr l)(sort lr s).
   Proof. eauto using perm_sort1. Qed.

   Hint Resolve perm_sort1 perm_sort2 perm_sort3: core.
   
 End Permutation. 




  Hint Resolve count_in_putin1 count_in_putin2 count_in_sorted: core.


  Hint Resolve sublist_intro sublist_intro1 sublist_reflex sublist_Subset sublist_elim1: core.
  Hint Resolve sublist_elim2 sublist_elim3 sublist_elim3a sublist_elim4: core.

  Hint Extern 0 (is_true ( sublist ?x ?z) ) =>
  match goal with
  | H: is_true (sublist x  ?y) |- _ => apply (@sublist_trans _ x y z)
  | H: is_true (sublist ?y  z) |- _ => apply (@sublist_trans _ x y z) 
  end.


  Hint Resolve included_intro1 included_intro2 included_intro3: core.
  Hint Resolve included_refl included_intro: core.
  Hint Resolve included_elim1 included_elim2 included_elim3: core.
  Hint Resolve included_elim4 included_elim5 included_elim: core.

  Hint Extern 0 (is_true ( included ?x ?z) ) =>
  match goal with
  | H: is_true (included x  ?y) |- _ => apply (@included_trans _ x y z)
  | H: is_true (included ?y  z) |- _ => apply (@included_trans _ x y z) 
  end.

  Hint Resolve nodup_subset_included: core.
  Hint Immediate sorted_included_sublist first_in_ordered_sublists:core.
 
  Hint Resolve  perm_intro0a  perm_intro0b perm_refl perm_nil perm_elim1 : core.
  Hint Immediate perm_elim perm_intro perm_sym: core.
  Hint Resolve perm_elim1 perm_elim2: core.

  Hint Extern 0 (is_true ( perm ?x ?z) ) =>
  match goal with
  | H: is_true (perm x  ?y) |- _ => apply (@perm_trans _ x y z)
  | H: is_true (perm ?y  z) |- _ => apply (@perm_trans _ x y z) 
  end.

  Hint Resolve perm_sort1 perm_sort2 perm_sort3: core.
