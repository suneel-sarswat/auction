



(*-------------- Description -----------------------------------------------------

 
 Lemma insert_nodup (a:A)(l: list A): NoDup l -> NoDup (insert a l).


 Lemma list_del_IsOrd (a:A)(l: list A): IsOrd l -> IsOrd (del_all a l).
 Lemma list_del_nodup (a:A)(l: list A): NoDup l -> NoDup (del_all a l).   *)


Require Export Lists.List.
Require Export GenReflect SetSpecs DecType.
Require Export SetReflect.

Set Implicit Arguments.

Section DecLists.

  Context { A: eqType }.

  Definition empty: list A:= nil.
  
  Lemma empty_equal_nil (l: list A): l [=] empty -> l = empty.
  Proof. { case l.  auto. intros s l0. unfold "[=]". intro H. 
           destruct H as [H1 H2]. absurd (In s empty). all: eauto. } Qed.


 (* -------------- list_insert operation and its properties---------------------------  *)
  Fixpoint insert (a:A)(l: list A): list A :=
    match l with
    |nil => a::nil
    |a1::l1 => match a == a1 with
              |true => a1::l1
              |false => a1:: (insert a l1)
              end
    end.
  (* this function adds an element correctly even in an unsorted list *)
  Lemma insert_intro1 (a b: A)(l: list A): In a l -> In a ( insert b l).
  Proof. { intro H. induction l.  inversion H.
         destruct H.
         { subst a0. simpl; destruct (b == a); eauto. }
         { simpl; destruct (b == a0); eauto. } } Qed.
  
  Lemma insert_intro2 (a b: A)(l: list A): a=b -> In a (insert b l).
  Proof. { intro. subst a. induction l.
         simpl. left;auto. simpl. destruct (b == a) eqn:H. move /eqP in H.
         subst b; auto. all: auto. } Qed.
  Lemma insert_intro (a b: A)(l: list A): (a=b \/ In a l) -> In a (insert b l).
  Proof. intro H. destruct H.  eapply insert_intro2;auto.  eapply insert_intro1;auto. Qed.
  Lemma insert_intro3 (a:A)(l: list A): In a (insert a l).
  Proof. { eapply insert_intro2. auto.  } Qed.
  Hint Resolve insert_intro insert_intro1 insert_intro2 insert_intro3: core.
  
  Lemma insert_not_empty (a: A)(l:list A): insert a l <> (empty).
  Proof. intro H. absurd (In a empty). simpl; auto. rewrite <- H.
         eauto.  Qed. 
    
  Lemma insert_elim (a b: A)(l: list A): In a (insert b l)-> ( a=b \/ In a l).
  Proof. { induction l.
         simpl. left. symmetry. tauto. intro H.
         simpl in H. destruct (b == a0) eqn: eqH.  
         right;auto. destruct H. right;subst a0;auto.
         cut (a=b \/ In a l). intro H1;destruct H1. left;auto. right; eauto.
         auto.  } Qed. 
  
  Lemma insert_elim1 (a b: A)(l: list A): In a (insert b l)-> ~ In a l -> a=b.
  Proof. { intros H H0.
         assert (H1: a=b \/ In a l). eapply insert_elim;eauto.
         destruct H1. auto. absurd (In a l);auto. } Qed.
  Lemma  insert_elim2 (a b: A)(l: list A): In a (insert b l)-> a<>b-> In a l.
  Proof. { intros H H0.
         assert (H1: a=b \/ In a l). eapply insert_elim;eauto.
         destruct H1. absurd (a=b); auto. auto. } Qed.
  
  Hint Resolve insert_elim insert_elim1 insert_elim2: core.
  Lemma insert_iff (a b:A)(l:list A): In a (insert b l) <-> (a=b \/ In a l).
  Proof. split; auto. Qed.

  
  Lemma insert_nodup (a:A)(l: list A): NoDup l -> NoDup (insert a l).
  Proof. { induction l. simpl. constructor;auto.
         { intro H. simpl. destruct (a == a0) eqn: eqH.
           { auto. }
           { constructor. intro H1.
           assert (H2: a0 =a \/ In a0 l); eauto.
           destruct H2. subst a0. switch_in eqH. apply eqH. eauto. 
           absurd (In a0 l); auto. eauto. } } } Qed.
  
  Hint Resolve insert_nodup : core.

    
  (*------------ list remove operation on ordered list ----------------------------------- *)
   Fixpoint delete (a:A)(l: list A): list A:=
    match l with
    |nil => nil
    | a1::l1 => match a == a1 with
               |true => l1
               |false => a1:: delete a l1
               end
    end.
   (* This function deletes only the first occurence of 'a' from the list l *)
  
  Lemma delete_elim1 (a b:A)(l: list A): In a (delete b l)-> In a l.
  Proof. { induction l. simpl. auto.
         { simpl. destruct (b == a0) eqn: eqH.
           { right;auto. }
           { intro H1. destruct H1. left;auto. right;auto. } } } Qed.
  
  Lemma delete_elim2 (a b:A)(l: list A): NoDup l -> In a (delete b l)-> (a<>b).
  Proof. { induction l. simpl. auto.
         { simpl. destruct  (b == a0) eqn: eqH.
           { intros H1 H2. move /eqP in eqH. subst b. intro H3. subst a.
             absurd (In a0 l); eauto. }
           { intros H1 H2. destruct H2. intro. subst a0; subst a.
             switch_in eqH. apply eqH. eauto. eauto. } } } Qed.
  
  Lemma delete_intro (a b: A)(l:list A): In a l -> a<>b -> In a (delete b l).
  Proof. { induction l. simpl.  auto.
         { simpl. destruct (b == a0) eqn: eqH.
           { intros H1 H2. destruct H1. move /eqP in eqH. subst a; subst b.
             absurd (a0=a0); auto. auto. }
           { intros H1 H2. simpl. destruct H1. left;auto. right;auto. } } } Qed.
            
  Hint Resolve delete_elim1 delete_elim2 delete_intro: core.
  Lemma delete_iff (a b:A)(l: list A): NoDup l -> (In a (delete b l) <-> (In a l /\ a<>b)).
  Proof. intro H. split. eauto.
         intro H0. destruct H0 as [H0 H1]. eauto.  Qed. 
  

   Lemma delete_nodup (a:A)(l: list A): NoDup l -> NoDup (delete a l).
  Proof.  { induction l. simpl. constructor.
          { intro H. simpl. destruct (a == a0) eqn: eqH. 
            { eauto. }
            {  switch_in eqH. constructor. intro H1. absurd (In a0 l). all: eauto. } } } Qed.
              
  Hint Resolve delete_nodup: core.
  
  

(*--- Index (idx x l) function to locate the first position of the element x in list l ----- *)
Fixpoint idx (x:A)(l: list A):= match l with
                                |nil => 0
                                |a::l' => match (x==a) with
                                        | true => 1
                                        |false => match (memb x l') with
                                                 |true => S (idx x l')
                                                 |false => 0
                                                 end
                                         end
                                end.
Lemma absnt_idx_zero (x:A)(l:list A): ~ In x l -> (idx x l)=0.
Proof. { induction l.
       { simpl. auto. }
       { intro H. simpl.
         replace (x ==a ) with false. replace (memb x l) with false. auto.
         symmetry;switch; auto.
         symmetry;switch;move /eqP. intro H1. subst x. auto. } } Qed.

Lemma idx_zero_absnt (x:A)(l:list A): (idx x l)=0 -> ~ In x l.
Proof. { induction l.
         { simpl. auto. }
         { intros H1 H2. inversion H1.
           destruct (x==a) eqn:Hxa. inversion H0.
           destruct (memb x l) eqn: Hxl. move /membP in Hxl.
           inversion H0. assert (H3: x=a \/ In x l). auto.
           destruct H3. subst x. conflict_eq. switch_in Hxl. apply Hxl.
           apply /membP. auto. } } Qed.

Lemma idx_gt_zero (x:A)(l: list A): In x l -> (idx x l) > 0.
Proof. { intro H. assert (H1: idx x l = 0 \/ ~ idx x l =0). eauto.
       destruct H1.
       { absurd (In x l). apply idx_zero_absnt. auto. auto. }
       { omega. } } Qed.

Lemma idx_is_one (a:A)(l: list A): idx a (a::l) = 1.
Proof. simpl. replace (a==a) with true; auto. Qed.

Hint Immediate absnt_idx_zero idx_zero_absnt idx_gt_zero idx_is_one: core.

Lemma idx_successor (x a:A)(l: list A): In x (a::l)-> x<>a -> idx x (a::l) = S (idx x l).
Proof. { intros H H1. destruct H.
         { subst a. conflict_eq. }
         { simpl. replace (x==a) with false. replace (memb x l) with true. all: auto. } } Qed.

Lemma nodup_idx_successor(x a: A)(l: list A):In x (a::l)-> NoDup(a::l)-> idx x (a::l)= S(idx x l).
Proof. { intros H H1. destruct H.
         { subst x. simpl. replace (a==a) with true. replace (idx a l) with 0.
           auto. symmetry. apply absnt_idx_zero; auto. auto. }
         { apply idx_successor. auto. intro H2. subst x. absurd (In a l);auto. } } Qed. 

Lemma diff_index (x y:A)(l: list A): In x l -> In y l -> x<>y -> (idx x l <> idx y l).
Proof. { induction l.
       { simpl;auto. }
       { intros Hx Hy Hxy.
         assert (Hxa: x=a \/ x<>a); eauto.
         assert (Hya: y=a \/ y <> a); eauto.
         destruct Hxa;destruct Hya.
         {(* case x=a y=a *)
           subst x. subst y. contradiction. }
         { (* case x=a y<> a *) 
           subst x. replace (idx a (a::l)) with 1.
           destruct Hy. contradiction.
           assert (H1: idx y l > 0). auto.
           simpl. replace (y==a) with false. replace (memb y l) with true.
           intro H2. inversion H2. rewrite <- H4 in H1. inversion H1.
           auto. symmetry. switch. move /eqP. auto. symmetry;auto. }
         { (* case x<> a y = a *)
           subst y. replace (idx a (a::l)) with 1.
           destruct Hx. subst x. contradiction.
           assert (H1: idx x l > 0). auto.
           simpl. replace (x==a) with false. replace (memb x l) with true.
           intro H2. inversion H2. rewrite H4 in H1. inversion H1.
           auto. symmetry. switch. move /eqP. auto. symmetry;auto. }
         { (* case x<>a y <> a *)
           destruct Hx. symmetry in H1; contradiction.
           destruct Hy. symmetry in H2;contradiction.
           replace (idx x (a::l)) with (S (idx x l)).
           replace (idx y (a::l)) with (S (idx y l)).
           cut (idx x l <> idx y l). auto.
           apply IHl;auto. all: symmetry; apply idx_successor;auto. } } } Qed.

Lemma same_index (x y:A)(l: list A): In x l -> In y l -> (idx x l = idx y l) -> x=y.
Proof. { intros H H1 H2.
       assert (H3: x=y \/ x<>y). eapply reflect_EM;auto.
       destruct H3. auto.
       absurd(idx x l = idx y l); auto using diff_index. } Qed.

Hint Resolve idx_successor diff_index same_index: core.



(*----------------- Properties of list cardinality ------------------------------------*)

 Lemma delete_size1 (a:A)(l: list A): In a l -> |delete a l| = (|l| - 1).
   Proof. { induction l.
          { simpl; auto. }
          { intro H. simpl.
            destruct (a==a0) eqn: H1. omega.
            assert (H2: a<>a0). switch_in H1. auto.
            assert (H3: In a l). eauto.
            simpl. replace (|delete a l|) with (|l| - 1).
            cut (|l| > 0). omega. eauto.  symmetry;auto. } } Qed.
   
  Lemma delete_size2 (a:A)(l: list A): ~ In a l -> |delete a l| = |l|.
  Proof. { induction l.
         { simpl; auto. }
         { intros H.
           assert (H1: a<> a0).
           { intro H1; subst a. absurd (In a0 (a0::l)); auto. }
           assert (H2: ~ In a l). auto.
           simpl. replace (a==a0) with false.
           simpl. auto. auto. } } Qed.
  
  Lemma delete_size (a:A) (l:list A): |delete a l| <=|l|.
  Proof. { assert (H: In a l \/ ~ In a l). eauto.
         destruct H. replace (|delete a l|) with (|l| - 1). omega.
         symmetry;auto using delete_size1.
         replace (|delete a l|) with (|l|). auto.
         symmetry; auto using delete_size2. } Qed.

  Hint Immediate delete_size delete_size1 delete_size2: core.

   
  Lemma subset_cardinal_le (l s: list A): NoDup l -> l [<=] s -> |l| <= |s|.
  Proof. { revert s. induction l.
         { simpl. intros. omega. }
         { intros s H H1. assert (H2: NoDup l). eauto.
           assert (H3: ~ In a l). eauto. assert (Has: In a s). auto.
           assert (H4: l [<=] (delete a s)).
           { intros x H4. apply delete_intro.
             auto. intro H5. subst x. contradiction. }
           simpl. assert (H5: |l| <= | delete a s|).
           { apply IHl;auto. }
           replace (|delete a s|) with (|s| -1) in H5. revert H5.
           cut(|s| > 0). intros. omega. eauto.
           symmetry. auto using delete_size1. } } Qed.
           
  Lemma subset_cardinal_lt (l s: list A)(a: A):
    NoDup l -> l [<=] s->  In a s -> ~ In a l -> |l| < |s|.
  Proof. { intros H H1 H2 H3.
         assert (H4: l [<=] (delete a s)).
         { intros x H4. apply delete_intro. auto.
           intro H5. subst x. contradiction. }
         assert (H5: |l| <= | delete a s|).
         { auto using subset_cardinal_le. }
         replace (|delete a s|) with (|s| -1) in H5. revert H5.
         cut(|s| > 0). intros. omega. eauto.
         symmetry. auto using delete_size1. } Qed.

  Hint Resolve subset_cardinal_le subset_cardinal_lt: core.

End DecLists.



 Hint Resolve insert_intro insert_intro1 insert_intro2 insert_intro3: core.
 Hint Resolve insert_elim insert_elim1 insert_elim2: core.
 Hint Resolve insert_nodup :core.

 Hint Resolve delete_elim1 delete_elim2 delete_intro delete_size: core.
 Hint Resolve delete_nodup: core.
 
Hint Immediate absnt_idx_zero idx_zero_absnt idx_gt_zero idx_is_one: core.
Hint Resolve idx_successor diff_index same_index: core.


 Hint Resolve subset_cardinal_le subset_cardinal_lt: core.
  