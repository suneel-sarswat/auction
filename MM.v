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


(*Dear Abhishek, The main problem is in this function. I tried with these variations:
Change the line :|true =>(((b,a),(bp b))::(produce_MM B' A')) to 
|true =>(({|bid:= b ; ask:= a ; tp:=(bp b) |})::(produce_MM B' A'))

but still there is error.

produce_MM works, when I remove ": (list fill_type)" part in the first line,
but then MM function gives error.
*)


Print fill_type.

(* Record fill_type : Set := Mk_fill { bid_of : Bid;  ask_of : Ask;  tp : nat } *)
Fixpoint produce_MM (B:list Bid) (A: list Ask): (list fill_type) :=
  match B with
  |nil => nil
  |b::B' => match A with
           |nil =>nil
           |a::A' => match (Nat.leb (sp a) (bp b)) with
                    |true => ({|bid_of:= b ; ask_of:= a ; tp:=(bp b) |})::(produce_MM B' A')
                    |false => produce_MM B A'
                    end
           end
  end.
  


  (**)

Print Make_FOA.
(* We have not implemented Make_FOA so before proceeding you need to define Make_FOA which 

   should be simmilar to Make_FOB and all its corresponding lemmas should be simmilar *)
   Print a_by_sp.


Definition MM (B:list Bid) (A: list Ask):list fill_type := 
(Make_FOA 

(Make_FOB 

(produce_MM (sort b_by_bp B) (rev (sort a_by_sp A))) 

(sort b_by_bp B)) 

(sort a_by_sp A)).






(*
Definition B1 := 125::120::112::91::83::82::69::37::12::nil.
Definition A1 := 121::113::98::94::90::85::79::53::nil.
Eval compute in (count B1 A1).


Fixpoint erase_top (T:Type) (n:nat) (l:list T): list T:=
  match l with
  |nil => nil
  |a::l' => match n with
           |0 => l
           |S n' => erase_top n' l'
           end
  end.

Eval compute in (erase_top 3 B1).
Check nil.
Definition nil_on (T1:Type)(T2:Type): list ((T1 [*] T2) [*] nat):= nil.

Fixpoint pair_top (n:nat) (l:list Bid) (s:list Ask): (list ((Bid [*] Ask)[*] nat)):=
  match (l,s) with
  |(nil,_) => (nil_on Bid Ask)
  |(_,nil) => (nil_on Bid Ask)
  |(b::l',a::s') => match n with
                   |0 => (nil_on Bid Ask)
                   |S n' => ((b,a),  (bp b)) ::(pair_top n' l' s')
                                   end
  end.


Definition produce_FM (M: list fill_type) (B: list Bid) (A: list Ask):=
  pair_top (|M|) B (erase_top (|A| - |M|) A).

Lemma Is_a_matching_FM (M: list fill_type) (B: list Bid) (A: list Ask):
 (IsOrd (rev B)) -> (IsOrd (rev A))-> (Is_a_matching M B A)-> Is_a_matching (produce_FM M B A) B A.
Proof.
  intros H1 H2 H3. Admitted.

Fixpoint bid_prices_of (B: list Bid) : (list nat) :=
  match B with
  |nil => nil
  |b::B'=> (bp b)::(bid_prices_of B')
  end.

Fixpoint ask_prices_of (A: list Ask) : (list nat) :=
  match A with
  |nil => nil
  |a::A'=> (sp a)::(ask_prices_of A')
  end.



Definition MM (B:list Bid) (A: list Ask):list fill_type :=
  pair_top (count (bid_prices_of B) (ask_prices_of A)) (B)
           (erase_top ((length A)-(count (bid_prices_of B) (ask_prices_of A))) A).   

Require Extraction.
Extraction MM.
Extraction pair_top. Extraction Nat.div2.
Check Bid.
Print Bid.
*)

Definition B2:= ({|b_id:= 1 ; bp:= 125 |}) ::({|b_id:= 2 ; bp:= 120 |}) ::({|b_id:= 3 ; bp:= 112 |}) ::({|b_id:= 4 ; bp:= 91 |}) ::({|b_id:= 5 ; bp:= 82 |}) ::({|b_id:= 6 ; bp:= 82 |}) ::({|b_id:= 7 ; bp:= 69 |}) ::({|b_id:= 8 ; bp:= 37 |}) :: nil.

Definition A2:= ({|s_id:= 1 ; sp:= 121 |}) ::({|s_id:= 3 ; sp:= 113 |}) ::({|s_id:= 5 ; sp:= 98 |}) ::({|s_id:= 9 ; sp:= 94 |}) ::({|s_id:= 90 ; sp:= 90 |}) ::({|s_id:= 78 ; sp:= 85 |}) ::({|s_id:= 67 ; sp:= 79 |}) ::({|s_id:= 45 ; sp:= 53 |}) ::nil.




Eval compute in |(produce_MM B2 A2)|.

Eval compute in (Make_FOA (Make_FOB (produce_MM B2 A2) B2) A2).





Theorem MM_is_fair(B: list Bid) (A:list Ask) : Is_fair (MM B A) B A.
Proof. Admitted.

Theorem MM_is_Ind_Rat (B: list Bid) (A:list Ask): Is_ind_rational ( MM B A).
Proof. Admitted.

Theorem MM_is_orderly (B: list Bid) (A:list Ask): Is_orderly ( MM B A).
Proof. Admitted.


Theorem MM_is_maximal (B: list Bid) (A:list Ask): forall M: list fill_type, Is_a_matching M -> |M| <= | (MM B A) |.
Proof. Admitted.

End MM.
