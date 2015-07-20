(** * MoreProp: More about Propositions and Evidence最后一道附加题 *)

Require Export "Prop".


(* ####################################################### *)
(** * Relations *)

(** A proposition parameterized by a number (such as [ev] or
    [beautiful]) can be thought of as a _property_ -- i.e., it defines
    a subset of [nat], namely those numbers for which the proposition
    is provable.  In the same way, a two-argument proposition can be
    thought of as a _relation_ -- i.e., it defines a set of pairs for
    which the proposition is provable. *)

Module LeModule.  


(** One useful example is the "less than or equal to"
    relation on numbers. *)

(** The following definition should be fairly intuitive.  It
    says that there are two ways to give evidence that one number is
    less than or equal to another: either observe that they are the
    same number, or give evidence that the first is less than or equal
    to the predecessor of the second. *)

Inductive le : nat -> nat -> Prop :=
  | le_n : forall n, le n n
  | le_S : forall n m, (le n m) -> (le n (S m)).

Notation "m <= n" := (le m n).


(** Proofs of facts about [<=] using the constructors [le_n] and
    [le_S] follow the same patterns as proofs about properties, like
    [ev] in chapter [Prop].  We can [apply] the constructors to prove [<=]
    goals (e.g., to show that [3<=3] or [3<=6]), and we can use
    tactics like [inversion] to extract information from [<=]
    hypotheses in the context (e.g., to prove that [(2 <= 1) -> 2+2=5].) *)

(** Here are some sanity checks on the definition.  (Notice that,
    although these are the same kind of simple "unit tests" as we gave
    for the testing functions we wrote in the first few lectures, we
    must construct their proofs explicitly -- [simpl] and
    [reflexivity] don't do the job, because the proofs aren't just a
    matter of simplifying computations.) *)

Theorem test_le1 :
  3 <= 3.
Proof.
  (* WORKED IN CLASS *)
  apply le_n.  Qed.

Theorem test_le2 :
  3 <= 6.
Proof.
  (* WORKED IN CLASS *)
  apply le_S. apply le_S. apply le_S. apply le_n.  Qed.

Theorem test_le3 :
  (2 <= 1) -> 2 + 2 = 5.
Proof. 
  (* WORKED IN CLASS *)
  intros H. inversion H. inversion H2.  Qed.

(** The "strictly less than" relation [n < m] can now be defined
    in terms of [le]. *)

End LeModule.

Definition lt (n m:nat) := le (S n) m.

Notation "m < n" := (lt m n).

(** Here are a few more simple relations on numbers: *)

Inductive square_of : nat -> nat -> Prop :=
  sq : forall n:nat, square_of n (n * n).

Inductive next_nat (n:nat) : nat -> Prop :=
  | nn : next_nat n (S n).

Inductive next_even (n:nat) : nat -> Prop :=
  | ne_1 : ev (S n) -> next_even n (S n)
  | ne_2 : ev (S (S n)) -> next_even n (S (S n)).

(** **** Exercise: 2 stars (total_relation) *)
(** Define an inductive binary relation [total_relation] that holds
    between every pair of natural numbers. *)
Inductive total_relation : nat->nat->Prop:=
  total: forall n m:nat, total_relation n m.

(* FILL IN HERE *)
(** [] *)

(** **** Exercise: 2 stars (empty_relation) *)
(** Define an inductive binary relation [empty_relation] (on numbers)
    that never holds. *)
Inductive empty_relation : nat->nat->Prop:=.

  
(* FILL IN HERE *)
(** [] *)

(** **** Exercise: 2 stars, optional (le_exercises) *)
(** Here are a number of facts about the [<=] and [<] relations that
    we are going to need later in the course.  The proofs make good
    practice exercises. *)

Lemma le_trans : forall m n o, m <= n -> n <= o -> m <= o.
Proof.
  intros.
  rewrite<-H in H0.
  apply H0.
Qed.
  (* FILL IN HERE *)

Theorem O_le_n : forall n,
  0 <= n.
Proof.
  intros.
  induction n as [|n'].
  Case "n=O".
    apply le_n.
  Case "n=S n'".
    rewrite->IHn'.
    apply le_S. apply le_n.
Qed.
  (* FILL IN HERE *)

Theorem n_le_m__Sn_le_Sm : forall n m,
  n <= m -> S n <= S m.
Proof.
  intros.
  induction H. apply le_n.
    rewrite->IHle.
    apply le_S.
    apply le_n.
Qed.

  (* FILL IN HERE *)


Theorem Sn_le_Sm__n_le_m : forall n m,
  S n <= S m -> n <= m.
Proof.
  induction m as [|m'].
  Case "m=0".
    generalize n. destruct n0 as [|n0'].
    SCase "n0=0".  intro. apply le_n.
    SCase "n0=S n0'". intro. inversion H. rewrite<-H1.  apply le_S. apply le_n.
  Case "m=S m'".
    generalize n. destruct n0 as [|n0'].
    SCase "n0=0". intro. inversion H. rewrite<-H1.  apply le_S. apply le_n.
    SCase "m0=S m0'". intro. inversion H. apply le_n.  rewrite<-H1. apply le_S.
              apply le_n.
Qed.
   
  (* FILL IN HERE *)


Theorem le_plus_l : forall a b,
  a <= a + b.
Proof.
  intros.
  induction b as [|b'].
  Case "b=0". rewrite->plus_0_r. apply le_n.
  Case "b=S b'". induction a as [|a'].
   SCase "a=0". simpl. simpl in IHb'. rewrite->IHb'. apply le_S. apply le_n.
   SCase "a=S a'".  rewrite->plus_comm.  simpl. apply le_S.
        rewrite<-plus_comm. apply IHb'.
Qed.
  (* FILL IN HERE *)
Theorem plus_lt : forall n1 n2 m,
  n1 + n2 < m ->
  n1 < m /\ n2 < m.
Proof. 
 unfold lt.
  intros.
  induction m as [|m'].
  Case "m=0". rewrite<-H. inversion H. rewrite<-H.
  Case "m=S m'". split.
   assert (n1<= n1+n2) as H1.
    apply le_plus_l.
    apply  n_le_m__Sn_le_Sm. apply H1.
   assert (n2<=n1+n2) as H1. rewrite->plus_comm.  apply le_plus_l.
    apply n_le_m__Sn_le_Sm. apply H1.
Qed.
 (* FILL IN HERE *)

Theorem lt_S : forall n m,
  n < m ->
  n < S m.
Proof.
  intros. rewrite->H. unfold lt. apply le_n.
Qed.
  (* FILL IN HERE *)

Theorem ble_nat_true : forall n m,
  ble_nat n m = true -> n <= m.
Proof.

  induction n as [|n'].
  Case "n=0". destruct m as [|m'].
    SCase "m=0". intro.
        apply le_n.
    SCase "m=S m'". intro. apply O_le_n.
  Case "n=S n'".
       destruct m as [|m']. 
    SCase "m=0". intro. inversion H.
    SCase "m=S m'". intros. simpl in H. 
      assert (n'<=m') as HH.
      apply IHn'. apply H.
      apply n_le_m__Sn_le_Sm. apply HH.
Qed.
  (* FILL IN HERE *)
Theorem ble_nat_refl' : forall n:nat,
  true = ble_nat n n.
Proof.
 intro n.
 induction n as [|n'] .
 Case "n=0".
  simpl. reflexivity.
 Case "n= S n'".
  simpl. rewrite <- IHn'.
  reflexivity.
Qed. 

Theorem le_ble_nat : forall n m,
  n <= m ->
  ble_nat n m = true.
Proof.
  intros n.
  induction n as [|n'].
  Case "n=0". induction m as [|m']. 
   SCase "m=0". intro. unfold ble_nat. reflexivity.
   SCase "m=S m'". intro. unfold ble_nat. reflexivity.
  Case "n=S n'". induction m as [|m']. 
   SCase "m=0". intro. inversion H. 
   SCase "m=S m'". intro. simpl. apply IHn'. apply Sn_le_Sm__n_le_m.
      apply H.
Qed. 
  (* Hint: This may be easiest to prove by induction on [m]. *)
  (* FILL IN HERE *)

Theorem ble_nat_true_trans : forall n m o,
  ble_nat n m = true -> ble_nat m o = true -> ble_nat n o = true.                               
Proof.
   intros.
   apply ble_nat_true in H.
   apply ble_nat_true in H0.
   apply le_ble_nat.  apply le_trans with (n:=m)(m:=n).
   apply H. apply H0.
Qed.
  (* Hint: This theorem can be easily proved without using [induction]. *)
  (* FILL IN HERE *)


(** **** Exercise: 3 stars (R_provability) *)
Module R.
(** We can define three-place relations, four-place relations,
    etc., in just the same way as binary relations.  For example,
    consider the following three-place relation on numbers: *)

Inductive R : nat -> nat -> nat -> Prop :=
   | c1 : R 0 0 0 
   | c2 : forall m n o, R m n o -> R (S m) n (S o)
   | c3 : forall m n o, R m n o -> R m (S n) (S o)
   | c4 : forall m n o, R (S m) (S n) (S (S o)) -> R m n o
   | c5 : forall m n o, R m n o -> R n m o.

(** - Which of the following propositions are provable?
      - [R 1 1 2]YES
      - [R 2 2 6]NO

    - If we dropped constructor [c5] from the definition of [R],
      would the set of provable propositions change?  Briefly (1
      sentence) explain your answer.
          NO CHANGE ： C1 C2 C3 C4 对于第一和第二个位置都是对称的。
    - If we dropped constructor [c4] from the definition of [R],
      would the set of provable propositions change?  Briefly (1
      sentence) explain your answer.
          NO CHANGE : 相当于少做一次C1 C2.

(* FILL IN HERE *)
[]
*)

(** **** Exercise: 3 stars, optional (R_fact) *)  
(** Relation [R] actually encodes a familiar function.  State and prove two
    theorems that formally connects the relation and the function. 
    That is, if [R m n o] is true, what can we say about [m],
    [n], and [o], and vice versa?
*)
Lemma plus_SS: forall m n, S m =S n -> m=n.
Proof.
  intros.
  induction m as [|m'].
  Case "m=0". destruct n as [|n'].
    SCase "n=0". reflexivity.
    SCase "n=S n'". inversion H.
  Case "m=S m'". destruct n as [|n'].
    SCase "n=o". inversion H.
    SCase "n=S n'".  inversion H. reflexivity.
Qed. 
Theorem R_fact : forall n m o,
  R m n o -> m + n =o.
Proof.
  intros.
  induction H as [|m' o'| n' o'|m' n' o'|].
  Case "c1". simpl. reflexivity.
  Case "c2". simpl. rewrite->IHR. reflexivity.
  Case "c3". rewrite->plus_comm. simpl. rewrite->plus_comm. rewrite->IHR. reflexivity.
  Case "c4". simpl in IHR. rewrite->plus_comm in IHR. simpl in IHR. apply plus_SS.
      apply plus_SS. rewrite->plus_comm. apply IHR.
  Case "c5". rewrite->plus_comm. apply IHR.
Qed.
Lemma S_n_0_n: forall n, R n 0 n.
Proof.
  intros. induction n as [|n'].
  Case "n=0". apply c1.
  Case "n=S n'". apply c2. apply IHn'.
Qed.
Lemma S_0_n_n: forall n, R 0 n n.
Proof.
  intros. induction n as [|n'].
  Case "n=0". apply c1.
  Case "n=S n'". apply c3. apply IHn'.
Qed.
Theorem R_fact_versa : forall n m o,
  m + n =o->R m n o.
Proof.
  intros n. 
  induction n as [|n'].
  Case "n=0". intros. rewrite->plus_comm in H. simpl in H. rewrite<-H.
     destruct m as [|m'].
     SCase "m=0". apply c1.
     SCase "m=S m'". rewrite->H. apply S_n_0_n.
  Case "n=S n'". destruct m as [|m'].
     SCase "m=0". intros. simpl in H. rewrite->H. apply S_0_n_n.
     SCase "m=S m'". intros. rewrite<-H. simpl. apply c2. apply c5. rewrite->plus_comm.
                simpl. apply c2. apply c5. apply IHn'. apply plus_comm.
Qed.
(* FILL IN HERE *)
(** [] *)

End R.


(* ##################################################### *)
(** * Programming with Propositions *)

(** A _proposition_ is a statement expressing a factual claim,
    like "two plus two equals four."  In Coq, propositions are written
    as expressions of type [Prop].  Although we haven't discussed this
    explicitly, we have already seen numerous examples. *)

Check (2 + 2 = 4).
(* ===> 2 + 2 = 4 : Prop *)

Check (ble_nat 3 2 = false).
(* ===> ble_nat 3 2 = false : Prop *)

Check (beautiful 8).
(* ===> beautiful 8 : Prop *)

(** Both provable and unprovable claims are perfectly good
    propositions.  Simply _being_ a proposition is one thing; being
    _provable_ is something else! *)

Check (2 + 2 = 5).
(* ===> 2 + 2 = 5 : Prop *)

Check (beautiful 4).
(* ===> beautiful 4 : Prop *)

(** Both [2 + 2 = 4] and [2 + 2 = 5] are legal expressions
    of type [Prop]. *)

(** We've mainly seen one place that propositions can appear in Coq: in
    [Theorem] (and [Lemma] and [Example]) declarations. *)

Theorem plus_2_2_is_4 : 
  2 + 2 = 4.
Proof. reflexivity.  Qed.

(** But they can be used in many other ways.  For example, we have also seen that
    we can give a name to a proposition using a [Definition], just as we have
    given names to expressions of other sorts. *)

Definition plus_fact : Prop  :=  2 + 2 = 4.
Check plus_fact.
(* ===> plus_fact : Prop *)

(** We can later use this name in any situation where a proposition is
    expected -- for example, as the claim in a [Theorem] declaration. *)

Theorem plus_fact_is_true : 
  plus_fact.
Proof. reflexivity.  Qed.

(** We've seen several ways of constructing propositions.  

       - We can define a new proposition primitively using [Inductive].

       - Given two expressions [e1] and [e2] of the same type, we can
         form the proposition [e1 = e2], which states that their
         values are equal.

       - We can combine propositions using implication and
         quantification. *)

(** We have also seen _parameterized propositions_, such as [even] and
    [beautiful]. *)

Check (even 4).
(* ===> even 4 : Prop *)
Check (even 3).
(* ===> even 3 : Prop *)
Check even. 
(* ===> even : nat -> Prop *)

(** The type of [even], i.e., [nat->Prop], can be pronounced in
    three equivalent ways: (1) "[even] is a _function_ from numbers to
    propositions," (2) "[even] is a _family_ of propositions, indexed
    by a number [n]," or (3) "[even] is a _property_ of numbers."  *)

(** Propositions -- including parameterized propositions -- are
    first-class citizens in Coq.  For example, we can define functions
    from numbers to propositions... *)

Definition between (n m o: nat) : Prop :=
  andb (ble_nat n o) (ble_nat o m) = true.

(** ... and then partially apply them: *)

Definition teen : nat->Prop := between 13 19.

(** We can even pass propositions -- including parameterized
    propositions -- as arguments to functions: *)

Definition true_for_zero (P:nat->Prop) : Prop :=
  P 0.

(** Here are two more examples of passing parameterized propositions
    as arguments to a function.  

    The first function, [true_for_all_numbers], takes a proposition
    [P] as argument and builds the proposition that [P] is true for
    all natural numbers. *)

Definition true_for_all_numbers (P:nat->Prop) : Prop :=
  forall n, P n.

(** The second, [preserved_by_S], takes [P] and builds the proposition
    that, if [P] is true for some natural number [n'], then it is also
    true by the successor of [n'] -- i.e. that [P] is _preserved by
    successor_: *)

Definition preserved_by_S (P:nat->Prop) : Prop :=
  forall n', P n' -> P (S n').

(** Finally, we can put these ingredients together to define
a proposition stating that induction is valid for natural numbers: *)

Definition natural_number_induction_valid : Prop :=
  forall (P:nat->Prop),
    true_for_zero P ->
    preserved_by_S P -> 
    true_for_all_numbers P. 

Check natural_number_induction_valid .


(** **** Exercise: 3 stars (combine_odd_even) *)
(** Complete the definition of the [combine_odd_even] function
    below. It takes as arguments two properties of numbers [Podd] and
    [Peven]. As its result, it should return a new property [P] such
    that [P n] is equivalent to [Podd n] when [n] is odd, and
    equivalent to [Peven n] otherwise. *)
Definition combine_odd_even' (Podd Peven : nat -> Prop)(n:nat):Prop :=
  match oddb n  with 
              |true=>Podd n 
              |false=>Peven n
            end. 

Definition combine_odd_even (Podd Peven : nat -> Prop): nat->Prop := 
   combine_odd_even' Podd Peven.
  (* FILL IN HERE *)

(** To test your definition, see whether you can prove the following
    facts: *)

Theorem combine_odd_even_intro : 
  forall (Podd Peven : nat -> Prop) (n : nat),
    (oddb n = true -> Podd n) ->
    (oddb n = false -> Peven n) ->
    combine_odd_even Podd Peven n.
Proof.
  intros. unfold combine_odd_even. unfold combine_odd_even'.
  destruct (oddb n).
  Case "oddb n = true". apply H. reflexivity.
  Case "oddb n = false". apply H0. reflexivity.
Qed. 
  (* FILL IN HERE *)

Theorem combine_odd_even_elim_odd :
  forall (Podd Peven : nat -> Prop) (n : nat),
    combine_odd_even Podd Peven n ->
    oddb n = true ->
    Podd n.
Proof.
  intros. unfold combine_odd_even in H. unfold combine_odd_even' in H.
         rewrite->H0 in H. apply H.
Qed.
  (* FILL IN HERE *) 

Theorem combine_odd_even_elim_even :
  forall (Podd Peven : nat -> Prop) (n : nat),
    combine_odd_even Podd Peven n ->
    oddb n = false ->
    Peven n.
Proof.
   intros. unfold combine_odd_even in H. unfold combine_odd_even' in H.
   rewrite->H0 in H. apply H.
Qed.
   
  (* FILL IN HERE *)

(** [] *)

(* ##################################################### *)
(** One more quick digression, for adventurous souls: if we can define
    parameterized propositions using [Definition], then can we also
    define them using [Fixpoint]?  Of course we can!  However, this
    kind of "recursive parameterization" doesn't correspond to
    anything very familiar from everyday mathematics.  The following
    exercise gives a slightly contrived example. *)

(** **** Exercise: 4 stars, optional (true_upto_n__true_everywhere) *)
(** Define a recursive function
    [true_upto_n__true_everywhere] that makes
    [true_upto_n_example] work. *)

(*****Fixpoint true_upto_n__true_everywhere (n:nat) (f:nat->bool):Prop:=*****)
  (* match n with 
    |O => (forall m : nat, f m = true)
    |S n'=> match (f n) with
            |true=>true_upto_n__true_everywhere n' f
            |false=>True
           end
   end.
*)
  (***** match f n with 
    |false=>False
    |true=>match (pred n) with
            |O => forall m : nat,f m = true
            |S n' => true_upto_n__true_everywhere n' f
           end
   end.
*****)
(* FILL IN HERE *)
(*****
Example true_upto_n_example :
    (true_upto_n__true_everywhere 3 (fun n => even n))
  = (even 3 -> even 2 -> even 1 -> forall m : nat, even m).
Proof. reflexivity.  Qed.*****)
(** [] *)

(* $Date: 2013-07-17 16:19:11 -0400 (Wed, 17 Jul 2013) $ *)

