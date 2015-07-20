(** * SfLib: Software Foundations Library *)

(* $Date: 2013-07-17 16:19:11 -0400 (Wed, 17 Jul 2013) $ *)

(** Here we collect together several useful definitions and theorems
    from Basics.v, List.v, Poly.v, Ind.v, and Logic.v that are not
    already in the Coq standard library.  From now on we can [Import]
    or [Export] this file, instead of cluttering our environment with
    all the examples and false starts in those files. *)

(** * From the Coq Standard Library *)

Require Omega.   (* needed for using the [omega] tactic *)
Require Export Bool.
Require Export List.
Export ListNotations.
Require Export Arith.
Require Export Arith.EqNat.  (* Contains [beq_nat], among other things *)

(** * From Basics.v *)

Definition admit {T: Type} : T.  Admitted.

Require String. Open Scope string_scope.

Ltac move_to_top x :=
  match reverse goal with
  | H : _ |- _ => try move x after H
  end.

Tactic Notation "assert_eq" ident(x) constr(v) :=
  let H := fresh in
  assert (x = v) as H by reflexivity;
  clear H.

Tactic Notation "Case_aux" ident(x) constr(name) :=
  first [
    set (x := name); move_to_top x
  | assert_eq x name; move_to_top x
  | fail 1 "because we are working on a different case" ].

Tactic Notation "Case" constr(name) := Case_aux Case name.
Tactic Notation "SCase" constr(name) := Case_aux SCase name.
Tactic Notation "SSCase" constr(name) := Case_aux SSCase name.
Tactic Notation "SSSCase" constr(name) := Case_aux SSSCase name.
Tactic Notation "SSSSCase" constr(name) := Case_aux SSSSCase name.
Tactic Notation "SSSSSCase" constr(name) := Case_aux SSSSSCase name.
Tactic Notation "SSSSSSCase" constr(name) := Case_aux SSSSSSCase name.
Tactic Notation "SSSSSSSCase" constr(name) := Case_aux SSSSSSSCase name.

Fixpoint ble_nat (n m : nat) : bool :=
  match n with
  | O => true
  | S n' =>
      match m with
      | O => false
      | S m' => ble_nat n' m'
      end
  end.

Theorem andb_true_elim1 : forall b c,
  andb b c = true -> b = true.
Proof.
  intros b c H.
  destruct b.
  Case "b = true".
    reflexivity.
  Case "b = false".
    rewrite <- H. reflexivity.  Qed.

Theorem andb_true_elim2 : forall b c,
  andb b c = true -> c = true.
Proof.
 intros.
 destruct b.
 Case "b=true". simpl in H. apply H.
 Case "c=false". simpl in H. inversion H.
Qed.
(* An exercise in Basics.v *)


Theorem beq_nat_sym : forall (n m : nat),
  beq_nat n m = beq_nat m n.
Proof.
  induction n as [|n'].
  Case "n=0". destruct m as [|m'].
    SCase "m=0". reflexivity.
    SCase "m=S m'". simpl. reflexivity.
  Case "n=S n'". destruct m as [|m'].
    SCase "m=0". simpl. reflexivity.
    SCase "m=S m'". simpl. apply IHn'.
Qed.
(* An exercise in Lists.v *)

(** * From Props.v *)

Inductive ev : nat -> Prop :=
  | ev_0 : ev O
  | ev_SS : forall n:nat, ev n -> ev (S (S n)).

(** * From Logic.v *)

Theorem andb_true : forall b c,
  andb b c = true -> b = true /\ c = true.
Proof.
  intros b c H.
  destruct b.
    destruct c.
      apply conj. reflexivity. reflexivity.
      inversion H.
    inversion H.  Qed.
Theorem ex_falso_quodlibet : forall (P:Prop),
  False -> P.
Proof.
  intros P contra.
  inversion contra.  Qed.

Theorem false_beq_nat: forall n n' : nat,
     n <> n' ->
     beq_nat n n' = false.
Proof.
 induction n as [|t].
 Case "n=0". destruct n' as [|t'].
   SCase "n'=0". intro. apply ex_falso_quodlibet.
          apply H. reflexivity.
   SCase "n'=S t'". intro. simpl. reflexivity.
 Case "n=S t". destruct n' as [|t'].
   SCase "n'=0". intro. simpl. reflexivity.
   SCase "n'=S t'". intro. simpl. apply IHt. unfold not.
               intro. unfold not in H. apply H. rewrite->H0.
                 reflexivity.
Qed. 
(* An exercise in Logic.v *)



Theorem ev_not_ev_S : forall n,
  ev n -> ~ ev (S n).
Proof.
 intros.
 induction H.
 Case "ev 0". unfold not. intro. inversion H.
 Case "ev_SS". unfold not. intro. unfold not in IHev.
               apply IHev. inversion H0. apply H2.
Qed.
(* An exercise in Logic.v *)
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
Theorem ble_nat_false : forall n m,
  ble_nat n m = false -> ~(n <= m).
Proof.
 unfold not.
  induction n as [|n'].
  Case "n=O". destruct m as [|m'].
    SCase "m=O". intros. inversion H.
    SCase "m=S m'". intros. inversion H.
  Case "n=S n'". destruct m as [|m'].
    SCase "m=O". intros. inversion H0.
    SCase "m=S m'". intros. inversion H in H0.
               apply IHn' with (m:=m'). apply H2. apply Sn_le_Sm__n_le_m.
               apply H0. 
Qed.
              
(* An exercise in Logic.v *)
Lemma O_le_n : forall n:nat,
  0<=n.
Proof.
  induction n as [|n'].
  Case "n=0".
   reflexivity.
  Case "n=S n'".
   apply le_S. apply IHn'.
Qed.
Lemma n_le_m__Sn_le_Sm: forall n m,
  n <= m->S n <= S m.
Proof.
  destruct n as [|n'].
  Case "n=0". induction m as [|m'].
    SCase "m=0". intro. reflexivity.
    SCase "m=S m'". intro. apply le_S.  apply IHm'. apply O_le_n.
  Case "n=S n'". induction m as [|m'].
    SCase "m=0". intro. inversion H.
    SCase "m=S m'". intro. inversion H. reflexivity. apply le_S. apply IHm'. apply H1.
Qed.

Theorem ble_nat_true : forall n m,
  ble_nat n m = true -> n <= m.
Proof.
  induction n as [|n'].
  Case "n=0". destruct m as [|m'].
    SCase "m=0". intro. reflexivity.
    SCase "m=S m'". intro. apply O_le_n.
  Case "n=S n'". destruct m as [|m'].
    SCase "m=0". intro. inversion H.
    SCase "m=S m'". simpl. intro. apply n_le_m__Sn_le_Sm. apply IHn'.
                      apply H.
Qed.
(* An exercise in Logic.v *)




Inductive appears_in (n : nat) : list nat -> Prop :=
| ai_here : forall l, appears_in n (n::l)
| ai_later : forall m l, appears_in n l -> appears_in n (m::l).


Inductive next_nat (n:nat) : nat -> Prop :=
  | nn : next_nat n (S n).

Inductive total_relation : nat -> nat -> Prop :=
  tot : forall n m : nat, total_relation n m.

Inductive empty_relation : nat -> nat -> Prop := .

(** * From Later Files *)

Definition relation (X:Type) := X -> X -> Prop.

Definition deterministic {X: Type} (R: relation X) :=
  forall x y1 y2 : X, R x y1 -> R x y2 -> y1 = y2. 

Inductive multi (X:Type) (R: relation X) 
                            : X -> X -> Prop :=
  | multi_refl  : forall (x : X),
                 multi X R x x
  | multi_step : forall (x y z : X),
                    R x y ->
                    multi X R y z ->
                    multi X R x z.
Implicit Arguments multi [[X]]. 

Tactic Notation "multi_cases" tactic(first) ident(c) :=
  first;
  [ Case_aux c "multi_refl" | Case_aux c "multi_step" ].

Theorem multi_R : forall (X:Type) (R:relation X) (x y : X),
       R x y -> multi R x y.
Proof.
  intros X R x y r.
  apply multi_step with y. apply r. apply multi_refl.   Qed.

Theorem multi_trans :
  forall (X:Type) (R: relation X) (x y z : X),
      multi R x y  ->
      multi R y z ->
      multi R x z.
Proof.
  intros.
  induction H. apply H0.
  apply multi_step with (x:=x)(z:=z)(y:=y).
  apply H. apply IHmulti.
  apply H0.
Qed.
  (* FILL IN HERE *) 

(**  Identifiers and polymorphic partial maps. *)

Inductive id : Type := 
  Id : nat -> id.

Theorem eq_id_dec : forall id1 id2 : id, {id1 = id2} + {id1 <> id2}.
Proof.
   intros id1 id2.
   destruct id1 as [n1]. destruct id2 as [n2].
   destruct (eq_nat_dec n1 n2) as [Heq | Hneq].
   Case "n1 = n2".
     left. rewrite Heq. reflexivity.
   Case "n1 <> n2".
     right. intros contra. inversion contra. apply Hneq. apply H0.
Defined. 

Lemma eq_id : forall (T:Type) x (p q:T), 
              (if eq_id_dec x x then p else q) = p. 
Proof.
  intros. 
  destruct (eq_id_dec x x); try reflexivity. 
  apply ex_falso_quodlibet;auto.
Qed.

Lemma neq_id : forall (T:Type) x y (p q:T), x <> y -> 
               (if eq_id_dec x y then p else q) = q. 
Proof.
  intros.
  destruct (eq_id_dec x y). apply ex_falso_quodlibet. apply H. apply e.
  reflexivity.
Qed.
  (* FILL IN HERE *)

Definition partial_map (A:Type) := id -> option A.

Definition empty {A:Type} : partial_map A := (fun _ => None). 

Notation "'\empty'" := empty.

Definition extend {A:Type} (Gamma : partial_map A) (x:id) (T : A) :=
  fun x' => if eq_id_dec x x' then Some T else Gamma x'.

Lemma extend_eq : forall A (ctxt: partial_map A) x T,
  (extend ctxt x T) x = Some T.
Proof.
  intros. unfold extend. rewrite eq_id; auto. 
Qed.

Lemma extend_neq : forall A (ctxt: partial_map A) x1 T x2,
  x2 <> x1 ->
  (extend ctxt x2 T) x1 = ctxt x1.
Proof.
  intros. unfold extend. rewrite neq_id; auto. 
Qed.

Lemma extend_shadow : forall A (ctxt: partial_map A) t1 t2 x1 x2,
  extend (extend ctxt x2 t1) x2 t2 x1 = extend ctxt x2 t2 x1.
Proof with auto.
  intros. unfold extend. destruct (eq_id_dec x2 x1)...
Qed.

(** -------------------- *)

(** * Some useful tactics *)

Tactic Notation "solve_by_inversion_step" tactic(t) :=  
  match goal with  
  | H : _ |- _ => solve [ inversion H; subst; t ] 
  end
  || fail "because the goal is not solvable by inversion.".

Tactic Notation "solve" "by" "inversion" "1" :=
  solve_by_inversion_step idtac.
Tactic Notation "solve" "by" "inversion" "2" :=
  solve_by_inversion_step (solve by inversion 1).
Tactic Notation "solve" "by" "inversion" "3" :=
  solve_by_inversion_step (solve by inversion 2).
Tactic Notation "solve" "by" "inversion" :=
  solve by inversion 1.
