(* coq-8.3 *)
(* どーでもいい *)

Require Export Omega.
Require Export Coq.Init.Wf.
Require Export Coq.Arith.Lt.
Require Export Coq.Bool.Bool.

(* First Definition *)
Definition even n:={a:nat&n=2*a}.
Definition odd n:={a:nat&n=2*a+1}.

Goal forall n m,even n->odd m->odd(n+m).
  intros n m P Q.
  destruct P as [a P];destruct Q as [b Q].
  assert(H : n+m=2*(a+b)+1) by omega.
  unfold odd;eauto.
Qed.

Goal forall n,even n+odd n.
  intro n.
  induction n.
  left.
  exists 0.
  auto.
  destruct IHn as [HL|HR].
  destruct HL as [a P].
  right;exists a;omega.
  destruct HR as [a P].
  left;exists (a+1);omega.
Qed.

Goal even 256.
  exists 128;auto.
Qed.



(* Second Definition *)
Inductive evenp:nat->Type :=
  |even_O : evenp O
  |even_S : forall n:nat,evenp n->evenp (S (S n)).

Inductive oddp:nat->Type :=
  | odd_I : oddp (S O)
  | odd_S : forall n:nat,oddp n->oddp (S (S n)).

Goal forall n,evenp n->oddp (n+1).
  intros n H.
  induction H.
  simpl;constructor.
  assert(H':S (S n)+1=S (S (n+1))) by omega.
  rewrite H';apply odd_S;auto.
Qed.

Goal forall n m,evenp n->oddp m->oddp (n+m).
  intros n m P Q.
  induction P.
  simpl;auto.
  assert(H:S (S n)+m=S (S (n+m))) by omega.
  rewrite H;apply odd_S;auto.
Qed.

Goal evenp 256.
  repeat constructor.
Qed.


(* 
-- Third Definition 
iseven/isoddの型をnat->boolにしておけば、
forall n,(iseven n=true) \/ (iseven n=false)
を一々証明しなくくていい

iseven/isoddの型をnat->Propやnat->Typeにすると、場合によっては
forall n,(iseven n=True) + (iseven n=False)
等を証明する必要があって。手間が一つ増える。その代わり、
forall n, iseven n=true -> even n
ではなく、
forall n ,iseven n-> even n
という書き方が許される

e.g.
Fixpoint iseven (n:nat) : Type :=
  match n with
    | O =>  (True:Tyep)
    | S O => (False:Type)
    | S (S n') => iseven n'
end.
*)

Fixpoint iseven (n:nat) : bool :=
  match n with
    | O => true
    | S O => false
    | S (S n') => iseven n'
end.

Fixpoint isodd (n:nat) : bool :=
  match n with
    | O => false
    | S O => true
    | S (S n') => isodd n'
end.

Goal forall n,even n->iseven n=true.
  intros n H.
  destruct H as [a H].
  subst.
  induction a.
  simpl;constructor.
  assert(H':2*(S a)=S (S (2*a))) by omega.
  rewrite H';simpl;auto.
Qed.



(* lt_wfと同じ。只の練習 *)
Goal well_founded lt.
  intro n.
  induction n as [|n IHn].
  constructor;intros;assert(XX:False) by omega;contradiction.
  constructor;intros m H.
  destruct (lt_eq_lt_dec n m) as [C1|C3].
  destruct C1 as [C1|C2].
  assert(XX:False) by omega;contradiction.
  rewrite <- C2;exact IHn.
  induction IHn as [n H1];exact (H1 m C3).
Qed.


Lemma iseven_is_valid: forall n,iseven n=true->even n.
  refine (well_founded_induction_type lt_wf (fun (n:nat)=>iseven n=true->even n) _).
  intros n H P.
  induction n as [|n _].
  exists 0;auto.
  remember (iseven n) as even_n.
  destruct even_n.
  assert(H':forall x,iseven (S x)=negb (iseven x)).
    induction x as [|x IHx].
    auto.
    rewrite IHx;rewrite negb_involutive;simpl;auto.
  rewrite (H' n) in P.
  rewrite (@eq_sym bool true (iseven n) Heqeven_n) in P.
  contradiction diff_true_false.
  simpl in P.
  exact (@eq_sym bool false true P).
  induction n as [|n].
  discriminate.
  destruct (H n).
  omega.
  simpl in P;auto.
  subst;exists (x+1);omega.
Qed.

Goal iseven 128=true.
  simpl;constructor.
Qed.


(* おまけ *)
Definition empty:Type := False.

Goal (unit:Type)<>empty.
  intro H.
  assert(lift:forall (A B:Type),(A=B)->(A->B)).
    intros A B P.
    induction P.
    tauto.
  assert(H':=lift unit empty H).
  tauto.
Qed.



