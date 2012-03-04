(* coq-8.3 *)
(* どーでもいい *)

Require Export Omega.
Require Export Coq.Init.Wf.
Require Export Coq.Arith.Lt.


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


(* Third Definition *)
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

Goal forall n,iseven n=iseven(n+2).
  induction n.
  intros;simpl;auto.
  assert(H':S n+2=S (S (S n))) by omega.
  rewrite H';simpl;auto.
Qed.

Goal forall n,even n->iseven n=true.
  intros n H.
  destruct H as [a H].
  subst.
  induction a.
  simpl;constructor.
  assert(H':2*(S a)=S (S (2*a))) by omega.
  rewrite H';simpl;auto.
Qed.


(* TODO:prove even_ind_step *)
Axiom even_ind_step: forall n:nat,(forall m:nat,m<n->iseven m=true->even m)->iseven n=true->even n.

Goal forall n,iseven n=true->even n.
  exact (well_founded_induction_type lt_wf (fun (n:nat)=>iseven n=true->even n) even_ind_step ).
Qed.


Goal iseven 128=true.
  simpl;constructor.
Qed.



(* おまけ *)
Inductive _empty :=.
Definition empty:Type := _empty.

Goal (unit:Type)<>empty.
  intro H.
  assert(lift:forall (A B:Type),(A=B)->(A->B)).
    intros A B P.
    induction P.
    tauto.
  assert(H':=lift unit empty H).
  assert(g:empty->False) by (intro p;induction p).
  tauto.
Qed.


