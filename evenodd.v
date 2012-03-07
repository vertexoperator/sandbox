(* coq-8.3 *)
(* どーでもいい *)

Require Export Omega.
Require Export NPeano.
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
-- Third definition
-- 色々めんどい
-- mod_lt/mod_add/mod_plusは標準ライブラリにありそうなもんだが
*)


(*
Fixpoint mod2 n :=
  match n with 
    | S (S n') => mod2 n'
    | _ => n
end.
*)

Definition mod2 n := n mod 2.

(*　面倒なので略 *)
Lemma mod_lt : forall n m,0 < m -> n mod m < m.
Admitted.

Lemma mod_plus : forall n n' m, 0 < m -> (n+n') mod m = ((n mod m) + (n' mod m)) mod m.
Admitted.

Lemma mod_add : forall a b c, 0 < c -> (a + b * c) mod c = a mod c.
Admitted.


Goal forall n,even n->mod2 n=0.
  unfold mod2.
  intros n H.
  destruct H as [a H].
  subst.
  induction a as [ | a IH].
  simpl;auto.
  assert(H':2* S a=2*a+1*2) by omega.
  assert(O_lt_2 : 0< 2) by omega.
  assert(H'':=mod_add (2*a) 1 2 O_lt_2).
  congruence.
Qed.


Lemma check_even_by_mod2 : forall n,mod2 n=0->even n.
  refine (well_founded_induction_type lt_wf (fun (n:nat)=>mod2 n=0->even n) _).
  unfold mod2.
  intros n H P.
  induction n as [|n _].
  exists 0;auto.
  (* omegaバグってる? *)
  assert(H':n mod 2=1).
    assert(H1:=mod_plus n 1 2).
    assert(H2:=mod_lt n 2).
    assert(H3:S n=n+1) by omega.
    rewrite H3 in P.
    rewrite P in H1.
    assert(H4:1 mod 2=1) by (simpl;auto).
    rewrite H4 in H1.
    assert(H6:0<2) by omega.
    assert(H7:=H2 H6).
    assert(H8:=H1 H6).
    assert(H9: n mod 2<>0).
      intro H9.
      rewrite H9 in H8.
      simpl in H8.
      omega.
    omega.
  induction n as [|n].
  discriminate.
  destruct (H n).
  omega.
  assert(O_lt_2:0<2) by omega.
  assert(H'':=mod_add n 1 2 O_lt_2).
  assert(H''':S (S n)=n+1*2) by omega.
  congruence.
  subst;exists (x+1);omega.
Qed.




(* 
-- Fourth Definition 
-- "n mod 2=0->even n"の証明は、Z/2Zが環になることとか
forall n,n mod 2 = 0 \/ n mod 2=1
の証明が意外と大変

以下のように、isevenを定義しておくと、証明が簡略化される
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


(* おまけ1 *)
(* lt_wfと同じ。只の練習 *)
Goal well_founded lt.
  intro n.
  induction n as [ |n IHn].
  constructor;intros m H.
  assert(H':~(m<0)) by omega;tauto.
  constructor;intros m H.
  assert(P:(n=m) \/ (m<n)) by omega.
  assert(P1:n=m -> Acc lt m) by congruence.
  assert(P2:m<n->Acc lt m).
    induction IHn as [n IHn];exact (IHn m).
  tauto.
Qed.


(* おまけ2 *)
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



