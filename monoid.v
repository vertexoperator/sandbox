(* coq8.3 *)
(* normalization by evalutionとproof by reflectionの練習 *)

Class MonoidStructure (M:Type) := {
  Mop : M -> M -> M;
  Mid : M;
  Mop_assoc : forall a b c:M , Mop a (Mop b c) = Mop (Mop a b) c;
  Mop_lunit : forall a:M , Mop Mid a = a;
  Mop_runit : forall a:M , Mop a Mid = a }.

Implicit Arguments Mop [M].
Implicit Arguments Mid [M].
Implicit Arguments Mop_assoc [M].
Implicit Arguments Mop_runit [M].
Implicit Arguments Mop_lunit [M].


Section MonoidReflect.
  Variable M:Type.
  Variable T:MonoidStructure M.

  Inductive MonoidTerm :=
    | identity : MonoidTerm
    | var : M -> MonoidTerm
    | op : MonoidTerm -> MonoidTerm -> MonoidTerm.

  Definition embed : MonoidTerm -> (MonoidTerm -> MonoidTerm).
    intro x.
    induction x as [ | a | _ M1 _ M2].
       exact (fun x=>x).
       exact (fun x=> op (var a) x).
       exact (fun x => (M1 (M2 x))).
  Defined.

  Definition normalize : MonoidTerm -> MonoidTerm := 
     (fun x => embed x identity).

  Definition eval : MonoidTerm -> M.
     intro x;induction x as [ | a | _ M1 _ M2].
        exact (Mid T).
        exact a.
        exact (Mop T M1 M2).
  Defined.

  Lemma op_eq_embed : forall (e e':MonoidTerm),eval (op e e') = eval (embed e e').
     intro e;induction e as [ | a | e1 M1 e2 M2].
        idtac "case of identity".
           exact (fun x => Mop_lunit T (eval x)).
        idtac "case of var a".
           reflexivity.
        idtac "case of var e1 e2".
           assert(H:forall x y,eval (op x y)=Mop T (eval x) (eval y)) by reflexivity.
           intro e';simpl.
           rewrite <- (M1 (embed e2 e')).
           rewrite (H e1 (embed e2 e')).
           rewrite <- (M2 e').
           rewrite (H e2 e').
           apply eq_sym;exact (Mop_assoc T _ _ _).
  Qed.

  Theorem monoid_reflect : forall (e e':MonoidTerm),normalize e=normalize e' -> eval e=eval e'.
     intros e e' H.
     assert(P:forall t,eval (normalize t) = eval t).
       intro t.
       assert(P1:=op_eq_embed t identity).
       assert(P2:=Mop_runit T (eval t)).
       assert(P3:eval (op t identity)=Mop T (eval t) (Mid T)) by reflexivity.
       unfold normalize;congruence.
     assert(H1 : eval (normalize e) = eval e) by (exact (P e)).
     assert(H2 : eval (normalize e') = eval e') by (exact (P e')).
     congruence.
  Qed.

  (*
-- 逆はいえない
-- @eval nat nat_is_monoid (op (var 1) (var 2)) = @eval nat nat_is_monoid (var 3)
-- but , normalize nat (op (var 1) (var 2)) <> normalize nat (var 3).
   *)
End MonoidReflect.

Implicit Arguments var [M].
Implicit Arguments op [M].
Implicit Arguments monoid_reflect [M].
Implicit Arguments eval [M].


(* 
   例:list_is_monoidをunfoldableにしておかないと、
   evalの簡約ができなくなるので注意 
*)
Require Import List.
Instance list_is_monoid {X} : MonoidStructure (list X) := 
   Build_MonoidStructure _ _ _ (@app_assoc X) (@app_nil_l X) (@app_nil_r X).

Goal forall X (x y z w :list X),(x++y)++(z++w)=((x++y)++z)++w.
   intros X x y z w.
   set (e1:=op (op (var x) (var y)) (op (var z) (var w))).
   set (e2:=op (op (op (var x) (var y)) (var z)) (var w)).
   let p:=fresh in assert(p:=monoid_reflect _ e1 e2 eq_refl);simpl in p;auto.
Qed.



