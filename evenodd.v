(* coq-8.3 *)
(* どーでもいい *)

Require Export Omega.
Definition even n:={a:nat&n=2*a}.
Definition odd n:={a:nat&n=2*a+1}.

Goal forall n m,even n->odd m->odd(n+m).
  intros n m P Q.
  destruct P as [a R];destruct Q as [b Q].
  exists (a+b).
  omega.
Qed.

Goal forall n,even n + odd n.
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

