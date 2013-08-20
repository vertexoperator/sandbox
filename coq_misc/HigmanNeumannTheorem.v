(* Coq-8.3 *)
(*
背景:
"Categorical Logic and Type Theory" Exercise 2.2.3(i)(ii)の証明

群（G,m,i,e)に於いて、left division d(x,y)=m(i(x),y)は
以下の公理を満たし、
d(d(d(z,d(x,d(x,x))),d(z,d(y,d(x,x)))),x)=y
逆に、dがあれば、Gの任意の元aによって、
e=d(a,a)
i(x)=d(x,d(a,a))
m(x,y)=d(d(x,d(a,a)),y)
は群の公理を満たすことの証明

元ネタは
G. Higman and B. H. Neuman, 'Groups as groupoids with one law', 
Publ. Math. Debrecen. 2 (1952), 215-221
にあるらしい

更に、その前Tarskiは"アーベル群の公理"
z-((x-y)-(x-z))=y
を見つけていたらしい。

証明は、機械的に完備化していけば終わる。けど、手でやるのは死ねるので
コンピュータの力を借りるべき

無駄とか多いだろうけど、整理する気にはならない。多分一生ならない

*)

Require Export Setoid.

Section Group.
Variable G:Set.
Variable m:G->G->G.
Variable i:G->G.
Variable e:G.

Definition assoc :Prop := forall (x y z:G),m (m x y) z= m x (m y z).
Definition invL : Prop := forall (x:G),m x (i x)=e.
Definition invR : Prop := forall (x:G),m (i x) x=e.
Definition unitL : Prop := forall (x:G),m x e = x.
Definition unitR : Prop := forall (x:G),m e x=x.

Definition group := assoc /\ invL /\ invR /\ unitL /\ unitR.
End Group.


Section Group'.
Variable G:Set.
Definition ldiv (d:G->G->G) (a:G) :Prop := forall (x y z:G),(d (d (d z (d x (d x x))) (d z (d y (d x x)))) x)=y.
End Group'.

Lemma inv_check:forall (G:Set) (m:G->G->G) (i:G->G) (e x y:G),group G m i e->m x y=e->i x=y.
Proof.
unfold group.
intros G m i e x y H H'.
destruct H;destruct H0;destruct H1;destruct H2.
congruence.
Qed.

Lemma inv_m:forall (G:Set) (m:G->G->G) (i:G->G) (e x y:G),group G m i e->i (m x y)=m (i y) (i x).
Proof.
intros G m i e x y H.
assert(H4:=inv_check G m i e (m x y) (m (i y) (i x)) H).
unfold group in H.
destruct H;destruct H0;destruct H1;destruct H2.
unfold assoc,invL,invR,unitL,unitR in *|-.
assert(H5:m (m x y) (m (i y) (i x))=e).
congruence.
exact (H4 H5).
Qed.


Lemma inv_inv:forall (G:Set) (m:G->G->G) (i:G->G) (e x:G),group G m i e->i (i x)=x.
Proof.
intros G m i e x H.
assert(H':=inv_check G m i e (i x) x H).
destruct H;destruct H0;destruct H1;destruct H2.
unfold invR in *|-.
exact (H' (H1 x)).
Qed.


Goal forall (G:Set) (m:G->G->G) (i:G->G) (e:G),group G m i e -> ldiv G (fun x y =>(m (i x) y)) e.
Proof.
intros G m i e H v1 v2 v3.
assert(H':=fun (x:G)=>inv_inv G m i e x H).
assert(H'':=fun (x y:G)=>inv_m G m i e x y H).
unfold group in *|-.
unfold ldiv in *|-.
destruct H;destruct H0;destruct H1;destruct H2.
unfold assoc,invL,invR,unitL,unitR in *|-.
congruence.
Qed.


Lemma e1 : forall (G:Set) (d:G->G->G) (a:G),ldiv G d a->(forall (v1 v2 v5 v6:G), (d (d v5 (d (d (d v6 (d (d v1 (d v1 v1)) (d (d v1 (d v1 v1)) (d v1 (d v1 v1))))) (d v6 (d v5 (d (d v1 (d v1 v1)) (d v1 (d v1 v1)))))) (d v2 (d v1 v1)))) v1) = v2).
Proof.
unfold ldiv;intros G d a H v1 v2 v5 v6.
assert(H':= H v1 v2 (d (d v6 (d (d v1 (d v1 v1)) (d (d v1 (d v1 v1)) (d v1 (d v1 v1))))) (d v6 (d v5 (d (d v1 (d v1 v1)) (d v1 (d v1 v1))))))).
rewrite (H (d v1 (d v1 v1)) v5 v6) in H'.
exact H'.
Qed.


Lemma e2 : forall (G:Set) (d:G->G->G) (a:G),ldiv G d a->(forall (v1 v2 v5 v6:G),(d (d (d (d (d v6 (d (d v2 (d v1 v1)) (d (d v2 (d v1 v1)) (d v2 (d v1 v1))))) (d v6 (d v5 (d (d v2 (d v1 v1)) (d v2 (d v1 v1)))))) (d v1 (d v1 v1))) v5) v1) = v2).
Proof.
unfold ldiv;intros G d a H v1 v2 v5 v6.
assert(H':=H v1 v2 (d (d v6 (d (d v2 (d v1 v1)) (d (d v2 (d v1 v1)) (d v2 (d v1 v1))))) (d v6 (d v5 (d (d v2 (d v1 v1)) (d v2 (d v1 v1))))))).
rewrite (H (d v2 (d v1 v1)) v5 v6) in H'.
exact H'.
Qed.

Lemma e3 : forall (G:Set) (d:G->G->G) (a:G),ldiv G d a->(forall (v1 v3 v5 v6 :G),(d (d (d v3 (d v1 (d v1 v1))) (d v3 v5)) v1) = (d (d v6 (d (d v1 v1) (d (d v1 v1) (d v1 v1)))) (d v6 (d v5 (d (d v1 v1) (d v1 v1)))))).
unfold ldiv;intros G d a H v1 v3 v5 v6.
assert(H':=H v1 (d (d v6 (d (d v1 v1) (d (d v1 v1) (d v1 v1)))) (d v6 (d v5 (d (d v1 v1) (d v1 v1))))) v3).
rewrite (H (d v1 v1) v5 v6) in H'.
exact H'.
Qed.

Lemma e4 : forall (G:Set) (d:G->G->G) (a:G),ldiv G d a->(forall (v2 v8 :G),(d (d v8 v8) v2) = v2).
Proof.
unfold ldiv;intros G d a H v2 v8.
assert(H':=e1 G d a H v2 v2 v8 a).
rewrite (H (d v2 (d v2 v2)) v8 a) in H'.
exact H'.
Qed.

Lemma e5 : forall (G:Set) (d:G->G->G) (a:G),ldiv G d a->(forall (v1 v2 :G),(d (d (d v1 (d v1 v1)) (d v2 (d v1 v1))) v1) = v2).
Proof.
unfold ldiv;intros G d a H v1 v2.
assert(H':=e2 G d a H v1 v2 (d v2 (d v1 v1)) a).
rewrite (e4 G d a H (d v1 (d v1 v1)) (d a (d (d v2 (d v1 v1)) (d (d v2 (d v1 v1)) (d v2 (d v1 v1)))))) in H'.
exact H'.
Qed.

Lemma e6 : forall (G:Set) (d:G->G->G) (a:G),ldiv G d a->(forall (v1 v4 :G),(d (d (d v1 (d v1 v1)) v4) v1) = (d v4 (d v1 v1)) ).
Proof.
unfold ldiv;intros G d a H v1 v4.
assert(H':=e5 G d a H v1 (d (d (d v1 v1) (d (d v1 v1) (d v1 v1))) (d v4 (d (d v1 v1) (d v1 v1))))).
rewrite (e5 G d a H (d v1 v1) v4) in H'.
repeat rewrite (e4 G d a H) in H'.
exact H'.
Qed.

Lemma e7 : forall (G:Set) (d:G->G->G) (a:G),ldiv G d a->unitL G (fun x y=>d (d x (d a a)) y) (d a a).
Proof.
unfold ldiv,unitL.
intros G d a H x.
assert(H':=e5 G d a H a x).
rewrite (e6 G d a H a (d x (d a a))) in H'.
exact H'.
Qed.

Lemma e8 : forall (G:Set) (d:G->G->G) (a:G),ldiv G d a->(forall (v2 v3 :G),(d (d v2 (d v3 v3)) (d v3 v3)) = v2).
Proof.
unfold ldiv;intros G d a H v2 v3.
assert(H':=e5 G d a H v3 v2).
rewrite (e6 G d a H v3 (d v2 (d v3 v3))) in H'.
exact H'.
Qed.

Lemma e9 :  forall (G:Set) (d:G->G->G) (a:G),ldiv G d a->(forall (x y:G),d x x=d y y).
Proof.
unfold ldiv;intros G d a H x y.
assert(H':=e8 G d a H (d y y) x).
rewrite (e4 G d a H (d x x) y) in H'.
rewrite (e4 G d a H) in H'.
exact H'.
Qed.

Lemma e10: forall (G:Set) (d:G->G->G) (a:G),ldiv G d a->invR G (fun x y=>d (d x (d a a)) y) (fun x=>d x (d a a)) (d a a).
Proof.
unfold ldiv,invR.
intros.
rewrite (e8 G d a H).
exact (e9 G d a H x a).
Qed.


Lemma e11: forall (G:Set) (d:G->G->G) (a:G),ldiv G d a->invL G (fun v w=>d (d v (d v v)) w) (fun x=>d x (d x x)) (d a a).
Proof.
unfold ldiv,invL.
intros.
assert(H1:=e1 G d a H).
assert(H2:=e2 G d a H).
assert(H3:=e3 G d a H).
assert(H4:=e4 G d a H).
assert(H5:=e5 G d a H).
assert(H6:=e6 G d a H).
assert(H7:=e7 G d a H).
assert(H8:=e8 G d a H).
assert(H9:=e9 G d a H).
assert(H10:=e10 G d a H).
congruence.
Qed.


Lemma e12 : forall (G:Set) (d:G->G->G) (a:G),ldiv G d a->unitR G (fun x y=>d (d x (d a a)) y) (d a a).
Proof.
unfold ldiv,unitR.
intros G d a H x.
assert(H1:=e1 G d a H).
assert(H2:=e2 G d a H).
assert(H3:=e3 G d a H).
assert(H4:=e4 G d a H).
assert(H5:=e5 G d a H).
assert(H6:=e6 G d a H).
assert(H7:=e7 G d a H).
assert(H8:=e8 G d a H).
assert(H9:=e9 G d a H).
assert(H10:=e10 G d a H).
congruence.
Qed.


Lemma e15: forall (G:Set) (d:G->G->G) (a:G),ldiv G d a->(forall (v1 v4 v7 v8:G),d (d (d (d v8 v4) (d v8 (d v7 (d v1 v1)))) (d v1 v1)) v7 = d v4 (d a a)).
Proof.
unfold ldiv;intros G d a H v1 v4 v7 v8.
assert(H':=e5 G d a H v1 (d (d (d (d v8 (d (d v4 (d (d v1 v1) (d v1 v1))) (d (d v4 (d (d v1 v1) (d v1 v1))) (d v4 (d (d v1 v1) (d v1 v1)))))) (d v8 (d v7 (d (d v4 (d (d v1 v1) (d v1 v1))) (d v4 (d (d v1 v1) (d v1 v1))))))) (d (d v1 v1) (d (d v1 v1) (d v1 v1)))) v7)).
rewrite (e2 G d a H (d v1 v1) v4 v7 v8) in H'.
assert(H4:=e4 G d a H).
assert(H8:=e8 G d a H).
assert(H9:=e9 G d a H).
repeat rewrite H4 in H'.
rewrite (H9 (d v4 (d v1 v1)) v1) in H'.
rewrite H8 in H'.
assert(H5:=e5 G d a H).
assert(H6:=e6 G d a H).
assert(H7:=e7 G d a H).
congruence.
Qed.


Lemma e16: forall (G:Set) (d:G->G->G) (a:G),ldiv G d a->(forall (x y:G),d (d x x) (d y y)=d a a).
Proof.
unfold ldiv;intros.
assert(H4:=e4 G d a H).
assert(H5:=e5 G d a H).
assert(H6:=e6 G d a H).
assert(H7:=e7 G d a H).
assert(H8:=e8 G d a H).
assert(H9:=e9 G d a H).
assert(H10:=e10 G d a H).
assert(H11:=e11 G d a H).
assert(H12:=e12 G d a H).
assert(H15:=e15 G d a H).
congruence.
Qed.


Lemma e17: forall (G:Set) (d:G->G->G) (a:G),ldiv G d a->(forall (v1 v10 :G),(d (d v1 (d v10 v10)) (d v10 v10)) = v1).
Proof.
unfold ldiv;intros.
assert(H4:=e4 G d a H).
assert(H5:=e5 G d a H).
assert(H6:=e6 G d a H).
assert(H7:=e7 G d a H).
assert(H8:=e8 G d a H).
assert(H9:=e9 G d a H).
assert(H10:=e10 G d a H).
assert(H11:=e11 G d a H).
assert(H12:=e12 G d a H).
assert(H15:=e15 G d a H).
congruence.
Qed.


Lemma e18: forall (G:Set) (d:G->G->G) (a:G),ldiv G d a->(forall (v4 v8:G),(d (d v8 v4) (d v8 (d a a))) = (d v4 (d a a))).
Proof.
unfold ldiv;intros.
assert(H':=e6 G d a H (d (d (d a (d a a)) v8) a) v4).
rewrite (e6 G d a H a v8) in H'.
rewrite (e9 G d a H (d v8 (d a a)) a) in H'.
rewrite (e17 G d a H v8 a) in H'.
exact H'.
Qed.


Lemma e19: forall (G:Set) (d:G->G->G) (a:G),ldiv G d a->(forall (v1 v2 v6 v8:G),(d (d v8 (d (d (d v6 v1) (d v6 (d v8 (d v1 v1)))) (d v2 (d v1 v1)))) v1) = v2).
Proof.
unfold ldiv;intros.
assert(H':=e1 G d a H v1 v2 (d (d a a) v8) v6 ).
rewrite (e4 G d a H v8 a) in H'.
rewrite (e9 G d a H (d v1 (d v1 v1)) v1) in H'.
rewrite (e8 G d a H v1 v1) in H'.
exact H'.
Qed.

Lemma e20: forall (G:Set) (d:G->G->G) (a:G),ldiv G d a->(forall (v1 v2 v5:G),(d (d v5 (d (d v1 (d v5 (d v1 v1))) (d v2 (d v1 v1)))) v1) = v2).
Proof.
unfold ldiv;intros.
assert(H':=e1 G d a H v1 v2 v5 (d v1 v1) ).
rewrite (e9 G d a H (d v1 (d v1 v1)) v1) in H'.
rewrite (e17 G d a H v1 v1) in H'.
rewrite (e4 G d a H v1 v1) in H'.
rewrite (e4 G d a H (d v5 (d v1 v1)) v1) in H'.
exact H'.
Qed.

Lemma e21: forall (G:Set) (d:G->G->G) (a:G),ldiv G d a->(forall (v6 v2 v5:G),(d (d v5 (d (d (d v6 (d a a)) (d v6 (d v5 (d a a)))) (d v2 (d a a)))) (d a a)) = v2).
Proof.
unfold ldiv;intros.
assert(H':=e1 G d a H (d a a) v2 v5 v6).
rewrite (e4 G d a H (d (d a a) (d a a)) a) in H'.
repeat rewrite (e4 G d a H (d a a) a) in H'.
exact H'.
Qed.

Lemma e22: forall (G:Set) (d:G->G->G) (a:G),ldiv G d a->(forall (v4 v9 v10:G),(d (d (d v9 (d v10 v10)) v4) v9) = (d v4 (d v10 v10))).
Proof.
unfold ldiv;intros.
assert(H':=e18 G d a H v4 (d v9 (d v10 v10))).
rewrite (e9 G d a H a v10) in H'.
rewrite(e17 G d a H v9 v10) in H'.
exact H'.
Qed.


Lemma e23: forall (G:Set) (d:G->G->G) (a:G),ldiv G d a->(forall (v10 v11 v12:G),(d v12 (d (d v12 (d v11 v11)) (d v11 (d v11 v11)))) = (d v11 (d v10 v10))).
Proof.
unfold ldiv;intros.
assert(H':=e22 G d a H v11 (d (d (d a (d (d v12 (d v11 v11)) (d (d v12 (d v11 v11)) (d v12 (d v11 v11))))) (d a (d (d v10 v10) (d (d v12 (d v11 v11)) (d v12 (d v11 v11)))))) (d v11 (d v11 v11))) v10).
rewrite (e2 G d a H v11 v12 (d v10 v10) a) in H'.
repeat rewrite (e9 G d a H (d v12 (d v11 v11)) v11) in H'.
rewrite (e17 G d a H v12 v11) in H'.
rewrite (e16 G d a H v10 v11) in H'.
rewrite (e18 G d a H v12 a) in H'.
rewrite (e9 G d a H a v11) in H'.
exact H'.
Qed.


Lemma e24: forall (G:Set) (d:G->G->G) (a:G),ldiv G d a->(forall (x y:G),d x (d (d x (d a a)) y)=y).
Proof.
unfold ldiv;intros.
assert(H':=e23 G d a H a (d y (d a a)) x).
rewrite (e9 G d a H (d y (d a a)) a) in H'.
rewrite (e17 G d a H y a) in H'.
exact H'.
Qed.

Lemma e24' : forall (G:Set) (d:G->G->G) (a:G),ldiv G d a->(forall x y z: G, d x (d (d x (d z z)) y) = y).
Proof.
unfold ldiv;intros.
assert(H':=e24 G d a H x y).
rewrite(e9 G d a H a z) in H'.
exact H'.
Qed.


Lemma e25: forall (G:Set) (d:G->G->G) (a:G),ldiv G d a->(forall (x y:G),d (d x y) (d a a)=d y x).
Proof.
unfold ldiv;intros.
assert(H':=e22 G d a H (d (d (d x (d a a)) (d a a)) y) x a).
rewrite (e24 G d a H (d x (d a a)) y) in H'.
rewrite (e17 G d a H x a) in H'.
exact (eq_sym H').
Qed.

Lemma e26: forall (G:Set) (d:G->G->G) (a:G),ldiv G d a->(forall (v1 v6 v8:G),(d (d v6 (d v8 (d v1 v1))) (d v6 v1))=(d (d v8 (d v1 v1)) v1)).
Proof.
unfold ldiv;intros.
assert(H':=e19 G d a H v1 (d (d (d v6 v1) (d v6 (d v8 (d v1 v1)))) (d v8 v8)) v6 v8).
rewrite(e24' G d a H (d (d v6 v1) (d v6 (d v8 (d v1 v1)))) (d v1 v1)) in H'.
rewrite(e9 G d a H v8 a) in H'.
rewrite(e25 G d a H (d v6 v1) (d v6 (d v8 (d v1 v1)))) in H'.
exact (eq_sym H').
Qed.

Lemma e27: forall (G:Set) (d:G->G->G) (a:G),ldiv G d a->(forall (v1 v14 v16:G),(d v16 (d (d v14 (d v16 (d v1 v1))) v1)) = (d (d v14 (d v1 v1)) v1)).
Proof.
unfold ldiv;intros.
assert(H':=e26 G d a H v1 (d v14 (d v16 (d (d v1 v1) (d v1 v1)))) v14).
rewrite (e26 G d a H (d v1 v1) v14 v16) in H'.
rewrite (e16 G d a H v1 v1) in H'.
rewrite (e9 G d a H a v1) in H'.
rewrite (e17 G d a H v16 v1) in H'.
exact H'.
Qed.

Lemma e28:forall (G:Set) (d:G->G->G) (a:G),ldiv G d a->(forall (v1 v6 v10:G),(d (d v6 v10) (d v6 v1)) = (d v10 v1)).
Proof.
unfold ldiv;intros.
assert(H':=e26 G d a H v1 v6 (d a (d (d (d a (d v1 v1)) (d a (d a (d (d v1 v1) (d v1 v1))))) (d v10 (d (d v1 v1) (d v1 v1)))))).
rewrite(e19 G d a H (d v1 v1) v10 a a) in H'.
exact H'.
Qed.

Lemma e29: forall (G:Set) (d:G->G->G) (a:G),ldiv G d a->(forall (v1 v8 v12 v18:G),(d (d v12 (d v18 v18)) (d (d v8 v12) v1)) = (d (d v8 (d v1 v1)) v1)).
Proof.
unfold ldiv;intros.
assert(H':=e26 G d a H  v1 (d (d (d v8 (d v1 v1)) (d v18 v18)) v12) v8).
rewrite(e22 G d a H v12 (d v8 (d v1 v1)) v18) in H'.
rewrite(e9  G d a H v1 v18) in H' at 1.
rewrite(e8 G d a H v8 v18) in H'.
exact H'.
Qed.

Lemma e30: forall (G:Set) (d:G->G->G) (a:G),ldiv G d a->(forall (x y z:G),d (d x (d a a)) (d (d y x) z)= d (d y (d a a)) z).
Proof.
unfold ldiv;intros.
assert(H':=e29 G d a H z y x a).
rewrite(e9 G d a H z a) in H'.
exact H'.
Qed.


Lemma e31: forall (G:Set) (d:G->G->G) (a:G),ldiv G d a->(forall (x y z:G),d x (d (d y (d a a)) z)=d (d y x) z).
unfold ldiv;intros.
assert(H':=e30 G d a H (d x (d a a)) (d x y) z).
rewrite (e17 G d a H x a) in H'.
rewrite (e18 G d a H y x) in H'.
rewrite (e25 G d a H x y) in H'.
exact H'.
Qed.

Lemma e32: forall (G:Set) (d:G->G->G) (a:G),ldiv G d a->assoc G (fun v w=>d (d v (d a a)) w).
Proof.
unfold ldiv,assoc;intros.
assert(H4:=e4 G d a H).
assert(H5:=e5 G d a H).
assert(H6:=e6 G d a H).
assert(H7:=e7 G d a H).
assert(H8:=e8 G d a H).
assert(H9:=e9 G d a H).
assert(H10:=e10 G d a H).
assert(H11:=e11 G d a H).
assert(H12:=e12 G d a H).
assert(H15:=e15 G d a H).
assert(H16:=e16 G d a H).
assert(H17:=e17 G d a H).
assert(H18:=e18 G d a H).
assert(H19:=e19 G d a H).
assert(H20:=e20 G d a H).
assert(H22:=e22 G d a H).
assert(H23:=e23 G d a H).
assert(H24:=e24 G d a H).
assert(H25:=e25 G d a H).
assert(H26:=e26 G d a H).
assert(H27:=e27 G d a H).
assert(H28:=e28 G d a H).
assert(H30:=e30 G d a H).
assert(H31:=e31 G d a H).
congruence.
Qed.

