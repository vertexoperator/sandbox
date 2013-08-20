(* coq-8.3 *)
(*
"Categorical Logic and Type Theory" excercises 5.5.1 and so on

テキストは、Higher order predicate logicの話だけれど、CICで証明する

(1)funtional extensionality and propositional extensionality
(2)predicate extensionality("extensionality of entailment" in CLTT)
(3)existence of quotient type

(A) (2) -> prop.ext. (exercises 5.5.1 in CLTT)
(B) (3) -> func.ext. (Lemma4.7.1 in CLTT)
(C) (1) -> (2)
(D) (2) -> (3)
ここで示すのは、(A)(C)(D)

従って
CIC |- (1)->(2)->(3)

(B)が正しいことを認めると(多分普通に証明できると思う)
CIC |- (1)<->(2)->(3)

もし、(3)->prop.ext.が言えれば、(1)(2)(3)は同値ということになる


[TODO]
Goal forall (A B:Type) (P:A->Prop) (Q:B->Prop),
  A=B->(forall a b, JMeq a b -> (P a=Q b)) -> {a:A & P a}={b:B & Q b}


[MEMO]
・equalityは同値関係で、"A=(A/eq)"で合ってほしいのだけど
ここの定義だと言えないので悲しい。Weak equivalentになることは、言えそう

・Coqでは商を作るのに、
(P)Setoidを使うか
(Q)"normalized type"を使う
という方法がある

normalized typeは
R x y<->norm(x)=norm(y)
となるような関数norm:A->Aが作れれば{x:A | x=norm(x)}を商集合の代用して使える
みたいな話。Courtieuは、CIC with normalized typesをちゃんと定義して、
strong normalization/decidable type checkingなどを示している。

現在のCoqでは、normalized typeをサポートしてないので、elimination ruleなどが自動生成されないけど、考え方としては使える

Z/pZの代わりに、{n:Z | 0<=n<p}を使うとか
ZのGrothendieckの構成の代わりに、...とか
Qの代わりに、{(n,m):Z*Z| m>0 /\ coprime n m}とか
多項式の代わりに、正規化した多項式の集合を使うとか

(Q)の方法は、Extractionとの相性がよいと思う。ここでやったような方法で、
関数f:Z->Z/pZを作っても、Extractionできないけど
関数f:Z->{n:Z | 0<=n<p}ならできて便利とか

プログラムを書く時に正規形に変換する操作を避けることはできないことを思えば当然
でもって、同値関係を定義できても正規形を得ることが不可能な場合もあるだろうので、
computationalには、任意の商が作れるという仮定は強すぎるのだろう

任意の商集合から代表元を取ってこれるとすると、選択公理が必要になると思うので、pred.ext.と合せると、排中律が出てしまい死亡するだろう


・"Higher inductive type"を使えば
Inductive quotient (A : Type) (R : A -> A -> hProp) : Type :=
  | proj : A -> quotient A R
  | relate : forall (x y : A), R x y -> paths (proj x) (proj y)
  | contr : forall (x y : quotient A R) (p q : paths x y), paths p q.
という定義になる。

elimination ruleの入れ方などは明らかになるが、
"CIC with HIT"は、formalに定義されてないし、
strong normalization/decidable type checking
のような性質を持つのか現時点では不明。

まあ、func.ext.が成り立ってcanonicityは壊れざるを得ない気がするけど
*)


Set Implicit Arguments.
Unset Strict Implicit.

(* prop.ext. -> proof irrelevanceの証明に使う *)
Require Import ClassicalFacts.


Definition func_ext := forall {A B:Type} (f g:A->B),(forall x,f x=g x)->f=g.
Definition prop_ext := forall {P Q:Prop},(P<->Q)->(P=Q).
Definition pred_ext := forall (A:Type) (f g:A->Prop) , (forall x, f x<->g x) -> (f=g).

(* excercises 5.1.1 *)
Lemma pred_ext_to_prop_ext: pred_ext -> prop_ext.
  unfold prop_ext.
  intros prf_pred_ext P Q H.
  assert(Hf:exists f:unit->Prop ,f tt=P).
    exists (fun _=>P);auto.
  assert(Hg:exists g:unit->Prop , g tt=Q).
    exists (fun _=>Q);auto.
  destruct Hf as [f Hf];destruct Hg as [g Hg].
  assert(H':forall x,f x<->g x) by (induction x;congruence).
  assert(H'':=@prf_pred_ext unit f g H').
  congruence.
Qed.

(* (1)->(2) *)
Goal func_ext -> prop_ext -> pred_ext.
  unfold pred_ext.
  intros prf_func_ext prf_prop_ext A f g H.
  assert(H1 := fun (x:A)=>@prf_prop_ext (f x) (g x) (H x)).
  exact (@prf_func_ext A Prop f g H1).
Qed.

(* Example 5.1.2 in CLTT *)
(* excercises 5.1.1 を使う *)
Goal pred_ext -> (forall (P:Prop), P<->(P=True)).
  intros prf_pred_ext P.    
  assert(HL:P=True->P) by (intros;subst;exact I).
  assert(HR:P->P=True).
    intro HP.
    apply (pred_ext_to_prop_ext prf_pred_ext).
    split.
    exact (fun _=>I).
    exact (fun _=>HP).
  firstorder.
Qed.


Axiom predicate_extensionality : forall (A:Type) (f g:A->Prop) , (forall x, f x<->g x) -> (f=g).

(* pred.ext. -> prop.ext. -> proof irrelevance *)
Lemma proof_irrelevance : forall (P:Prop) (x y:P),x=y.
   apply ext_prop_dep_proof_irrel_cic.
   apply pred_ext_to_prop_ext.
   exact predicate_extensionality.
Qed.


Lemma sig_eq : forall (A:Type) (P:A->Prop) (a b:sigT P), projT1 a=projT1 b -> a=b.
  intros A P a b H.
  destruct a as [a Ha];destruct b as [b Hb].
  simpl in H.
  revert Ha Hb.
  rewrite H.
  intros Ha Hb.
  assert(H':=@proof_irrelevance (P b) Ha Hb).
  rewrite H';reflexivity.
Qed.


Definition Relation (U:Type) := U -> U -> Prop.
Section equivalence.
  Variable U:Type.
  Variable R:Relation U.
  Definition Reflexive := forall x : U, R x x.
  Definition Transitive := forall x y z : U, R x y -> R y z -> R x z.
  Definition Symmetric := forall x y : U, R x y -> R y x.
  Structure Equivalence : Prop :=
  {Prf_refl : Reflexive;
   Prf_trans : Transitive;
   Prf_sym : Symmetric}.
End equivalence.

Hint Unfold Reflexive.
Hint Unfold Transitive.
Hint Unfold Symmetric.
Hint Resolve Build_Equivalence.

Definition Equiv (U:Type) := {R:Relation U & Equivalence R}.
Definition Quotient (S:Type) (R:Equiv S) := {P:S->Prop & exists(x:S),P=projT1 R x}.

Lemma eq_is_equiv : forall {A:Type},Equivalence (@eq A).
  intro A;apply Build_Equivalence.
  unfold Reflexive;auto.
  unfold Transitive;intros x y z;apply eq_trans.
  unfold Symmetric;auto.
Qed.

(* 商写像q:U->U/R , q(x) = x mod R *)
Definition quot_map : forall {U} (R:Equiv U) , U->Quotient R.
  intros U R x.
  destruct R as [R H].
  exists (R x).
  exists x.
  simpl.
  auto.
Defined.

(* q(x)=q(y) -> R x y *)
Goal forall {A:Type} (R:Equiv A) (x y:A),quot_map R x = quot_map R y -> projT1 R x y.
   intros A R x y H.
   destruct R as [R H0].
   simpl;simpl in H.
   assert(resp : forall {A B} (u:A->B) {a1 a2:A},a1 = a2 -> u a1 = u a2) by congruence.
   assert (H1:=resp _ _ (projT1 (P:=(fun P : A -> Prop => exists x : A ,P = R x))) _ _ H).
   simpl in H1.
   rewrite H1.
   apply Prf_refl;exact H0.
Qed.

(* R x y -> q(x)=q(y) *)
Goal forall {A:Type} (R:Equiv A),forall x y,projT1 R x y->quot_map R x=quot_map R y.
   intros A R x y H.
   destruct R as [R H0].
   simpl in *|-*.
   apply sig_eq.
   apply predicate_extensionality.
   intro z.
   simpl.
   split.
   exact (Prf_trans H0 (Prf_sym H0 H)).
   exact (Prf_trans H0 H).
Qed.


