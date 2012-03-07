(* coq-8.3 *)
(*
quotient types from "predicate extensionality"

[概要]
定義はこんなの。Rは、S上の同値関係
Definition Quotient (S:Type) (R:Equiv S) := {P:S->Prop & exists(x:S),P=projT1 R x}.

これが、商として適切な性質を持つことを言うには、proof irrelevance
forall (P:Prop) (x y:P),x=y.
と次の形のextensionality
forall (A:Type) (f g:A->Prop) , (forall x, f x<->g x) -> (f=g).
が必要

#predicate extensionalityという名前にしてるけど、
Coqでpredicate extensionalityと呼んでるものは
forall P Q:bool -> Prop, (forall b:bool, P b <-> Q b) -> P = Q.
という定義になってて違うので注意。


predicate extensionalityは、func.ext.とprop.ext.から出る
(そして多分univalence axiomはもっと強い)

proof irrelevanceは、実際には、上記のextensionalityの帰結として出る
propositional extentionalityが出て、CICでは、
prop. ext.->proof irrelevance
なのはよく知られた事実(CoqのClassicalFacts.vに証明がある)

まとめると、
univalence -> func.ext. and prop.ext. -> pred.ext.-> prop.ext. -> proof irrelevane

が、とりあえずproof irrelevanceを公理として入れておく


Definition func_ext := forall {A B:Type} (f g:A->B),(forall x,f x=g x)->f=g.
Definition prop_ext := forall {P Q:Prop},(P<->Q)->(P=Q).
Definition pred_ext := forall (A:Type) (f g:A->Prop) , (forall x, f x<->g x) -> (f=g).
Goal pred_ext -> prop_ext.
   unfold prop_ext.
   intros pred_ext P Q H.
   assert(Hf:exists f:unit->Prop ,f tt=P).
     exists (fun _=>P);auto.
   assert(Hg:exists g:unit->Prop , g tt=Q).
     exists (fun _=>Q);auto.
   destruct Hf as [f Hf];destruct Hg as [g Hg].
   assert(H':forall x,f x<->g x) by (induction x;congruence).
   assert(H'':=@pred_ext unit f g H').
   congruence.
Qed.


Goal func_ext -> prop_ext -> pred_ext.
   unfold pred_ext.
   intros func_ext prop_ext A f g H.
   assert(H1 := fun (x:A)=>@prop_ext (f x) (g x) (H x)).
   exact (@func_ext A Prop f g H1).
Qed.



[TODO]
商について言えたので、subsetについても
Goal forall (A B:Type) (P:A->Prop) (Q:B->Prop),
A=B->(forall a b, JMeq a b -> (P a=Q b))->{a:A & P a}={b:B & Q b}
とか示したい


[more TODO]
proof irrelevanceを公理として課さずに、VoevodskyのhPropを使いたい
というのがある。predicate extensionalityからproof irrelevanceが出るので、
意味がないのだけど、predicate extensionality自体をもっと弱い形、例えば
forall (A:hSet) (f g:A->hProp) , (forall x, f x<->g x) -> (f=g)
くらいにして、これが証明できるとよい。多分これくらいでも実用上は問題ない
(一々、natがhSetであることなどは証明しないといけなくなるので、手間は増えるけど)

*)


Set Implicit Arguments.
Unset Strict Implicit.

Axiom proof_irrelevance : forall (P:Prop) (x y:P),x=y.
Axiom predicate_extensionality : forall (A:Type) (f g:A->Prop) , (forall x, f x<->g x) -> (f=g).

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
   exact  (Prf_trans H0 (Prf_sym H0 H)).
   exact (Prf_trans H0 H).
Qed.


