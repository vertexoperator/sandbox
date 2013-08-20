(* coq-8.3 *)
(* require "-impredicative-set" *)
(*
-- Reynolds' paper:"Polymorphism is not set-theoretic"
-- See also "Categorical Logic and Type Theory" Chapter 8.3
*)

(* Assume functional extensionality and proof irrelevance *)
Require Import FunctionalExtensionality.
Require Import ProofIrrelevance.

(* consequence of proof irrelevance *)
Lemma sig_eq :  forall (s:Set) (p : s->Prop) (x y:sig p),
	proj1_sig x = proj1_sig y -> x=y.
Proof.
   intros s p x y H.
   destruct x as [x Hx].
   destruct y as [y Hy].
   simpl in H.
   revert Hx Hy.
   rewrite H.
   intros Hx Hy.
   assert(Hx=Hy) by (apply proof_irrelevance).
   congruence.
Qed.



(*---- Basic Definition ----*)
(* Tはfunctorであり、Tのinitial algebraを作るのが目標 *)
Definition T (s:Set) := (s->bool)->bool.

Definition Tmap {s s':Set} (rho:s->s') :T s->T s' :=
   (fun h:(s->bool)->bool => (fun g:s'->bool => h (fun x:s=>g (rho x)))).

Lemma Tmap_identity_law: forall (s:Set), Tmap (@id s) = @id (T s).
   intro s.
   extensionality x.
   extensionality k.
   assert(Hk:(fun x0 : s => k x0)=k) by (apply eta_expansion).
   compute.
   rewrite Hk.
   reflexivity.
Qed.

Lemma Tmap_composition_law : 
   forall {X Y Z:Set} (f:X->Y) (g:Y->Z),
      (forall x, Tmap g (Tmap f x)=Tmap (fun x=>g (f x)) x).
Proof.
   intros X Y Z f g x;extensionality k.
   compute.
   reflexivity.
Qed.


(* Lemma2 in Reynolds' paper *)
Definition P := forall (s:Set), (T s->s)->s.
Definition rho {s:Set} (f:T s->s) : P->s := (fun p:P => p s f).
Definition H (h:T P):P :=  fun (S:Set) (f:T S->S) => f (Tmap (rho f) h).

Lemma ReynoldsLemma2 : 
   forall (s:Set) (f:T s->s),
      forall (h:T P),rho f (H h) = f (Tmap (rho f) h).
Proof.
   compute.
   reflexivity.
Qed.


(* Lemma3 in Reynolds' paper *)
Definition parametric (p:P) :=
   forall (s1 s2:Set) (a:s1->s2) (f1: T s1 ->s1) (f2:T s2->s2),
      (forall x, a (f1 x) = f2 (Tmap a x)) -> rho f2 p = a (rho f1 p).

Definition P' := {p : P | parametric(p) }.

Definition J:P'->P := @proj1_sig P (fun p=>parametric(p)).

Definition rho' {s:Set} (f:T s->s) x := rho f (J x).

Definition H' : T P'->P'.
   intro h'.
   exists (H (Tmap J h')).
   red.
   intros s1 s2 a f1 f2 C.
   assert(HA : rho f2 (H (Tmap J h')) = f2 (Tmap (rho f2) (Tmap J h')) ) by (apply ReynoldsLemma2).
   assert(HB : rho f1 (H (Tmap J h')) = f1 (Tmap (rho f1) (Tmap J h')) ) by (apply ReynoldsLemma2).
   rewrite HA.
   rewrite HB.
   rewrite C.
   assert(HC:Tmap (rho f2) (Tmap J h')=Tmap a (Tmap (rho f1) (Tmap J h'))).
     repeat (rewrite Tmap_composition_law).
     assert(HC':(fun x : P' => rho f2 (J x))=(fun x : P' => a (rho f1 (J x))) ).
        extensionality x.
        destruct x as [p Hp].
        apply Hp.
        exact C.
     rewrite HC'.
     reflexivity.
   congruence.
Defined.

Section Reynolds_Lemma3.
   Variable s:Set.
   Variable f:T s->s.
   Variable theta : P'-> s.
   Lemma ReynoldsLemma3_1 :(theta=rho' f) -> (forall (h':T P'),theta (H' h')= f (Tmap theta h')).
      intros H h'.
      rewrite H;compute.
      reflexivity.
   Qed.

   Lemma ReynoldsLemma3_2 : 
      (forall (h':T P'),theta (H' h')= f (Tmap theta h')) ->
         (forall x,rho' f x=theta (rho' H' x)).
   Proof.
      intros H [p Hp].
      apply Hp.
      exact H.
   Qed.
End Reynolds_Lemma3.


(* Lemma4 in Reynolds' paper *)
Definition rho0' (p':P') := rho' H' p'.
Definition P'' := {p | rho0' p = p}.

Definition Gamma : P' -> P''.
   intro p'.
   exists (rho0' p').
   symmetry.
   apply ReynoldsLemma3_2.
   reflexivity.
Defined.

Definition K :P''->P' := @proj1_sig P' (fun p=>rho0' p=p) .

Definition H'' : T P'' -> P'' := (fun p => Gamma (H' (Tmap K p))).
Definition rho'' {s:Set} (f:T s->s) (x:P'') := rho' f (K x).


Section Reynolds_Lemma4.
   Variable s:Set.
   Variable f:T s->s.
   Variable theta:P''->s.

   Lemma ReynoldsLemma4 : (theta=rho'' f)<->(forall p,theta (H'' p)=f (Tmap theta p)).
      assert(E : forall p', rho0' (H' p')=H' (Tmap rho0' p') ).
         apply ReynoldsLemma3_1.
         reflexivity.
      assert(F1 : forall x,K (Gamma x)=rho0' x) by reflexivity.
      assert(F2 : forall x, Gamma (K x)=x) by (intros [p Hp];apply sig_eq;exact Hp).
      assert(F3 : rho0'=(fun x=> K (Gamma x))).
         extensionality x;congruence.
      assert(F4 : (fun x : P'' => K (Gamma (K x))) = K).
         extensionality x;congruence.
      assert(F : forall (p'':T P''), K (H'' p'')=H' (Tmap K p'') ).
         intro p''.
         unfold H''.
         rewrite F1.
         rewrite E.
         rewrite F3.
         rewrite Tmap_composition_law.
         rewrite F4.
         reflexivity.
      assert(G : forall p', Gamma (H' p')=H'' (Tmap Gamma p')).
         intro p'.
         unfold H''.
         rewrite Tmap_composition_law.
         congruence.
      split.
      (* -> part *)
      intro H;rewrite H.
      intro p.
      unfold rho''.
      rewrite (F p).
      apply ReynoldsLemma3_1.
      reflexivity.
      (* <- part *)
      intro D.
      assert(H:forall x,rho' f x=theta (Gamma (rho0' x))).
         apply (@ReynoldsLemma3_2 s f (fun p=>theta (Gamma p))).
         intro p'.
         rewrite G.
         rewrite D.
         rewrite Tmap_composition_law.
         reflexivity.
      extensionality x.
      unfold rho''.
      congruence.
   Qed.
End Reynolds_Lemma4.

(*
Lemma4によって、P''がTの真のinitial algebraなので、P''と(T P'')は同型になる。
これは
P''と(P''->bool)->bool
が同型になるということなので、set-theoreticなモデルの非存在を示す
*)

