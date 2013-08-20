(* coq-8.3 *)
(*
-- "Categorial Logic and Type Theory" Excercise 8.1.5
-- See also Example 5.1.4
-- need option "-impredicative-set"
*)

(* encode/decode True *)
Goal True->(forall (P:Prop),P->P).
  intros t P p.
  exact (@True_ind P p t).
Qed.

Goal (forall (P:Prop),P->P)->True.
  intro H.
  exact (H True I).
Qed.


(* encode/decode unit *)
Definition encode_unit : unit -> (forall (X:Type),X->X).
  intros u X x.
  exact (@unit_rect (fun _=>X) x u).
Defined.

Definition decode_unit : (forall (X:Type),X->X) -> unit.
  intro H.
  exact (H unit tt).
Defined.


(* encode/decode False:Type *)
Goal False -> (forall (X:Type),X).
  exact (@False_rect (forall X,X)).
Qed.

Goal (forall (X:Type),X) -> False.
  intro H.
  exact (H False).
Qed.


(* encode/decode or *)
Goal forall (A B:Prop),(A \/ B)->(forall (P:Prop),(A->P)->(B->P)->P).
   intros A B p P H0 H1.
   exact (@or_ind A B P H0 H1 p).
Qed.

Goal forall (A B:Prop),(forall (P:Prop),(A->P)->(B->P)->P)->(A \/ B).
   intros A B H.
   exact (H (A \/ B) (@or_introl A B) (@or_intror A B)).
Qed.


(* encode/decode sum *)
Definition encode_sum {A B:Set}:(A + B) -> (forall X,(A->X)->(B->X)->X).
   intros p X H0 H1.
   exact (@sum_rect A B (fun _=> X) H0 H1 p).
Defined.

Definition decode_sum {A B:Set}:(forall (X:Type),(A->X)->(B->X)->X) -> (A + B).
   intros H.
   exact (H (A+B)%type (@inl A B) (@inr A B)).
Defined.


(* encode/decode prod *)
Definition encode_prod {A B:Set}:(A * B) -> (forall X,(A->B->X)->X).
   intros p X H.
   exact (@prod_rect A B (fun _=> X) H p).
Defined.

Definition decode_prod {A B:Set}:(forall (X:Type),(A->B->X)->X) -> (A * B).
   intros H.
   exact (H (A*B)%type (@pair A B)).
Defined.

(* encode/decode exists *)
Goal forall (A:Type) (P:A->Prop) , (exists x,P x) -> (forall (X:Prop),(forall x,P x->X)->X).
   intros A P p X H0.
   exact (@ex_ind A P X H0 p).
Qed.

Goal forall (A:Type) (P:A->Prop) , (forall (X:Prop),(forall x,P x->X)->X) -> (exists x , P x).
   intros A P H.
   exact (H (exists x,P x) (@ex_intro A P)).
Qed.


(* 以下の弱い形は排中律を必要とする *)
Definition decode_exist_weak_desc :=
   forall (A:Type) (P:A->Prop) ,((forall x,P x->False)->False) -> (exists x,P x).

Goal decode_exist_weak_desc -> (forall (P:Prop),~~P->P).
   unfold decode_exist_weak_desc.
   intros H P NNP.
   assert(NNP':(unit->P->False)->False) by firstorder.
   assert(H':= H unit (fun _=>P) NNP').
   firstorder.
Qed.


(* modus ponens *)
Definition encode_const :forall (A:Set),A -> (forall (X:Set),(A->X)->X) :=
  (fun A a=>(fun X f=>f a)).

Definition decode_const : forall (A:Set),(forall (X:Set),(A->X)->X) -> A :=
  (fun A f => f A (@id A)).


(* impredicative encodings of "not" *)
Goal forall (A:Prop),(~A) -> (forall (P:Prop),(A->P)).
   intros A NA P a.
   exact (False_ind P (NA a)).
Qed.

Goal forall (A:Prop),(forall (P:Prop),(A->P)) -> (~A).
   unfold not.
   intros A H a.
   exact (H False a).
Qed.


(* encode/decode eq *)
Goal forall {A:Type} (x y:A) , (x=y) -> (forall (P:A->Type),P x->P y).
   intros A x y p P H0.
   exact (@eq_rect A x P H0 y p).
Qed.

Goal forall {A:Type} (x y:A) , (forall (P:A->Type),P x->P y) -> (x=y).
   intros A x y H.
   exact (H (fun a=>x=a) (@eq_refl A x)).
Qed.


(* encode/decode nat *)
Definition encode_nat : nat -> (forall (X:Set),(X->X)->X->X).
   intros n X HS HO.
   assert(HS':forall m:nat,X->X) by firstorder.
   exact (@nat_rect (fun _=>X) HO HS' n).
Defined.

Definition decode_nat : (forall (X:Set),(X->X)->X->X) -> nat.
   intro H.
   exact (H nat S O).
Defined.


(*  =================== parametricity ===================  *)
(* unit relation *)
Definition unitR (h h':forall X,X->X) :=
  forall (X X':Set) (R:X->X'->Prop),
    (forall x x',R x x' -> R (h X x) (h' X' x')).

Goal unitR (encode_unit tt) (encode_unit tt).
  compute.
  auto.
Qed.

Goal forall f,unitR f f->(forall (X:Set) (x:X) , f X x=encode_unit (decode_unit f) X x).
  intros f H X x.
  unfold decode_unit.
  assert(H0 : x=encode_unit tt X x) by reflexivity.
  exact (H X unit (fun x1 x2=>x1=encode_unit x2 X x) x tt H0).
Qed.


(* empty relation *)
Definition emptyR (h h':forall X,X) := forall (X X':Set) (R:X->X'->Prop),R (h X) (h' X').

Goal forall f,~(emptyR f f).
   intros f H.
   exact (H unit nat (fun _ _=>False)).
Qed.


(* const relation *)
Definition constR (A:Set) (h h':forall (X:Set),(A->X)->X) :=
  forall (X X':Set) (R:X->X'->Prop),(forall g g',(forall a a',a=a'->R (g a) (g' a'))->R (h X g) (h' X' g')).

Goal forall (A:Set) (a:A) , constR A (encode_const A a) (encode_const A a).
  compute.
  intros.
  exact (H a a eq_refl).
Qed.

Goal forall (A:Set) f,constR A f f->(forall (X:Set) (g:A->X),f X g=encode_const A (decode_const A f) X g).
   intros A f H X g.
   unfold decode_const.
   apply (H X A).
   compute.
   congruence.
Qed.


(* sum relation *)
Definition sumR {A B:Set} (h h':forall X,(A->X)->(B->X)->X) :=
  forall (X X':Set) (R:X->X'->Prop) ,
    forall f f',(forall a a',a=a' -> R (f a) (f' a'))->
      forall g g' ,(forall b b',b=b'->R (g b) (g' b'))->
         R (h X f g) (h' X' f' g').


Goal forall (A B:Set) f,
   sumR f f -> (exists (k:(A+B)%type),(forall (X:Set) fa fb,f X fa fb=encode_sum k X fa fb)).
Proof.
  intros A B f H.
  exists (f (A+B)%type inl inr).
  intros X fa fb.
  apply (H X (A+B)%type).
  compute;congruence.
  compute;congruence.
Qed.


(* product relation *)
Definition prodR {A B:Set} (h h':forall X,(A->B->X)->X) :=
   forall (X X':Set) (R:X->X'->Prop) ,
      forall f f',(forall a a' b b',a=a'->b=b'-> R (f a b) (f' a' b'))->
         R (h X f) (h' X' f').


Goal forall (A B:Set) f, prodR f f ->
   (exists (k:(A*B)%type),(forall (X:Set) p,f X p=encode_prod k X p)).
Proof.
  intros A B f H.
  exists (f (A*B)%type pair).
  intros X p.
  apply (H X (A*B)%type).
  compute.
  congruence.
Qed.


(* church numeral/natural number relation *)
Require Import Setoid.

Definition natR (h h':forall X,(X->X)->X->X) :=
  forall (X X':Set) (R:X->X'->Prop) ,
    forall s s',(forall x x',R x x'->R (s x) (s' x'))->
      forall z z',R z z' -> R (h X s z) (h' X' s' z').

Goal forall n,n=decode_nat (encode_nat n).
  induction n.
  compute;reflexivity.
  rewrite IHn at 1.
  reflexivity.
Qed.

Goal forall f,natR f f->(forall (X:Set) (s:X->X) (z:X),f X s z=encode_nat (decode_nat f) X s z).
   intros f H X s z.
   unfold decode_nat.
   apply (H X nat).
   intros x n HS;rewrite HS;compute;reflexivity.
   compute;reflexivity.
Qed.


(* Peirce's Law *)
Definition PeirceLaw := forall (X Y:Prop),((X->Y)->X)->X.

Definition Peirce_R  (h h':PeirceLaw) :=
  forall (X X' Y Y':Prop) (RX:X->X'->Prop) (RY:Y->Y'->Prop),
      forall x1 x2,(forall y1 y2,(forall z1 z2,RX z1 z2->RY (y1 z1) (y2 z2))->RX (x1 y1) (x2 y2)) ->
          RX (h X Y x1) (h' X' Y' x2).

Goal forall f,~(Peirce_R f f).
    intros f H.
    apply (H True True True False (fun _ _=>False) (fun _ _=>True)).
    firstorder.
    firstorder.
    firstorder.
Qed.

Definition EM_to_Peirce: (forall (P:Prop),~~P->P) -> PeirceLaw.
    unfold PeirceLaw.
    intros H0 X Y H1.
    assert(H2:=H0 X).
    firstorder.
Defined.



(* composition or 三段論法 *)
Definition composeR (h h':forall X Y Z,(X->Y)->(Y->Z)->(X->Z)) :=
  forall X X' Y Y' Z Z' (RX:X->X'->Prop) (RY:Y->Y'->Prop) (RZ:Z->Z'->Prop),
     forall (f:X->Y) (f':X'->Y') (g:Y->Z) (g':Y'->Z') (x:X) (x':X'),
        (forall x0 x0',RX x0 x0' -> RY (f x0) (f' x0')) ->
        (forall y0 y0',RY y0 y0' -> RZ (g y0) (g' y0')) ->
        (RX x x' -> RZ (h X Y Z f g x) (h' X' Y' Z' f' g' x')).

Goal composeR (fun X Y Z f g x=>g (f x)) (fun X Y Z f g x=>g (f x)).
  compute.
  firstorder.
Qed.

Goal forall c,composeR c c->
  (forall X Y Z (f:X->Y) (g:Y->Z) (x:X),c X Y Z f g x = g (f x)).
Proof.
  intros c H X Y Z f g x.
  set (encode_comp := (fun (_:unit) => fun X Y Z (f:X->Y) (g:Y->Z) x,g (f x))).
  set (decode_comp := (fun (h:forall X Y Z,(X->Y)->(Y->Z)->(X->Z)) => h unit unit unit (@id unit) (@id unit) tt)).
  assert(p:g (f x)=encode_comp (decode_comp c) X Y Z f g x).
    compute;reflexivity.
  rewrite p.
  set (RX := fun xx t=>f x=encode_comp t X Y Y f (@id Y) xx).
  set (RY := fun y t=>f x=encode_comp t Y Y Y (@id Y) (@id Y) y).
  apply (H X unit Y unit Z unit RX RY).
  compute;congruence.
  compute;congruence.
  compute;congruence.
Qed.





(*
================ Wadler's note "Recursive types for free!" ==================
See http://homepages.inf.ed.ac.uk/wadler/papers/free-rectypes/free-rectypes.txt
*)

Record Functor := {
  objmap : Set -> Set;
  fmap : forall {X X':Set} , (X->X')->(objmap X->objmap X');
  functor_identity_law : forall (X:Set) (x:objmap X),(@fmap X X (@id X)) x = x;
  functor_composition_law :
     forall {X Y Z:Set} (f:X->Y) (g:Y->Z) (x':objmap X),
        (@fmap Y Z g (@fmap X Y f x')) = @fmap X Z (fun x=> g (f x)) x'
}.

Coercion objmap : Functor >-> Funclass.

Definition LFix (F:Functor) := forall X,(F X->X)->X.

Definition fold : forall {F:Functor} (X:Set),(F X->X)->(LFix F)->X.
   intros F X f H.
   exact (H X f).
Defined.

Definition intmap : forall {F:Functor},F (LFix F) -> (LFix F).
   red.
   intros F s X k.
   exact (k (@fmap F (LFix F) X (@fold F X k) s)).
Defined.


Definition extmap (F:Functor) : (LFix F) -> F (LFix F) :=
   @fold F (F (LFix F)) (fmap F (@intmap F)).


Section nat_as_weak_initial_algebra.
   Definition _NatF (X:Set) := (unit + X)%type.

   Definition NatF_fmap (X X':Set) (f:X->X') (x:_NatF X) : _NatF X'.
      destruct x as [u|n].
      exact (inl u).
      exact (inr (f n)).
   Defined.

   Lemma NatF_identity_law : forall (X:Set) (x:_NatF X),@NatF_fmap X X (@id X) x=x.
      intros X x.
      destruct x as [u|n].
      reflexivity.
      reflexivity.
   Qed.

   Lemma NatF_composition_law :
      forall (X Y Z:Set) (f:X->Y) (g:Y->Z) (x:_NatF X),
        (@NatF_fmap Y Z g (@NatF_fmap X Y f x)) = @NatF_fmap X Z (fun x=> g (f x)) x.
   Proof.
      intros X Y Z f g x.
      destruct x as [u|n].
      reflexivity.
      reflexivity.
   Qed.

   Definition NatF := @Build_Functor _NatF NatF_fmap NatF_identity_law NatF_composition_law.
End nat_as_weak_initial_algebra.


Section nat_as_initial_algebra.
   Definition fold_nat : forall {X:Set},(NatF X->X)->nat->X.
      intros X k n.
      induction n.
      exact (k (inl tt)).
      exact (k (inr IHn)).
   Defined.

   Definition int_nat: NatF nat->nat.
      intro n.
      destruct n as [u|n].
      exact 0.
      exact (S n).
   Defined.

   Definition ext_nat : nat -> NatF nat:=
      fold_nat (fmap NatF int_nat).

   Lemma int_ext_nat_is_id : forall (n:nat),int_nat (ext_nat n)=n.
      induction n as [|n IHn].
         reflexivity.
         simpl;rewrite IHn;reflexivity.
   Qed.

   Goal forall (n:NatF nat),ext_nat (int_nat n)=n.
      destruct n as [u|n].
        induction u;reflexivity.
        induction n as[|n IHn].
           reflexivity.
           assert(H:=int_ext_nat_is_id n).
           simpl;rewrite H;reflexivity.
   Qed.

   (*
            T : weak initial glebra of F

            diagram2:
                    int_nat
            F T --------------> T
             |                  |
             |                  |
F (fold X k) |                  | fold X k
             |                  |
             |                  |
            F X --------------> X
                       k
   *)
   Remark diagram2 : 
      forall (X:Set) (k:NatF X->X) (x:NatF nat),
         @fold_nat X k (int_nat x) = k (@fmap NatF nat X (@fold_nat X k) x).
   Proof.
      intros X k x.
      destruct x as [u|n].
      induction u.
         reflexivity.
      induction n.
         reflexivity.
         reflexivity.
    Qed.

    Lemma nat_is_initial_algebra : 
       forall (X:Set) (k:NatF X->X) (h:nat->X) ,
          (forall x:NatF nat,h (int_nat x) = k (@fmap NatF nat X h x)) -> 
              (forall (n:nat), h n=@fold_nat X k n).
    Proof.
       intros X k h Hx n.
       induction n.
          assert(H0 : 0=int_nat (inl tt)) by reflexivity.
          rewrite H0;rewrite Hx.
          reflexivity.
          assert(H1 : S n=int_nat (inr n)) by reflexivity.
          rewrite H1.
          rewrite Hx.
          simpl.
          rewrite <- IHn.
          reflexivity.
    Qed.

End nat_as_initial_algebra.



(*
-- Greatest Fixpoints 
-- need to overwrite sigS to avoid type inconsistency
Definition GFix (F:Functor) := {X:Set & ((X->F X)*X)%type}.

*)

Inductive sigS {A:Type} (P:A->Type) : Set :=
   existS : forall x:A ,P x->sigS P.

Definition GFix (F:Functor) := sigS (fun (X:Set) => ((X-> F X)*X)%type).

Definition unfold : forall {F:Functor} {X:Set} , (X->F X)->X->(GFix F).
   intros F X f x.
   exists X.
   exact (f,x).
Defined.

Definition outmap : forall (F:Functor), GFix F -> F (GFix F).
   intros F t.
   destruct t as [X v].
   destruct v as [k x].
   exact (@fmap F X (GFix F) (@unfold F X k) (k x)).
Defined.


Definition cntmap (F:Functor) : F (GFix F)->(GFix F) :=
   unfold (fmap F (@outmap F)).

Definition LFix_to_GFix (F:Functor) : (LFix F)->(GFix F) :=
  unfold (extmap F).

Definition LFix_to_GFix2 (F:Functor) : (LFix F)->(GFix F) :=
  @fold  F (GFix F) (cntmap F).




(* =============== natural transformation/Yoneda's Lemma =============== *)
Section identity_functor.
   Definition _IdF (X:Set) := X.
   Definition IdF_fmap (X X':Set) (f:X->X') :_IdF X ->_IdF X'.
      exact f.
   Defined.
   Lemma IdF_identity_law : forall (X:Set) (x:_IdF X),@IdF_fmap X X (@id X) x=x.
      reflexivity.
   Qed.
   Lemma IdF_composition_law : forall (X Y Z:Set) (f:X->Y) (g:Y->Z) (x':_IdF X),
        (@IdF_fmap Y Z g (@IdF_fmap X Y f x')) = @IdF_fmap X Z (fun x=> g (f x)) x'.
      reflexivity.
   Qed.
   Definition IdF := @Build_Functor _IdF IdF_fmap IdF_identity_law IdF_composition_law.
End identity_functor.


Section hom_functor.
   Variable A:Set.
   Definition _homF (X:Set) := (A->X).
   Definition homF_fmap (X X':Set) (f:X->X') : _homF X -> _homF X'.
      exact (fun h => (fun a=>(f (h a)))).
   Defined.
   Lemma homF_identity_law : forall (X:Set) (x:_homF X),@homF_fmap X X (@id X) x=x.
      reflexivity.
   Qed.
   Lemma homF_composition_law : forall (X Y Z:Set) (f:X->Y) (g:Y->Z) (x':_homF X),
        (@homF_fmap Y Z g (@homF_fmap X Y f x')) = @homF_fmap X Z (fun x=> g (f x)) x'.
      reflexivity.
   Qed.
   Definition homF := @Build_Functor _homF homF_fmap homF_identity_law homF_composition_law.
End hom_functor.


Record NT (F G:Functor) := {
  NTmap : forall (X:Set), F X-> G X;
  NT_law : forall (X Y:Set) (f:X->Y) (x:F X),NTmap Y (fmap F f x)=fmap G f (NTmap X x)
}.

Coercion NTmap : NT >-> Funclass.

Definition YonedaF {A:Set} {F:Functor} : (forall (X:Set),(A->X)->F X)->F A.
  intro H.
  exact (H A (@id A)).
Defined.

Definition YonedaR {A:Set} {F:Functor} : F A -> (forall (X:Set),(A->X)->F X).
  intros p X f.
  exact (fmap F f p).
Defined.


Goal forall (A:Set) (F:Functor) (a:F A),YonedaF (YonedaR a)=a.
  intros.
  unfold YonedaF;unfold YonedaR.
  apply functor_identity_law.
Qed.

(*
以下の命題を証明しようと思ったら、parametricity(とfunctional extensionality)が必要
例えば、Fが恒等関手IdFの時は、Aと(forall X,(A->X)->X)の同型を意味する

Goal forall (A:Set) (F:Functor) (p:forall (X:Set),(A->X)->F X),YonedaR (YonedaF p)=p.
*)
