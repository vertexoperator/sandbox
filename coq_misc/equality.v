(* coq-8.3 *)
Set Implicit Arguments.
Unset Strict Implicit.

(* Proof irrelevance *)
Definition isprop (A:Type) : Type := forall (t1 t2:A),t1=t2.

(* Uniqueness of Identity Proofs(UIP) *)
Definition isset (A:Type) := forall (x y:A),isprop (x=y).

(* decidablity *)
Definition isdec (A:Type) := forall (x0 x1:A),(x0=x1) + (x0<>x1).

(* Streicher's Axiom K *)
Definition AxiomK (A:Type) := forall (x:A) (P:x=x->Prop), P (refl_equal x) -> forall (p:x = x), P p.


(*
- decidable->UIP(by Hedberg)
- 証明はCoqに含まれるものを改変
*)

Section hedberg_lemma.
  Variable A : Type.
  Variable eq_dec : isdec(A).

  Let comp (x y y':A) (eq1:x = y) (eq2:x = y') : y = y' :=
    eq_ind _ (fun a => a = y') eq2 _ eq1.

  Remark trans_sym_eq : forall (x y:A) (u:x = y), comp u u = refl_equal y.
  Proof.
    intros.
    case u; trivial.
  Qed.


  Let nu (x y:A) (u:x = y) : x = y :=
    match eq_dec x y with
      | inl eqxy => eqxy
      | inr neqxy => False_ind _ (neqxy u)
    end.

  Let nu_constant : forall (x y:A) (u v:x = y), nu u = nu v.
    intros.
    unfold nu in |- *.
    case (eq_dec x y); intros.
    reflexivity.
    case n; trivial.
  Qed.

  Let nu_inv (x y:A) (v:x = y) : x = y := comp (nu (refl_equal x)) v.

  Remark nu_left_inv : forall (x y:A) (u:x = y), nu_inv (nu u) = u.
  Proof.
    intros.
    case u; unfold nu_inv in |- *.
    apply trans_sym_eq.
  Qed.

  Theorem dec_is_UIP : isset(A).
  Proof.
    red;intros x y p1 p2.
    elim nu_left_inv with (u := p1).
    elim nu_left_inv with (u := p2).
    elim nu_constant with x y p1 p2.
    reflexivity.
  Qed.
End hedberg_lemma.


(* 
- application of hedberg's lemma(1)
- nat and list of decidable set is UIP
*)
Lemma nat_is_set: isset(nat).
  apply dec_is_UIP.
  unfold isdec;intro n;induction n.
  intro m;induction m;auto.
  intro m;induction m;auto.
  destruct (IHn m) as [HL | HR];auto.
Qed.

Definition tail {A} (x:list A):list A := match x with
  | nil => nil
  | cons a x' => x'
end.

Definition head' {A} (default:A) (x:list A) :=
  match x with
    | nil => default
    | cons a _ => a
end.

Goal forall (A:Type),isdec(A)->isdec(list A).
  unfold isdec;intros A H;intro x;induction x.
  intro y;induction y;auto.
  right.
  red;intro H1.
  assert(H2:0=S (length y)).
  change(length (@nil A)=length (a::y)%list).
  rewrite H1;auto.
  exact (O_S (length y) H2).
  intro y;induction y.
  right.
  red;intro H1.
  assert(H2:0=S (length x)).
  change(length (@nil A)=length (a::x)%list).
  rewrite H1;auto.
  exact (O_S (length x) H2).
  destruct (H a a0) as [HL|HR];destruct (IHx y) as [IHL|IHR].
  left;congruence.
  right.
  contradict IHR.
  rewrite HL in IHR.
  change(tail (cons a x)=tail (cons a y)).
  congruence.
  right.
  red;intro p.
  contradict HR.
  rewrite IHL in p.
  change(head' a (cons a y)=head' a (cons a0 y)).
  rewrite p;auto.
  right.
  contradict IHR.
  change(tail (cons a x)=tail (cons a0 y)).
  rewrite IHR;auto.
Qed.


(* 
- application of Hedberg's lemma(2) 
- Voevodsky's isprop is equivalent to "proof irrelevance"
*)
Definition iscontr (T:Type) :Type := {c:T & forall t:T,t=c}.
Definition isprop' (T:Type) : Type := forall (t1 t2:T),iscontr (t1=t2).

Goal forall {U},isprop'(U)->isprop(U).
Proof.
  red.
  intros U X t1 t2.
  destruct (X t1 t2) as [c _].
  exact c.
Qed.

Goal forall {U},isprop(U)->isprop'(U).
Proof.
  intros U H.
  assert(H0:isdec(U)).
  unfold isdec;intros x y;rewrite (H x y);auto.
  assert(H1:=dec_is_UIP H0).
  unfold isprop.
  intros x y;rewrite (H x y).
  exists (refl_equal y).
  intro p.
  exact (H1 y y p eq_refl).
Qed.



(*
色々な同型

{A:Type & isset(A)}については、
weq<->iso<->bijective
一般には、
eq->weq->iso->bijective
となるように思う
*)

(* empty typeに対して、逆は成立しない *)
Lemma iscontr':forall {A:Type},iscontr A -> (forall (x y:A),x=y).
Proof.
  intros A H x y.
  destruct H as [a H].
  exact (eq_trans (H x) (eq_sym (H y))).
Qed.


Goal forall {A} (x:A),iscontr({a:A & a=x}).
Proof.
  unfold iscontr.
  intros A x.
  assert(H':{a:A & a=x}).
  exists x.
  auto.
  exists H'.
  destruct H' as [x' H'].
  intro H.
  destruct H as [a H].
  rewrite H;rewrite H';auto.
Qed.

Lemma resp : forall {A B} (u:A->B) (a1 a2:A),a1 = a2 -> u a1 = u a2.
  intros A B u a b H;rewrite H;auto.
Qed.


Definition fiber {X Y:Type} (f:X->Y) (y:Y) := {x:X & @eq Y (f x) y}.
Definition isweq {X Y:Type} (f:X->Y) := forall (y:Y),iscontr (fiber f y).
Definition Weq (X Y:Type) := {f:X->Y & isweq f}.
Definition injective {X Y:Type} (f:X->Y) := forall (x0 x1:X),f x0=f x1->x0=x1.
Definition surjective {X Y:Type} (f:X->Y) := forall (y:Y),{x:X & f x = y}.
Definition epic {X Y} (f:X->Y) := forall (Z:Type) (g1 g2:Y->Z), (forall (x:X),
   g1 (f x)=g2 (f x))->(forall y, g1 y=g2 y).
Definition monic {X Y} (f:X->Y) := forall (Z:Type) (g1 g2:Z->X),(forall (z:Z),
   f (g1 z)=f (g2 z))->(forall z ,g1 z = g2 z).
Definition isiso {X Y:Type} (f:X->Y) := 
  {g :Y->X & (forall (x:X),g (f x) = x) & (forall (y:Y),f (g y) = y)}.
Definition Iso (X Y:Type) := {f:X->Y & isiso(f)}.



(* 
See also 
- Coq.Logic.EqdepFacts.eq_sigT_eq_dep
- Coq.Logic.EqdepFacts.eq_dep_eq_sigT
*)
Lemma sig_eq' : forall (A:Type) (P:A->Type) (a b:sigT P),
  (forall (a:A),isprop(P a)) -> projT1 a=projT1 b -> a=b.
Proof.
  intros A P a b H H0.
  destruct a as [a Ha];destruct b as [b Hb].
  simpl in H0.
  revert Ha Hb.
  rewrite H0.
  intros Ha Hb.
  rewrite (H b Ha Hb).
  reflexivity.
Qed.


Definition coerce_Weq_to_Fun : forall {X Y},Weq X Y->(X->Y).
Proof.
  intros X Y f;destruct f as [f _];exact f.
Defined.
Coercion coerce_Weq_to_Fun : Weq >-> Funclass.


Lemma surjection_is_epic : forall {X Y} (f:X->Y),surjective(f)->epic(f).
Proof.
  intros X Y f H.
  unfold epic;intros Z g1 g2 H0 y.
  destruct (H y) as [x0 H1].
  rewrite <- H1.
  exact (H0 x0).
Qed.

Lemma injection_is_monic : forall {X Y} (f:X->Y),injective(f)->monic(f).
Proof.
  intros X Y f H.
  unfold monic.
  intros Z g1 g2 P z.
  exact (H (g1 z) (g2 z) (P z)).
Qed.


Lemma mono_is_injective : forall {X Y} (f:X->Y),monic(f)->injective(f).
  intros X Y f H.
  unfold injective.
  intros x0 x1 H0.
  assert(H':=H unit (fun _=> x0) (fun _=>x1)).
  simpl in H'.
  exact  (H' (fun _=>H0) tt).
Qed.


Lemma weq_is_surjective : forall {X Y} (f:X->Y),isweq(f)->surjective(f).
Proof.
  intros X Y f H.
  unfold surjective;intro y.
  destruct (H y) as [x _].
  destruct x as [x Hx].
  exists x;exact Hx.
Qed.

Lemma weq_is_injective : forall {X Y} (f:X->Y),isweq(f)->injective(f).
Proof.
  unfold injective.
  intros X Y f H x0 x1 H'.
  destruct (H (f x0)) as [x2 H0].
  destruct x2 as [x2 H1].
  assert(H3:=H0 (existT _ x1 (@eq_sym Y (f x0) (f x1) H'))).
  assert(H4:=H0 (existT _ x0 eq_refl)).
  assert(H5:=resp (B:=X) (projT1 (P:=(fun x : X => f x = f x0))) H3).
  assert(H6:=resp (B:=X) (projT1 (P:=(fun x : X => f x = f x0))) H4).
  simpl in H5,H6.
  congruence.
Qed.

Lemma iso_is_injective : forall {X Y} (f:X->Y),isiso(f)->injective(f).
Proof.
  intros X Y f H.
  unfold injective;intros x0 x1 p.
  destruct H as [g H1 H2].
  assert(q:g (f x0)=g (f x1)).
  rewrite p;auto.
  congruence.
Qed.

Lemma iso_is_surjective : forall {X Y} (f:X->Y),isiso(f)->surjective(f).
Proof.
  intros X Y f H.
  unfold surjective.
  intro y.
  destruct H as [g H1 H2].
  exists (g y).
  exact (H2 y).
Qed.

Lemma bijective_is_weq : forall {X Y} (f:X->Y),isset(Y)->injective(f)->surjective(f)->isweq(f).
Proof.
  intros X Y f H0 H1 H2.
  unfold isweq;intro y.
  destruct (H2 y) as [x H2'].
  exists (existT (fun x=>f x=y) x H2').
  intro x'.
  destruct x' as [x' H3].
  assert(H4:=H1 x x'  (eq_trans H2' (@eq_sym Y (f x') y H3))).
  revert H2' H3.
  rewrite H4.
  intros p q.
  apply sig_eq'.
  intro a;exact (H0 (f a) y).
  simpl.
  apply H1;congruence.
Qed.


(*
- properties of weak equivalence 
- X=Y -> Weq X Y 
*)
Definition weqmap {X Y} : X = Y -> Weq X Y.
Proof.
  intro H;rewrite H;exists (@id Y).
  unfold isweq,id.
  unfold iscontr,fiber.
  intro y.
  assert(H':{x : Y & x = y}).
  exists y;auto.
  exists H'.
  intro H'';destruct H' as [x' H'];destruct H'' as [x'' H''].
  rewrite H';rewrite H'';auto.
Defined.


Definition wid {A:Type} : Weq A A := weqmap eq_refl.

Definition winv' {X Y} : Weq X Y->(Y->X).
Proof.
  intros H y.
  destruct H as [f H].
  destruct (H y) as [[x H'] _].
  exact x.
Defined.


Definition wmul' {X Y Z} : Weq X Y -> Weq Y Z -> (X->Z).
Proof.
  intros H1 H2.
  destruct H1 as [f1 H1].
  destruct H2 as [f2 H2].
  exact(fun x=> f2 (f1 x)).
Defined.

Definition wmul {X Y Z} : isset(Z)->Weq X Y->Weq Y Z->Weq X Z.
  intros H f g;destruct f as [f Hf];destruct g as [g Hg].
  exists (fun x=>(g (f x))).
  unfold isweq;intro z.
  destruct (Hg z) as [y H0].
  destruct y as [y H1].
  destruct (Hf y) as [[x H0'] H1'].
  assert (x0:fiber (fun x: X => g (f x)) z).
  exists x.
  congruence.
  exists x0.
  intro x1.
  destruct x0 as [x0 Hx0].
  destruct x1 as [x1 Hx1].
  assert(p1:=H0 (existT _ (f x0) Hx0)).
  assert(p2:=resp (B:=Y) (projT1 (P:=(fun x : Y => g x = z))) p1).
  simpl in p2.
  assert(p3:=H0 (existT _ (f x1) Hx1)).
  assert(p4:=resp (B:=Y) (projT1 (P:=(fun x : Y => g x = z))) p3).
  simpl in p4.
  assert(q1:=H1' (existT _ x0 p2)).
  assert(q2:=H1' (existT _ x1 p4)).
  assert(q3:=resp (B:=X) (projT1 (P:=(fun x : X => f x = y))) q1).
  assert(q4:=resp (B:=X) (projT1 (P:=(fun x : X => f x = y))) q2).
  simpl in q3,q4.
  assert(r:=eq_trans q3 (@eq_sym X x1 x q4)).
  revert Hx0 Hx1 p1 p3.
  rewrite r.
  intros P1 P2 P3 P4.
  apply sig_eq'.
  intro a;exact (H (g (f a)) z).
  simpl;congruence.
Qed.


Lemma wmul_Lunit_law : forall {X Y} (f:Weq X Y) (x:X),wmul' f wid x=f x.
Proof.
  intros;unfold wmul',wid.
  destruct f as [f H].
  simpl.
  auto.
Qed.


Lemma winv_is_section : forall {X Y} (f:Weq X Y) (y:Y),f (winv' f y)=y.
Proof.
  intros X Y f y.
  destruct f as [f H].
  simpl.
  destruct (H y) as [[x H'] _].
  exact H'.
Qed.

Lemma winv_is_retraction : forall {X Y} (f:Weq X Y) (x:X), winv' f (f x)=x.
Proof.
  intros X Y f x.
  destruct f as [f H].
  simpl.
  destruct (H (f x)) as [[x' H0] H1].
  assert (H':= H1 (existT (fun a=>f a=f x) x eq_refl)).
  congruence.
Qed.


Lemma weq_is_iso :  forall {X Y} (f:X->Y),isweq(f)->isiso(f).
Proof.
  intros X Y f H;unfold isiso.
  exists (winv' (existT _ f H)).
  intro x.
  apply winv_is_retraction.
  intro y.
  assert (H':=winv_is_section (existT _ f H) y).
  simpl in H';simpl.
  exact H'.
Qed.


Lemma iso_is_weq :forall {X Y},isset(Y)->Iso X Y->Weq X Y.
Proof.
  intros X Y H0 H1.
  destruct H1 as [f H1].
  assert(H2 := iso_is_injective H1).
  assert(H3 := iso_is_surjective H1).
  exists f.
  exact (bijective_is_weq H0 H2 H3).
Qed.


(* univalence axiom *)
Axiom univalence : forall {X Y:Type},isweq(@weqmap X Y).

Lemma weak_univalence : forall {X Y},Weq X Y->X=Y.
Proof.
  intros X Y.
  assert(H':Weq (X=Y) (Weq X Y)).
  exists weqmap.
  exact univalence.
  exact (winv' H').
Qed.



(*
-- (1)consequence of univalence axiom
-- nat={even numbers}.
*)
Definition mul2 : nat -> {x:nat & {n:nat & x=2*n}}.
  intro n.
  exists(2*n).
  exists n.
  auto.
Defined.

Definition div2 : {x:nat & {n:nat & x=2*n}} -> nat.
  intro p.
  destruct p as [m [n _]].
  exact n.
Defined.

Lemma Weq_nat_evens : Weq ({x:nat & {n:nat & x=2*n}}:Type) (nat:Type).
Proof.
  apply iso_is_weq.
  exact nat_is_set.
  exists div2;exists mul2.
  intro x;destruct x as [n [m p]].
  rewrite p.
  unfold mul2,div2;simpl.
  reflexivity.
  intro;unfold div2,mul2;simpl;auto.
Qed.


Goal ({x : nat & {n : nat & x = 2 * n}}:Type) = (nat:Type).
  exact (weak_univalence Weq_nat_evens).
Qed.



(*
-- another consequence of univalence axiom;
-- can prove "unit=interval"

-- interval is defined using "higher inductive type";
Inductive interval : Type :=
  | zero : interval
  | one : interval
  | segment : paths zero one
*)

Inductive paths {A : Type} : A -> A -> Type :=
   | idpath : forall (a : A), @paths A a a.

Definition path_refl {A:Type} (x:A) : @paths A x x.
   apply idpath.
Defined.

Definition path_subst {A:Type} {P:A->Type} {x y:A} (p:@paths A x y) : P x -> P y.
   exact (@paths_rect A (fun a b _=>P a -> P b) (fun a=>@id (P a)) x y p).
Defined.

Goal forall {A:Type} (x y:A),paths x y -> x=y.
   intros A x y p.
   exact (path_subst p (eq_refl x)).
Qed.

Goal forall {A:Type} (x y:A),x=y -> paths x y.
   intros A x y H;rewrite H;apply idpath.
Qed.


Lemma contr_is_set : forall {A:Type},iscontr(A)->isset(A).
  intros A P.
  destruct P as [a P].
  apply dec_is_UIP.
  unfold isdec;intros a1 a2.
  assert(H1:=P a1).
  assert(H2:=P a2).
  left.
  exact (eq_trans H1 (eq_sym H2)).
Qed.

Lemma contr_is_unique: forall (A B:Type),iscontr(A)->iscontr(B)->Weq A B.
  intros A B P Q.
  assert(H:=contr_is_set Q).
  destruct P as [a P].
  destruct Q as [b Q].
  exists (fun _=> b).
  unfold isweq.
  intro b'.
  rewrite (Q b').
  exists (existT (fun _ : A => b = b) a eq_refl).
  intro a'.
  apply sig_eq'.
  intros;apply H.
  simpl;apply P.
Qed.


Lemma unit_is_contractible : iscontr(unit).
  exists tt;intro t;induction t;auto.
Qed.


Axiom interval : Type.
Axiom zero : interval.
Axiom one : interval.
Axiom segment : paths zero one.

Definition transport {X:Type} {P:X->Type} {x y:X} (p:paths x y) (a:P x) : P y :=
  path_subst p a.

Axiom interval_rect : 
  forall (P:interval->Type) (d_src : P zero) (d_tgt : P one) 
         (d_seg : paths (transport segment d_src) d_tgt) (x:interval),P x.

Lemma interval_is_contractible : iscontr(interval).
  exists zero.
  exact (@interval_rect (fun x=>x=zero) (eq_refl zero) (transport segment (eq_refl zero)) (idpath (transport segment eq_refl))).
Qed.

Goal (unit:Type)=interval.
  apply weak_univalence.
  exact (contr_is_unique unit_is_contractible interval_is_contractible).
Qed.




