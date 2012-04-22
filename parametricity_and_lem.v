(* coq-8.3 *)
(*
Parametricity is inconsistent with classical logic
https://lists.chalmers.se/pipermail/agda/2012/003916.html
https://lists.chalmers.se/pipermail/agda/attachments/20120420/771f6024/parametricity.obj
*)

Inductive empty :Type := .

Definition empty_elim : forall P , empty->P.
  contradiction.
Defined.

Inductive IsInj1 {A B:Type} : (A+B)%type -> Type :=
  inj1 :forall {x:A} ,IsInj1 (inl x).

Inductive IsInj2 {A B:Type} : (A+B)%type -> Type :=
  inj2 : forall {x:B} ,IsInj2 (inr x).

Inductive Dec (A:Type) : Type :=
  | yes : A -> Dec A
  | no : (A->empty) -> Dec A.

Definition LEM := forall (A:Type), Dec A.
Definition LEM':= forall (A:Type), unit -> (A+(A->empty))%type.

Definition lem_to_lem' : LEM -> LEM'.
  unfold LEM';intros lem A x.
  destruct (lem A) as [y | n].
    exact (inl y).
    exact (inr n).
Defined.


Definition lem_Bot : forall (lem:LEM'),IsInj2 (lem empty tt).
   induction lem.
     contradiction.
     apply inj2.
Defined.

Definition lem_T : forall (lem:LEM'), IsInj1 (lem unit tt).
   induction lem.
     apply inj1.
     assert(p:=b tt);contradiction.
Defined.

Definition map_t {A B C D:Type} : (A->B) -> (C->D) -> unit -> unit := fun _ _ x => x.

Definition map_tor {A B C D:Type} (ab:A->B) (cd:C->D) : (C+(B->empty))%type -> (D+(A->empty))%type.
  intro p;destruct p as [c | not_b].
    exact (inl (cd c)).
    exact (inr (fun a=> not_b (ab a))).
Defined.

Definition contra {A B:Type} : 
  forall (g:A->B) l r,IsInj2 l -> IsInj1 r -> (map_tor (fun x=>x) g l=map_tor g (fun x=>x) r -> empty).
Proof.
  intros g l r HL HR H.
  induction HL;induction HR;discriminate.
Defined.


Definition dinatural :=
  forall 
    (F G:Type->Type->Type) 
    (mapF : forall A B C D,(A->B)->(C->D)->F B C->F A D)
    (mapG : forall A B C D,(A->B)->(C->D)->G B C->G A D)
    (f:forall A,F A A->G A A) A B (g:A->B) x,
        mapG _ _ _ _ (fun x =>x) g (f _ (mapF _ _ _ _ g (fun x=>x) x)) = 
        mapG _ _ _ _ g (fun x=>x) (f _ (mapF _ _ _ _ (fun x=>x) g x)).


Goal dinatural -> (LEM->empty).
  intros dinatural_fn lem.
  set(lem' := lem_to_lem' lem).
  assert(not_H := contra (empty_elim _) _ _ (lem_Bot lem') (lem_T lem')).
  assert(H := dinatural_fn (fun _ _=>unit) (fun A B=>(B+(A->empty))%type) (@map_t) (@map_tor) lem' empty unit (empty_elim unit) tt).
  contradiction.
Qed.

(* and parametric -> polymophic function is dinatural *)



