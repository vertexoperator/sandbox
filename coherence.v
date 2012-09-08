(* coq-8.3 *)
Inductive Id {A:Type} : A->A->Type := id_refl : forall (t:A),Id t t.

Notation "x == y" := (Id x y) (at level 70).

Definition concat {A} {x y z:A} : (x==y) -> (y==z) -> (x==z).
  intros p q.
  induction p.
  exact q.
Defined.

Definition inverse {A} {x y:A} : (x==y) -> (y==x).
  intros p.
  induction p.
  apply id_refl.
Defined.


Notation "p @ q" := (concat p q) (at level 60).
Notation "! p" := (inverse p) (at level 50).


Definition id_left_unit {A} {x y:A} (p:x==y) : (id_refl x) @ p == p.
  induction p.
  apply id_refl.
Defined.

Definition id_right_unit {A} {x y:A} (p:x==y) : p @ (id_refl y) == p.
  induction p.
  apply id_refl.
Defined.

Definition id_right_inverse {A} {x y:A} (p:x==y) : (p @ !p) == (id_refl x).
  induction p.
  apply id_refl.
Defined.

Definition id_left_inverse {A} {x y:A} (p:x==y) : (!p @ p) == (id_refl y).
  induction p.
  apply id_refl.
Defined.

Definition assoc {A} {x y z w:A} (p:x==y) (q:y==z) (r:z==w) : (p @ q) @ r == p @ (q @ r).
  induction p;induction q;induction r.
  apply id_refl.
Defined.



(*========= ここからbicategory coherence laws ============*)
(* K4 coherence is pentagon equation *)
Definition concat2 {A} {x y z:A} {p q:x==y} {r s:y==z} : p==q -> r==s -> p @ r == q @ s.
  intros f g.
  induction f ;induction g.
  apply id_refl.
Defined.


Notation "p [@] q" := (concat2 p q) (at level 61).

Definition K4 {A} {x y z w u:A} (a:x==y) (b:y==z) (c:z==w) (d:w==u) :
   ((assoc a b c) [@] (id_refl d)) @ (assoc a (b @ c) d) @ ((id_refl a) [@] (assoc b c d)) ==
      (assoc (a @ b) c d) @ (assoc a b (c @ d)).
  induction a;induction b;induction c;induction d.
  apply id_refl.
Defined.


Definition u3 {A} {x y z:A} (a:x==y) (b:y==z) :
   (concat2 (id_right_unit a) (id_refl b))==
      (assoc a (id_refl y) b) @ (concat2(id_refl a) (id_left_unit b)).
  induction a;induction b.
  apply id_refl.
Defined.



(* inverseに対するcoherence? *)
Definition left_rigid1 {A} {x y:A} (a:x==y) :
   !(id_left_unit a) @ (concat2 (!(id_right_inverse a)) (id_refl a)) @
        (assoc a (!a) a) @ (concat2 (id_refl a) (id_left_inverse a)) @ (id_right_unit a) ==
           id_refl a.
  induction a.
  apply id_refl.
Defined.


Definition left_rigid2 {A} {x y:A} (a:x==y) :
  !(id_right_unit (!a)) @ (concat2 (id_refl (!a)) (!(id_right_inverse a))) @
      !(assoc (!a) a (!a)) @ (concat2 (id_left_inverse a) (id_refl (!a))) @ (id_left_unit (!a)) ==
         id_refl (!a).
  induction a.
  apply id_refl.
Defined.




(*=========== K5 coherence ============*)
Definition concat3 {A} {x y z:A} {p q:x==y} {r s:y==z} {X Y:p==q} {Z W:r==s} : X==Y -> Z==W -> X [@] Z==Y [@] W.
  intros f g.
  induction f ;induction g.
  apply id_refl.
Defined.


Notation "p [[@]] q" := (concat3 p q) (at level 62).


(* 
  distl and distr are special cases of "(a@b)[@](c@d) == (a[@]b)@(c[@]d)"
*)
Definition distr {A} {x y z:A} {p q r:x==y} (s:y==z) (X:p==q) (Y:q==r) :
  (X @ Y) [@] (id_refl s) == (X[@](id_refl s)) @ (Y[@](id_refl s)).
Proof.
  induction X;induction Y.
  apply id_refl.
Defined.


Definition distl {A} {x y z:A} {p q r:y==z} (s:x==y) (X:p==q) (Y:q==r) :
   (id_refl s) [@] (X @ Y) == ((id_refl s) [@] X) @ ((id_refl s) [@] Y).
Proof.
  induction X;induction Y.
  apply id_refl.
Defined.



Definition assoc2 {A} {x y z w:A} {p p':x==y} {q q':y==z} {r r':z==w} (f:p==p') (g:q==q') (h:r==r'):
  (f[@]g[@]h)@(assoc p' q' r') == (assoc p q r)@(f[@](g[@]h)).
Proof.
  induction f;induction g;induction h.
  induction t;induction t0;induction t1.
  apply id_refl.
Defined.


Definition id_save {A} {x y z:A} (p:x==y) (q:y==z) : (id_refl p) [@] (id_refl q) == id_refl (p@q).
  induction p;induction q;apply id_refl.
Defined.



Definition K5_LHS {A} {x y z w u v:A} (a:x==y) (b:y==z) (c:z==w) (d:w==u) (e:u==v) :=
         (
            ((assoc _ _ _) [@] (id_refl _)) @
            (assoc _ (_@_) _) 
         ) @
         (
           (
             ( 
               (!(distr e ((assoc a b c)[@](id_refl d)) (assoc a (b@c) d))) [@] 
               (id_refl ( (id_refl a) [@] (assoc b c d) [@] (id_refl e) )) 
             ) @
             (
               (!(distr e _ _))
             )
           ) [@] 
           (
              (id_refl _)
           )
        ) @
        ( 
          (
            ( (K4 a b c d) [[@]] (id_refl (id_refl e)) ) @ 
            ( distr e (assoc (a @ b) c d) (assoc a b (c @ d)) )
          ) [@]
          (id_refl 
            ( (assoc a (b@(c@d)) e) @ 
              ((id_refl a) [@] (assoc b (c@d) e)) @ 
              ((id_refl a) [@] ((id_refl b) [@] (assoc c d e))) 
            )
          )
        ) @
        (
          !(assoc (_@_) (_@_) _) @
          ((assoc _ _ (_@_)) [@] (id_refl _)) @ 
          (((id_refl _) [@] !(assoc _ _ _))[@](id_refl _))
        ) @
        ( 
           (id_refl ( (assoc (a@b) c d) [@] (id_refl e) )) [@] 
           (K4 a b (c@d) e) [@] 
           (id_refl (( (id_refl a) [@] ((id_refl b) [@] (assoc c d e)) )))
        ) @
        (
           (!(assoc _ _ _) [@] (id_refl _)) @ (assoc _ _ _)
        ) @
        (
           (id_refl ( (assoc (a@b) c d) [@] (id_refl e) )) [@]
           (id_refl (assoc (a@b) (c@d) e)) [@]
           ( 
             !(assoc2 (id_refl a) (id_refl b) (assoc c d e)) @
             ( ((id_save a b) [[@]] (id_refl (assoc c d e))) [@] (id_refl _) )
           )
        ) @
        (
           !(assoc _ _ _)
        ) @
        ( 
           (K4 (a@b) c d e) [@] (id_refl (assoc a b _))
        ).



Definition K5_RHS {A} {x y z w u v:A} (a:x==y) (b:y==z) (c:z==w) (d:w==u) (e:u==v) :=
        (
           (assoc (_@_) _ _) [@] (id_refl _) [@] (id_refl _)
        ) @
        (
           (id_refl ((assoc a b c) [@] (id_refl d) [@] (id_refl e))) [@]
           (id_refl ((assoc a (b@c) d) [@] (id_refl e))) [@]
           (assoc2 (id_refl a) (assoc b c d) (id_refl e)) [@]
           (id_refl ((id_refl a) [@] (assoc b (c@d) e))) [@]
           (id_refl ((id_refl a) [@] ((id_refl b) [@] (assoc c d e))))
        ) @
        ( 
           ( (!(assoc (_@_) _ _)) [@] (id_refl _) [@] (id_refl _) ) @
           ( assoc (_@_@_@_) _ _ ) @
           ( assoc (_@_@_) _ (_@_) ) @
           ( (id_refl _) [@] ((id_refl _) [@] (!(distl a _ _))) ) @
           ( (id_refl _) [@] (!(distl a _ _)) ) @
           ( (id_refl _) [@] ((id_refl (id_refl a)) [[@]] !(assoc _ _ _)) )
        ) @
        (
           (id_refl ((assoc a b c) [@] (id_refl d) [@] (id_refl e))) [@]
           (id_refl ((assoc a (b@c) d) [@] (id_refl e))) [@]
           (id_refl (assoc a _ e)) [@]
           ( (id_refl (id_refl a)) [[@]] (K4 b c d e) )
        ) @
        (
           ((id_refl _) [@] (distl a _ _)) @
           !(assoc _ _ _) @
           ( (assoc _ _ _) [@] (id_refl _) [@] (id_refl _) ) @
           ( (assoc _ _ _) [@] (id_refl _) )
        ) @
        (
           (id_refl ((assoc a b c[@]id_refl d)[@]id_refl e) ) [@]
           (K4 a (b@c) d e) [@]
           (id_refl ((id_refl a) [@] (assoc _ _ _)))
        ) @
        ( 
          ( !(assoc _ _ _) [@] (id_refl _) )
        ) @
        (
          ((assoc2 (assoc a b c) (id_refl d) (id_refl e))) [@]
          (id_refl (assoc _ _ _)) [@]
          (id_refl ((id_refl a) [@] (assoc _ _ _)))
        ) @
        (
          ( ( (id_refl _) [@] 
              ((id_refl (assoc a b c))[[@]](id_save d e)) ) [@]
            (id_refl _) ) [@]
          (id_refl _)
        ) @
        (      
           (assoc (_ @ _) _ _) @ 
           (assoc _ _ (_ @ _)) @
           ((id_refl _) [@] !(assoc _ _ _))
        ) @
        (
           (id_refl _) [@] (K4 a b c (d@e))
        ) @
        ( 
           !(assoc _ _ _) 
        ).


Definition K5 {A}  {x y z w u v:A} (a:x==y) (b:y==z) (c:z==w) (d:w==u) (e:u==v) :
    K5_LHS  a b c d e == K5_RHS a b c d e.
Proof.
   induction a;induction b;induction c;induction d;induction e.
   apply id_refl.
Defined.


