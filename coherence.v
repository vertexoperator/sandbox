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



(*========= basic naturality laws ========*)
Definition concat2 {A} {x y z:A} {p q:x==y} {r s:y==z} : p==q -> r==s -> p @ r == q @ s.
  intros f g.
  induction f ;induction g.
  apply id_refl.
Defined.


Notation "p [@] q" := (concat2 p q) (at level 61).


Definition assoc_is_left_monoidal {A} {x y z:A} (q:x==y) (r:y==z) : (assoc (id_refl _) q r)==(id_refl (q@r)).
  induction q;induction r;apply id_refl.
Defined.


Definition assoc_is_center_monoidal {A} {x y z:A} (p:x==y) (r:y==z) : 
   (assoc p (id_refl _) r)==(id_right_unit p)[@](id_refl r).
Proof.
  induction p;induction r;apply id_refl.
Defined.


Definition assoc_is_right_monoidal {A} {x y z:A} (p:x==y) (q:y==z) :
  (assoc p q (id_refl _))==(id_right_unit (p@q))@(id_refl p[@]!id_right_unit q).
Proof.
  induction p;induction q;apply id_refl.
Defined.


Definition id_right_unit_is_natural {A} {x y:A} {p q:x==y} (f:p==q) : 
   (f [@] (id_refl _))@(id_right_unit q)==(id_right_unit p)@f.
Proof.
  induction f;induction t;apply id_refl.
Defined.


Definition assoc_is_natural {A} {x y z w:A} {p p':x==y} {q q':y==z} {r r':z==w} (f:p==p') (g:q==q') (h:r==r'):
  (f[@]g[@]h)@(assoc p' q' r') == (assoc p q r)@(f[@](g[@]h)).
Proof.
  induction f;induction g;induction h.
  induction t;induction t0;induction t1.
  apply id_refl.
Defined.


(*========= bicategory coherence laws ============*)
(* K4 coherence is pentagon equation *)

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
             (!assoc_is_natural (id_refl a) (id_refl b) (assoc c d e)) @
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
           (assoc_is_natural (id_refl a) (assoc b c d) (id_refl e)) [@]
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
          ((assoc_is_natural (assoc a b c) (id_refl d) (id_refl e))) [@]
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


(*===================== higher commutativity laws =====================*)
Definition interchange {A} {x y z:A} {p q r:x==y} {s t u:y==z} (a:p==q) (b:q==r) (c:s==t) (d:t==u) : 
  (a @ b) [@] (c @ d) == (a [@] c) @ (b [@] d).
Proof.
   induction a;induction b;induction c;induction d.
   apply id_refl.
Defined.


Definition concat2_is_left_unital {A} {x y:A} {p q:x==y} (s:p==q) :
  (id_refl (id_refl x)) [@] s == (id_left_unit p) @ s @ !(id_left_unit q).
Proof.
  induction s.
  induction t.
  apply id_refl.
Defined.

Definition concat2_is_right_unital {A}  {x y:A} {p q:x==y} (s:p==q) :
  s [@] (id_refl (id_refl y)) == (id_right_unit p) @ s @ !(id_right_unit q).
Proof.
  induction s.
  induction t.
  apply id_refl.
Defined.



Definition concat2_is_left_unital_pt {A} {x:A} (s:(id_refl x)==(id_refl x)) : 
   (id_refl (id_refl x)) [@] s == s.
Proof.
   exact( (concat2_is_left_unital s) @ (id_right_unit (_@s)) ).
Defined.


Definition concat2_is_right_unital_pt {A} {x:A} (s:(id_refl x)==(id_refl x)) : 
   s [@] (id_refl (id_refl x)) == s.
Proof.
   exact( (concat2_is_right_unital s) @ (id_right_unit s) ).
Defined.


(*
Eckmann-Hilton argument:
a @ b == (e [@] a) @ (b [@] e) == (e @ b) [@] (a @ e) == b [@] a == 
(b @ e) [@] (e @ a) == (b [@] e) @ (e [@] a) == b@a
*)

Definition comm {A} {x:A} (a b:(id_refl x)==(id_refl x)): a @ b == b @ a.
  set (e:=id_refl (id_refl x)).
  assert(p1 := ((concat2_is_left_unital_pt a) [@] (concat2_is_right_unital_pt b))).
  assert(p2 := interchange e b a e).
  assert(p3 := (!id_left_unit b) [[@]] (!id_right_unit a)).
  assert(p4 := (!id_right_unit b) [[@]] (!id_left_unit a)).
  assert(p5 := interchange b e e a).
  assert(p6 := ((concat2_is_right_unital_pt b) [@] (concat2_is_left_unital_pt a))).
  exact ( ((!p1) @ (!(p3 @ p2))) @ ((p4 @ p5) @ p6) ).
Defined.



Definition comm_is_dinatural {A} {x:A} {a b a' b':(id_refl x)==(id_refl x)} (f:a==a') (g:b==b') :
   (f [@] g)@(comm a' b')==(comm a b)@(g [@] f).
Proof.
   induction f;induction g.
   exact (!id_right_unit _).
Defined.



(* =====  prove hexagon and Yang-Baxter equation ======*)
(*
Reference:
A.Joyal and R.Street,
Braided tensor categories, Advances in Math. 102 (1993) 20-78
http://maths.mq.edu.au/~street/JS1.pdf
*)

(* analogous to Hom(X,Y) -> Hom(Y^{*},X^{*}) *)
Definition dualize {A} {x y:A} {p q:x==y} : (p==q) -> (!q==!p).
Proof.
  intro f.
  exact(
    (!id_right_unit (!q)) @ 
    ((id_refl _) [@] (!id_right_inverse p)) @
    ((id_refl _) [@] (f [@] id_refl _)) @ 
    (!assoc (!q) (q) (!p)) @
    ((id_left_inverse _) [@] (id_refl _)) @ 
    (id_left_unit _)
  ).
Defined.


Definition inv_dist {A} {x y z:A} (p:x==y) (q:y==z):!(p @ q)==!q @ !p.
  induction p;induction q;apply id_refl.
Defined.

Definition dualize_dist {A}  {x y:A} {p q r:x==y} (s:p==q) (t:q==r) : 
   dualize (s @ t) == (dualize t) @ (dualize s).
Proof.
   induction s;induction t.
   induction t.
   apply id_refl.
Defined.

Definition dualize_id_left_unit {A} {x y:A} (p:x==y) : 
   (dualize (id_left_unit p)) == (!id_right_unit (!p))@(!inv_dist (!id_refl x) p).
Proof.
   induction p;apply id_refl.
Defined.

Definition inv_sq {A} {x y:A} (p:x==y) : !(!p)==p.
   induction p;apply id_refl.
Defined.


Definition dualize_sq {A} {x y:A} {p q:x==y} (s:p==q) : 
  (dualize (dualize s))==(inv_sq p)@s@(!inv_sq q).
Proof.
  induction s;induction t;apply id_refl.
Defined.


Definition dualize_commute_inv {A} {x y:A} {p q:x==y} (s:p==q):
   dualize (!s)==!(dualize s).
Proof.
 induction s;induction t;apply id_refl.
Defined.


Definition inv3 {A} {x y:A} {p q:x==y} {s t:p==q} : s==t -> dualize t==dualize s.
   intro f;induction f;apply id_refl.
Defined.


Definition MF3 {A} {x y z:A} {p1 p2 p3 p4:x==y} {q1 q2 q3 q4:y==z}
   (a:p1==p2) (b:p2==p3) (c:p3==p4) (a':q1==q2) (b':q2==q3) (c':q3==q4):
      (interchange a (b@c) a' (b'@c'))@
      ((id_refl (a[@]a')) [@] (interchange b c b' c'))@
      (!assoc (a[@]a') (b[@]b') (c[@]c'))
      ==
      (!((assoc a b c) [[@]] (assoc a' b' c')))@
      (interchange (a@b) c (a'@b') c')@
      ((interchange a b a' b') [@] (id_refl (c[@]c'))).
Proof.
  induction a;induction b;induction c;induction a';induction b';induction c'.
  apply id_refl.
Defined.


Definition id_left_unit_is_identity {A} {x y:A} (p:x==y):id_left_unit p==id_refl p.
   induction p;apply id_refl.
Defined.


Definition PI_partL {A} {x y:A} {p q r:x==y} (a:p==q) (b:q==r) :
   (id_left_unit p @ a @ !id_left_unit q) @ (id_left_unit q @ b @ !id_left_unit r)==
     (id_left_unit p)@(a@b)@(!id_left_unit r).
Proof.
exact(
  (
     (
        ((id_refl _) [@] (!dualize (id_left_unit_is_identity q))) @ 
        (id_right_unit (_@a)) @
        ((id_left_unit_is_identity p) [@] (id_refl _))  
     ) [@]
     (
        ((id_refl _) [@] (!dualize (id_left_unit_is_identity r))) @ 
        (id_right_unit (_@b)) @
        ((id_left_unit_is_identity q) [@] (id_refl _)) 
     )
  ) @
  !(
     ((id_refl _) [@] (!dualize (id_left_unit_is_identity r))) @ 
     (id_right_unit (_@(a@b))) @
     ((id_left_unit_is_identity p) [@] (id_refl _)) 
  )
).
Defined.


Definition PIL_proto {A} {x y:A} {p q r:x==y} (a:p==q) (b:q==r) :
  concat2_is_left_unital (a@b) == 
     (interchange _ _ a b) @
     (concat2_is_left_unital a [@] concat2_is_left_unital b) @
     (PI_partL a b).
Proof.
   induction a;induction b.
   induction t.
   apply id_refl.
Defined.


Definition PIL {A} {x:A} (a b:(id_refl x)==(id_refl x)) :
  concat2_is_left_unital_pt (a@b) ==
    ( interchange (id_refl (id_refl x)) (id_refl (id_refl x)) a b ) @
    ( concat2_is_left_unital_pt a [@] concat2_is_left_unital_pt b ).
Proof.
  set(Hab := id_right_unit (id_left_unit (id_refl x) @ (a @ b))).
  set(Ha := id_right_unit (id_left_unit (id_refl x) @ a)).
  set(Hb := id_right_unit (id_left_unit (id_refl x) @ b)).
  set(c := id_right_unit (a @ b) @ id_refl (a @ b)).
  exact (
    ((PIL_proto a b) [@] (id_refl Hab)) @
    (assoc _ (PI_partL a b) Hab) @
    ((id_refl _) [@] (assoc _ (!c) Hab)) @
    ((id_refl _) [@] ((id_refl _) [@] ((inv_dist _ _)[@](id_refl Hab)))) @
    ((id_refl _) [@] ((id_refl _) [@] (id_left_inverse _))) @
    ((id_refl _) [@] (id_right_unit _)) @
    (assoc _ _ _) @
    ((id_refl _) [@] (((id_refl _) [[@]] (id_refl _)) [@] ((id_right_unit Ha) [[@]] (id_right_unit Hb)))) @
    ((id_refl _) [@] (!interchange _ Ha _ Hb))
  ).
Defined.


Definition inv_dist2 {A} {x y z:A} {p q:x==y} {r s:y==z} (X:p==q) (Y:r==s) : !(X[@]Y)==(!X[@]!Y).
  induction X;induction Y;apply id_refl.
Defined.


Definition PI_partR {A} {x y:A} {p q r:x==y} (a:p==q) (b:q==r) :
   (id_right_unit p @ a @ !id_right_unit q) @ (id_right_unit q @ b @ !id_right_unit r)==
     (id_right_unit p)@(a@b)@(!id_right_unit r).
Proof.
  set(H:=
    (assoc a (!id_right_unit q) (id_right_unit q @ b)) @
    ((id_refl a) [@] (!assoc (!id_right_unit q) _ b)) @
    ((id_refl a) [@] ((id_left_inverse _) [@] (id_refl b))) @
    ((id_refl a) [@] (id_left_unit b))
  ).
  exact(
    ((assoc (id_right_unit p) a (!id_right_unit q)) [@] (id_refl (id_right_unit q @ b @ !id_right_unit r))) @
    (assoc (id_right_unit p) _ _)@
    ((id_refl (id_right_unit p)) [@] (!assoc _ _ _))@
    (!assoc (id_right_unit p) _ (!id_right_unit r)) @
    ((id_refl (id_right_unit p)) [@] H [@] (id_refl _))
  ).
Defined.


Definition PIR_proto {A} {x y:A} {p q r:x==y} (a:p==q) (b:q==r) :
  concat2_is_right_unital (a@b) == 
     (interchange a b _ _) @
     (concat2_is_right_unital a [@] concat2_is_right_unital b) @
     (PI_partR a b).
Proof.
   induction a;induction b.
   induction t.
   apply id_refl.
Defined.


Definition PIR {A} {x:A} (a b:id_refl x==id_refl x) :
  concat2_is_right_unital_pt (a@b) ==
    ( interchange a b (id_refl (id_refl x)) (id_refl (id_refl x)) ) @
    ( concat2_is_right_unital_pt a [@] concat2_is_right_unital_pt b ).
Proof.
  set(p:=id_refl x).
  set(q:=id_refl x).
  set(r:=id_refl x).
  set(va:=a @ (!id_right_unit q)).
  set(vb:=(id_right_unit q) @ b).

  set(redH :=
    (
      (
        (
          (assoc_is_center_monoidal a (id_right_unit q @ b)) [@]
          ((id_refl (id_refl a)) [[@]] (!dualize (assoc_is_center_monoidal (!id_right_unit q) b))) [@]
          (id_refl ((id_refl a) [@] ((id_left_inverse _) [@] (id_refl b))))
        )@(id_right_unit _)@(id_right_unit _)
      )[@]
      (id_refl ((id_refl a) [@] (id_left_unit b)))
    )@(!interchange _ _ _ _)@((id_right_unit _)[[@]](id_left_unit _))
  ).

  set(redX:=
    (!id_right_unit _)@
    ((id_refl _)[@](!id_right_inverse _))@
    (!assoc _ _ _)@
    (
      (assoc_is_natural (id_refl (id_right_unit p)) 
                        (id_right_unit a[@]id_left_unit b) 
                        (id_refl (!id_right_unit r)))[@]
      (id_refl (!assoc (id_right_unit p) (a @ b) (!id_right_unit r)))
    )@
    ( (id_refl _)[@](!dualize (assoc_is_left_monoidal (a@b) (!id_right_unit r))) )@
    (id_right_unit _)@
    ( (assoc_is_left_monoidal _ _)[@](id_refl _) )@
    (id_left_unit _)
  ).

  set(redP:=
    (id_refl (PI_partR a b))@
    (
       ( 
          (assoc_is_left_monoidal a (!id_right_unit q)) [[@]] 
          (id_refl (id_refl (id_right_unit q @ b @ !id_right_unit r)))
       )[@]
       (
          assoc_is_left_monoidal (a @ !id_right_unit q) (id_right_unit q @ b @ !id_right_unit r)
       )[@]
       (id_refl _)[@]
       (
          !dualize (assoc_is_left_monoidal ((a @ !id_right_unit q) @ (id_right_unit q @ b)) (!id_right_unit r))
       )[@]
       ( (id_refl _)[[@]]redH[[@]](id_refl _) )
    )@
    ( ((id_right_unit _)@(id_left_unit _)) [@] (id_refl _) )@
    ( (id_refl _)[@]redX )@
    ( !interchange (id_refl (id_right_unit p)) (id_refl (id_right_unit p)) (!assoc va vb _) _)@
    ( 
      (id_left_unit (id_refl (id_right_unit p))) [[@]] 
      ( 
        (
          (!dualize (assoc_is_right_monoidal va vb))@(inv_dist _ _)[@]
          (concat2_is_right_unital _)
        )@
        (!assoc (_@_) (_@_) _)@
        ((!assoc (_@_) _ _)[@](id_refl _))@
        ((assoc _ _ _)[@](id_refl _)[@](id_refl _))@
        (( (inv_dist2 _ _)@((id_refl _)[[@]](inv_sq _)) )[@](id_left_inverse _)[@](id_refl _)[@](id_refl _))@
        ((id_right_unit _)[@](id_refl _)[@](id_refl _))@
        ((!interchange (!id_refl va) (id_right_unit a) (id_right_unit vb) (id_left_unit b))[@](id_refl _))
      )
    )
  ).

  set(redA:=
    (
      (
        redP@
        (interchange 
           (id_refl (id_right_unit p)) 
           (id_refl (id_right_unit p)) 
           (!id_refl va @ id_right_unit a[@]id_right_unit vb @ id_left_unit b)
           (!id_right_unit (a@b))
        )@
        ((id_refl _)[@]
         (
           (concat2_is_left_unital (!id_right_unit (a @ b)))@
           ((id_left_unit_is_identity _) [@] (id_refl _) [@] (!dualize (id_left_unit_is_identity _)))@
           (id_right_unit _)@(id_left_unit _)
         )
        )
      )[@](id_refl (id_right_unit (a@b)))
    )@(assoc _ _ _)@((id_refl _)[@](id_left_inverse _))@(id_right_unit _)
  ).

  exact(
    ((PIR_proto a b)[@](id_refl (id_right_unit (a @ b)))) @
    (assoc _ (PI_partR a b) (id_right_unit (a @ b)))@
    ((id_refl _)[@](
      redA@(concat2_is_left_unital _)@
      ((id_left_unit_is_identity _) [@] (id_refl _) [@] (!dualize (id_left_unit_is_identity _)))
      @(id_right_unit _)@(id_left_unit _)@
      ((id_left_unit _)[[@]](
          (!id_right_unit_is_natural (id_left_unit b))@
          (((id_left_unit_is_identity _)[[@]](id_refl _))[@](id_refl _))@(id_left_unit _)
      ))
    ))@
    (assoc _ _ _)@((id_refl _)[@](!interchange _ _ _ _))
  ).
Defined.



Definition hexagonR {A} {x:A} (a b c:(id_refl x)==(id_refl x)) :
  (assoc a b c) @ (comm a (b@c)) @ (assoc b c a) == 
     ((comm a b) [@] (id_refl c)) @ (assoc b a c) @ ((id_refl b) [@] (comm a c)).
Proof.
  assert(H1:(id_refl (b@a)[@](id_refl c))==id_refl _) by (apply id_refl).
  assert(H2:(id_refl b)[@](id_refl (c @ a)) == id_refl (b@(c@a))) by (apply id_refl).
  set (e:=id_refl (id_refl x)).
  set(LA:=concat2_is_left_unital_pt a).
  set(RB:=concat2_is_right_unital_pt b).
  set(RC:=concat2_is_right_unital_pt c).

  set(R1:=
      ((PIR b c)[[@]](id_refl LA))@
      (interchange _ (RB[@]RC) (id_refl (e[@]a)) LA)
  ).

  set(L1:=
        ( ((id_refl LA)[[@]](PIR b c))[@](id_refl (!assoc a b c)) )@
        ( (interchange (id_refl (e[@]a)) LA _ (RB[@]RC))[@](id_refl (!assoc a b c)) )@
        (assoc _ _ (!assoc a b c))@
        ( (id_refl _)[@]
          (
              ((!id_left_inverse _)[@](id_refl (LA[@](RB[@]RC)))[@](id_refl _))@
              ((assoc _ _ _)[@](id_refl _))@
              ((id_refl (!assoc (e[@]a) (b[@]e) (c[@]e)))[@](!assoc_is_natural LA RB RC)[@](id_refl (!assoc a b c)))@
              (assoc _ (_@_) _)@
              ((id_refl _)[@](assoc _ _ _))@
              ((id_refl _)[@]((id_refl _)[@](id_right_inverse _)))@
              ((id_refl _)[@](id_right_unit _))
           )
        )@
        (!assoc _ _ _)
   ).

   set(L2:=
      ((id_refl (interchange e (b @ c) a (e @ e)))[@]L1)@
      (!assoc _ (_@_) _)@((!assoc _ _ _)[@](id_refl (LA[@]RB[@]RC)))@
      ((MF3 e b c a e e)[@](id_refl _))
   ).

  set(T1:=
     (!id_right_unit _)@
     ((id_refl _)[@](!H1))@
     ((id_refl _)[@]((!id_left_unit _)[[@]](!id_left_inverse RC)))@
     ((id_refl _)[@](interchange _ _ (!RC) RC))@
     (!assoc ((comm a b)[@](id_refl c)) ((id_refl (b@a))[@](!RC)) ((id_refl (b@a)[@]RC)))@
     (
       (
         (!interchange (comm a b) (id_refl _) (id_refl _) (!RC))@
         ((id_right_unit (comm a b))[[@]](id_left_unit (!RC)))@
         ((!id_left_unit (comm a b))[[@]](!id_right_unit (!RC)))@
         (interchange (id_refl _) (comm a b) (!RC) (id_refl _))
       )[@](id_refl _)
     )@
     ((id_refl _)[@](interchange _ _ (id_refl _) (id_refl _))[@](id_refl _))@
     ((!assoc _ _ _)[@](id_refl _))@(assoc (_@_) _ _)@
     ((!interchange _ _ _ _)[@](!interchange _ _ _ _))@
     (((id_left_unit _)[[@]](id_refl _))[@]((id_right_unit _)[[@]](id_refl _)))@
     ((interchange (!(LA[@]RB)) _ (!RC) (id_refl (c[@]e)))[@](interchange _ (RB[@]LA) (id_refl (c[@]e)) RC))@
     (((!inv_dist2 (LA[@]RB) RC)[@](id_refl _))[@](id_refl _))@
     (!assoc (_@_) _ _)@((assoc _ _ _)[@](id_refl _))
   ).

   set(T2:=
     (!id_right_unit _)@
     ((id_refl _)[@](!H2))@
     ((id_refl _)[@]((!id_left_inverse RB)[[@]](!id_left_unit _)))@
     ((id_refl _)[@](interchange (!RB) RB _ _))@
     (!assoc ((id_refl b)[@](comm a c)) ((!RB)[@](id_refl (c@a))) (RB[@](id_refl (c@a))))@
     (
       (
         (!interchange (id_refl b) (!RB) (comm a c) (id_refl _))@
         ((id_left_unit (!RB))[[@]](id_right_unit _))@
         ((!id_right_unit (!RB))[[@]](!id_left_unit _))@
         (interchange _ _ _ _)
       )[@](id_refl _)
     )@
     ((id_refl _)[@](interchange (id_refl (b[@]e)) (id_refl (b[@]e)) _ _)[@](id_refl _))@
     ((!assoc _ _ _)[@](id_refl _))@
     (assoc (_@_) _ _)@
     ((!interchange (!RB) (id_refl (b[@]e)) (id_refl _) _)[@](!interchange (id_refl (b[@]e)) RB _ _))@
     (((id_refl _)[[@]](id_left_unit _))[@]((id_refl _)[[@]](id_right_unit _)))@
     ((interchange (!RB) (id_refl (b[@]e)) _ _)[@](interchange _ RB _ (RC[@]LA)))@
     (((!inv_dist2 RB (LA[@]RC))[@](id_refl _))[@](id_refl _))@
     (assoc _ _ (_@_))@((id_refl _)[@](!assoc _ _ _))
   ).

   set(T3:=
     (T1[@](id_refl (assoc b a c))[@]T2)@
     ((assoc (_@(_@_)) _ _)[@](id_refl _))@
     (assoc _ _ _)@((id_refl (_@(_@_)))[@](!assoc (_@_) _ _))@
     (
       (id_refl _)[@](
       (
           ((assoc_is_natural RB LA RC)[@](id_refl (!(RB[@](LA[@]RC)))))@
           (assoc _ _ _)@
           ((id_refl _)[@](id_right_inverse _))@
           (id_right_unit _)
       )[@]
       (id_refl _))
     )@
     ((id_refl _)[@](!assoc _ _ _))@
     (!assoc _ _ _)
   ).

   (* FIXME: M1を示す。(MF3 b e c e a e)を変形するだけ *)
   assert(M1 : (interchange b e e a[@]id_refl (c[@]e))@
               (assoc (b[@]e) (e[@]a) (c[@]e))@
               (id_refl (b[@]e)[@]!interchange e c a e)==
               (!interchange (b @ e) c (e @ a) e)@
               (assoc b e c[[@]]assoc e a e)@
               (interchange b (e @ c) e (a @ e)) ).

   (* FIXME: M2を示す。(!dualize (MF3 e b c a e e))を変形 *)
   assert(M2 : (!interchange e b a e[@]id_refl (c[@]e))@
               (!interchange (e @ b) c (a @ e) e)@
               (assoc e b c[[@]]assoc a e e) ==
               (assoc (e[@]a) (b[@]e) (c[@]e))@
               (id_refl (e[@]a)[@]!interchange b c e e)@
               (!interchange e (b @ c) a (e @ e)) ).

   assert(M3 : (interchange b (c @ e) e (e @ a)@
               (id_refl (b[@]e)[@]interchange c e e a))@
               (!assoc (b[@]e) (c[@]e) (e[@]a)) ==
               (!(assoc b c e[[@]]assoc e e a))@
               (interchange (b @ c) e (e @ e) a) @
               (interchange b c e e[@]id_refl (e[@]a)) ).
     exact (MF3 b c e e e a).
   (* FIXME: Goalを示す
      (1)T3をM1で変形
      (2)(1)の結果をM2とM3で変形
      (3)(2)の結果をL1とL2で変形
      (49多分、あと何か
   *)
Admitted.


(* FIXME:hexagonRと同様にして示す *)
Definition hexagonL {A} {x:A} (a b c:(id_refl x)==(id_refl x)) :
  (!assoc a b c)@(comm (a@b) c)@(!assoc c a b)==
    ((id_refl a)[@](comm b c))@(!assoc a c b)@((comm a c)[@](id_refl b)).
Proof.
Admitted.



(* FIXME:Yang-Baxter方程式を示す *)
Definition YBE {A} {x:A} (a b c:(id_refl x)==(id_refl x)) :
  ((comm a b)[@](id_refl c)) @ (assoc b a c) @ 
  ((id_refl b)[@](comm a c)) @ (!assoc b c a) @ 
  ((comm b c)[@](id_refl a)) @ (assoc c b a) ==
  (assoc a b c) @ ((id_refl a)[@](comm b c)) @ 
  (!assoc a c b) @ ((comm a c)[@](id_refl b)) @ 
  (assoc c a b) @ ((id_refl c)[@](comm a b)).
Proof.
  (* N : comm a (b @ c) @ (comm b c[@]id_refl a) == (id_refl a[@]comm b c) @ comm a (c @ b) *)
  set(N := !comm_is_dinatural (id_refl a) (comm b c)).

  (* hexagonR a b c *)
  assert(BX : (comm a b[@]id_refl c) @ (assoc b a c) @ 
             ((id_refl b)[@](comm a c)) @ (!assoc b c a) ==
             (assoc a b c) @ (comm a (b @ c)) ).

  (* hexagonR a c b *)
  assert(BY : (comm a (c @ b))@assoc c b a ==
              (!assoc a c b) @ ((comm a c)[@](id_refl b)) @ 
              (assoc c a b) @ ((id_refl c)[@](comm a b)) ).

  (*
     set(P:=
       (BX [@] (id_refl (comm b c[@]id_refl a))@
       (assoc _ _ _)@
       ((id_refl (assoc a b c))[@]N)
     ).
     set(Q:=
       (P [@] (id_refl (assoc c b a)))@
       (....)@
       (.... [@] BY)
     ).
     etc.
   *)
Admitted.


(*
MEMO:YBEがZamolodchikov tetrahedron equationを満たすこと

((YBE a b c)[@](id_refl d))[[@]]???? : (1)==(2)
???[[@]]???[[@]]((id_refl c)[@](YBE a b d))[[@]]??? : (2)==(3)

(4)==(4.5) from  ((id_refl a)[@](YBE b c d))
(4.5)==(5) from naturality of comm

(1)(ABC)D->(BAC)D->(BCA)D->(CBA)D->CBDA->CDBA->DCBA
(2)(ABC)D->(ACB)D->(CAB)D->(CBA)D->CBDA->CDBA->DCBA
(3)(ABC)D->(ACB)D->CABD->CADB->CDAB->CDBA->DCBA
(3.5)
(4)ABCD->ACBD->ACDB->ADCB->DACB->DCAB->DCBA
(4.5)ABCD->ABDC->ADBC->ADCB->DACB->DCAB->DCBA
(5)ABCD->ABDC->ADBC->DABC->DACB->DCAB->DCBA

(1')=(1)
(2')ABCD->BACD->BCAD->BCDA->BDCA->DBCA->DCBA
(3')ABCD->BACD->BADC->BDAC->DBAC->DBCA->DCBA
(4')ABCD->ABDC->ADBC->DABC->DBAC->DBCA->DCBA
(5')=(5)


References:
[1]Kapranov and Voevodsky ,2-categories and Zamolodchikov tetrahedra equations, in Algebraic Groups and Their Generalizations

*)



(* 
 (pivotal) monoidal categoryに於けるcategorical trace
 Q1: left traceとright traceがあるけど、一致する？
 
 多分、Whitehead bracketは、
   WB x y := trace ((comm x y)@(comm y x))
 Whitehead half-square mapは、
   WM x := trace (comm x x)
 
 Q2: (WB x y)@(WM x)@(WM y) == WM (x@y)が言える?

 Q3: n-基本亜群(n>2)に於ける標準的なWhitehead積$\pi_2 \times \pi_2 \to \pi_3$とこの定義が一致することの証明

Reference: Fusion categories and homotopy theory(arXiv:0909.3140) Chapter7.3

*)

Definition trace {A} {x:A} {a:id_refl x==id_refl x} (f:a==a) :=
  (!id_right_inverse a) @ (f [@] (id_refl (!a))) @ 
  ((!inv_sq a)[@](id_refl (!a))) @ (id_left_inverse (!a)).



