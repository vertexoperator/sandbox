(* coq-8.3 *)
(* ====================================================== *)
Class Hoge (X:Type) := {
  R: X->X->Prop;
  R_dec : forall (x y:X),{R x y} + {~(R x y)}
}.

Instance nat_is_hoge : Hoge nat.
   apply (Build_Hoge nat (@eq nat)).
   decide equality.
Qed.

Goal Hoge nat.
   firstorder.
Qed.


(* ====================================================== *)
Require Import List.

Class MonoidType (M:Type) := {
  Mop : M -> M -> M;
  Mid : M;
  Mop_assoc : forall a b c:M , Mop a (Mop b c) = Mop (Mop a b) c;
  Mop_lunit : forall a:M , Mop Mid a = a;
  Mop_runit : forall a:M , Mop a Mid = a }.

Instance list_is_monoid {X} : MonoidType (list X) :=
   Build_MonoidType _ _ _ (@app_assoc X) (@app_nil_l X) (@app_nil_r X).

Goal forall X, MonoidType (list X).
   firstorder.
Qed.

(* ====================================================== *)
Class Decidable (X:Type) := {
   eq_dec : forall (x y :X),{x=y}+{x<>y}
}.

Instance nat_is_decidable : Decidable nat.
   apply Build_Decidable;decide equality.
Defined.

(* firstorderは通らない *)
Goal Decidable nat.
   intuition.
Qed.

