(* coq-8.3 *)
(* 基本的にConCATのコピペ *)
(*
目標 : ConCATからSetoid_dupとかCategory_dup2とかを追放したい

それをやろうとすると、以下の問題が発生

1)関手圏が定義できるように、自然変換にSetoidの構造を入れると、
Setoidの圏が定義できなくなる(universe inconsistency)=>米田の補題とかも書けない

2)Setoidの圏を定義すると、自然変換全体をSetoidにできない(universe inconsistency)
=>関手圏が定義できない


米田の補題が直接書けなくても、
任意のXについてHom(A,X)とHom(B,X)が同型 -> AとBが同型
は多分言えるので、あんまり問題ない

*)
(*
別のアプローチ
1)Type Classを使う(>Coq v 8.2)
Matthieu Sozeauさん(Type Class提唱した本人？)の実装
darcs get http://mattam.org/repos/coq/cat

Benedikt Ahrensさんの実装
darcs get http://web.math.unifi.it/~benedikt/coq/cat/ 

とりあえず、
forall (C:Category Ob Hom),...
とか書きたくないよね。CoqのType Classって、あんまり意味がないような


2)Hofmann-Streicherの論文に書いてあるアプローチ
The Groupoid Interpretation of Type Theory
http://citeseerx.ist.psu.edu/viewdoc/summary?doi=10.1.1.37.606

5.5節に"A new formulation of category theory"とか
Hom:Ob->Ob->Setoidの代わりに
Hom:Ob->Ob->Uを使う

それで、all OKになるかはしらない。まあ、どっちにしろ、基本的には大きく変わらない

*)


Set Implicit Arguments.
Unset Strict Implicit.


(* -------------------------------------------------------------------------- *)
(* RelationとSetoidの定義 *)
(* Coqの標準ライブラリにあるけど、Coqのバージョン毎に定義が違うので、自前で *)

Definition Relation (U:Type) := U -> U -> Prop.
Section equivalence.
  Variable U:Type.
  Variable R:Relation U.
  Definition Reflexive := forall x : U, R x x.
  Definition Transitive := forall x y z : U, R x y -> R y z -> R z x.
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


Structure  Setoid : Type := {
  Carrier :> Type;
  Equal : Relation Carrier;
  Prf_equiv :> Equivalence Equal
}.

(* Coq-8.3の記法に合わせる *)
Infix "==" := Equal (at level 70).

(* Infix "=_S" := Equal (at level 70). *)



(* -------------------------------------------------------------------------- *)
(* Setoid間の写像の定義。外延性が成り立つ *)

Definition Map_law (A B:Setoid) (f : Carrier A->Carrier B) := 
   forall x y : Carrier A, x == y -> f x == f y.

Structure  Map (A:Setoid) (B:Setoid) :Type := {
  Ap :> Carrier A -> Carrier B;
  Pres : Map_law Ap
}.

Section map_ext.
  Variable A B:Setoid.
  Definition Ext (f g : Map A B) := forall x : A, f x == g x.
  Lemma Ext_equiv : Equivalence Ext.
  Proof.
    apply Build_Equivalence.
    unfold Reflexive;unfold Ext;intros f x;apply (Prf_equiv B).
    unfold Transitive;unfold Ext;intros f g h H1 H2 x;
    exact ((Prf_trans (Prf_equiv B)) (f x) (g x) (h x) (H1 x) (H2 x)).
    unfold Symmetric;unfold Ext;intros f g H x.
    exact ((Prf_sym (Prf_equiv B)) (f x) (g x) (H x)).
  Qed.
End map_ext.

Canonical Structure Map_setoid (A B:Setoid) : Setoid := Build_Setoid (Ext_equiv A B).
Infix "===>" := Map_setoid (at level 95, right associativity).

(* -------------------------------------------------------------------------- *)
(* Definition of category *)
(*
  射の合成の型を
  Hom a b->Hom b c->Hom a c
  にすると、f==g -> h o f == h o gとかが言えなくて困る
*)
Section cat.
  Variables (Ob : Type) (Hom : Ob -> Ob -> Setoid).
  Variable comp : forall a b c : Ob, (Hom a b) ===> (Hom b c) ===> (Hom a c).
  Implicit Arguments comp [a b c].
  Infix "o" := (fun f g=> comp g f) (at level 20, right associativity).
  Definition Assoc_law :=
    forall (a b c d : Ob) (f:Hom a b) (g:Hom b c) (h:Hom c d),  
      h o (g o f) == (h o g) o f.

  Variable Id : forall a : Ob,Hom a a.
  Definition Idl_law := forall (a b : Ob) (f : Hom a b), Id _ o f == f.
  Definition Idr_law := forall (a b : Ob) (f : Hom b a), f == f o Id _.
End cat.

Structure Category : Type := {
  Ob : Type;
  Hom : Ob->Ob->Setoid;
  Op_comp : forall a b c : Ob,(Hom a b) ===> (Hom b c) ===> (Hom a c);
  Id : forall a:Ob,(Hom a a);
  Prf_ass : Assoc_law Op_comp;
  Prf_idl : Idl_law Op_comp Id;
  Prf_idr : Idr_law Op_comp Id
}.

Implicit Arguments Op_comp [a b c0 c].

Infix "o" := (fun f g=> Op_comp g f) (at level 20, right associativity).


(* -------------------------------------------------------------------------- *)
(* 射が等しいことの定義 *)
(* Hom a bはSetoidなのでEqualによって等しいことが定義されている *)
(* Functorのequalityを定義するのにHom a bとHom c dの間の比較が必要 *)
(* TODO: f =_H g -> f == gが証明できるはずだけど、どうすればいい？ *) 

Inductive Equal_hom (C : Category) (a b : Ob C) (f : Hom a b) :
  forall c d : Ob C, (Hom c d) -> Prop :=
    Build_Equal_hom : forall g : Hom a b, f == g -> Equal_hom f g.

Hint Resolve Build_Equal_hom.

Infix "=_H" := Equal_hom (at level 70).

Section equal_hom_equiv.
   Variables (C:Category) (a b:Ob C) (f:Hom a b).
   Lemma Equal_hom_refl : f =_H f.
   Proof.
     apply Build_Equal_hom.
     exact (Prf_refl (Prf_equiv (Hom a b)) f).
   Qed.
   Variables (c d : Ob C) (g : Hom c d).
   Lemma Equal_hom_sym : f =_H g -> g =_H f.
   Proof.
     intros H;induction H.
     apply Build_Equal_hom.
     exact (Prf_sym (Prf_equiv (Hom a b)) H).
   Qed.
   Variables (a' b':Ob C) (h:Hom a' b').
   Lemma Equal_hom_trans : f =_H g -> g =_H h -> h =_H f.
   Proof.
     intros H0 H1.
     induction H0;induction H1.
     apply Build_Equal_hom.
     exact (Prf_trans (Prf_equiv (Hom a b)) H H0).
   Qed.
End equal_hom_equiv.

Hint Resolve Equal_hom_refl.
Hint Resolve Equal_hom_sym.


(* -------------------------------------------------------------------------- *)
(* Definition of Functor *)
(* FMapの型をHom a b->Hom (F a) (F b)にすると、
   f == g -> fmap F f == fmap F gがいえない 
*)

Section functor_law.
  Variable C D:Category.
  Variable (F : Ob C -> Ob D).
  Variable (FMap : forall (a b:Ob C), (Hom a b) ===> (Hom (F a) (F b))).
  Definition functor_comp_law :=
    forall (a b c:Ob C) (f:Hom a b) (g:Hom b c),
      @FMap a c (g o f) == (@FMap b c g) o (@FMap a b f).
  Definition functor_id_law :=
    forall (a:Ob C),@FMap a a (Id a) == Id (F a).
End functor_law.


Structure Functor (C D:Category) : Type := {
  ApF :> Ob C -> Ob D;
  FMap : forall (a b:Ob C),Map (Hom a b) (Hom (ApF a) (ApF b));
  Prf_fcomp_law : functor_comp_law FMap;
  Prf_fid_law : functor_id_law FMap
}.

Definition fmap (C D:Category) (F : Functor C D) (a b : Ob C) (f : Hom a b) := FMap F a b f.



Section functor_equality.
  Variable (C D:Category).
  Definition Equal_Functor (F G : Functor C D) :=
     forall (a b : Ob C) (f : Hom a  b), fmap F f =_H fmap G f.
  
  Lemma Equal_Functor_equiv : Equivalence Equal_Functor.
  Proof.
    unfold Equal_Functor;apply Build_Equivalence.
    unfold Reflexive;intros F a b f;apply Equal_hom_refl.
    unfold Transitive;intros F F' F'' H H' a b f.
    apply Equal_hom_trans with (F' a) (F' b) (fmap F' f);auto;auto.
    auto.
  Qed.
End functor_equality.

Infix "=_F" := Equal_Functor (at level 70).


Canonical Structure Functor_setoid (C D:Category) := 
     Build_Setoid (Equal_Functor_equiv C D).



(* -------------------------------------------------------------------------- *)
(* 自然変換の定義 *)

Section natural_transformation_law.
  Variables (C D:Category) (F G:Functor C D).
  Definition NT_law (T:forall (a:Ob C),Hom (F a) (G a)) :=
    forall (a b:Ob C) (f:Hom a b), (T b) o (fmap F f) == (fmap G f) o (T a).
End natural_transformation_law.


Structure NT (C D:Category) (F G:Functor C D) :Type := {
  ApNT :> forall (a:Ob C),Hom (F a) (G a);
  Prf_NT_law : NT_law ApNT
}.


Section NT_equality.
  Variables (C D:Category) (F G:Functor C D).
  Definition Equal_NT (T T' : NT F G) := forall (a:Ob C),T a == T' a.
  
  Lemma Equal_NT_equiv : Equivalence Equal_NT.
  Proof.
    unfold Equal_NT.
    apply Build_Equivalence.
    unfold Reflexive;intros T a.
    exact (Prf_refl (Prf_equiv (Hom (F a) (G a))) (T a)).
    unfold Transitive;intros T T' T'' H0 H1 a.
    exact (Prf_trans (Prf_equiv (Hom (F a) (G a))) (H0 a) (H1 a)).
    unfold Symmetric;intros T T' H a.
    exact (Prf_sym (Prf_equiv (Hom (F a) (G a))) (H a)).
  Qed.
End NT_equality.

Infix "=_NT" := Equal_NT (at level 70).


Canonical Structure NT_setoid (C D:Category) (F G:Functor C D) := 
  Build_Setoid (Equal_NT_equiv F G).


(* -------------------------------------------------------------------------- *)
(* 具体的な圏を作る準備 *)
(* 射の合成 Hom a b->Hom b c->Hom a cは簡単に作れることが多い *)
(* これから、Hom a b ===> Hom b c ===> Hom a cを作る *)
(* 具体的な圏を作るときは大体これを経由する *)

Section composition_to_operator.
  Variables (A : Type) (H : A -> A -> Setoid).
  Variable (Cfun : forall a b c : A, H a b -> H b c -> H a c).
  Definition Congl_law :=
    forall (a b c : A) (f g : H b c) (h : H a b),
      f == g -> Cfun h f == Cfun h g.
  Definition Congr_law :=
    forall (a b c : A) (f g : H a b) (h : H b c),
      f == g -> Cfun f h == Cfun g h.

  Hypothesis pcgl : Congl_law.
  Hypothesis pcgr : Congr_law.
  Variable a b c : A.

  Lemma Comp1_map_law : forall (f:H a b),(Map_law (@Cfun a b c f)).
  Proof.
    unfold Map_law;intros f g g'.
    exact (pcgl f).
  Qed.

  Definition Comp1_map (f:H a b) := Build_Map (Comp1_map_law f).
  Lemma Comp_map_law : Map_law Comp1_map.
  Proof.
    unfold Map_law.
    intros f g H'.
    unfold Comp1_map.
    simpl.
    unfold Ext.
    intro h.
    simpl.
    auto.
  Qed.
  Definition Build_Comp := Build_Map Comp_map_law.
End composition_to_operator.


(* -------------------------------------------------------------------------- *)
(* Setoidの圏SETを作る(universe inconsistency) *)

Section base_of_category_of_setoid.
  Variable (A:Setoid).
  Lemma Id_satisfies_map_law : Map_law (fun (x:A)=>x).
  Proof.
    unfold Map_law; trivial.
  Qed.
  Canonical Structure Id_map : Map A A := Build_Map Id_satisfies_map_law.

  Variables (B C : Setoid) (f:Map A B) (g:Map B C).
  Definition comp_map (x:A) := g (f x).
  Lemma comp_satisfies_map_law : Map_law comp_map.
  Proof.
    unfold Map_law;unfold comp_map.
    intros x y H.
    exact (Pres g (Pres f H)).
  Qed.
  Canonical Structure Comp_map : Map A C := Build_Map comp_satisfies_map_law.
End base_of_category_of_setoid.

Lemma Comp_map_congl : Congl_law Comp_map.
Proof.
  unfold Congl_law in |- *; simpl in |- *.
  unfold Ext in |- *; simpl in |- *.
  unfold comp_map in |- *; auto.
Qed.

Lemma Comp_map_congr : Congr_law Comp_map.
Proof.
  unfold Congr_law in |- *; simpl in |- *.
  unfold Ext in |- *; simpl in |- *.
  unfold comp_map in |- *.
  intros a b c f g h e x.
  apply Pres; auto.
Qed.

Definition Comp_SET := Build_Comp Comp_map_congl Comp_map_congr.
Definition Id_SET := Id_map.


Lemma Assoc_SET : Assoc_law Comp_SET.
Proof.
  unfold Assoc_law.
  simpl.
  unfold Ext.
  intros A B C D f g h x.
  simpl.
  apply (Prf_refl (Prf_equiv D)).
Qed.

Lemma Idl_SET : Idl_law Comp_SET Id_SET.
Proof.
  unfold Idl_law.
  intros A B f.
  unfold Comp_SET;simpl.
  unfold Comp_map;unfold Ext.
  simpl.
  intro x.
  exact (Prf_refl (Prf_equiv B) (f x)).
Qed.


Lemma Idr_SET : Idr_law Comp_SET Id_SET.
Proof.
  unfold Idr_law;intros A B f.
  unfold Comp_SET;unfold Comp_map;simpl.
  intro x;simpl.
  unfold comp_map.
  unfold Id_map;simpl.
  exact (Prf_refl (Prf_equiv A) (f x)).
Qed.

(* Error:universe inconsistency *)
(*
Canonical Structure SET := Build_Category Assoc_SET Idl_SET Idr_SET.
*)

(* -------------------------------------------------------------------------- *)
(* CoqのTypeを圏にする *)
(* 
射の集まりは、a->bだけど、これをSetoidにする方法は2つある
1)普通にLeibnitz equalityで定義する方法
2)外延性foall x, f x=g x->f=gで定義する方法

1)で定義するとprodが直積になることとか、非自明なことは殆ど何もいえない
つまらないの2)でやる 
*)

Section fun_equiv.
  Variable A B:Type.
  Definition Fun:Type := A->B.
  Definition Equal_Fun (f g:Fun) := forall (x:A),f x=g x.

  Lemma Equal_Fun_equiv : Equivalence Equal_Fun.
  Proof.
    unfold Equal_Fun;apply Build_Equivalence.
    auto.
    unfold Transitive;intros f g h H H0 x.
    exact (eq_sym  (eq_trans (H x) (H0 x))).
    unfold Symmetric;auto.
   Qed.
   Canonical Structure TypeHom : Setoid := Build_Setoid Equal_Fun_equiv.
End fun_equiv.

Definition Id_fun (A:Type) := (fun (x:A)=>x).
Definition Comp_fun (A B C:Type) (f:Fun A B) (g:Fun B C) := fun x => g (f x).

Lemma Comp_fun_congr : Congr_law Comp_fun.
Proof.
  unfold Congr_law;simpl.
  unfold Equal_Fun.
  intros a b c f g h H x.
  unfold Comp_fun;simpl.
  rewrite (H x) in |-*.
  auto.
Qed.

Lemma Comp_fun_congl : Congl_law Comp_fun.
Proof.
  unfold Congl_law;simpl.
  unfold Equal_Fun.
  intros a b c f g h H x.
  unfold Comp_fun;simpl.
  auto.
Qed.

Definition Comp_TYPE := Build_Comp Comp_fun_congl Comp_fun_congr.

Lemma Assoc_TYPE : Assoc_law Comp_TYPE.
Proof.
  unfold Assoc_law;simpl.
  unfold Equal_Fun,Comp_TYPE;simpl.
  unfold Comp_fun;simpl.
  auto.
Qed.

Lemma Idl_TYPE : Idl_law Comp_TYPE Id_fun.
Proof.
  unfold Idl_law.
  unfold Comp_TYPE,Id_fun;simpl.
  unfold Equal_Fun,Comp_fun;simpl.
  auto.
Qed.


Lemma Idr_TYPE : Idr_law Comp_TYPE Id_fun.
Proof.
  unfold Idr_law.
  unfold Comp_TYPE,Id_fun;simpl.
  unfold Equal_Fun,Comp_fun;simpl.
  auto.
Qed.

(* 後でBiCartesianCategoryとして定義する *)
(*
Canonical Structure TYPE := Build_Category Assoc_TYPE Idl_TYPE Idr_TYPE.
*)

(* -------------------------------------------------------------------------- *)
(* 関手圏 *)
(* TODO:Comp_NT_lawの証明を完成させる *)

Lemma Comp_l : forall (C:Category) (a b c:Ob C) (f g : Hom a b) (h:Hom b c), 
  f == g -> h o f == h o g.
Proof.
  intros;simpl.
  assert(H': (@Op_comp C a b c f == @Op_comp C a b c g)).
  apply Pres;auto;auto.
  auto.
Qed.

Lemma Comp_r : forall (C:Category) (a b c:Ob C) (f g : Hom b c) (h:Hom a b), 
  f == g -> f o h == g o h.
Proof.
  intros;simpl.
  apply Pres;auto.
Qed.

Section functor_category.
  Variable C D:Category.
  Section comp_nt.
    Variables (F G H:Functor C D) (T:NT F G) (T':NT G H).
    Definition comp_nt (a:Ob C) := T' a o T a.
    Lemma Comp_NT_law : NT_law comp_nt.
    Proof.
      unfold comp_nt,NT_law;simpl.
      intros a b f.
    Admitted.

    Canonical Structure Comp_NT : NT F H := Build_NT Comp_NT_law.
  End comp_nt.

  Section id_catfunct_def.
    Variable F : Functor C D.
    Definition Id_NT (a : Ob C) := Id (F a).
    Lemma Id_NT_law : NT_law Id_NT.
    Proof.
      unfold NT_law,Id_NT.
      intros a b f;simpl.
      apply (Prf_trans (Prf_equiv (Hom (F a) (F b)))) with (fmap F f).
      apply (Prf_sym (Prf_equiv (Hom (F a) (F b)))).
      apply Prf_idr.
      apply (Prf_sym (Prf_equiv (Hom (F a) (F b)))).
      apply Prf_idl.
    Qed.
    Canonical Structure Id_FUNCT := Build_NT Id_NT_law.
  End id_catfunct_def.


  Lemma Comp_NT_congr : Congr_law Comp_NT.
  Proof.
    unfold Congr_law;unfold Comp_NT;simpl.
    unfold Equal_NT;simpl.
    unfold comp_nt.
    intros F G H T T' T'' H0 a.
    apply Comp_l;auto.
  Qed.

  Lemma Comp_NT_congl : Congl_law Comp_NT.
  Proof.
    unfold Congl_law;unfold Comp_NT;simpl.
    unfold Equal_NT;simpl.
    unfold comp_nt.
    intros F G H T T' T'' H0 a.
    apply Comp_r.
    auto.
  Qed.

  Definition Comp_FUNCT := Build_Comp Comp_NT_congl Comp_NT_congr.
  Lemma Assoc_FUNCT : Assoc_law Comp_FUNCT.
  Proof.
    unfold Assoc_law;simpl.
    unfold Equal_NT.
    unfold Comp_NT;simpl.
    unfold comp_nt;simpl.
    intros.
    apply Prf_ass.
  Qed.

  Lemma Idl_FUNCT : Idl_law Comp_FUNCT Id_FUNCT.
  Proof.
    unfold Idl_law,Comp_NT,Id_FUNCT;simpl.
    unfold Equal_NT,Comp_NT;simpl;unfold comp_nt;simpl.
    unfold Id_NT.
    intros;apply Prf_idl.
  Qed.

  Lemma Idr_FUNCT : Idr_law Comp_FUNCT Id_FUNCT.
  Proof.
    unfold Idr_law,Comp_NT,Id_FUNCT;simpl.
    unfold Equal_NT,Comp_NT;simpl;unfold comp_nt;simpl.
    unfold Id_NT;intros;apply Prf_idr.
  Qed.

  Canonical Structure FUNCT := Build_Category Assoc_FUNCT Idl_FUNCT Idr_FUNCT.

End functor_category.

(* -------------------------------------------------------------------------- *)
(* 圏の圏(universe inconsistencyになる) *)

Section functor_composition.
  Variables (C D E:Category) (F:Functor C D) (G:Functor D E).
  Definition Comp_F (a:Ob C) := G (F a).
  Section functor_composition_morphism.
    Variable a b:Ob C.
    Definition Comp_fmap (f:Hom a b) := fmap G (fmap F f).

    Lemma Comp_FMap_law : Map_law Comp_fmap.
    Proof.
      unfold Map_law , Comp_fmap.
      intros f g H.
      apply Pres.
      apply Pres.
      auto.
    Qed.
    Definition Comp_FMap := Build_Map Comp_FMap_law.
  End functor_composition_morphism.

  Lemma Comp_Functor_comp_law : functor_comp_law Comp_FMap.
  Proof.
    unfold functor_comp_law , Comp_FMap;simpl.
    unfold Comp_fmap;simpl.
    intros.
    apply (Prf_trans (Prf_equiv (Hom (G (F a)) (G (F c))))) with (fmap G (fmap F g o fmap F f)).
    exact (Prf_sym (Prf_equiv (Hom (G (F a)) (G (F c)))) (Prf_fcomp_law G (fmap F f) (fmap F g))).
    apply Pres.
    apply (Prf_sym (Prf_equiv (Hom (F a) (F c)))).
    apply Prf_fcomp_law.
  Qed.
  
  Lemma Comp_Functor_id_law : functor_id_law Comp_FMap.
  Proof.
    unfold functor_id_law,Comp_FMap;simpl.
    unfold Comp_fmap.
    intro a.
    apply (Prf_trans (Prf_equiv _)) with (fmap G (Id (F a))).
    apply (Prf_sym (Prf_equiv _)).
    apply Prf_fid_law.
    apply Pres.
    apply (Prf_sym (Prf_equiv _)).
    apply Prf_fid_law.
  Qed.
  Canonical Structure Comp_Functor :=
    Build_Functor Comp_Functor_comp_law Comp_Functor_id_law.
End functor_composition.

Section idCat.
  Variable C : Category.
  Definition Id_CAT_ob (a : Ob C) := a.
  Definition Id_CAT_map (a b : Ob C) := Id_map (Hom a b).

  Lemma Id_CAT_comp_law : functor_comp_law Id_CAT_map.
  Proof.
    unfold functor_comp_law;intros.
    apply (Prf_refl (Prf_equiv _)).
  Qed.
  Lemma Id_CAT_id_law : functor_id_law Id_CAT_map.
  Proof.
    unfold functor_id_law;intros.
    apply (Prf_refl (Prf_equiv _)).
  Qed.
  Canonical Structure Id_CAT := Build_Functor Id_CAT_comp_law Id_CAT_id_law.
End idCat.


Lemma Comp_Functor_congl : Congl_law Comp_Functor.
Proof.
  unfold Congl_law,Comp_Functor.
  unfold Equal_Functor.
  unfold fmap;simpl.
  intros C D E F G H H0 a b f.
  unfold Comp_fmap;simpl.
  unfold fmap;simpl.
  apply H0.
Qed.

Lemma Comp_Functor_congr : Congr_law Comp_Functor.
Proof.
  unfold Congr_law;simpl.
  unfold Comp_Functor,Equal_Functor.
  intros C D E F G H H0 a b f.
  unfold fmap;simpl.
  unfold Comp_fmap.
  elim (H0 a b f).
  intros g H1.
  apply Build_Equal_hom.
  apply Pres.
  auto.
Qed.

Definition Comp_CAT := Build_Comp Comp_Functor_congl Comp_Functor_congr.


Lemma Assoc_CAT : Assoc_law Comp_CAT.
Proof.
  unfold Assoc_law,Comp_CAT;simpl.
  intros C D E F G H X.
  unfold Equal_Functor;simpl.
  unfold fmap;simpl.
  intros a b f.
  unfold Comp_fmap.
  unfold Comp_Functor,fmap;simpl.
  apply Build_Equal_hom.
  unfold fmap.
  apply  (Prf_refl (Prf_equiv _)).
Qed.

Lemma Idl_CAT : Idl_law Comp_CAT Id_CAT.
Proof.
   unfold Idl_law,Comp_CAT,Id_CAT.
   unfold Equal_Functor;simpl.
   unfold fmap,Comp_Functor;simpl.
   intros C D F a b f.
   unfold Comp_fmap
   unfold fmap;simpl.
   apply Build_Equal_hom.
  apply  (Prf_refl (Prf_equiv _)).
Qed.



Lemma Idr_CAT : Idr_law Comp_CAT Id_CAT.
Proof.
   unfold Idr_law,Comp_CAT,Id_CAT.
   unfold Equal_Functor;simpl.
   unfold fmap,Comp_Functor;simpl.
   intros C D F a b f.
   unfold Comp_fmap.
   unfold fmap;simpl.
   apply Build_Equal_hom.
   unfold Comp_fmap;simpl.
   unfold fmap;simpl.
   apply  (Prf_refl (Prf_equiv _)).
Qed.

(*
Canonical Structure CAT : Category :=
  Build_Category Assoc_CAT Idl_CAT Idr_CAT.
*)


(* -------------------------------------------------------------------------- *)
(* objectの同型 *)
(* Structureの方がよい? *)

Section iso_def.
  Variable (C:Category).
  Definition Iso (a b:Ob C) := 
    exists (f:Hom a b) (g:Hom b a),f o g == Id b /\ g o f== Id a.

  Lemma iso_euiv : Equivalence Iso.
  Proof.
    unfold Iso;apply Build_Equivalence.
    unfold Reflexive.
    intro x.
    exists(Id x);exists(Id x).
    split;apply Prf_idl;apply Prf_idl.
    unfold Transitive.
    intros x y z H H'.
    destruct H as [f H];destruct H as [f' H];destruct H as [H1 H2].
    destruct H' as [g H'];destruct H' as [g' H'];destruct H' as [H1' H2'].
    exists (f' o g');exists(g o f).
    split.
    apply (Prf_trans (Prf_equiv _)) with (f' o (g' o (g o f))).
    apply (Prf_trans (Prf_equiv _)) with (f' o ((g' o g) o f)).
    apply Comp_l.
    apply Prf_ass.
    apply (Prf_trans (Prf_equiv _)) with (f' o ((Id y) o f)).
    apply (Prf_trans (Prf_equiv _)) with (f' o f).
    apply Comp_l.
    apply Prf_idl.
    exact H2.
    apply Comp_l;apply Comp_r.
    apply (Prf_sym (Prf_equiv _)).
    exact H2'.
    apply Prf_ass.
    apply (Prf_trans (Prf_equiv _)) with (g o (f o (f' o g'))).
    apply (Prf_trans (Prf_equiv _)) with (g o ((f o f') o g')).
    apply Comp_l.
    apply Prf_ass.
    apply (Prf_trans (Prf_equiv _)) with (g o ((Id _) o g')).
    apply (Prf_trans (Prf_equiv _)) with (g o g').
    apply Comp_l.
    apply Prf_idl.
    exact H1'.
    apply Comp_l;apply Comp_r.
    apply (Prf_sym (Prf_equiv _)).
    exact H1.
    apply Prf_ass.
    unfold Symmetric.
    intros x y H;destruct H as [f H];destruct H as [f' H];destruct H as [H1 H2].
    exists f';exists f.
    exact (conj H2 H1).
  Qed.
End iso_def.

Infix "=_iso" := Iso (at level 70).


(* -------------------------------------------------------------------------- *)
(* 直和と直積 *)
(*
  TODO 
  1)関手圏にCartesianCategoryの構造入れる
  2)natが始代数になることとか
  3)TYPEはBiCartesianClosedCategoryになるはず
  4)ていうか、"米田の補題"の証明
  5)CartesianCartesian -> MonoidalCategoryとか
*)

Structure CartesianCategory : Type := {
  Base0 :> Category;
  product : Ob Base0 -> Ob Base0 -> Ob Base0;
  projl : forall (a a':Ob Base0),Hom (product a a') a;
  projr : forall (a a':Ob Base0),Hom (product a a') a';
  fprod : forall (a b c:Ob Base0),Hom c a -> Hom c b -> Hom c (product a b);
  unique_prod : forall (a a' b:Ob Base0) (f1:Hom b a) (f2:Hom b a') (h:Hom b (product a a')),
    f1 == (projl a a') o h -> f2 == (projr a a') o h -> h == fprod f1 f2
}.

Structure BiCartesianCategory :Type := {
  Base1 :> CartesianCategory;
  coproduct : Ob Base1 -> Ob Base1 -> Ob Base1;
  cinl : forall (a a':Ob Base1),Hom a (coproduct a a');
  cinr : forall (a a':Ob Base1),Hom a' (coproduct a a');
  fcoprod : forall (a b c:Ob Base1),Hom a c -> Hom b c -> Hom (coproduct a b) c;
  unique_coprod : forall (a a' b:Ob Base1) (f1:Hom a b) (f2:Hom a' b) (h:Hom (coproduct a a') b),
    f1 == h o (cinl a a') -> f2 == h o (cinr a a') -> h == fcoprod f1 f2
}.

Lemma pair_universality : forall (a a' b:Type) (f1:Fun b a) (f2:Fun b a') (h:Fun b (prod a a')),
  (forall x,f1 x = fst (h x)) -> (forall x,f2 x=snd (h x)) -> (forall x,h x=pair (f1 x) (f2 x)).
Proof.
  intros a a' b f1 f2 h H0 H1 x.
  rewrite H0 ,H1.
  induction (h x).
  auto.
Qed.

Definition liftSum (a a' b:Type) (f:a->b) (f':a'->b) (x:sum a a') :=
  match x with
    | inl x => f x
    | inr x => f' x
end.

Lemma sum_universality : forall (a a' b:Type) (f1:a->b) (f2:a'->b) (h:(sum a a')->b),
  (forall x,f1 x= h (inl x)) -> (forall x,f2 x=h (inr x)) ->(forall x,h x=liftSum f1 f2 x).
Proof.
  intros a a' b f1 f2 h H0 H1 x.
  unfold liftSum.
  induction x.
  auto.
  auto.
Qed.



Definition TYPE := 
  Build_BiCartesianCategory
    (Base1 := Build_CartesianCategory (Base0:=Build_Category Assoc_TYPE Idl_TYPE Idr_TYPE) pair_universality)
    sum_universality.

(* -------------------------------------------------------------------------- *)
(* initial object and terminal object *)

Section initial_terminal_def.
  Variable (C:Category).
  Structure Terminal : Type := {
    obT :> Ob C;
    bang_t : forall (x:Ob C),Hom x obT;
    unique_t : forall x (f g:Hom x obT),f == g
  }.
  Structure Initial : Type := {
    obI :> Ob C;
    bang_in : forall (x:Ob C),Hom obI x;
    unique_in : forall x (f g:Hom obI x),f == g
  }.


  Lemma initial_is_unique : forall (t t':Initial),t =_iso t'.
  Proof.
    intros t t'.
    unfold Iso.
    exists (bang_in t t');exists(bang_in t' t).
    exact (conj (unique_in _ _) (unique_in _ _)).
  Qed.

  Lemma terminal_is_unique : forall (t t':Terminal),t =_iso t'.
  Proof.
    intros t t'.
    unfold Iso.
    exists (bang_t t' t);exists(bang_t t t').
    exact (conj (unique_t _ _) (unique_t _ _) ).
  Qed.

End initial_terminal_def.

Lemma unit_type_is_terminal : forall (t:Type) (f g:t->unit), forall x,f x=g x.
Proof.
  intros t f g x.
  induction (f x).
  induction (g x).
  auto.
Qed.

Definition unitT := Build_Terminal (fun (x:Ob TYPE) (a:x)=>tt) unit_type_is_terminal.


(* 射が作れない *)
(*
Inductive empty :=.
Lemma empty_type_is_initial : forall (t:Type) (f g:empty->t),(forall x, f x=g x).
Proof.
  intros t f g x;induction x.
Qed.
*)

(* -------------------------------------------------------------------------- *)
(* epic and monic/full and faithful *)

Definition epic (C:Category) (X Y:Ob C) (f:Hom X Y) :=
  forall (Z:Ob C) (g h:Hom Y Z),g o f == h o f -> g == h.

Definition monic (C:Category) (X Y:Ob C) (f:Hom X Y) :=
  forall (Z:Ob C) (g h:Hom Z X),f o g == f o h -> g == h.

Definition full (C D:Category) (F:Functor C D) := 
  forall (X Y:Ob C) (f:Hom X Y),epic (fmap F f).

Definition faithful (C D:Category) (F:Functor C D) :=
  forall (X Y:Ob C) (f:Hom X Y),monic (fmap F f).

(* -------------------------------------------------------------------------- *)

(* 
natが以下のNatFについて始代数であることの証明(sketch)

Definition NatF (A:Type):Type := (unit+A)%type.

#nat_rect
Definition nat_reflect : forall f : nat -> Type, 
  f O -> (forall x, f x -> f (S x)) -> forall x, f x.
intros f H0 HS.
induction x.
exact H0.
exact (HS x IHx).
Defined.

#sum_rect
Definition sum_reflect : forall (A B : Type) (P : (A+B)%type -> Type),
       (forall a : A, P (inl a)) ->
       (forall b : B, P (inr b)) -> forall s : (A+B)%type, P s.
intros.
induction s.
exact (X a).
exact (X0 b).
Defined.

#NatFをFunctorにする
Definition NatFM (A B:Type) (f:A->B):NatF A->NatF B :=
  sum_reflect unit A (fun _=>(unit+B)%type) (fun _=>inl tt) (fun c=>inr (f c)).

#natにNatF代数の構造を与える射
Definition in_nat:NatF nat->nat := sum_reflect unit nat (fun _=>nat) (fun _=>0) S.

#catamorphismの構成
Definition cata_nat (X:Type) (t:NatF X->X) := 
   fun n=>nat_reflect (fun _=>X) (t (inl tt)) (fun _=>(fun c=> t (inr c))) n.


#catamorphismの一意性
Goal forall (X:Type) (t:NatF X->X) (h:nat->X) ,
  (forall (x:NatF nat),h (in_nat x)=t (NatFM nat X h x))->forall (n:nat),h n=cata_nat X t n.
Proof.
intros X t h H.
induction n.
simpl.
exact(H ((inl tt):NatF nat)).
simpl;rewrite<-IHn.
exact (H ((inr n):NatF nat)).
Qed.

*)

