From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** Some basic functions *)

Definition const {A B} (a : A) := fun _ : B => a.

Definition flip {A B C} (f : A -> B -> C) : B -> A -> C :=
  fun b a => f a b.

Arguments const {A B} a _ /.
Arguments flip {A B C} f b a /.


(* move to logic_exercises *)
Section IntLogic.

Variables A B C D : Prop.

Lemma axiomK :
  A -> B -> A.
Proof. exact: const. Qed.


(* note: flip is more general *)
Lemma contraposition :
  (A -> ~ B) -> (B -> ~ A).
Proof. exact: flip. Qed.


Lemma p_imp_np_iff_np : (A -> ~A)  <->  ~A.
Proof.
  split. move => a b. move: (b). exact: a b.
  exact: const.
Qed.


(* We can generalize the previous lemma into *)
Lemma p_p_q_iff_p_q : (A -> A -> B)  <->  (A -> B).
Proof.
  split. move => a b. move: (b). exact: a b.
  exact: const.
Qed.

Lemma p_is_not_equal_not_p :
  ~ (A <-> ~ A). (* (A -> ~A) /\ (~A -> A) -> False *)
Proof.
  move=> [aina naia].
  move: (aina).
  move/p_imp_np_iff_np.
  move=> na.
  move: (naia na).
  move=> aa.
  exact.
Defined.

Lemma not_not_lem : ~ ~ (A \/ ~ A).
Proof.
  move => not_lem.
  apply: (not_lem).
  right.
  move => a.
  apply: not_lem.
  by  left.
Qed.


Lemma constructiveDNE :
  ~ ~ ~ A  ->  ~ A.
Proof.
  move=> nnna aa.
  apply: (nnna).
  move=> na.
  move: aa.
  exact: na.
Qed.

End IntLogic.




(* Boolean logic (decidable fragment enjoys classical laws) *)

Section BooleanLogic.

Compute (orb).

Lemma LEM_decidable a :
  a || ~~ a.
Proof.
  case a.
  exact.
  exact.
Qed.

Lemma disj_implb a b :
  a || (a ==> b).
Proof.
  case a.
  exact.
  exact.
Qed.

Lemma iff_is_if_and_only_if a b :
  (a ==> b) && (b ==> a) = (a == b).
Proof.
  case a.
  case b.
  exact.
  exact.
  exact.
Qed.


Lemma implb_trans : transitive implb.
Proof.
  move=> y x z.
  case x.
  case y.
  exact.
  exact.
  exact.
Qed.


Lemma triple_compb (f : bool -> bool) :
  f \o f \o f =1 f.
Proof.
Admitted.


(* negb \o odd means "even" *)
Lemma even_add :
  {morph (negb \o odd) : x y / x + y >-> x == y}.
Proof.
  have: forall (n : nat), odd n = ~~ odd n.+1.
  move=> n.
  compute.
  set oddn := (fix odd (n0 : nat) : bool :=
       match n0 with
       | 0 => false
       | n'.+1 => if odd n' then false else true
       end) n.
  by case oddn.
  move=> ne_oddnnp1.

  have: forall (x y : nat), x.+1 + y = (x + y).+1. by case; case.
  move=> addSn.

  have: forall (x y : nat), x + y.+1 = (x + y).+1.
  elim. exact.
  move=> n h y.
  by rewrite addSn; rewrite addSn; rewrite h.
  move=> addnS.

  have: forall (x y : bool), x = y <-> ~~ x = ~~y. by case; case.
  move => notenot.

  have: forall (x : bool), x = ~~ ~~ x. by case.
  move => not_not.

  move=> x y.
  rewrite /funcomp.
  move: x y.
  elim.
  exact.
  move=> n h y.
  rewrite addSn.
  rewrite -ne_oddnnp1.
  rewrite notenot.
  rewrite h.
  rewrite ne_oddnnp1.
  rewrite -not_not.
  have: forall (a b : bool), (a == ~~ b) = (~~ a != ~~ b). by case; case.
  move => ne.
  by rewrite ne.
Qed.

End BooleanLogic.


(* some properties of functional composition *)

Section eq_comp.
Variables A B C D : Type.

Lemma compA (f : A -> B) (g : B -> C) (h : C -> D) :
  h \o g \o f = h \o (g \o f).
Proof.
  compute.
  exact.
Qed.

Lemma eq_compl (f g : A -> B) (h : B -> C) :
  f =1 g -> h \o f =1 h \o g.
Proof.
  compute.
  move=> eqfg x.
  rewrite eqfg.
  exact.
Qed.

Lemma eq_compr (f g : B -> C) (h : A -> B) :
  f =1 g -> f \o h =1 g \o h.
Proof.
  compute.
  move=> eqfg x.
  by rewrite eqfg.
Qed.

Lemma eq_idl (g1 g2 : A -> B) (f : B -> B) :
  f =1 id -> f \o g1 =1 f \o g2 -> g1 =1 g2.
Proof.
  compute.
  move=> eqfid eqfg x.
  move: (eqfg x).
  rewrite eqfid; by rewrite eqfid.
Qed.

Lemma eq_idr (f1 f2 : A -> B) (g : A -> A) :
  g =1 id -> f1 \o g =1 f2 \o g -> f1 =1 f2.
Proof.
  compute.
  move=> eqgid eqfg x.
  move: (eqfg x).
  by rewrite eqgid.
Qed.

End eq_comp.



