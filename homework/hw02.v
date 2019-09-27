From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Section IntLogic.

Variables A B C : Prop.

Lemma notTrue_iff_False : (~ True) <-> False.
Proof.
 split.
 - rewrite /not. move=> nt. exact: (nt I).
 - rewrite /not. move=> f _. exact.
Qed.

Lemma dne_False : ~ ~ False -> False.
Proof.
  rewrite /not.
  move=> nnf.
  by apply: nnf.
Qed.

Lemma dne_True : ~ ~ True -> True.
Proof.
  by move=> _.
Qed.

Lemma weak_peirce : ((((A -> B) -> A) -> A) -> B) -> B.
Proof.
  move=> aibiaiaib.
  apply: (aibiaiaib).
  apply.
  move=> a.
  exact: aibiaiaib.
Qed.

Lemma imp_trans : (A -> B) -> (B -> C) -> (A -> C).
Proof.
  move=> aib bic.
  exact (bic \o aib).
Qed.

End IntLogic.


(** Let's get familiarize ourselves with some lemmas from [ssrbool] module.
    The proofs are very easy, so the lemma statements are more important here.
 *)
Section BooleanLogic.

Variables (A B : Type) (x : A) (f : A -> B) (a b : bool) (vT vF : A).

Lemma negbNE : ~~ ~~ b -> b.
Proof.
  by case b.
Qed.

(** Figure out what [involutive] and [injective] mean
    using Coq's interactive queries. Prove the lemmas.
    Hint: to unfold a definition in the goal use [rewrite /definition] command.
*)
Lemma negbK : involutive negb.
Proof.
  rewrite /involutive. rewrite /cancel.
  move=> x0. by case x0.
Qed.

Lemma negb_inj : injective negb.
Proof.
  rewrite /injective.
  by case; case.
Qed.

Lemma ifT : b -> (if b then vT else vF) = vT.
Proof.
  by move=> bt; rewrite bt.
Qed.

Lemma ifF : b = false -> (if b then vT else vF) = vF.
Proof.
  by move=> bf; rewrite bf.
Qed.

Lemma if_same : (if b then vT else vT) = vT.
Proof.
  by case b.
Qed.

Lemma if_neg : (if ~~ b then vT else vF) = if b then vF else vT.
Proof.
  by case b.
Qed.

Lemma fun_if : f (if b then vT else vF) = if b then f vT else f vF.
Proof.
  by case b.
Qed.

Lemma if_arg (fT fF : A -> B) :
  (if b then fT else fF) x = if b then fT x else fF x.
Proof.
  by case b.
Qed.

Lemma andbK : a && b || a = a.
Proof.
  by case a; case b.
Qed.

(** Find out what [left_id], [right_id] mean
    using Coq's interactive queries. Prove the lemmas.
 *)
Lemma addFb : left_id false addb.    (* [addb] means XOR (eXclusive OR operation) *)
Proof.
  rewrite /left_id.
  by case.
Qed.

Lemma addbF : right_id false addb.
Proof.
  rewrite /right_id.
  by case.
Qed.

Lemma addbC : commutative addb.
Proof.
  rewrite /commutative.
  by case; case.
Qed.

Lemma addbA : associative addb.
Proof.
  rewrite /associative.
  by case; case; case.
Qed.


(** Formulate analogous laws (left/right identity, commutativity, associativity)
    for boolean AND and OR and proove those.
    Find the names of corresponding lemmas in the standard library using
    [Search] command. For instance: [Search _ andb left_id.]
    Have you noticed the naming patterns?
 *)
Lemma andTb : left_id true andb.
Proof.
  rewrite /left_id.
  by move=> x0.
Qed.

Lemma andbT : right_id true andb.
Proof.
  rewrite /right_id.
  by case.
Qed.

Lemma andbC : commutative andb.
Proof.
  rewrite /commutative.
  by case; case.
Qed.

Lemma andbA : associative andb.
Proof.
  rewrite /associative.
  by case.
Qed.

End BooleanLogic.



Section NaturalNumbers.
(** Figure out what [cancel], [succn], [predn] mean
    using Coq's interactive queries. Prove the lemmas.
 *)
Lemma succnK : cancel succn predn.
Proof.
  rewrite /cancel.
  case.
  exact.
  by rewrite /cancel; case.
Qed.

Lemma add0n : left_id 0 addn.
Proof.
  by rewrite /left_id; case.
Qed.

Lemma addSn m n : m.+1 + n = (m + n).+1.
Proof.
  by case m; case n.
Qed.

Lemma add1n n : 1 + n = n.+1.
Proof.
  by case n.
Qed.

Lemma add2n m : 2 + m = m.+2.
Proof.
  by case m.
Qed.

Lemma subn0 : right_id 0 subn.
Proof.
  by rewrite /right_id; case.
Qed.

End NaturalNumbers.
