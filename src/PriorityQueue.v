Require Import Utf8.
Require Import List.
Require Import Nat.

Module Type PRIQUEUE.
  Definition key := nat.
  Parameter  priqueue : Type.
  Parameter  permutation : list key  -> list key  -> Prop.
  Parameter  empty : priqueue.
  Parameter  insert : key -> priqueue -> priqueue.
  Parameter  delete_min : priqueue -> option (key * priqueue).
  Parameter  merge : priqueue -> priqueue -> priqueue.
  Parameter  priq : priqueue -> Prop.
  Parameter  Abs : priqueue -> list key -> Prop.

  Axiom can_relate : forall p, priq p -> exists al, Abs p al.
  Axiom abs_perm : 
    forall p al bl, priq p -> Abs p al -> Abs p bl -> permutation al bl.
  Axiom empty_priq : priq empty.
  Axiom empty_relate : Abs empty nil.
  Axiom insert_priq : forall k p, priq p -> priq (insert k p).
  Axiom insert_relate :
    forall p al k, priq p -> Abs p al -> Abs (insert k p) (k::al).
  Axiom delete_min_None_relate :
    forall p, priq p -> (Abs p nil <-> delete_min p = None).
  Axiom delete_min_Some_priq :
    forall p q k, priq p → delete_min p = Some(k,q) → priq q.
  Axiom delete_min_Some_relate :
    forall (p q: priqueue) k (pl ql: list key), priq p →
       Abs p pl →
       delete_min p = Some (k,q) →
       Abs q ql →
       permutation pl (k::ql) ∧ Forall (le k) ql.
  Axiom merge_priq : forall p q, priq p -> priq q -> priq (merge p q).
  Axiom merge_relate :
    forall p q pl ql al,
       priq p -> priq q ->
       Abs p pl -> Abs q ql -> Abs (merge p q) al ->
       permutation al (pl++ql).

End PRIQUEUE.

Module CartesianTree <: PRIQUEUE.

  Inductive cartesian_tree : Type :=
  | leaf : cartesian_tree
  | node : nat -> cartesian_tree -> cartesian_tree -> cartesian_tree.

  Definition ct_empty : cartesian_tree := leaf.

  Definition ct : cartesian_tree -> Prop.
  Admitted.

  Definition abs : cartesian_tree -> list nat -> Prop.
  Admitted.

  Definition perm : list nat -> list nat -> Prop.
  Admitted.

  Definition create_cartesian_tree : list nat -> cartesian_tree.
  Admitted.

  Definition ct_insert : nat -> cartesian_tree -> cartesian_tree.
  Admitted.

  Definition ct_delete_min : cartesian_tree -> option (nat * cartesian_tree).
  Admitted.

  Definition ct_merge : cartesian_tree -> cartesian_tree -> cartesian_tree.
  Admitted.

  Definition ct_flatten : cartesian_tree -> list nat.
  Admitted.


  Theorem can_relate_ct : forall p, ct p -> exists al, abs p al.
  Proof. Admitted.

  Theorem abs_perm_ct : 
    forall p al bl, ct p -> abs p al -> abs p bl -> perm al bl.
  Proof. Admitted.

  Theorem empty_ct : ct ct_empty.
  Proof. Admitted.

  Theorem empty_relate_ct : abs ct_empty nil.
  Proof. Admitted.

  Theorem insert_ct : forall k p, ct p -> ct (ct_insert k p).
  Proof. Admitted.

  Theorem insert_relate_ct :
    forall p al k, ct p -> abs p al -> abs (ct_insert k p) (k::al).
  Proof. Admitted.

  Theorem delete_min_None_relate_ct :
    forall p, ct p -> (abs p nil <-> ct_delete_min p = None).
  Proof. Admitted.

  Theorem delete_min_Some_ct :
    forall p q k, ct p → ct_delete_min p = Some(k,q) → ct q.
  Proof. Admitted.

  Theorem delete_min_Some_relate_ct :
    forall (p q: cartesian_tree) k (pl ql: list nat), ct p →
       abs p pl →
       ct_delete_min p = Some (k,q) →
       abs q ql →
       perm pl (k::ql) ∧ Forall (le k) ql.
  Proof. Admitted.

  Theorem merge_ct : forall p q, ct p -> ct q -> ct (ct_merge p q).
  Proof. Admitted.

  Theorem merge_relate_ct :
    forall p q pl ql al,
       ct p -> ct q ->
       abs p pl -> abs q ql -> abs (ct_merge p q) al ->
       perm al (pl++ql).
  Proof. Admitted.

  Theorem in_order_traversal : forall (l : list nat), (l = (ct_flatten (create_cartesian_tree l))).
  Proof. Admitted.

  Definition key := nat.
  Definition insert := ct_insert.
  Definition priqueue := cartesian_tree.
  Definition permutation := perm.
  Definition empty := ct_empty.
  Definition delete_min := ct_delete_min.
  Definition merge := ct_merge.
  Definition priq := ct.
  Definition Abs := abs.

(*Essa parte ainda está com erro, vou ler o artigo sobre ModuleSystem para ver
  como fazer a correlação entre os Axiom e os Lemma
  Artigo em: https://github.com/coq/coq/wiki/ModuleSystemTutorial*)

  Lemma can_relate : can_relate_ct.
  Lemma abs_perm : abs_perm_ct.
  Lemma empty_priq : empty_ct.
  Lemma empty_relate : empty_relate_ct.
  Lemma insert_priq : insert_ct.
  Lemma insert_relate : insert_relate_ct.
  Lemma delete_min_None_relate : delete_min_None_relate_ct.
  Lemma delete_min_Some_priq : delete_min_Some_ct.
  Lemma delete_min_Some_relate : delete_min_Some_relate_ct.
  Lemma merge_priq : merge_ct.
  Lemma merge_relate : merge_relate_ct.

End CartesianTree.