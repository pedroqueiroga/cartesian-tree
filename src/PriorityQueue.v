Module Type PRIQUEUE.
  Definition key := nat.
  Parameter priqueue: Type.
  Parameter permutation: list key  -> list key  -> Prop.
  Parameter empty : priqueue.
  Parameter insert: key -> priqueue -> priqueue.
  Parameter delete_min: priqueue -> option (key * priqueue).
  Parameter merge: priqueue -> priqueue -> priqueue.
  Parameter priq: priqueue -> Prop.
  Parameter Abs: priqueue -> list key -> Prop.

  Axiom can_relate: forall p, priq p -> exists al, Abs p al.
  Axiom abs_perm: forall p al bl,
   priq p -> Abs p al -> Abs p bl -> permutation al bl.
  Axiom empty_priq: priq empty.
  Axiom empty_relate: Abs empty nil.
  Axiom insert_priq: forall k p, priq p -> priq (insert k p).
  Axiom insert_relate:
        forall p al k, priq p -> Abs p al -> Abs (insert k p) (k::al).
  Axiom delete_min_None_relate:
        forall p, priq p -> (Abs p nil <-> delete_min p = None).
  Axiom merge_priq: forall p q, priq p -> priq q -> priq (merge p q).
  Axiom merge_relate:
    forall p q pl ql al,
       priq p -> priq q ->
       Abs p pl -> Abs q ql -> Abs (merge p q) al ->
       permutation al (pl++ql).

End PRIQUEUE.

Require Import List.

Module CartesianTree <: PRIQUEUE.
  
  Definition key := nat.
  Definition insert:= ct_insert.
  Definition priqueue: .
  Definition permutation: .
  Definition empty : .

  Definition delete_min: .
  Definition merge: .
  Definition priq: .
  Definition Abs: .

  Inductive tree : Type :=
  | leaf : tree
  | node : nat -> tree -> tree -> tree.

  Definition create_cartesian_tree : list nat -> tree.
  Admitted.

  Definition ct_insert : nat -> tree -> tree.
  Admitted.

  Definition delete_min : tree -> tree.
  Admitted.

  Definition merge : tree -> tree -> tree.
  Admitted.

  Definition empty : tree := leaf.
  Admitted.

  Definition flatten : tree -> list nat.
  Admitted.

  Theorem in_order_traversal : forall (l : list nat), (l = (flatten (create_cartesian_tree l))).
  Proof. Admitted.

End CartesianTree.