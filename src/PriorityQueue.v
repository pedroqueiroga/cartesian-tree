Require Import Utf8.
Require Import List.
Require Import Nat.
Require Import Permutation.

Module Type PRIQUEUE.
  Definition key := nat.
  Parameter  priqueue : Type.
  Parameter  empty : priqueue.
  Parameter  insert : key -> priqueue -> priqueue.
  Parameter  delete_min : priqueue -> option (key * priqueue).
  Parameter  merge : priqueue -> priqueue -> priqueue.
  Parameter  priq : priqueue -> Prop.
  Parameter  Abs : priqueue -> list key -> Prop.

  Axiom can_relate : forall p, priq p -> exists al, Abs p al.
  Axiom abs_perm : 
    forall p al bl, priq p -> Abs p al -> Abs p bl -> Permutation al bl.
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
       Permutation pl (k::ql) ∧ Forall (le k) ql.
  Axiom merge_priq : forall p q, priq p -> priq q -> priq (merge p q).
  Axiom merge_relate :
    forall p q pl ql al,
       priq p -> priq q ->
       Abs p pl -> Abs q ql -> Abs (merge p q) al ->
       Permutation al (pl++ql).

End PRIQUEUE.

Module CartesianTree <: PRIQUEUE.

  Inductive cartesian_tree : Type :=
  | leaf : cartesian_tree
  | node : nat -> cartesian_tree -> cartesian_tree -> cartesian_tree.

  Definition ct_empty : cartesian_tree := leaf.

  Definition ct  (ct: cartesian_tree) : Prop := True.

  Fixpoint ct_insert (n: nat) (ct: cartesian_tree) : cartesian_tree :=
  match ct with
  | leaf => node n leaf leaf
  | node x l r => 
               if x <? n then node x  l (ct_insert n r) 
               else if n <? x then node n (node x l r) leaf
               else node x l (node n r leaf)
  end.

  Fixpoint create_cartesian_tree  (l: list nat) : cartesian_tree :=
  match l with
  | nil => leaf
  | (x::xs) => 
            match xs with
            | nil => node x leaf leaf
            | y::ys => fold_right ct_insert leaf (y::ys)
            end
  end.

  Compute create_cartesian_tree (8 :: 4 :: 6 :: 3 :: 5 :: nil).

  Fixpoint ct_append_left (sub_ct : cartesian_tree) (ct : cartesian_tree) : cartesian_tree :=
    match ct with
    | leaf => sub_ct
    | node x l r => node x (ct_append_left sub_ct l) r
    end.

  Definition ct_delete_min (ct : cartesian_tree) : option (nat * cartesian_tree) :=
    match ct with
    | leaf => None
    | node x (node xl ll lr) (node xr rl rr) => Some (x, (node xr (ct_append_left ll rl) rr))
    | node x leaf r => Some (x, r)
    | node x l leaf => Some (x, l)
    end.

  Definition ct_merge (ct1: cartesian_tree ) (ct2: cartesian_tree) : cartesian_tree.
  Admitted.

  Fixpoint ct_flatten (ct: cartesian_tree) : list nat :=
  match ct with
  | leaf => nil
  | node x l r => ct_flatten l ++ cons x nil ++ ct_flatten r
  end.

  
  Definition abs (ct: cartesian_tree) (l: list nat) : Prop :=
  match ct, l with:
  | leaf, nil => True
  | node x l r, x::xs => Permutation (flatten ct) l
  | _, _ => False
  end.

  Theorem can_relate_ct : forall p, ct p -> exists al, abs p al.
  Proof. Admitted.

  Theorem abs_perm_ct : 
    forall p al bl, ct p -> abs p al -> abs p bl -> Permutation al bl.
  Proof. Admitted.

  Theorem empty_ct : ct ct_empty.
  Proof. reflexivity. Qed.

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
       Permutation pl (k::ql) ∧ Forall (le k) ql.
  Proof. Admitted.

  Theorem merge_ct : forall p q, ct p -> ct q -> ct (ct_merge p q).
  Proof. Admitted.

  Theorem merge_relate_ct :
    forall p q pl ql al,
       ct p -> ct q ->
       abs p pl -> abs q ql -> abs (ct_merge p q) al ->
       Permutation al (pl++ql).
  Proof. Admitted.

  Theorem in_order_traversal : forall (l : list nat), (l = (ct_flatten (create_cartesian_tree l))).
  Proof. Admitted.

  Definition key := nat.
  Definition insert := ct_insert.
  Definition priqueue := cartesian_tree.
  Definition empty := ct_empty.
  Definition delete_min := ct_delete_min.
  Definition merge := ct_merge.
  Definition priq := ct.
  Definition Abs := abs.

(*Usei o Let identifier := term
  Em: https://coq.inria.fr/refman/language/gallina-extensions.html#coq:exn.ident-already-exists-let*)

  Let can_relate := can_relate_ct.
  Let abs_perm := abs_perm_ct.
  Let empty_priq := empty_ct.
  Let empty_relate := empty_relate_ct.
  Let insert_priq := insert_ct.
  Let insert_relate := insert_relate_ct.
  Let delete_min_None_relate := delete_min_None_relate_ct.
  Let delete_min_Some_priq := delete_min_Some_ct.
  Let delete_min_Some_relate := delete_min_Some_relate_ct.
  Let merge_priq := merge_ct.
  Let merge_relate := merge_relate_ct.

End CartesianTree.
