Require Import Utf8.
Require Import List.
Require Import Nat.
Require Import Permutation.
Require Import Bool.
Scheme Equality for list.

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
               else if n <? x then node n ct leaf
               else node x l (node n r leaf)
  end.

  Fixpoint create_cartesian_tree  (l: list nat) : cartesian_tree :=
  match l with
  | nil => leaf
  | (x::xs) => 
            match xs with
            | nil => node x leaf leaf
            | y::ys => fold_right ct_insert leaf (rev (x::y::ys))
            end
  end.

  Fixpoint ct_flatten (ct: cartesian_tree) : list nat :=
  match ct with
  | leaf => nil
  | node x l r => ct_flatten l ++ cons x nil ++ ct_flatten r
  end.

  Definition ct_merge (ct1: cartesian_tree ) (ct2: cartesian_tree) : cartesian_tree :=
  create_cartesian_tree ((ct_flatten ct1) ++ (ct_flatten ct2)).

  Definition ct_delete_min (ct : cartesian_tree) : option (nat * cartesian_tree) :=
  match ct with
  | leaf => None
  | node x l r => Some (x, ct_merge l r)
  end.

  Print Is_true.
  Print list_beq.
  Print remove.

  Fixpoint remv (n: nat) (l: list nat) : list nat :=
  match l with
  | nil => nil
  | (x::xs) => if n =? x then xs else (cons x nil )++ (remv n xs)
  end.

  Fixpoint l_eq (l1: list nat) (l2: list nat) : bool :=
  match l1, l2 with
  | nil, nil => true
  | nil, _ => false
  | _, nil => false
  | (x::xs), (y::ys) => if x =? y then l_eq xs ys else false
  end.

  Fixpoint perm (l1: list nat) (l2: list nat): bool :=
  match l1, l2 with
  | nil, nil => true
  | (x::xs), (y::ys) => if andb (l_eq (remv x (y::ys)) nil) (negb (l_eq ys nil)) then false else perm xs (remv x (y::ys))
  | _, _ => false
  end.

  Definition abs (ct: cartesian_tree) (l: list nat) : Prop :=
  match ct, l with
  | leaf, nil => True
  | node n l r, x::xs => if perm (ct_flatten ct) (x::xs) then True else False
  | _, _ => False
  end.

  Compute abs (node 3 (node 8 leaf leaf) (node 5 leaf leaf)) (5::3::8::nil).
  Compute create_cartesian_tree (8::4::6::3::5::4::nil).
  Compute ct_flatten (create_cartesian_tree (8::4::6::3::5::4::nil)).
  Compute create_cartesian_tree (8::nil).
  Compute create_cartesian_tree (8::4::nil).
  Compute ct_insert 3 (node 4 (node 8 leaf leaf) (node 6 leaf leaf)).
  Compute ct_insert 5 (node 3 (node 4 (node 8 leaf leaf) (node 6 leaf leaf)) leaf).
  Compute ct_flatten (node 3 (node 4 (node 8 leaf leaf) (node 6 leaf leaf)) (node 5 leaf leaf)).
  Compute create_cartesian_tree (8 :: 4 :: 6 :: 3 :: 5 :: nil).
  Compute ct_flatten (node 3 (node 8 leaf leaf) (node 5 leaf leaf)).
  Compute ct_delete_min (node 3 (node 4 (node 8 leaf leaf) (node 6 leaf leaf)) leaf).
  Compute ct_delete_min (node 4 (node 8 leaf leaf) (node 6 leaf leaf)).
  Compute ct_delete_min (node 3 (node 4 (node 8 leaf leaf) (node 6 leaf leaf)) (node 5 leaf leaf)).

  Theorem can_relate_ct : forall (p : cartesian_tree), exists al, abs p al.
  Proof.
    intros.
    eexists.
    instantiate (1:=(ct_flatten p)).
    unfold abs. destruct p eqn:H.
    - simpl. reflexivity.
    - simpl. Abort.

  Theorem abs_perm_ct : 
    forall (p : cartesian_tree) al bl, abs p al /\ abs p bl -> Permutation al bl.
  Proof. Admitted.

  Theorem empty_ct : ct ct_empty.
  Proof. reflexivity. Qed.

  Theorem empty_relate_ct : abs ct_empty nil.
  Proof. unfold abs. reflexivity. Qed. 

  Theorem insert_ct : forall k p, ct p -> ct (ct_insert k p).
  Proof. intros. unfold ct. reflexivity. Qed.

  Theorem insert_relate_ct :
    forall p al k, ct p -> abs p al -> abs (ct_insert k p) (k::al).
  Proof. Admitted.

  Theorem delete_min_None_relate_ct :
    forall p, ct p -> (abs p nil <-> ct_delete_min p = None).
  Proof. Admitted.

  Theorem delete_min_Some_ct :
    forall p q k, ct p → ct_delete_min p = Some(k,q) → ct q.
  Proof. intros. destruct q. 
    - reflexivity. 
    - apply H.
  Qed.

  Theorem delete_min_Some_relate_ct :
    forall (p q: cartesian_tree) k (pl ql: list nat), ct p →
       abs p pl →
       ct_delete_min p = Some (k,q) →
       abs q ql →
       Permutation pl (k::ql) ∧ Forall (le k) ql.
  Proof. Admitted.

  Theorem merge_ct : forall p q, ct p -> ct q -> ct (ct_merge p q).
  Proof. intros. reflexivity. Qed.

  Theorem merge_relate_ct :
    forall p q pl ql al,
       ct p -> ct q ->
       abs p pl -> abs q ql -> abs (ct_merge p q) al ->
       Permutation al (pl++ql).
  Proof. Admitted.

  Theorem in_order_traversal : forall (l : list nat), (l = (ct_flatten (create_cartesian_tree l))).
  Proof. intros. destruct l.
    - unfold create_cartesian_tree. simpl. reflexivity.
    - unfold create_cartesian_tree. Admitted.

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
