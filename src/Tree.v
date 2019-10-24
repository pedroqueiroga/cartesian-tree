Inductive tree : Type :=
| leaf : tree
| node : nat -> tree -> tree -> tree.

Definition create_cartesian_tree : list nat -> tree.
Admitted.

Definition insert : nat -> tree -> tree.
Admitted.

Definition delete_min : tree -> tree.
Admitted.

Definition merge : tree -> tree -> tree.
Admitted.

Definition empty : tree := leaf.
