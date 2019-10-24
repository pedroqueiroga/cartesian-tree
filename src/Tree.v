Inductive tree : Type :=
| leaf : tree
| node : nat -> tree -> tree -> tree.

Compute (node 1 leaf leaf).

Compute (node 1 (node 2 leaf leaf) leaf).
