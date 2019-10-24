Module Type PRIQUEUE.
  Definition key := nat.
  Parameter perm: list key -> list key -> Prop.
  Parameter priqueue: Type.
  Parameter permutation: list key  -> list key  -> Prop.

  Parameter empty : priqueue.
  Parameter insert: key -> priqueue -> priqueue.
  Parameter delete_min: priqueue -> option (key * priqueue).
  Parameter merge: priqueue -> priqueue -> priqueue. 
  
  Parameter exist: priqueue -> Prop.
  Parameter len: priqueue -> list key -> Prop.
  Axiom can_relate: forall p, exist p -> exists al, len p al.
  Axiom abs_perm: forall p al bl,
   exist p -> len p al -> len p bl -> permutation al bl.
  Axiom empty_priq: exist empty.
  Axiom empty_relate: len empty nil.
  Axiom insert_priq: forall k p, exist p -> exist (insert k p).
  Axiom insert_relate:
        forall p al k, exist p -> len p al -> len (insert k p) (k::al).
  Axiom delete_min_None_relate:
        forall p, exist p -> (len p nil <-> delete_min p = None).
  Axiom merge_priq: forall p q, exist p -> exist q -> exist (merge p q).
  Axiom merge_relate:
    forall p q pl ql al,
       exist p -> exist q ->
       len p pl -> len q ql -> len (merge p q) al ->
       permutation al (pl++ql).

End PRIQUEUE.