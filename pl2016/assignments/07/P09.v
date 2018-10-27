Require Export D.



(** **** Exercise: 2 stars (update_same)  *)
Theorem update_same : forall n1 x1 x2 (st : state),
  st x1 = n1 ->
  (update st x1 n1) x2 = st x2.
Proof.
  exact GIVEUP.
Qed.

