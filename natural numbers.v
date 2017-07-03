Inductive N: Set:=
| javad : N
| S: N -> N.

Definition I: N:= S javad.

Definition II: N:= S I.

Definition III: N:= S II.

Fixpoint sum (m n :N):=
match n with
   | javad => m
   | S n'=> S (sum m n')
end.

Lemma ghazie1: sum I II=III.
Proof.
simpl.
trivial.
Qed.

Lemma unity: forall n:N, sum javad n=n.
Proof.
induction n.
-trivial.
-simpl. rewrite IHn. trivial.
Qed.

Lemma komaki2: forall m n:N, sum (S m) n=sum m (S n).
Proof.
induction n.
-simpl. trivial.
-simpl. rewrite IHn. reflexivity.
Qed.

Theorem comm: forall m n:N, sum m n=sum n m.
Proof.
intros.
induction m.
- simpl. apply unity.
- simpl. rewrite <- IHm. apply komaki2.
Qed.

(*Definition product(m n:N) Admitted*)

(*sdggsdfgsfdfg*)




