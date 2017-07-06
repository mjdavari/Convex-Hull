Inductive N: Set:=
| zero : N
| S: N -> N.

Definition I: N:= S zero.

Definition II: N:= S I.

Definition III: N:= S II.

Fixpoint sum (m n :N):=
match n with
   | zero => m
   | S n'=> S (sum m n')
end.

Lemma ghazie1: sum I II=III.
Proof.
simpl.
trivial.
Qed.

Lemma unity: forall n:N, sum zero n=n.
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
(* ha ha .. gharar bud ta 5 shanbe zarbo to git bezari.. inam zarb*)


Fixpoint mult (m n:N):=
match n with
  |zero => zero
  |S n'=> sum (mult m n') m
end.

Definition VII: N:= S (S (S III)).

Lemma do_seta_shishta: mult II III=VII.
Proof. 
simpl. trivial.
Qed.

Theorem mozdavaj:forall n, mult n I=n.
Proof.
intros.
simpl.
apply unity.
Qed.

(*proof next lemma as exercise*)
Lemma sherkat: forall l m n:N, mult (mult l m) n=mult l (mult m n).




