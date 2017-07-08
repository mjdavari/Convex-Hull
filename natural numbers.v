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
(*****************************       All   Done!       ******************)
Fixpoint mult (m n:N):=
match n with
  |zero => zero
  |S n'=> sum (mult m n') m
end.

Definition VII: N:= S (S (S III)).
(*Albatte in nemade 7 ha :D*)
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

Lemma Zero_Mult: forall a:N , mult zero a = zero.
Proof.
induction a.
-trivial.
-simpl. apply IHa.
Qed.
Lemma Helper3: forall a b :N , sum ( S a ) b = S (sum a b).
Proof.
intros.
rewrite komaki2. simpl. trivial.
Qed.
Lemma Helper2: forall a b c :N, sum (sum a b ) c = sum a (sum b c).
Proof.
intros.
induction a.
-simpl. rewrite unity. rewrite unity. trivial.
-rewrite Helper3. rewrite Helper3. rewrite Helper3. rewrite IHa. trivial.
Qed.
Lemma Helper1: forall a b:N, mult (S a) b = sum (mult a b) b.
Proof.
intros.
induction b.
-trivial.
-simpl. rewrite IHb. rewrite Helper2. 
rewrite Helper2. rewrite comm with a b. trivial.
Qed.
Lemma Jabejaei_Mult: forall a b :N, mult a b = mult b a.
Proof. 
intros.
induction a.
-simpl. apply Zero_Mult.
- simpl. rewrite <-IHa. apply Helper1.
Qed.

Lemma Associativity_Mult: forall a m n :N, mult a (sum m n) = 
sum (mult a m) (mult a n).
Proof.
intros.
induction a.
- rewrite Zero_Mult. rewrite Zero_Mult. rewrite Zero_Mult. simpl. trivial.
- rewrite Helper1. rewrite Helper1. rewrite Helper1. rewrite IHa. 
rewrite Helper2 with (mult a m) m (sum (mult a n) n). rewrite comm with m (sum (mult a n) n).
rewrite Helper2 with (mult a n) n m. rewrite comm with n m. 
rewrite Helper2 with (mult a m) (mult a n) (sum m n). trivial.
Qed.

(*proof next lemma as exercise*)
Lemma Comutativity_Mult: forall l m n:N, mult (mult l m) n=mult l (mult m n).
Proof.
intros.
simpl.
induction n.
-simpl. trivial.
-simpl. rewrite IHn. rewrite Associativity_Mult. trivial.
Qed.




