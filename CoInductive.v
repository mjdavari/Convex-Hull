Set Implicit Arguments.
Require Setoid.
Require Import List.

CoInductive Stream (A: Type) :Type :=
| Cons : A->Stream A->Stream A.

CoInductive LList(A:Type):Type:=
|LNil: LList A
|LCons : A -> LList A -> LList A.

Definition head(A:Type) (s : Stream A) :=
match s with
|Cons a s' => a 
end.

Definition tail(A:Type) (s : Stream A) :=
match s with
|Cons a s' => s' 
end.

CoFixpoint zeroes : Stream nat := Cons 0 zeroes.

CoFixpoint repeat (A:Type)(a:A) : Stream A :=
Cons a (repeat a).

Lemma head_constant: forall (A:Set)(a:A),
head (repeat a)=a.
Proof.
intros.
simpl in *.
trivial.
Qed.

CoFixpoint iterate (A:Set)(f:A -> A)
(a:A):Stream A
:= Cons a (iterate f (f a)).

Lemma head_tail: forall (A:Set)(a:A)
(f:A->A),head (tail (iterate f a))=f a.
Proof.
intros.
simpl in *.
reflexivity.
Qed.

CoFixpoint true_false:Stream bool:=
Cons true til with
til:Stream bool:=Cons false true_false.

CoFixpoint zero_one:Stream nat:=
Cons 0 t with
t:Stream nat:= Cons 0 u with
u:Stream nat:=Cons 1 zero_one.

Fixpoint nth_stream
(A:Set)(n:nat)(s:Stream A):A:=
match n with
  |0=> head s
  |S n'=> nth_stream n' (tail s)
end.

(*Variable A:Set.
Variable f:A->A.
Variable a:A.
Eval compute in 
(nth_stream 5 (iterate f a)).
*)

Fixpoint approx (A:Set) (s : Stream A)(n : nat):
list A:=
match n with
   |O => nil
   |S n' => 
        match s with
           |Cons h t=> h :: approx t n'
           end
end.

(*
Eval compute in (approx (iterate f (f (f a))) 4).
Check map. 
*)

CoFixpoint map_stream (A B:Set)(f:A->B)(s:Stream A):Stream  B:=
match s with
|Cons h t => Cons (f h) (map_stream f t)
end.



Check cons.

Theorem cons_injective : 
  forall (A : Set)(a: A)(l m : list A),
    a :: l = a :: m <-> l = m.
Proof.
split.
-
intros.
fold (tl (cons a l)).
rewrite H.
unfold tl.
reflexivity.
- intros. rewrite H. reflexivity.
Qed.

Check cons_injective.

Lemma a_out:forall (A:Set)(a:A)(s:Stream A)(n:nat),
approx (Cons a s) (S n)=a :: approx s n.
Proof.
intros.
simpl in *.
reflexivity.
Qed. 

Lemma help_1:forall (A:Set)(s:Stream A)(n:nat),
approx s (S n)=(head s)::(approx (tail s) n).
Proof.
intros.
destruct s. rewrite a_out. simpl in *.
apply cons_injective. trivial.
Qed.

Lemma map_stream_works: forall (n:nat)(A B:Set)(f:A->B) (s: Stream A), 
approx (map_stream f s) n = map f (approx s n).
Proof.
intros.
induction n.
- simpl in *. auto.
- rewrite help_1. 
admit.









