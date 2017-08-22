Require Import QArith. 
Require Import Arith.
Require Import Reals.
Require Import Psatz.
Require Import QArith.Qminmax.
Require Lra.

Require Import List.

Structure Point2D := {
first:> Q;
second:> Q;
}.

Definition sum_point(p1 p2:Q*Q):=
 (fst p1 + fst p2  ,snd p1 + snd p2).

Definition sum_pair(p1 p2:Q*Q):=(fst p1 + fst p2, snd p1 + snd p2).

Definition is_left (p q s : Q*Q):=
Qle  ((snd q - snd p) * (fst s - fst p)) ((fst q - fst p) * (snd s - snd p)) .

Definition is_right (p q s : Q*Q):=
Qle  ((fst q - fst p) * (snd s - snd p)) ((snd q - snd p) * (fst s - fst p)).

(* Prop for a list to being a clockwise order of some convex polygon *)
Definition is_convex_list (l : list (Q*Q))(d:Q*Q) :=
(length l > 2)%nat ->  ((forall i: nat, (i>=0/\i<=((length l)-3))%nat-> 
is_right ( nth i l d) (nth (i+1) l d) (nth (i+2) l d)) /\
is_right ( nth ((length l)-2) l d) (nth ((length l)-1) l d) (nth O l d) /\
is_right ( nth ((length l)-1) l d) (nth O l d) (nth (S O) l d)).

Definition point_in_convex (p: Q*Q) (l: list (Q*Q)) (d :Q*Q) :=
(is_convex_list l d)  /\ (forall i: nat, (i>=0/\i<=((length l)-2))%nat-> 
is_right ( nth i l d) (nth (i+1) l d) p)->is_right (nth ((length l)-1) l d)
(nth 0 l d) p.

Definition is_in_right_b (p q s : Q*Q):= 
Qle_bool  ((fst q - fst p) * (snd s - snd p)) ((snd q - snd p) * (fst s - fst p)).

Structure convex_set := {
pts :> list (Q*Q);
count :> nat;
}.

Definition scale_point (a:Q)(p:Q*Q) :=
 (a * (fst p) ,  a * (snd p)) .
Fixpoint sum_list(l:list Q) :=
match l with
| nil => 0
| a::l' => (a + sum_list l')
end.

Fixpoint inner_prod_list (l : list Q)( pt : list (Q*Q)):=
match l , pt with
| nil, nil => (0,0)
| a::l' , nil => (0,0)
| nil , p :: pt' => (0,0)
| a::l' , p :: pt' => sum_point (scale_point a p) (inner_prod_list l' pt')
end.

Definition convex_set_membership (c: convex_set) (p :Q*Q) :=
exists lmb: (list Q), (sum_list lmb = 1) /\ (inner_prod_list lmb (pts c)=p).

Fixpoint replace_in_list (i :nat)(l : list Q)(b : Q):=
match i,l with
| O , nil => nil
| O ,  _::l' => b :: l'
| S i' , nil =>  nil
| S i' , a::l' => a :: (replace_in_list i' l' b)
end.

Fixpoint zero_list (i :nat):=
match i with
|O => nil
|S i' => 0::zero_list i'
end.

Fixpoint find_in_list (p:Q*Q) (l : list (Q*Q)) (i:nat) :=
match l with
|nil => S i
| a :: l' =>
if (Qeq_bool (fst a) (fst p) && Qeq_bool (snd a)  (snd p))
 then i else find_in_list p l' (i+1)
end.

(* Lemma Qadd_comm: forall (x y : Q) , x+y = y+x.
Proof.
intros. . *)

Lemma list_sum_replace : forall (n i:nat)(l:list Q) (t:Q), (lt i (length l))
 -> sum_list (replace_in_list i l t) + (nth i l 0) == t + sum_list l.
Proof.
 intros.
induction l.
- simpl in *. lia.
- simpl in H. induction i.
    + rewrite <- Nat.add_1_r in H. simpl in *. lra . 
    + simpl. apply lt_S_n in H. 
      apply  Nat.lt_lt_succ_r in H. 
      assert ( ((i < length l)%nat ->
       sum_list (replace_in_list i l t) + nth i l 0 == t + sum_list l) ->
      sum_list (replace_in_list i (a :: l) t) + nth i (a :: l) 0 ==
      t + sum_list (a :: l)).
        -- auto.
        -- assert(( sum_list (replace_in_list i l t) + nth i l 0 == t + sum_list l) ->
     sum_list (replace_in_list i (a :: l) t) + nth i (a :: l) 0 ==
     t + sum_list (a :: l)).
            ++ auto.
            ++ simpl. dmit.

      Search lt.
      Nat.lt_succ_r
        


Lemma points_in_convex_set: forall (p: Q*Q)(c : convex_set),
(In p (pts c)) ->  convex_set_membership c p.
Proof.
intros.
unfold convex_set_membership.
remember (pts c) as pt.
remember (replace_in_list (find_in_list p (pts c) 0) (zero_list (length (pts c))) 1) as lmb'.
exists lmb'. split.
- induction pt.
    + simpl in *. elim H.
    + simpl in *. elim H.
        -- intro. remember (length c) as lc. remember (find_in_list p c 0) as ind.
           remember (zero_list lc) as zl. admit.
        -- intro. admit.
- admit.

Definition insert_to_convex_list (p : Q*Q) (l : list (Q*Q)):=
match l with
| nil => p::nil
| a0::l' => match l' with
        | nil => p::a0::nil
        | a1::l'' => if  is_in_right_b a0 a1 p
                      then n::ms
                      else m::(insert n ms')
  end
end.

Fixpoint convex_hull (l: list (Q*Q)):=
match l with
| nill => l
|a :: l' => insert_to_convex_list (a convex_hull l')
end.




Section stream.
  Variable A : Type.

  CoInductive stream : Type :=
  | Cons : A -> stream -> stream.
End stream.


Section stream_eq.
  Variable A : Type.
  CoInductive stream_eq : stream A -> stream A -> Prop :=
  | Stream_eq : forall h t1 t2,
    stream_eq t1 t2
    -> stream_eq (Cons h t1) (Cons h t2).
End stream_eq.


CoInductive stream_equality : list Q -> list Q -> Prop.
stream_equality: forall h t1 t2 , stream_equality t1 t2 -> 
stream_equality (h :: t1) (h :: t2).






