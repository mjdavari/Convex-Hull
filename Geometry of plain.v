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

Definition sum_point(p1 p2:Point2D):=
{| first:=  (first p1 + first p2 ); second :=  (second p1 + second p2)|}.

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

Lemma head_is_in:forall (l:list (Q*Q)) (d:Q*Q), (is_convex_list l d )-> point_in_convex (nth 0 l d) l d.
Proof.
intros.
unfold point_in_convex.





