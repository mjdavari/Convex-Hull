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
Check second.

Check (2#1,3#1).

Definition sum_point(p1 p2:Point2D):=
{| first:=  (first p1 + first p2 ); second :=  (second p1 + second p2)|}.

Check fst.

Definition sum_pair(p1 p2:Q*Q):=(fst p1 + fst p2, snd p1 + snd p2).

Structure box :=
{
p1 :Q*Q;
p2 :Q*Q;p3 :Q*Q;p4 :Q*Q;
p1p4 : fst p1 = fst p4;
p1p2 : snd p1 = snd p2;
p2p3 : fst p2 = fst p3;
p3p4 : snd p3 = snd p4;
cwp1p2 : fst p1 < fst p2;
cwp3p4 : fst p4 < fst p3;
cwp1p4 : snd p4 < snd p1;
cwp2p3 : snd p3 < snd p2;
}.

Check p1.
Check box. 

Definition point_in_box (p: Q*Q )( b :box) :=
fst p < fst (p3 b) /\ fst p > fst (p1 b)
/\ snd p < snd (p1 b) /\ snd p > snd (p3 b).

(* waybelow relation based on set inclusion*)
Definition box_waybelow (A  B : box) :=
(point_in_box (p1 B) A) /\ (point_in_box (p3 B) A). 

Lemma waybelow_point_inclusion: forall A B:box , forall p:Q*Q , 
(box_waybelow A B ) -> (point_in_box p B ) -> (point_in_box p A).
Proof.
intros.
unfold box_waybelow in *.
unfold point_in_box in *.
destruct H. destruct H. destruct H2. destruct H3.
destruct H1. destruct H5. destruct H6. destruct H0. destruct H8. destruct H9.
split. lra. 
split. lra.
split.  lra.  lra.
Qed.

Check waybelow_point_inclusion.
Lemma waybelow_trans : forall A B C : box,
box_waybelow A B -> box_waybelow B C -> box_waybelow A C.
Proof.
intros.
unfold box_waybelow .
destruct H0.
split. apply (waybelow_point_inclusion   A B (p1 C)). 
-exact H.
-exact H0.
-apply (waybelow_point_inclusion   A B (p3 C)).
  ++exact H.
  ++exact H1.
Qed.

Eval compute in (0 >= 1).
Eval compute in Qle_bool (3#5) (3#2).

Definition is_left (p q s : Q*Q):=
Qle  ((snd q - snd p) * (fst s - fst p)) ((fst q - fst p) * (snd s - snd p)) .

Definition is_right (p q s : Q*Q):=
Qle  ((fst q - fst p) * (snd s - snd p)) ((snd q - snd p) * (fst s - fst p)).

(*(Qlt_le_dec ((snd q - snd p) * (fst s - fst p)) ((fst q - fst p) * (snd s - snd p)) ).*)

Check is_left.
Check Qlt_le_dec.
Check Qle.
(*Definition length (A : Type) : list A -> Q :=
  fix length l :=
  match l with
   | nil => 0
   | _ :: l' => (length l') + 1
  end.
*)

Definition l23 : list nat
  := 2 :: 3 :: nil.

Eval compute in (nth 0 l23).

Eval compute in ((is_left (1#1,1#1) (1#1,2#1) (2#1,3#1)) \/ True).
Check length.
Check nth.
Check 0.

(* Prop for a list to being a clockwise order of some convex polygon *)
Definition is_convex_list (l : list (Q*Q))(d:Q*Q) :=
(length l > 2)%nat ->  ((forall i: nat, (i>=0/\i<=((length l)-3))%nat-> 
is_right ( nth i l d) (nth (i+1) l d) (nth (i+2) l d)) /\
is_right ( nth ((length l)-2) l d) (nth ((length l)-1) l d) (nth O l d) /\
is_right ( nth ((length l)-1) l d) (nth O l d) (nth (S O) l d)).
(* Definition is_convex_list (l : list (Q*Q))(d:Q*Q) :=
  match l with
  | nil => True
  | a :: m => ( (lt (length m)  2)) \/ ( is_convex_list m d /\
(is_left (nth ( (length m) - 2) m d) (nth 0 m d) a)) /\
(is_left a (nth 0 m d) (nth 1 m d) )  /\
(is_left (nth ((length m) - 3) m d) a (nth ((length m) - 2) m d)) 
  end. *)

Definition lpoint : list (Q*Q)
  := (0 , 0) :: (0 , 1 ) :: (1 , 1)::(1 ,0) ::  nil.
Eval compute in( length lpoint).

Eval compute in (is_convex_list lpoint (4#1,0)).

Definition point_in_convex (p: Q*Q) (l: list (Q*Q)) (d :Q*Q) :=
(is_convex_list l d)  /\ (forall i: nat, (i>=0/\i<=((length l)-2))%nat-> 
is_right ( nth i l d) (nth (i+1) l d) p)->is_right (nth ((length l)-1) l d)
(nth 0 l d) p.

Check point_in_convex.

Lemma head_is_in:forall (l:list (Q*Q)) (d:Q*Q), (is_convex_list l d )-> point_in_convex (nth 0 l d) l d.
Proof.
intros.
unfold point_in_convex.
split.





