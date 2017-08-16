Require Import QArith. 
Require Import Arith.
Require Import Reals.
Require Import Psatz.
Require Import QArith.Qminmax.
Require Lra.

Require Import List.

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