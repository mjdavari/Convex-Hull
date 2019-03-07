Add LoadPath "C:\Users\javad\Desktop\PhD\coq\GitProject\Convex Hull".
Require Import QArith. 
Require Import Psatz.
Require Import QArith.Qminmax.
Require Import Coq.Arith.PeanoNat.
Require Import Coq.Logic.Classical_Prop.
Require Import Bool Basics OrdersTac Minus.
Require Import Coq.ZArith.BinInt.

Require Import Wellfounded.

Require Lra.
Require Omega.
Require Ring.
Require Import Knuth.
Load PointSort.

Axiom Point2D_dec:forall (pt1 pt2 :Point2D), {pt1 = pt2 } + {pt1 <> pt2}.
Axiom Point2D_eq_eq: forall (pt1 pt2 :Point2D)(ls:list Point2D),
        well_formed_list ls -> is_in_list ls pt1 /\ is_in_list ls pt2 ->
         eq_nat pt1 pt2 -> pt1 = pt2.

Lemma ccw_dec :forall (p q r : Point2D) , {is_ccw p q r} +  {~ is_ccw p q r}.
Proof. intros. unfold is_ccw in *. remember (order_det p q r) as qval.
clear Heqqval. assert(H:=Q_dec qval 0). destruct H.
- destruct s.
  + right. lra.
  + tauto.
- right. lra.

Qed. 

(*====================== ConvexHull Prop =========================*)
(*================================================================*)

Definition Is_Convex (ls : list Point2D) : Prop := 
well_formed_list ls  /\ forall (pt1 pt3:Point2D), 
is_in_list ls pt1  /\ is_in_list ls (next_in_list ls pt1) /\ is_in_list ls pt3 
-> ~ is_ccw pt1 (next_in_list ls pt1) pt3.


Fixpoint is_in_right_S1 ( pre1 pre2 : Point2D)(ls:list Point2D)(pt : Point2D) :=
match ls with
| [] => ~is_ccw pre1 pre2 pt
| pt1 :: ls' => ~is_ccw pre1 pre2 pt /\ is_in_right_S1 pre1 pt1 ls' pt
end.

Fixpoint is_in_right_list (ls : list Point2D) (pt : Point2D) :=
match ls with 
| [] => True
| pt1 :: ls' => match ls' with 
                | [] => True
                | pt2 :: ls'' =>  is_in_right_S1 pt1 pt2 ls pt
                end
end.
Definition Is_non_colinear (ls : list Point2D) : Prop :=
forall (p1 p2 p3 :Point2D) , ~p1=p2 /\ ~p2=p3 /\ ~p3=p1 /\ is_in_list ls p1 /\
                             is_in_list ls p2 /\ is_in_list ls p3 ->
                           ~is_colinear p1 p2 p3.

Lemma next_in_list_simpl: forall (ls:list Point2D) (p a p1 : Point2D) ,
~eq_nat p1 a /\ ~eq_nat p p1 -> next_in_list (p:: a :: ls) p1 = next_in_list (p::ls) p1 .
Proof.
intros.
simpl. case(eq_nat_decide p p6). intros. tauto.
intros. case(eq_nat_decide a p6). intros. apply eq_nat_eq in e.
symmetry in e. apply eq_eq_nat in e. tauto. intros. tauto.
Qed.

Lemma next_in_list_eq: forall(ls:list Point2D) (p a : Point2D) ,
well_formed_list ls /\ is_in_list ls p /\ is_in_list ls a -> 
next_in_list ls p = next_in_list ls a -> eq_nat p a.
Proof.
intros. destruct H. destruct H1. induction ls.
- tauto.
- simpl in H1. simpl in H2.
  destruct H1. destruct H2. rewrite <- H1 in H2. symmetry in H2.
  apply eq_eq_nat. tauto.
 
  destruct ls. tauto. assert (eq_a_a0:=eq_nat_dec a0  a).
  case (eq_a_a0). intro. rewrite e in H1. rewrite H1.
  apply eq_nat_refl.

 intro. clear eq_a_a0.
 remember (next_in_list (a0 :: p0 :: ls) a) as nexa.
   assert(next_in_list (a0 :: p0 :: ls) p = p0).
  simpl.  case(eq_nat_decide a0 p). tauto. intro. elim n0.
  symmetry in H1. apply eq_eq_nat in H1. tauto. rewrite H3 in H0.
   rewrite H0 in H. pose(next_in_list_remove). specialize o with (p0::ls) a0 a.
    assert(a0_neq_a:=n).
    apply o in n; clear o. destruct n.
  clear IHls.

 induction ls. simpl in H2.  destruct H2. simpl in Heqnexa.
  case(eq_nat_decide a0 a) in *. apply eq_nat_eq in e. tauto.
  case(eq_nat_decide p0 a) in *. rewrite Heqnexa in H. simpl in H.
  tauto. rewrite H2 in n0. elim n0.
  apply eq_nat_refl. tauto.
   destruct ls. clear IHls. simpl in H2. destruct H2. simpl in Heqnexa.
  case(eq_nat_decide a0 a) in *. apply eq_nat_eq in e. tauto.
  case(eq_nat_decide p0 a) in *. rewrite Heqnexa in H.
  simpl in H. tauto. rewrite H2 in n0. elim n0. apply eq_nat_refl.
  destruct H2. simpl in Heqnexa. case(eq_nat_decide a0 a) in *.
  apply eq_nat_eq in e. tauto. case(eq_nat_decide p0 a) in *.
  rewrite Heqnexa in H. simpl in H. tauto. case(eq_nat_decide a1 a) in *. 
  rewrite Heqnexa in H. simpl in H. tauto. rewrite H2 in n1. elim n1.
  apply eq_nat_refl. tauto.

 assert (id a1 <> id a). intro. simpl in Heqnexa.
  case(eq_nat_decide a0 a) in *. apply eq_nat_eq in e. tauto.
  case(eq_nat_decide p0 a) in *. rewrite Heqnexa in H. simpl in H. tauto.
  case(eq_nat_decide a1 a) in *. rewrite Heqnexa in H. simpl in H. tauto.
  rewrite H5 in n1. elim n1. apply eq_nat_refl.

 assert(id a <> id a0). intro. symmetry in H6. tauto.
  assert( well_formed_list (a0 :: nexa :: p6 :: ls)). simpl in H. simpl. tauto.
 pose proof(IHls H7);clear IHls. assert(is_in_list (p0 :: p6 :: ls) a).
  simpl. simpl in H2. destruct H2. tauto. destruct H2.
  symmetry in H2. tauto. tauto.

  pose proof(H8 H9);clear H8. assert(nexa = next_in_list (a0 :: p0 :: p6 :: ls) a).
  simpl. simpl in Heqnexa.
  case(eq_nat_decide a0 a) in *. tauto. case( eq_nat_decide p0 a) in *. 
  rewrite Heqnexa in H.  simpl in H. tauto. case(eq_nat_decide p6 a) in *.
  case(eq_nat_decide a1 a) in *. rewrite Heqnexa in H. simpl in H. tauto.
  tauto.
  case(eq_nat_decide a1 a) in *. rewrite Heqnexa in H. simpl in H. tauto.
  tauto. pose proof(H10 H8); clear H10. assert( next_in_list (a0 :: p0 :: p6 :: ls) p = p0).
   simpl. simpl in H3. case(eq_nat_decide a0 p) in *. tauto.
  case(eq_nat_decide p0 p) in *. rewrite H3 in H. rewrite H0 in H.
  simpl in H. tauto.  case(eq_nat_decide p6 p) in *. case(eq_nat_decide a1 p) in *.
  rewrite H3 in H. rewrite H0 in H. simpl in H. tauto. tauto.
  case(eq_nat_decide a1 p) in *. rewrite H3 in H. rewrite <- H0 in H.
  simpl in H. tauto. tauto. 
  apply H11. pose( next_in_list_remove). specialize o with ( p0 :: p6 :: ls) a0 a.
  
assert(id a0 <> id a). intro. symmetry in H12. tauto. 
  pose proof(o H12); clear o. assert(is_in_list ( p0 :: p6 :: ls) a ).
 simpl. simpl in H2. tauto. pose proof(H13 H14);clear H14.
  destruct H15. tauto. rewrite H14 in *. rewrite H8 in H. 
  simpl in H. tauto. rewrite H4 in *. rewrite Heqnexa in H. simpl in H. tauto.
  simpl in H2. destruct H2. rewrite H4 in Heqnexa. rewrite Heqnexa in H.
  simpl in H. tauto.
   rewrite H4 in Heqnexa. rewrite Heqnexa in H.
  simpl in H. tauto. tauto.
 
 assert(a_neq_a0:=eq_nat_decide a0 a) . case(a_neq_a0).
  intro. destruct ls. tauto. 
  remember (next_in_list (a0 :: p0 :: ls) a) as nexa. 
 clear IHls a_neq_a0. 

  induction ls. 
  simpl in H1. destruct H1. simpl in *. case(eq_nat_decide a0 a) in *.
  case(eq_nat_decide a0 p) in *. apply eq_nat_eq in e1. rewrite H1 in e1.
  rewrite e1 in H.   tauto. case(eq_nat_decide p0 p) in *. rewrite H0 in H.
  rewrite Heqnexa in H. tauto. elim n0. rewrite H1. apply eq_nat_refl.
  tauto. tauto.
  assert(p_eq_a1:=eq_nat_dec p a1). case(p_eq_a1). 
  intro. destruct ls. clear H2. simpl in H1.
  destruct H1. simpl in H. rewrite <- H1 in H. rewrite <- e0 in H.
 tauto. destruct H1. rewrite H1 in *. rewrite Heqnexa in H0.
  simpl in H0. case(eq_nat_decide a0 p) in *. apply eq_nat_eq in e1.
  simpl in H. rewrite e1 in H. rewrite H1 in H. tauto.
  case(eq_nat_decide p0 p) in *. apply eq_nat_eq in e1. 
  simpl in H. rewrite e1 in H. rewrite H1 in H. tauto.
  case(eq_nat_decide a1 p) in *. case(eq_nat_decide a0 a) in *.
  rewrite H0 in H. simpl in H. tauto. tauto.
  rewrite H1 in n1. elim n1. apply eq_nat_refl. tauto.
  assert(next_in_list (a0 :: p0 :: a1 :: p6 :: ls) a = p0).
  simpl. case(eq_nat_decide a0 a) in *. tauto. tauto.
  rewrite H3 in Heqnexa. assert(next_in_list (a0 :: p0 :: a1 :: p6 :: ls) p = p6).
  simpl. case(eq_nat_decide a0 p) in *. apply eq_nat_eq in e1.
  simpl in H. rewrite e1 in H. rewrite e0 in H. tauto.
  case(eq_nat_decide p0 p) in *. simpl in H.
  apply eq_nat_eq in e1.  rewrite e1 in H. rewrite  e0 in H. tauto.
  case(eq_nat_decide a1 p) in *. tauto. rewrite e0 in n1. elim n1.
  apply eq_nat_refl. rewrite H4 in H0. simpl in H. rewrite <-Heqnexa in H.
  rewrite H0 in H. tauto.

  intro. clear p_eq_a1. 
  assert(well_formed_list (a0 :: p0 :: ls)). simpl. simpl in H. tauto.
  pose proof(IHls H3);clear IHls. assert(is_in_list (p0 :: ls) p).
  simpl. simpl in H1. tauto. pose proof(H4 H5) ; clear H4.
  assert(id a = id a0 \/ is_in_list (p0 :: ls) a). left. apply eq_nat_eq in e.
  symmetry in e. tauto.
  pose proof(H6 H4);clear H6.
  assert(nexa = next_in_list (a0 :: p0 :: ls) a). simpl.
  simpl in Heqnexa. case(eq_nat_decide a0 a) in *. tauto.
  tauto. pose proof(H7 H6);clear H7.
  assert(next_in_list (a0 :: p0 :: ls) p = nexa). simpl.
  simpl in H0. case(eq_nat_decide a0 p) in *. tauto.
  case(eq_nat_decide p0 p) in *. rewrite Heqnexa in H0.
  simpl in H0. case(eq_nat_decide a0 a) in *. rewrite H0 in H.
  simpl in H. tauto. tauto. case(eq_nat_decide a1 p) in *.
  elim n. symmetry. apply eq_nat_eq in e0. tauto. tauto.
  tauto. 

  intro. destruct H2. rewrite H2 in n. elim n. apply eq_nat_refl.
  apply IHls. apply well_formed_remove in H. tauto. tauto. tauto.
  pose (next_in_list_remove). specialize o with ls a0 p.
  assert ( a0 <> p). intro. rewrite H3 in H. simpl in H. tauto.
 assert(id a0 <> id p). intro. simpl in H. destruct H. destruct H5.
   clear H H6. destruct H5. clear H5 H2 H0 IHls a_neq_a0 n o H3.
  induction ls. tauto. simpl in *. destruct H1. rewrite H0 in H4.
  tauto. apply not_or_and in H. destruct H. tauto.
 pose proof(o H4);clear o.
  assert(HN:is_in_list ls p). tauto. pose proof(H5 HN);clear H5.
  pose (next_in_list_remove). specialize o with ls a0 a.
  assert (~eq_nat a0 a). intro. simpl in H. destruct H. destruct H7.
  destruct H7.
  clear H H1 H9 H8 H0 IHls a_neq_a0 n o H3 H6 HN H4.
  apply eq_nat_eq in H5. induction ls. tauto.
  simpl in H7. simpl in H2. apply not_or_and in H7.
  destruct H2. rewrite H in H5. tauto. tauto.
 assert(id a0 <> id a). intro. elim n.
  rewrite H7 . apply eq_nat_refl. pose proof(o H7);clear o.
  assert(HN2:is_in_list ls a). tauto. pose proof(H8 HN2);clear H5.
  clear IHls a_neq_a0 H8. destruct H9. destruct H6.
   rewrite <- H6. rewrite <- H5. tauto.
  rewrite H5 in H0. rewrite H6 in H0. assert(is_in_list ls a0).
  rewrite H0. apply next_in_list_exist. tauto. tauto. simpl in H. tauto.
  destruct H6. rewrite H5 in H0. rewrite H6 in H0. assert(is_in_list ls a0).
  rewrite <-H0. apply next_in_list_exist. tauto. tauto. simpl in H. tauto.
  clear H0 HN HN2. induction ls. tauto. 
  assert(next_in_list (a1 :: ls) p = a1). clear H2 H5 IHls.
  induction ls. simpl in H1. destruct H1. simpl. case(eq_nat_decide a1 p) in *.
  tauto. elim n0. rewrite H0. apply eq_nat_refl. tauto.
  destruct ls. simpl. simpl in H6. simpl in H1. case(eq_nat_decide a0 p) in *.
   rewrite H6 in H. simpl in H. tauto. case(eq_nat_decide a1 p) in *.
  rewrite H6 in H. simpl in H. tauto. case(eq_nat_decide a2 p) in *.
  tauto. destruct H1. rewrite H0 in *. elim n1. apply eq_nat_refl.
  destruct H0. rewrite H0 in *. elim n2. apply eq_nat_refl. tauto.
  assert(id p <> id a2). intro. simpl in H6. case(eq_nat_decide a0 p) in *.
  simpl in H. rewrite H6 in H. tauto. case(eq_nat_decide a1 p) in *.
  simpl in H. rewrite H6 in H. tauto. case(eq_nat_decide a2 p) in *.
  simpl in H. rewrite H6 in H. tauto. rewrite H0 in n2. elim n2.
  apply eq_nat_refl. assert(well_formed_list (a0 :: a1 :: p0 :: ls)).
  simpl. simpl in H. tauto. pose proof(IHls H2);clear IHls.
  assert(is_in_list (a1 :: p0 :: ls) p). simpl. simpl in H1.
  tauto. pose proof(H5 H8); clear H5. 
  assert(next_in_list (a0 :: a1 :: p0 :: ls) p = a0). simpl. simpl in H6.
  case(eq_nat_decide a0 p) in *. tauto. case(eq_nat_decide a1 p) in *.
  simpl in H. rewrite H6 in H. tauto. case(eq_nat_decide p0 p) in *.
  case(eq_nat_decide a2 p) in *. apply eq_nat_eq in e0. symmetry in e0.
   tauto. tauto. 
  case(eq_nat_decide a2 p) in *. apply eq_nat_eq in e. symmetry in e. tauto.
  clear  H2 H9 H8. induction ls. simpl in H1. destruct H1. 
  rewrite H1 in *. elim n1. apply eq_nat_refl. destruct H1.
  rewrite H1 in *. elim n3. apply eq_nat_refl. destruct H1.
  rewrite H1 in *. elim n2. apply eq_nat_refl. tauto.
  assert(well_formed_list (a0 :: a1 :: a2 :: p0 :: ls)). 
  simpl. simpl in H. tauto. pose proof(IHls H2);clear IHls.
  destruct ls. simpl in H1. destruct H1. rewrite H1 in *. elim n1.
  apply eq_nat_refl. destruct H1. rewrite H1 in *. elim n3.
  apply eq_nat_refl. destruct H1. rewrite H1 in *. elim n2.
  apply eq_nat_refl. destruct H1. simpl. case(eq_nat_decide a3 p) in *.
  tauto. rewrite H1 in *. elim n4. apply eq_nat_refl. tauto.
  assert(id p <> id a3). intro. simpl in H6. 
  case(eq_nat_decide a3 p) in *. simpl in H. rewrite H6 in H.
  tauto. rewrite H8 in *. elim n4. apply eq_nat_refl. tauto.
  pose proof(H9 H5); clear H9. simpl. simpl in H10.
  case(eq_nat_decide a1 p) in *. rewrite H10 in H. simpl in H. tauto.
  case(eq_nat_decide a2 p) in *. apply eq_nat_eq in e.
  symmetry in e. tauto. case(eq_nat_decide p0 p) in *. tauto. tauto.
  assert(next_in_list (a1 :: ls) a = a1). clear IHls. clear H1 H6 H0.
  induction ls. simpl in H2. simpl in H5. destruct H2.
  case(eq_nat_decide a0 a) in *. tauto. simpl. case(eq_nat_decide a1 a) in *.
  tauto. rewrite H0 in *. elim n1. apply eq_nat_refl. tauto.
  destruct ls. simpl in H2. simpl in H5. destruct H2.
  case(eq_nat_decide a0 a) in *. tauto. simpl. case(eq_nat_decide a1 a) in *.
  rewrite H5 in H. simpl in H. tauto. rewrite H0 in n1. 
  elim n1. apply eq_nat_refl. destruct H0. simpl. 
  case(eq_nat_decide a1 a) in *. apply eq_nat_eq in e. rewrite H0 in *. 
  simpl in H. rewrite e in H. tauto.
  case(eq_nat_decide a2 a) in *. tauto. rewrite H0 in n1. elim n1.
  apply eq_nat_refl. tauto. 
  assert(id a <> id a2). intro. simpl in H5.
  case(eq_nat_decide a0 a) in *. rewrite H5 in H. 
  simpl in H. tauto. case(eq_nat_decide a1 a) in *.
   rewrite H5 in *. simpl in H. tauto. case(eq_nat_decide a2 a) in *.
  rewrite H5 in H. simpl in H. tauto. rewrite H0 in n2. elim n2.
  apply eq_nat_refl. assert(well_formed_list (a0 :: a1 :: p0 :: ls)).
  simpl. simpl in H. tauto. pose proof(IHls H1);clear IHls.
  assert(is_in_list (a1 :: p0 :: ls) a). simpl. simpl in H2.
  tauto. pose proof(H6 H8);clear H6.
  assert(next_in_list (a0 :: a1 :: p0 :: ls) a = a0 ). simpl.
  simpl in H5. case(eq_nat_decide a0 a) in *. tauto.
  case(eq_nat_decide a1 a) in *. rewrite H5 in H. simpl in H. tauto.
  case(eq_nat_decide a2 a) in *. rewrite H5 in H. simpl in H. tauto.
  case(eq_nat_decide p0 a) in *. tauto. tauto. 
  pose proof( H9 H6);clear H9. clear H1. simpl.
  simpl in H10. case(eq_nat_decide a1 a) in *. rewrite H10 in H.
  simpl in H. tauto. case(eq_nat_decide a2 a) in *. 
  apply eq_nat_eq in e. rewrite e in H0. tauto. tauto.
  rewrite H0. rewrite H8. tauto.
Qed.

Lemma next_in_list_distinct: forall(ls: list Point2D)(p1 p2 p3:Point2D),
well_formed_list(p1::p2::ls)-> is_in_list (p1::p2::ls) p3 -> 
p3 <> next_in_list (p1::p2::ls) p3.
Proof. intros.
induction ls.
  - intro. simpl in *. destruct H0.  case(eq_nat_decide p6 p8) in *.
    rewrite <-H1 in H. rewrite H0 in H. tauto.
    elim n. rewrite H0. apply eq_nat_refl. case(eq_nat_decide p6 p8) in *.
    apply eq_nat_eq in e. rewrite e in H. rewrite H1 in H. tauto.
    case(eq_nat_decide p7 p8)in*. rewrite H1 in n. elim n.
    apply eq_nat_refl. destruct H0. 
    rewrite H0 in n0. elim n0. apply eq_nat_refl. tauto.
  - assert(well_formed_list (p6 :: p7 :: ls)). simpl. simpl in H.
    tauto. pose proof(IHls H1);clear IHls. pose(Point2D_dec p8 a).
    destruct s. destruct ls. intro. simpl in H0. simpl in H3. 
    case(eq_nat_decide p6 p8) in *. apply eq_nat_eq in e0.
    simpl in H.  rewrite e0 in H. rewrite <- e in H. tauto.
    case(eq_nat_decide p7 p8) in *. apply eq_nat_eq in e0. 
    simpl in H. rewrite e0 in H. rewrite <- e in H. tauto.
    case(eq_nat_decide a p8) in *. apply eq_nat_eq in e0. 
    simpl in H. rewrite <-H3 in H. rewrite <- e in H. tauto.
    destruct H0. symmetry in H0. apply eq_eq_nat in H0. tauto.
    destruct H0. symmetry in H0. apply eq_eq_nat in H0. tauto.
    destruct H0. symmetry in H0. apply eq_eq_nat in H0. tauto. tauto.
    intro. rewrite <-e in *. simpl in H3. case(eq_nat_decide p6 p8) in *.
    rewrite H3 in H. simpl in H. tauto. case(eq_nat_decide p7 p8) in *.
    apply eq_nat_eq in e0. simpl in H. rewrite e0 in H. tauto.
    case(eq_nat_decide p8 p8) in *. simpl in H. rewrite H3 in H. tauto.
    elim n1. apply eq_nat_refl. assert (is_in_list (p6 :: p7 :: ls) p8).
    simpl in H0. simpl . destruct H0. tauto. destruct H0. tauto.
    destruct H0. assert (p8=a).
    pose proof( Point2D_eq_eq p8 a (p6 :: p7 :: a :: ls)). apply H3;clear H3.
     tauto. simpl. tauto. rewrite H0. apply eq_nat_refl. tauto. tauto.
    pose proof(H2 H3).
    simpl. simpl in H4. case(eq_nat_decide p6 p8) in *. tauto. case(eq_nat_decide p7 p8) in *.
     tauto. case(eq_nat_decide a p8) in*. assert(a=p8).
  pose proof( Point2D_eq_eq a p8 (p6 :: p7 :: a :: ls)). apply H5;clear H3. 
    tauto. simpl. tauto. tauto. symmetry in H5. tauto. tauto.
Qed.
Lemma is_in_list_neq: forall(ls:list Point2D) (p1 p2:Point2D) , 
well_formed_list ls -> is_in_list ls p1 /\ is_in_list ls p2 -> p1<>p2 -> 
~eq_nat p1 p2.
Proof. intros. intro. pose(Point2D_eq_eq). specialize e with p6 p7 ls.
tauto.
Qed.
Lemma ccw_helper: forall (pt1 pt pt3 pt4 a :Point2D), 
~ is_colinear pt1 pt pt3 /\ ~ is_colinear pt1 pt pt4 /\ ~ is_colinear pt1 pt a /\
~ is_colinear pt1 pt3 pt4 /\ ~ is_colinear pt1 pt3 a /\ ~ is_colinear pt1 pt4 a /\ 
~ is_colinear pt pt3 pt4 /\ ~ is_colinear pt  pt3 a /\ ~ is_colinear pt pt4 a /\ 
~ is_colinear pt3 pt4 a  /\ 
~is_ccw pt1 pt a /\ ~is_ccw pt1 pt pt3/\ ~is_ccw pt1 pt pt4 /\
~is_ccw pt3 pt4 a /\ ~is_ccw pt3 pt4  pt/\ ~is_ccw pt3 pt4 pt1 /\
is_ccw pt3 pt1 a
-> ~is_ccw pt pt3 a.
Proof. intros.
 repeat (match goal with
         | [ H : _ /\ _ |- _ ] => destruct H
        
                 end).
 unfold Is_non_colinear in *. 
assert (Dec:=cw_dec pt pt4 a).
destruct Dec. 
- apply negccw_transitivity2 with pt4 pt1 .

split. tauto. split.
intro. apply colinear_eq in H16. tauto.
split. intro. apply colinear_eq in H16. tauto. split. intro. apply colinear_eq in H16. tauto.
split. intro. apply colinear_eq in H16. tauto. split. intro. apply colinear_eq in H16.
 tauto. split. intro. apply colinear_eq in H16. tauto. split. intro. apply colinear_eq in H16.
 tauto. split. intro. apply colinear_eq in H16. tauto. split.
intro. apply colinear_eq in H16. tauto. split. tauto. split. tauto.
split. tauto. split. apply negccw_symmetric in H13.
apply negccw_symmetric in H13.  tauto. 
unfold is_cw in i. unfold is_ccw. lra.
- assert(is_ccw pt3 pt a). apply ccw_transitivity with pt1 pt4.
split.  intro. apply colinear_eq in H16. tauto. split.
intro. apply colinear_eq in H16. tauto.
split. intro. apply colinear_eq in H16. tauto. split. intro. apply colinear_eq in H16. tauto.
split. intro. apply colinear_eq in H16. tauto. split. intro. apply colinear_eq in H16.
elim H8. apply colinear_eq. tauto. split. intro. apply colinear_eq in H16. tauto. split. intro. apply colinear_eq in H16.
 tauto. split. intro. apply colinear_eq in H16. tauto. split.
intro. apply colinear_eq in H16. tauto. split. 
apply negccw_Antisymmetry in H13. destruct H13. apply ccw_symmetric in H13.
apply ccw_symmetric in H13. tauto. apply colinear_eq in H13. tauto. split. 
apply negccw_Antisymmetry in H14. destruct H14. apply ccw_symmetric in H14.
apply ccw_symmetric in H14. tauto. apply colinear_eq in H14. tauto.  split.
apply negccw_Antisymmetry in H12. destruct H12.  
apply ccw_symmetric in H12.
apply ccw_symmetric in H12. tauto. apply colinear_eq in H12.
 tauto. split. apply negccw_Antisymmetry in H10. destruct H10.
 apply ccw_symmetric in H10. tauto. apply colinear_eq in H10.
tauto. tauto. apply ccw_Antisymmetry in H16. apply negccw_symmetric in H16.
apply negccw_symmetric in H16. tauto. 
Qed.
Lemma Is_Convex_remove: forall (ls : list Point2D) (pt : Point2D) ,
Is_non_colinear (pt::ls) /\ Is_Convex(pt::ls) -> Is_Convex ls.
Proof.
intros. unfold Is_Convex . destruct H. assert(NonCo := H). clear H. 
assert(H:=H0). clear H0. split.
+ unfold Is_Convex in *. destruct H.
  apply well_formed_remove in H. tauto.
+ intros. unfold Is_Convex in H. 
  repeat (match goal with
         | [ H : _ /\ _ |- _ ] => destruct H
        
                 end). 
    case (eq_nat_decide pt pt1) in *.
    - specialize H3 with pt pt3.  
      clear H3 H1 H2. unfold well_formed_list in H. 
       repeat (match goal with
         | [ H : _ /\ _ |- _ ] => destruct H
        
                 end). clear H H2. simpl in H1. destruct H1.
       simpl in *. clear H1. 
       induction ls. 
        ++ tauto. 
        ++ clear IHls.           
           unfold is_in_list in *. fold is_in_list in *. 
           destruct H0.
           -- apply not_or_and in H. destruct H. apply eq_nat_is_eq in e.
              rewrite <- e in H0. tauto.
           -- apply not_or_and in H. destruct H. 
              apply -> (is_in_list_equality ls pt1 pt) in H0 .
              * tauto. 
              * apply eq_nat_is_eq in e. apply eq_nat_is_eq.
                symmetry in e. tauto.
    -  assert(HC := H3). specialize H3 with pt1 pt3. apply imply_to_or in H3.
      destruct H3.
       ++ apply not_and_or in H3. destruct H3.
          -- apply (is_in_list_add ls pt1 pt) in H0. tauto.
          -- apply not_and_or in H3. destruct H3.
             * unfold is_in_list in *. fold is_in_list in *.
               apply not_or_and in H3. destruct H3.
                unfold next_in_list in *. fold next_in_list in *.
                apply (next_in_list_exist_h1 ls pt1 pt) in H0.
                unfold next_in_list_h1 in *. fold next_in_list_h1 in *.
                case (eq_nat_decide pt pt1) in *.
                 ** tauto.
                 ** destruct H0. rewrite H0 in H3. tauto. tauto.
             * simpl in H3. destruct H3. tauto.
       ++ assert(next_in_list (pt:: ls) pt1 = (next_in_list (ls) pt1) \/ next_in_list (pt :: ls) pt1 = pt).
             * apply (next_in_list_remove) . intro. rewrite H4 in n. elim n. apply eq_nat_refl. tauto.
             * destruct H4. rewrite H4 in H3. tauto. simpl in H4.
               case (eq_nat_decide pt pt1) in *. intro. tauto. 
               induction ls.
                ** tauto. 
                ** assert (next_in_list (a :: ls) pt1 = a).
                    +++ simpl. simpl in H4. case (eq_nat_decide a pt1) in *.
                        --- apply Point2D_eq in e. rewrite e in *. destruct ls. tauto. rewrite H4 in H. simpl in H. tauto.
                        --- clear HC H3 H1 H2 NonCo. clear IHls. induction ls.
                            ++++  simpl in H0. 
                                  destruct H0.  rewrite H0 in n1 . destruct n1. apply eq_nat_refl.
                                  tauto.
                            ++++ unfold next_in_list_h1.  fold next_in_list_h1. 
                                   simpl. case(eq_nat_decide a0 pt1).
                                 ---- intro. destruct ls. tauto. apply Point2D_eq in e.
                                      rewrite e in H4. simpl in H4. case(eq_nat_decide pt1 pt1) in *.
                                      rewrite H4 in H. simpl in H. tauto.
                                      destruct n2. apply eq_nat_refl.
                                 ---- intro. apply IHls.
                                       *** simpl.  simpl in H. tauto. 
                                       *** clear IHls. simpl. simpl in H0.
                                           destruct H0. tauto.
                                           destruct H0. rewrite H0 in n2. destruct n2. apply eq_nat_refl. tauto.
                                       *** clear IHls . simpl. simpl in H4. case(eq_nat_decide a0 pt1) in *.
                                           tauto. tauto.
                    
                 +++ clear IHls. rewrite H5. assert(next_in_list (pt :: a :: ls) pt1 = pt).
                     simpl.  simpl in H4. case(eq_nat_decide pt pt1) in *. tauto.
                     case(eq_nat_decide a pt1) in *. tauto. tauto.
                     assert(forall pt0 :Point2D , is_in_list ls pt0 -> ~is_ccw pt1 pt pt0).
                     intros. specialize HC with pt1 pt0. 
                     
                     rewrite H6 in HC. apply HC. split. simpl. simpl in H0. tauto.
                     split. simpl. tauto. simpl. tauto.
                     
                  
                     assert (nat_eq_eq:forall (p1 p2 :Point2D) ,is_in_list (pt :: a :: ls) p1 /\ is_in_list(pt :: a :: ls) p2 
                                    /\ eq_nat p1 p2  -> p1 = p2).
                     intros. pose proof( Point2D_eq_eq p6 p7 (pt :: a :: ls)).
                     apply H9. tauto. tauto. tauto.
                      

                     pose proof(Nat.eq_dec pt1 pt3).
                     case H8. intros.  assert(pt1 = pt3). apply nat_eq_eq.
                     simpl. split. tauto. split. tauto. rewrite e. apply eq_nat_refl.
                     rewrite H9. unfold is_ccw. unfold order_det. lra.
                     intro. 
                     assert (pt1_neq_pt3:~eq_nat pt1 pt3). intro. apply eq_nat_eq  in H9. tauto.
                     clear H8 n1.
                     
                     pose proof(Nat.eq_dec pt3 a).
                     case H8. intros.  assert(pt3 = a). apply nat_eq_eq.
                     simpl. split. tauto. split. tauto. rewrite e. apply eq_nat_refl.
                     rewrite H9. unfold is_ccw. unfold order_det. lra.
                     intro. 
                   
                     assert (pt3_neq_a:~eq_nat pt3  a). intro. apply eq_nat_eq  in H9. tauto.
                     clear H8 n1.

                      pose proof(Nat.eq_dec pt1 a).
                     case H8. intros.  assert(pt1 = a). apply nat_eq_eq.
                     simpl. split. tauto. split. tauto. rewrite e. apply eq_nat_refl.
                     rewrite H9. unfold is_ccw. unfold order_det. lra.
                     intro. 
                   
                     assert (pt1_neq_a:~ eq_nat pt1  a). intro. apply eq_nat_eq  in H9. tauto.
                     clear H8 n1.
                     assert (Hdec:= ccw_dec). specialize Hdec with pt1 a pt3.
                     destruct Hdec. apply ccw_symmetric in i. 
                                  

                     induction ls.
                          ---
                           simpl in H0. destruct H0. rewrite H0 in *. elim pt1_neq_a.
                           apply eq_nat_refl.  tauto.                           
                          --- assert(T1:Is_non_colinear (pt:: a :: ls)).
                              clear IHls. unfold Is_non_colinear.
                              unfold Is_non_colinear in NonCo.
                              intros. specialize NonCo with p6 p7 p8. apply NonCo.
                              simpl in H8. simpl. repeat (split; try(tauto)). 
                              pose proof (IHls T1). clear IHls T1.
  
                              assert(T1:well_formed_list (pt :: a :: ls)).  simpl. simpl in H.
                              tauto. pose proof (H8 T1). clear H8 T1.

                              assert(T1:~ is_ccw pt1 (next_in_list (pt :: a :: ls) pt1) pt3).
                              clear H9. simpl. simpl in H1. simpl in H3. simpl in H4. 
                              case(eq_nat_decide pt pt1) in *.
                              tauto. case(eq_nat_decide a pt1) in *. apply eq_nat_eq in e.
                              symmetry in e. rewrite e in *. elim pt1_neq_a.
                              apply eq_nat_refl. case(eq_nat_decide a0 pt1) in *.
                              assert(a0 =pt1). apply nat_eq_eq. simpl.
                              tauto. rewrite H8 in *. destruct ls. simpl in H2.
                              destruct H2. apply eq_eq_nat in H2. tauto. 
                              destruct H2. symmetry in H2. apply eq_eq_nat in H2. tauto. tauto.
                              simpl. rewrite H4 in H. simpl in H. tauto. tauto.

                              pose proof(H9 T1). clear H9 T1.
                              
                              simpl in H0. simpl in H5. destruct H0. apply eq_eq_nat in H0. tauto.
                              destruct H0. assert(pt1=a0).
                              apply nat_eq_eq. simpl. split. tauto. split. tauto.
                              rewrite H0. apply eq_nat_refl. rewrite <- H9 in *.
                              destruct ls. simpl in H2. destruct H2. apply eq_eq_nat in H2.
                              tauto. destruct H2. symmetry in H2. apply eq_eq_nat in H2.
                              tauto. tauto. case(eq_nat_decide a pt1) in *. apply eq_nat_eq in e.
                              symmetry in e. apply eq_eq_nat in e. tauto. 
                              case(eq_nat_decide pt1 pt1) in *. rewrite H5 in H. simpl in H.
                              tauto. elim n2. apply eq_nat_refl. case(eq_nat_decide a pt1) in *.
                              rewrite H5 in H. simpl in H. tauto.
                              
                              assert(T1:is_in_list (a :: ls) pt1). simpl. tauto. 
                              pose proof (H8 T1). clear  H8.
                           
                              assert(T2:is_in_list (a :: ls) (next_in_list (a :: ls) pt1)).
                              apply next_in_list_exist. tauto. tauto.
                              pose proof(H9 T2). clear H9 T1 T2.

                              simpl in H2. destruct H2. apply eq_eq_nat in H2.
                              tauto. destruct H2. assert (pt3=a0). apply nat_eq_eq.
                              simpl. split. tauto. split. tauto. rewrite H2. apply eq_nat_refl.
                              rewrite H9. clear H8. assert( ~is_ccw a a0 pt1). specialize HC with a pt1.
                              simpl in HC.
                              case(eq_nat_decide pt a) in *. assert (pt = a). apply nat_eq_eq.
                              simpl. tauto. rewrite H8 in H. simpl in H. tauto. 
                                 case (eq_nat_decide a a) in *.  apply HC. tauto. elim n3.
                                 apply eq_nat_refl. apply negccw_symmetric. apply negccw_symmetric.
                                 tauto.
                               
                              assert(T2:is_in_list (a :: ls) pt3). simpl. tauto.
                              pose proof(H8 T2). clear H8 H5 T2.
                              
                              assert(HC1:=HC). specialize HC1 with a pt1. assert(HC2:=HC).
                              specialize HC with a0 pt1. destruct ls. simpl in H0. tauto.
                              assert(ccw_pt1_pt:forall (pt0 :Point2D) , is_in_list (pt :: a :: a0 ::p :: ls) pt0 
                                      -> ~is_ccw pt1 pt pt0). intros. specialize HC2 with pt1 pt0.
                               rewrite H6 in HC2. apply HC2. simpl. split. tauto. split. tauto.
                              simpl in H5. tauto.
                              clear ccw_pt1_pt HC1 HC  H9 H3 H1 n n0 H4 n1 H7 H9.
                              intro. 
                              remember (next_in_list (p :: ls) pt3) as pt4.
                              assert(pt4_in_list:is_in_list (p::ls) pt4). rewrite Heqpt4.
                              apply next_in_list_exist. tauto. tauto.
                              
                              assert(pt1 <> pt). intro. rewrite <- H3 in H.
                              simpl in H0. simpl in H. destruct H0. rewrite H0 in H. tauto.
                              tauto. 
                              
                              assert(pt1 <> pt3). intro. rewrite H4 in H1.
                              unfold is_ccw in H1. unfold order_det in H1. lra.
                              
                              assert(pt3 <> pt). intro. rewrite <- H5 in H. simpl in H2.
                              destruct H2. simpl in H. rewrite H2 in H. tauto. 
                              simpl in H. tauto.
  
                              assert(pt1 <> pt4). intro. simpl in H. specialize HC2 with pt3 a.
                              assert(next_in_list (pt :: a :: a0 :: p :: ls) pt3 = next_in_list (p::ls) pt3).
                              
                              assert(nex_pt3_neq_pt:next_in_list (pt :: a :: a0 :: p :: ls) pt3 <> pt).
                              intro. assert (eq_nat pt3 pt1). apply next_in_list_eq with (pt :: a :: a0 :: p :: ls).
                              split. simpl. tauto. split. simpl. simpl in H2. tauto.
                              simpl. simpl in H0. tauto. rewrite H6.  rewrite H8. tauto.
                               assert (pt1 = pt3). apply nat_eq_eq. split. simpl. tauto.
                              split.  simpl. tauto. apply eq_nat_eq in H9. rewrite H9. apply eq_nat_refl.
                              tauto.

                              rewrite next_in_list_simpl. rewrite next_in_list_simpl.
                              pose (next_in_list_remove). specialize o with ( p :: ls) pt pt3.
                              assert(H3C:(id pt)<>(id pt3)). intro. symmetry in H8. 
                              assert(pt3 =pt). apply nat_eq_eq. split. simpl. tauto.
                              split. simpl. tauto. rewrite H8. apply eq_nat_refl.
                              rewrite <-H9 in H. tauto.
                              pose proof(o H3C); clear o. assert(is_in_list  (p :: ls) pt3 ). tauto.
                              pose proof(H8 H9); clear H8. 
                              destruct H10. tauto. 
                              
                              assert(next_in_list (pt :: p :: ls) pt1 = pt).
                              simpl. simpl in H6. case(eq_nat_decide pt pt1) in *. rewrite H6 in H. tauto.
                              case(eq_nat_decide p pt1) in *. case(eq_nat_decide a pt1) in *.
                              rewrite H6 in H. tauto. case(eq_nat_decide a0 pt1) in *. 
                              rewrite H6 in H. tauto. tauto. case(eq_nat_decide a pt1) in *.
                              rewrite H6 in H. tauto. case(eq_nat_decide a0 pt1) in *.
                              rewrite H6 in H. tauto. tauto. assert(eq_nat pt1 pt3).      
                              apply next_in_list_eq with (pt:: p :: ls). split. simpl. tauto.
                              split. simpl. tauto. simpl. tauto. rewrite H8. rewrite H10. tauto.
                              apply eq_nat_eq in H11. assert(pt1=pt3). apply nat_eq_eq.
                              simpl. split. tauto. split.  tauto.  rewrite H11. apply eq_nat_refl.
                              tauto.
                              
                              split. intro. apply eq_nat_eq in H8. assert(pt3=a0).
                              apply nat_eq_eq . split. simpl. tauto. split. simpl. tauto.
                              rewrite H8. apply eq_nat_refl. rewrite <- H9 in H. tauto. 
                              intro. assert(pt = pt3). apply nat_eq_eq. 
                              split.  simpl.  tauto.  split. simpl.  tauto. tauto. 
                              rewrite H9 in H. tauto. split. intro. assert(pt3 = a).
                              apply nat_eq_eq. split. simpl. tauto. split. simpl. tauto. tauto.
                              rewrite <- H9 in H. tauto. intro. assert(pt = pt3). apply nat_eq_eq.
                              simpl. tauto. rewrite H9 in H. tauto.

                              rewrite <-Heqpt4 in H8. rewrite <- H7 in H8.
                              rewrite H8 in HC2.
                              
                              assert(~ is_ccw pt3 pt1 a). apply HC2. split. simpl. tauto.
                              split. simpl. tauto. simpl. tauto. apply negccw_symmetric in H9.
                              apply negccw_symmetric in H9. tauto. 

                              assert(pt1 <> a). intro. simpl in H0. destruct H0.
                              rewrite <-H8 in H. simpl in H. rewrite H0 in H. tauto.
                              rewrite <-H8 in H. simpl in H. tauto.

                              assert(pt3 <> pt4). destruct ls. simpl in H0.
                              simpl in H2. destruct H0. assert (pt1 = p).
                              apply nat_eq_eq. simpl. split. tauto. split. tauto.
                              rewrite H0. apply eq_nat_refl. destruct H2.
                              assert(pt3=p). apply nat_eq_eq. simpl. split. tauto.
                              split. tauto. rewrite H2. apply eq_nat_refl.  
                              rewrite <- H9 in H10. symmetry in H10. tauto.
                              tauto. tauto. pose(next_in_list_distinct). 
                              specialize n with  ls p p0 pt3. 
                              rewrite Heqpt4. apply n. simpl in H. simpl. tauto.
                              tauto.                              
                              
                              assert(pt3 <> a). intro. rewrite <- H10 in H. simpl in H2.
                              destruct H2. simpl in H. rewrite H2 in H. tauto. simpl in H. tauto.
                              assert(pt4 <> pt). intro.  rewrite <-H11 in H. simpl in H. tauto.
                              assert(pt4 <> a). intro. rewrite <- H12 in H. simpl in H. tauto.
                              assert(a <> pt). intro. rewrite H13 in H. simpl in H. tauto.
                           
                              
                              assert( ~is_ccw pt1 pt pt4). specialize HC2 with pt1 pt4.                                    
                                    rewrite H6 in HC2. apply HC2. simpl. split. tauto.
                                    split. tauto. simpl in pt4_in_list. tauto.
                                                                    
                              assert( ~is_ccw pt1 pt a).  specialize HC2 with pt1 a.
                                    
                                    rewrite H6 in HC2. apply HC2. simpl. simpl in H0. tauto.
                                                                    
                              assert( ~is_ccw pt1 pt pt3). specialize HC2 with pt1 pt3.
                                    
                                    rewrite H6 in HC2. apply HC2. simpl. simpl in H0. tauto.
                             
                              assert((next_in_list (pt :: a :: a0 :: p :: ls) pt3) = pt4).
                                    pose(next_in_list_remove). specialize o with (p::ls) pt pt3.
                                    rewrite next_in_list_simpl. rewrite next_in_list_simpl.
                                    assert(is_in_list (p :: ls) pt3 ->
                                    next_in_list (pt :: p :: ls) pt3 = next_in_list (p :: ls) pt3 \/
                                    next_in_list (pt :: p :: ls) pt3 = pt). apply o;clear o. intro.
                                    symmetry in H17. assert(pt3=pt). apply nat_eq_eq. simpl.
                                    split. tauto. split. tauto. rewrite H17. apply eq_nat_refl. tauto.
                                    pose proof (H17 H2);clear H18;clear o. pose proof(H17 H2); clear H17.
                                    destruct H18. rewrite Heqpt4. tauto. 
                                    assert(next_in_list (pt :: p :: ls) pt1 = pt).   
                                    rewrite next_in_list_simpl in H6. rewrite next_in_list_simpl in H6. tauto.
                                    split. intro. apply eq_nat_eq in H18. simpl in H.
                                    rewrite <-H18 in H. assert(pt1 = a0). apply nat_eq_eq.
                                    simpl. split. tauto. split. tauto. rewrite H18. apply eq_nat_refl.
                                    rewrite <- H19 in H. tauto. intro. assert(pt=pt1).
                                    apply nat_eq_eq. simpl. tauto. symmetry in H19. tauto.
                                    split. intro. assert(pt1 = a). apply nat_eq_eq. simpl. tauto. tauto.
                                    intro. assert(pt=pt1). apply nat_eq_eq. simpl. tauto. symmetry in H19. tauto.
                                    pose(next_in_list_eq). specialize e with (pt :: p :: ls) pt1 pt3.
                                     assert(eq_nat pt1 pt3). apply e;clear e. split. simpl. simpl in H. tauto.
                                    split. simpl. simpl in H0. tauto. simpl. tauto. rewrite H17. rewrite H18. tauto.
                                    tauto. 
                                    split. intro. assert(pt3 = a0). apply nat_eq_eq. simpl. tauto.
                                    rewrite <- H18 in H. simpl in H. tauto. 
                                    intro. assert(pt = pt3). apply nat_eq_eq. simpl. tauto.
                                    rewrite H18 in H. simpl in H. tauto. split. tauto. 
                                    intro. assert(pt = pt3). apply nat_eq_eq. simpl. tauto.
                                    rewrite  H18 in H. simpl in H. tauto.

                                   
                              assert( ~is_ccw pt3 pt4 pt1). specialize HC2 with pt3 pt1.
                                    
                                    rewrite H17 in HC2. apply HC2. simpl. split. tauto.
                                    split. assert(is_in_list (p::ls) pt4). 
                                    rewrite Heqpt4. apply next_in_list_exist. tauto. tauto.
                                    simpl in H8. tauto. tauto.   
                              assert( ~is_ccw pt3 pt4 pt).  specialize HC2 with pt3 pt.
                                    rewrite H17 in HC2. apply HC2. simpl. split. tauto.
                                    split. assert(is_in_list (p::ls) pt4). 
                                    rewrite Heqpt4. apply next_in_list_exist. tauto. tauto.
                                    simpl in H8. tauto. tauto.   
                              assert( ~is_ccw pt3 pt4 a). specialize HC2 with pt3 a.
                                    rewrite H17 in HC2. apply HC2. simpl. split. tauto.
                                    split. assert(is_in_list (p::ls) pt4). 
                                    rewrite Heqpt4. apply next_in_list_exist. tauto. tauto.
                                    simpl in H8. tauto. tauto. 
                            
                              assert(~ is_ccw pt pt3 a). apply ccw_helper with pt1 pt4.
                               unfold Is_non_colinear in NonCo. split.
                               assert(N1:=NonCo). specialize N1 with pt1 pt pt3.
                                apply N1;clear N1. simpl.
                               simpl in H. split. tauto. split. intro. symmetry in H21. tauto.
                              split. intro. symmetry in H21. tauto. tauto.
                              split. assert(N2:=NonCo).  specialize N2 with pt1 pt pt4. apply N2. split.
                              tauto. split. intro. symmetry in H21. tauto. split. intro.
                              symmetry in H21. tauto. simpl. tauto. split.
                                assert(N1:=NonCo). specialize N1 with pt1 pt a.
                                apply N1;clear N1. simpl. split. tauto. split. intro.
                                 symmetry in H21. tauto. split. intro. symmetry in H21. tauto. tauto.
                              split. assert(N1:=NonCo). specialize N1 with pt1 pt3 pt4.
                                apply N1;clear N1. simpl.
                                split. tauto. split. tauto.
                              split. intro. symmetry in H21. tauto. tauto. split.
                              assert(N1:=NonCo). specialize N1 with pt1 pt3 a.
                                apply N1;clear N1. simpl.
                                split. tauto. split. tauto.
                              split. intro. symmetry in H21. tauto. tauto. split.
                              assert(N1:=NonCo). specialize N1 with pt1 pt4 a.
                                apply N1;clear N1. simpl.
                                split. tauto. split. tauto.
                              split. intro. symmetry in H21. tauto. tauto. split.
                              assert(N1:=NonCo). specialize N1 with pt pt3 pt4.
                                apply N1;clear N1. simpl.
                                split. intro. symmetry in H21. tauto. split. tauto.
                              split.  tauto. tauto. split.
                              assert(N1:=NonCo). specialize N1 with pt pt3 a.
                                apply N1;clear N1. simpl.
                                split. intro. symmetry in H21. tauto. split. tauto.
                              split. tauto. tauto. split.
                              assert(N1:=NonCo). specialize N1 with pt pt4 a.
                                apply N1;clear N1. simpl.
                                split. intro. symmetry in H21. tauto. split. tauto.
                              split. tauto. tauto. split.
                              assert(N1:=NonCo). specialize N1 with pt3 pt4 a.
                                apply N1;clear N1. simpl.
                                split. tauto. split. tauto.
                              split. intro. symmetry in H21. tauto. tauto. split.
                              tauto. split. tauto. split. tauto. split. tauto.
                              split. tauto. split. tauto. apply ccw_symmetric in i. tauto.
                              
                              assert(~is_ccw pt a pt3). specialize HC2 with pt pt3.
                              assert((next_in_list (pt :: a :: a0 :: p :: ls) pt = a)). simpl.
                                  case(eq_nat_decide pt pt) in *. tauto. elim n. apply eq_nat_refl.
                              rewrite H22 in HC2. apply HC2. simpl. tauto.
                              apply negccw_Antisymmetry in H22. destruct H22. tauto.
                              unfold Is_non_colinear in NonCo. specialize NonCo with pt pt3 a.
                              assert(~ is_colinear pt pt3 a). apply NonCo. split. intro.
                              symmetry in H23. tauto. split. tauto. split. tauto. simpl. tauto. tauto.
                        --- tauto.
Qed.
(*================================================================*)

(*================================================================*)
(*====================== ConvexHull Algorithm ====================*)
(*================================================================*)
Fixpoint Convexlist_delete (first_point:Point2D)(chlist: list Point2D)(pt: Point2D) : list Point2D :=
match chlist with
| [] => chlist
| pt1 :: ls' => match ls' with 
            | [] => if cw_dec pt pt1 first_point then chlist else [] 
            | pt2 :: ls'' => if cw_dec pt pt1 pt2 then chlist else
      Convexlist_delete first_point (ls') pt
      end
end.

Fixpoint ConvexHull_insert_point (first_point:Point2D)(chlist: list Point2D)(pt: Point2D) : list Point2D :=
match chlist with
| [] => chlist
| pt1 :: ls' => match ls' with |[]  => chlist ++ [pt]
| pt2 :: ls'' => if cw_dec pt1 pt2 pt then pt1 :: ConvexHull_insert_point first_point (ls') pt
 else  Convexlist_delete first_point (ls') pt 
end
end.

Fixpoint ConvexHull_insert_list (first_point:Point2D)(chlist: list Point2D)(ls: list Point2D) : list Point2D :=
match ls with
| [] => chlist
| pt1 :: ls' => ConvexHull_insert_list first_point (ConvexHull_insert_point first_point chlist pt1) ls'
end.

Definition create_triangle (pt1 pt2 pt3 :Point2D) := 
if cw_dec pt1 pt2 pt3 then pt1:: pt2 :: pt3 :: []
else pt1 :: pt3 :: pt2 :: []. 

Fixpoint ConvexHull (ls: list Point2D) : list Point2D :=
match ls with
| [] => ls
| pt1 :: [] => ls
| pt1 :: pt2 :: [] => ls
| pt1 :: pt2 :: pt3 :: ls' => ConvexHull_insert_list pt1 (create_triangle pt1 pt2 pt3) ls'
end.

(*================================================================*)

(*================================================================*)
(*============= ConvexHull Algorithm correctness==================*)
(*================================================================*)
Lemma ConvexHull_works: forall (ls: list Point2D),
well_formed_list ls -> is_sortedByX ls -> Is_Convex( ConvexHull ls).
Proof.
intros. induction ls. admit.

unfold ConvexHull.
  destruct ls. admit.
Qed.

(*================ Tests  =========================*)

(* Definition p1: Point2D := {|id:=1 ; x:=1 ; y:= 1#1|}.
Definition p2: Point2D := {|id:=2 ; x:=5#2 ; y:= 2#1|}.
Definition p3: Point2D := {|id:=3 ; x:=5#2 ; y:= 3#1|}.
Definition p4: Point2D := {|id:=4 ; x:=4#1 ; y:= 2#1|}.
Definition p5: Point2D := {|id:=5 ; x:=5#7 ; y:= 2#1|}.

Definition plist : ListP :=  LI 1 p1 (LI 2%nat p2 (LI 3 p3 (LI 4 p4 (LI 5 p5 Lz)))).
 *)
Compute first(split plist).
Compute mergeSort plist.
(*Eval compute in (mergeSort plist).*)
Compute is_sorted(plist).
Compute is_sorted( mergeSort plist).
Compute (sort [p1;p2;p3;p4;p5]).
Check leb.
Check PointOrderByX.leb.

Compute (order_det p1 p2 p3).
Compute (is_colinear p1 p2 p3).
Compute (is_cw p1 p2 p3).
Compute (is_ccw p1 p2 p3).
(*Compute (Sorted [p1;p2;p3;p4;p5]).*)
(*================ Tests  =========================*)




