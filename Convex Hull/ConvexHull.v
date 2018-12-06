(*Add LoadPath "C:\Users\javad\Desktop\coq\GitProject\Convex Hull".*)
Require Import QArith. 
Require Import Psatz.
Require Import QArith.Qminmax.
Require Import Coq.Arith.PeanoNat.
Require Import Coq.Logic.Classical_Prop.
Require Import Bool Basics OrdersTac Minus.
Require Import Coq.ZArith.BinInt.

Require Lra.
Require Omega.
Require Ring.

Load PointSort.

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

Lemma Is_Convex_remove: forall (ls : list Point2D) (pt : Point2D) ,
Is_Convex(pt::ls) -> Is_Convex ls.
Proof.
intros. unfold Is_Convex . split.
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
                ** clear IHls. assert (next_in_list (a :: ls) pt1 = a).
                    +++ simpl. simpl in H4. case (eq_nat_decide a pt1) in *.
                        --- apply Point2D_eq in e. rewrite e in *. destruct ls. tauto. rewrite H4 in H. simpl in H. tauto.
                        --- clear HC H3 H1 H2. induction ls.
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
                 +++ simpl in H3. case (eq_nat_decide pt pt1) in *.
                     rewrite H5. tauto. case(eq_nat_decide a pt1) in *.
                     simpl in H4. case(eq_nat_decide a pt1) in *. 
                     induction ls. rewrite H5. apply Point2D_eq in e.
                     rewrite e. unfold is_ccw. unfold order_det. lra.
                      rewrite H4 in H. simpl in H.
                     tauto.
                     apply Point2D_eq in e. 
                     rewrite H5 . rewrite e. unfold is_ccw. unfold order_det.
                     lra.
                      rewrite H5 . induction ls. simpl in H0.
                     destruct H0. unfold eq_nat in H0.
                     rewrite H0 in n2.  elim n2. apply eq_nat_refl. 
                     tauto. clear IHls. simpl in H4. 
                     case(eq_nat_decide a pt1) in *. rewrite H4 in H. 
                     simpl in H.  tauto. case(eq_nat_decide a0 pt1) in *. 
                     destruct ls. simpl in H2. destruct H2.
                     assert(eq_nat pt3 a). crush. apply Point2D_eq in H6. 
                     rewrite H6. unfold is_ccw. unfold order_det. lra.
                     destruct H2. apply Point2D_eq in e. rewrite <-e.
                     assert(eq_nat pt3 a0). crush. apply Point2D_eq in H6.
                     rewrite H6. unfold is_ccw. unfold order_det. lra.
                     tauto.
                     rewrite H4 in H. simpl in H. tauto.
                     simpl in H5. case(eq_nat_decide a pt1) in *.
                     simpl in H. tauto. case (eq_nat_decide a0 pt1) in *.
                     tauto.
                     induction ls.
                     --- simpl in H0. destruct H0. 
                         destruct n3. rewrite H0. apply eq_nat_refl.
                         destruct H0. destruct n4. rewrite H0. 
                         apply eq_nat_refl. tauto.
                     ---  simpl in H2. destruct H2. assert(pt3 = a).
                         apply Point2D_eq. rewrite H2. apply eq_nat_refl.
                         rewrite H6. unfold is_ccw. unfold order_det. lra.
                         destruct H2. assert (pt3 = a0). apply Point2D_eq.
                         rewrite H2. apply eq_nat_refl. rewrite H6.
                         specialize HC with a pt1. assert(~ is_ccw a (next_in_list (pt :: a :: a0 :: a1 :: ls) a) pt1).
                         apply HC. simpl. split. tauto. case(eq_nat_decide pt a).
                         intro. split. tauto. tauto. intro. case(eq_nat_decide a a).
                         intro. split. tauto. tauto. intro. destruct n8. apply eq_nat_refl.
                         simpl in H7. case(eq_nat_decide pt a) in *. apply Point2D_eq in e.
                         rewrite e in H. simpl in H. tauto. case(eq_nat_decide a a) in *.
                         intro. apply negccw_symmetric.  apply negccw_symmetric in H7. admit.
                         destruct n8. apply eq_nat_refl.
                         admit.
                              
                    

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

Fixpoint create_triangle (pt1 pt2 pt3 :Point2D) := 
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
well_formed_list ls -> is_sorted ls -> Is_Convex( ConvexHull ls).
Proof.
intros.

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




