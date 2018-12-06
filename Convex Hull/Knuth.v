Require Import Arith.
Require Import Reals.
Require Import Psatz.
Require Import Coq.Init.Nat.
Require Import QArith. 
Require Import QArith.QArith_base.
Require Import Coq.Arith.PeanoNat.
Require Lra.
Require Import Omega.
Require Import Orders.
Require Import MyQ.
Require Import Point2D.

(* ==================== Knuth test for order  ========================*)
(* ============== det=(x2−x1)(y3−y1)−(y2−y1)(x3 −x1)=====================*)
(* ==================== ========== =========================*)
Definition order_det (pt1 pt2 pt3 : Point2D) : Q :=
((Xp pt2) - (Xp pt1)) * ((Yp pt3) - (Yp pt1)) - ((Yp pt2) - (Yp pt1))* ((Xp pt3) - (Xp pt1)) .


(* ======== propoistion to check if pt3 is on the right side of pt1 pt2 vector=========================*)
Definition is_cw (pt1 pt2 pt3 : Point2D) : Prop :=
(order_det pt1 pt2 pt3) < 0.

(* ======== propoistion to check if pt3 is on the left side of pt1 pt2 vector=========================*)
Definition is_ccw (pt1 pt2 pt3 : Point2D) : Prop :=
(order_det pt1 pt2 pt3) > 0.

(* (* ======== propoistion to check if pt1 pt2 pt3 are colinear =========================*) *)
Definition is_colinear (pt1 pt2 pt3 : Point2D) : Prop :=
(order_det pt1 pt2 pt3) = 0.

(* ================== Knuth axoims ================================
Cyclic symmetry: If pqr then qrp.
Antisymmetry: If pqr then not prq.
Nondegeneracy: Either pqr or prq.
Interiority: If tqr and ptr and pqt, then pqr.
Transitivity: If tsp and tsq and tsr, and tpq and tqr, then tpr.*)
(*================================================================*)
Lemma cw_symmetric: forall (p q r : Point2D) , is_cw p q r -> is_cw q r p.
Proof. intros. unfold is_cw in *. unfold order_det in *. 
lra.
Qed.

Lemma ccw_symmetric: forall (p q r : Point2D) , is_ccw p q r -> is_ccw q r p.
Proof. intros. unfold is_ccw in *. unfold order_det in *. 
lra.
Qed.
Lemma negccw_symmetric: forall (p q r : Point2D) , ~is_ccw p q r -> ~is_ccw q r p.
Proof. intros. unfold is_ccw in *. unfold order_det in *. 
lra.
Qed. 
Lemma cw_Antisymmetry: forall (p q r : Point2D) , is_cw p q r -> ~ is_cw p r q.
Proof. intros. unfold is_cw in *. unfold order_det in *. 
lra.
Qed.

Lemma cw_dec :forall (p q r : Point2D) , {is_cw p q r} +  {~ is_cw p q r}.
Proof. intros. unfold is_cw in *. remember (order_det p q r) as qval.
clear Heqqval. case (Qlt_le_dec qval 0).
- intros. tauto.
- intro.  apply Qle_not_lt in q0. tauto.
Qed. 

Lemma det_equation_helper_x: forall (a b c d e f g h :Q),
~ g * c - g * d - b * c - h * f + h * b + d * f == 0 ->
((a-b) == (g - b) * ((a - b) * (c - d) - (e - d) * (f - b)) /
((g - b) * (c - d) - (h - d) * (f - b)) 
 + (f - b) *
((a - b) * (h - d) - (e - d) * (g - b)) /
((f - b) * (h - d) - (c - d) * (g - b))).
Proof.
intros.
 repeat (match goal with
         | [ H : _ |- _ ] => try (rewrite Q_mult_dist_eq || rewrite Qmult_plus_distr_r||
                             rewrite Qmult_minus_dist|| rewrite Q_mult_par)
                 end).

assert (H0:(g * c - g * d - b * c + b * d - (h * f - h * b - d * f + d * b)) == 
g * c - g * d - b * c - h * f + h * b + d * f ).
lra. rewrite H0.
assert (H1:(f * h - f * d - b * h + b * d - (c * g - c * b - d * g + d * b)) ==
-(g * c - g * d - b * c - h * f + h * b + d * f )). lra. rewrite H1.
assert (H2:(g * a * c - g * a * d - g * b * c + g * b * d -
 (g * e * f - g * e * b - g * d * f + g * d * b) -
 (b * a * c - b * a * d - b * b * c + b * b * d) +
 (b * e * f - b * e * b - b * d * f + b * d * b)) ==
g * a * c - g * a * d - g * b * c 
 - g * e * f + g * e * b + g * d * f -
 b * a * c + b * a * d + b * b * c +
 b * e * f - b * e * b - b * d * f 
). lra. rewrite H2. 
assert (H3: (f * a * h - f * a * d - f * b * h + f * b * d -
 (f * e * g - f * e * b - f * d * g + f * d * b) -
 (b * a * h - b * a * d - b * b * h + b * b * d) +
 (b * e * g - b * e * b - b * d * g + b * d * b)) ==
f * a * h - f * a * d - f * b * h -
 f * e * g + f * e * b + f * d * g -
 b * a * h + b * a * d + b * b * h +
 b * e * g - b * e * b - b * d * g ).
lra. rewrite H3. rewrite Q_div_sign_ch.
 rewrite Q_div_plus_denum .

assert (H4:(g * a * c - g * a * d - g * b * c - g * e * f + g * e * b + g * d * f -
 b * a * c + b * a * d + b * b * c + b * e * f - b * e * b - b * d * f +
 -
 (f * a * h - f * a * d - f * b * h - f * e * g + f * e * b + f * d * g -
  b * a * h + b * a * d + b * b * h + b * e * g - b * e * b - b * d * g)) == 
(g * a * c - g * a * d - g * b * c  -
 b * a * c  + b * b * c - b * d * f +
 - f * a * h + f * a * d + f * b * h +
  b * a * h  - b * b * h + b * d * g)).
lra. rewrite H4.

assert (H5: (g * a * c - g * a * d - g * b * c - b * a * c + b * b * c - b * d * f +
 - f * a * h + f * a * d + f * b * h + b * a * h - b * b * h + b * d * g) ==
(a -b) * (g * c - g * d - b * c - h * f + h * b + d * f)). lra.
rewrite H5. rewrite Qdiv_mult_l. lra. tauto.
Qed.

Lemma det_equation_helper_y: forall (a b c d e f g h :Q),
 ~ g * c - g * b - e * c - f * h + f * e + b * h == 0 ->
a - b ==
(c - b) *
((d - e) * (f - b) - (a - b) * (g - e)) /
((h - e) * (f - b) - (c - b) * (g - e)) +
(f - b) *
((d - e) * (c - b) - (a - b) * (h - e)) /
((g - e) * (c - b) - (f - b) * (h - e)).
Proof.
intros.
 repeat (match goal with
         | [ H : _ |- _ ] => try (rewrite Q_mult_dist_eq || rewrite Qmult_plus_distr_r||
                             rewrite Qmult_minus_dist|| rewrite Q_mult_par)
                 end).

assert (H0:(g * c - g * b - e * c + e * b - (f * h - f * e - b * h + b * e) == 
g * c - g * b - e * c - f * h + f * e + b * h)).
lra. rewrite H0.
assert (H1:(h * f - h * b - e * f + e * b - (c * g - c * e - b * g + b * e)) ==
-(g * c - g * b - e * c - f * h + f * e + b * h )). lra. rewrite H1.
assert (H2:(c * d * f - c * d * b - c * e * f + c * e * b -
 (c * a * g - c * a * e - c * b * g + c * b * e) -
 (b * d * f - b * d * b - b * e * f + b * e * b) +
 (b * a * g - b * a * e - b * b * g + b * b * e)) ==
c * d * f - c * d * b - c * e * f -
 c * a * g + c * a * e + c * b * g -
b * d * f + b * d * b + b * e * f +
b * a * g - b * a * e - b * b * g 
). lra. rewrite H2. 
assert (H3: (f * d * c - f * d * b - f * e * c + f * e * b -
 (f * a * h - f * a * e - f * b * h + f * b * e) -
 (b * d * c - b * d * b - b * e * c + b * e * b) +
 (b * a * h - b * a * e - b * b * h + b * b * e)) ==
f * d * c - f * d * b - f * e * c + f * e * b -
f * a * h + f * a * e + f * b * h - f * b * e -
b * d * c + b * d * b + b * e * c - b * e * b +
b * a * h - b * a * e - b * b * h + b * b * e ).
lra. rewrite H3. rewrite Q_div_sign_ch.
 rewrite Q_div_plus_denum .

assert (H4:(-
 (c * d * f - c * d * b - c * e * f - c * a * g + c * a * e + c * b * g -
  b * d * f + b * d * b + b * e * f + b * a * g - b * a * e - b * b * g) +
 (f * d * c - f * d * b - f * e * c + f * e * b - f * a * h + f * a * e +
  f * b * h - f * b * e - b * d * c + b * d * b + b * e * c - b * e * b +
  b * a * h - b * a * e - b * b * h + b * b * e)) == 
  c * a * g - c * a * e - c * b * g 
  - b * e * f - b * a * g + b * b * g +
 - f * a * h + f * a * e +
  f * b * h + b * e * c  +
  b * a * h  - b * b * h ).
lra. rewrite H4.

assert (H5: (c * a * g - c * a * e - c * b * g - b * e * f - b * a * g + b * b * g +
 - f * a * h + f * a * e + f * b * h + b * e * c + b * a * h - b * b * h) ==
(a -b) * (g * c - g * b - e * c - f * h + f * e + b * h)). lra.
rewrite H5. rewrite Qdiv_mult_l. lra. tauto.
Qed.
Lemma cw_Interiority:forall (p q r t: Point2D) , is_cw t q r /\ is_cw p t r 
/\ is_cw p q t ->  is_cw p q r.
Proof. intros.
 unfold is_cw in *. unfold order_det in *. lra. Qed.


Lemma cw_transitivity: forall (p q r s t: Point2D) ,
~ is_colinear p q r /\ ~ is_colinear p q s /\ ~ is_colinear p q t /\
~ is_colinear t s p /\ ~ is_colinear t s q /\ ~ is_colinear t s r /\ 
~ is_colinear r s p /\ ~ is_colinear r t p /\ ~ is_colinear r s q /\ 
~ is_colinear r q t /\ 
is_cw s t p /\ is_cw s t q /\ is_cw s t r /\ is_cw t p q 
/\ is_cw t q r -> is_cw t p r.
Proof.
intros.
 repeat (match goal with
         | [ H : _ /\ _ |- _ ] => destruct H
                 end).
unfold is_colinear in *.  unfold is_cw in *.
remember  ((order_det t r s) / (order_det t q s)) as a.
remember  ((order_det t r q) / (order_det t s q)) as b.
assert (Ha: 0 < a). 
- assert ((order_det t r s) < 0).
  + unfold order_det in *. lra.
  + assert ((order_det t q s) < 0).
    -- unfold order_det in *. lra.
    -- rewrite Heqa. remember (order_det t q s) as r1.
       remember (order_det t r s) as r2. apply Q_lt_0_div. tauto. tauto.
- assert (Hb: 0 < b).
  + assert ((order_det t r q) > 0).
    -- unfold order_det in *. lra.
    -- assert ((order_det t s q) > 0).
      ++ unfold order_det in *. lra.
      ++ rewrite Heqb. remember (order_det t s q) as r1. remember (order_det t r q) as r2.
         apply Q_gt_0_div. tauto. tauto.
  + assert(Hx: ( Xp r- Xp t) ==  (Xp q - Xp t)* a + (Xp s- Xp t) * b).
    -- simpl. unfold order_det in *. rewrite Heqa . rewrite Heqb.
      rewrite Q_mult_div_nom. rewrite Q_mult_div_nom.
       apply det_equation_helper_x. lra.
    -- 
    assert(Hy: ( Yp r- Yp t) ==  (Yp q - Yp t)* a + (Yp s- Yp t) * b).
     simpl. unfold order_det in *. rewrite Heqa . rewrite Heqb.
      rewrite Q_mult_div_nom. rewrite Q_mult_div_nom.
       apply det_equation_helper_y. lra.
      unfold order_det in *. rewrite Hx. rewrite Hy. 
     assert(Hf1:(Xp p - Xp t) * ((Yp q - Yp t) * a + (Yp s - Yp t) * b) == 
            (Xp p - Xp t) * (Yp q - Yp t) * a + (Xp p - Xp t) * (Yp s - Yp t) * b).
       lra. rewrite Hf1.
      assert(Hf2:(Yp p - Yp t) * ((Xp q - Xp t) * a + (Xp s - Xp t) * b) == 
            (Yp p - Yp t) * (Xp q - Xp t) * a + (Yp p - Yp t) * (Xp s - Xp t) * b).
       lra. rewrite Hf2.
    assert (Hf3:(Xp p - Xp t) * (Yp q - Yp t) * a + (Xp p - Xp t) * (Yp s - Yp t) * b -
          ((Yp p - Yp t) * (Xp q - Xp t) * a + (Yp p - Yp t) * (Xp s - Xp t) * b) ==
          ((Xp p - Xp t) * (Yp q - Yp t) - (Yp p - Yp t) * (Xp q - Xp t)) * a +
          ((Xp p - Xp t) * (Yp s - Yp t) - (Yp p - Yp t) * (Xp s - Xp t)) * b).
        lra. rewrite Hf3.
        assert (Hf4:((Xp p - Xp t) * (Yp q - Yp t) - (Yp p - Yp t) * (Xp q - Xp t)) * a < 0).
           apply Q_mult_negpos. tauto. tauto.
         assert (Hf5:((Xp p - Xp t) * (Yp s - Yp t) - (Yp p - Yp t) * (Xp s - Xp t)) * b < 0).
           apply Q_mult_negpos. lra.  tauto.
           apply Q_lt_0_plus. tauto. tauto.
Qed. 