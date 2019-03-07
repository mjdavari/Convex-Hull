Require Import Arith.
Require Import Reals.
Require Import Psatz.
Require Import Coq.Init.Nat.
Require Import QArith. 
Require Import QArith.QArith_base.
Require Import Coq.Arith.PeanoNat.
Require Import ZArith.
Require Import BinNat Bool Equalities GenericMinMax
 OrdersFacts ZAxioms ZProperties.
Require Import BinIntDef BinInt Zorder Zcompare Znat Zmin Zmax Zminmax
 Zabs Zeven auxiliary ZArith_dec Zbool Zmisc Wf_Z  
 Zcomplements Zsqrt_compat Zpow_def Zpow_alt Zpower Zdiv Zwf  Int Zpow_facts Zdigits.
Require BinIntDef.
Require Lra.
Require Import Ring.
Axiom Q_equality : forall (q1 q2 : Q), q1 == q2 -> q1 = q2.


Lemma Qlt_dec: forall (q1 q2:Q), {q1<q2} + {~ q1 < q2}.
Proof.
intros.
case (Qlt_le_dec q1 q2).
-intro. auto.
-intro. apply Qle_not_lt in q. auto.
Defined. 

Lemma Q_mult_dist: forall (a b c : Q) , a * (b - c) == a * b - a * c.
Proof. intros. lra. Qed.

Lemma Q_mult: forall (a b c d : Q), (a - b) * (c - d) == a*c - a*d - b*c + b*d.
Proof. intros.
 lra. Qed. 
Lemma Qle_neq_lt : forall (r1 r2 : Q),
  r1 <= r2 -> r1 <> r2 -> r1 < r2.
Proof.
intros r1 r2 H1 H2. apply Qle_lteq in H1. destruct H1.  
tauto. apply Q_equality in H. tauto.
Qed.

Lemma Q_gt_0_plus : forall (r1 r2 : Q),
  r1 > 0 -> r2 > 0 -> r1 + r2 > 0.
Proof.
intros r1 r2 H1 H2. lra.
Qed.
Lemma Q_gt_0_mult : forall (r1 r2 : Q),
  r1 > 0 -> r2 > 0 -> r1 * r2 > 0.
Proof.
intros. assert (H1:= Qmult_lt_compat_r 0 r1 r2) . 
apply H1 in H0. - lra. - tauto.
Qed.

Lemma Q_gt_0_div : forall (r1 r2 : Q),
  r1 > 0 -> r2 > 0 -> r1 * / r2 > 0.
Proof.
intros r1 r2 H1 H2.
apply Q_gt_0_mult.
 assumption. apply Qinv_lt_0_compat . tauto.
Qed.
Lemma Q_lt_0_plus : forall (r1 r2 : Q),
  r1 < 0 -> r2 < 0 -> r1 + r2 < 0.
Proof.
intros r1 r2 H1 H2. lra.
Qed.
Lemma Z_neg_mult: forall (a b:Z) , (a < 0)%Z -> (b<0)%Z -> (a*b >0)%Z.
Proof.
intros.
assert(H2:=Z.mul_neg_neg a b). apply Zgt_iff_lt. tauto.
Qed.

Lemma Q_lt_0_mult : forall (r1 r2 : Q),
  r1 < 0 -> r2 < 0 -> r1 * r2 > 0.
Proof.
intros. 
 unfold Qgt in *. simpl in *. rewrite Z.mul_comm in H.
 rewrite Z.mul_1_l in H.  rewrite Z.mul_comm in H0.
 rewrite Z.mul_1_l in H0. rewrite <- Z.gt_lt_iff in H. rewrite <- Z.gt_lt_iff in H0.
rewrite <- Z.gt_lt_iff . rewrite Z.mul_comm. rewrite Z.mul_1_l.
apply Zgt_iff_lt. apply (Z.mul_neg_neg (Qnum r1) (Qnum r2)).
apply Zgt_iff_lt in H. tauto. apply Zgt_iff_lt in H0. tauto.
Qed.
Lemma Q_lt_0_neg: forall(a:Q) , a<0 -> -a > 0.
Proof. intros.
apply Qlt_minus_iff in H.
assert (H1:= (Qplus_0_l (-a)) ). rewrite H1 in H. tauto.
Qed.
Lemma Q_gt_0_neg: forall(a:Q) , a>0 -> -a < 0.
Proof. intros. lra.
Qed.
Lemma Q_mult_negpos: forall (a b:Q) , a<0 -> b>0 -> a * b < 0.
Proof.
intros. 
 apply Q_lt_0_neg in H.   assert (H2:-a * b > 0).
 apply (Q_gt_0_mult ). tauto. tauto. 
lra.
Qed.
Lemma Q_lt_0_div : forall (r1 r2 : Q),
  r1 < 0 -> r2 < 0 -> 0 <r1  */ r2 .
Proof.
intros.
apply Q_lt_0_mult. tauto. apply Q_lt_0_neg in H0.
apply Qinv_lt_0_compat in H0. apply Q_gt_0_neg in H0. 
induction r2. simpl in *. unfold Qinv in *. simpl.
induction Qnum. simpl in *. lra. tauto. tauto.
Qed.
Lemma Q_mult_div : forall (r1 r2 r3 : Q),
  r1 = r2 * r3 -> r2 > 0 -> r1 * / r2 = r3.
Proof.
intros r1 r2 r3 H1 H2.
subst r1. assert (H:=Qmult_comm r2 r3). apply Q_equality in H.
rewrite H. assert (H1:= Qdiv_mult_l r3 r2). apply Q_equality. apply H1.
lra.
Qed.
 
Lemma Q_mult_dist_eq: forall(r1 r2 r3 r4 :Q),
(r1-r2)*(r3-r4)=r1*r3-r1*r4-r2*r3+r2*r4.
Proof.
intros. assert (H: (r1 - r2) * (r3 - r4) == r1 * r3 - r1 * r4 - r2 * r3 + r2 * r4).
apply Q_mult.
apply Q_equality. tauto.
Qed.

Lemma Q_mult_par: forall (a b c :Q), a* (b * c) == a* b * c.
Proof. intros. lra.
Qed.

Lemma Qmult_minus_dist : forall (a b c :Q) , a * (b  -  c) == a* b - a*c.
Proof.
intros. lra.
Qed.
Lemma Q_mult_sign_ch:forall (a b :Q) , a * (-b) == (-a) * b.
Proof.
intros. lra. 
Qed. 

Lemma Q_inv_sign_ch:forall (a b :Q) , a */ (-b) == (-a) */ b.
Proof. intros. induction b. induction a.

 unfold Qinv in *. simpl.
induction (Qnum ). simpl in *. lra. simpl. unfold Qeq. simpl. lia.
simpl. unfold Qeq. simpl. lia.
Qed. 
Lemma Q_div_sign_ch: forall (a b :Q) ,  a / -b == -a / b.
Proof. intros.
 unfold Qdiv. rewrite Q_inv_sign_ch. lra.
Qed.
Lemma Q_div_plus_denum: forall(a b c:Q) , a/b + c/b == (a+c)/b.
Proof. intros. unfold Qdiv. lra.
Qed.
Lemma Q_div_minus_denum: forall(a b c:Q) , a/b - c/b == (a-c)/b.
Proof. intros. unfold Qdiv. lra.
Qed.
Lemma Q_mult_div_nom: forall (a b c:Q) , a * (b/c) == (a *b) / c.
Proof. intros.
unfold Qdiv. lra.
Qed.
