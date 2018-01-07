Require Import QArith. 
Require Import Arith.
Require Import Reals.
Require Import Psatz.
Require Import QArith.Qminmax.
Require Import Coq.Arith.PeanoNat.
Require Lra.

Structure Point2D := {
fst:> Q;
snd:> Q;
}.
Axiom Q_equality : forall (x y : Q), x == y -> x = y.

Inductive dim: Set := zero : dim | one :dim.

Lemma eq_dim_dec : forall (i:dim)(j:dim), {i=j} + {~i=j}.
Proof.
intros.
induction i .
-induction j.
  + tauto.
  + right. discriminate.
-induction j.
  + right. discriminate.
  + tauto.
Qed.

Definition dart := nat.
Definition eq_dart_dec := eq_nat_dec.
Definition nil := 0%nat.
Definition default_point : Point2D := {| fst:=0 ; snd:=0|}.

Inductive Hmap : Set := 
V : Hmap
| I : Hmap -> dart -> Point2D -> Hmap
| L : Hmap -> dim -> dart -> dart -> Hmap.

Fixpoint fpoint (m:Hmap) (d:dart) : Point2D :=
match m with
V => default_point
| I m0 x p => if eq_dart_dec x d then p else  fpoint m0 d
| L m0 _ _ _ => fpoint m0 d
end.

Fixpoint exd (m:Hmap) (d:dart) : Prop :=
match m with
V => False
| I m0 x _ => x =d \/ exd m0  d
| L m0 _ _ _ => exd m0 d
end.

Fixpoint k_succ (m:Hmap)(k:dim)(d:dart) : dart :=
match m with
V => nil
|I m0 _ _ => k_succ m0 k d
|L m0 k0 x y =>
if eq_dim_dec k k0
then if eq_dart_dec x d then y else k_succ m0 k d
else k_succ m0 k d
end.

Fixpoint k_succ_cl (m:Hmap)(k:dim)(d:dart): dart :=
match m with
V => nil
|I m0 _ _ => k_succ_cl m0 k d
|L m0 k0 x y => 
if eq_dim_dec k k0
  then if eq_dart_dec x d then y else k_succ m0 k d
else k_succ_cl m0 k d
end.

Fixpoint k_pred (m:Hmap)(k:dim)(d:dart) : dart :=
match m with
V => nil
|I m0 _ _ => k_pred m0 k d
|L m0 k0 x y =>
if eq_dim_dec k k0
then if eq_dart_dec y d then x else k_pred m0 k d
else k_pred m0 k d
end.

Definition k_succ_rev := k_pred.

Definition has_succ (m:Hmap)(k:dim)(d:dart) : Prop := k_succ m k d <> nil.
Definition has_pred (m:Hmap)(k:dim)(d:dart) : Prop := k_pred m k d <> nil.

Lemma nat_succ_ne_zero: forall (x:nat) ,S x <> nil.
Proof.
induction x.
- auto.
- unfold nil. lia.
Qed.

Lemma succ_dec: forall (m:Hmap)(k:dim)(d:dart) , has_succ m k d + (~has_succ m k d).
Proof.
intros.
unfold has_succ. remember (k_succ m k d) as x.
induction x.
- tauto.
- left . apply nat_succ_ne_zero.
Qed.

Lemma pred_dec: forall (m:Hmap)(k:dim)(d:dart) , has_pred m k d + (~has_pred m k d).
Proof.
intros.
unfold has_pred. remember (k_pred m k d) as x.
induction x.
- tauto.
- left . apply nat_succ_ne_zero.
Qed.
Definition det (p q r : Point2D) : Q := 
((fst p) * (snd q)) - (fst q )* (snd p) - (fst p) * (snd r) + 
(fst r )* (snd p) + (fst q) * (snd r) - (fst r) * (snd q).

Definition prec_I (m:Hmap)(x:dart) : Prop := x <> nil /\ ~ exd m x.
Definition prec_L (m:Hmap)(k:dim)(x:dart)(y:dart) : Prop :=
exd m x /\ exd m y /\ ~has_succ m k x /\ ~has_pred m k y /\ k_succ_cl m k x <> y.

Fixpoint inv_hmap (m:Hmap) :Prop := 
match m with
V => True
| I m0 x p => inv_hmap m0 /\ prec_I m0 x
| L m0 k x y => inv_hmap m0 /\ prec_L m0 k x y
end.
Definition collinear (x y z :Point2D) : Prop :=
(det x y z) = 0.

Definition noncollinear (m:Hmap) : Prop :=
forall (d1 d2 d3 : dart),
let p1 := (fpoint m d1) in let p2 := (fpoint m d2) in
let p3 := (fpoint m d3) in exd m d1 -> exd m d2 -> exd m d3 ->
p1 <> p2 -> p1 <> p3 -> p2 <> p3 -> ~ collinear p1 p2 p3.

Definition well_emb (m:Hmap) : Prop :=
forall (x:dart), exd m x -> let px := (fpoint m x) in
let x0 := (k_succ m zero x) in let px0 := (fpoint m x0) in
let x1 := (k_succ m one x) in let px1 := (fpoint m x1) in
let x_0 := (k_succ_rev m zero x) in let px_0 := (fpoint m x_0) in
let x_1 := (k_succ_rev m one x) in let px_1 := (fpoint m x_1) in
(has_succ m zero x -> px <> px0) /\ (has_succ m one x -> px = px1) /\
(has_pred m zero x -> px <> px_0) /\ (has_pred m one x -> px = px_1) /\
(forall y:dart, exd m y -> let py := (fpoint m y) in
y <> x -> y <> x1 -> y <> x_1 -> px <> py).

Definition ccw (p q r : Point2D) : Prop := det p q r > 0.
Fixpoint max_dart (m:Hmap) : dart :=
match m with
V => nil
| I m0 x p => if(lt_dec (max_dart m0) x) then x else (max_dart m0) 
| L m0 _ _ _ => (max_dart m0)
end.

Lemma q_lt_bar: forall (x y:Q), ~x<y <-> x>=y.
Proof.
intros. split.
- apply Qnot_lt_le.
- apply Qle_not_lt.
Qed.

Lemma Qlt_dec: forall (x y:Q), {x<y} + {~ x < y}.
Proof.
intros.
case (Qlt_le_dec x y).
-intro. auto.
-intro. apply Qle_not_lt in q. auto.
Qed. 

Lemma ccw_dec: forall (p q r : Point2D) , {ccw p q r} + {~ ccw p q r}.
Proof.
intros.
unfold ccw.
remember (det p q r) as d.
apply Qlt_dec.
Qed.

Fixpoint linkless (m:Hmap) : Prop :=
match m with
V => True
|I m0 _ _ => linkless m0
|L m0 _ _ _ => False
end.

Fixpoint mem_count (m:Hmap) : nat:=
match m with 
V => nil
|I m0 _ _ => mem_count m0 + 1
|L m0 _ _ _ => mem_count m0
end.
Lemma det_colinear: forall (p q:Point2D) , 
~ccw p p q /\ ~ccw p q p /\ ~ccw q p p .
Proof.
intros.
split.
unfold ccw. unfold det. lra.
split. unfold ccw. unfold det. lra. unfold ccw. unfold det. lra.
Qed.
Lemma ccw_not: forall (p q r:Point2D),
ccw p q r -> ~ccw p r q.
Proof.
intros.
unfold ccw in *. unfold det in *. lra.
Qed.
Lemma ccw_cyclity: forall( p r q:Point2D),
ccw p q r -> ccw q r p.
Proof. intros. unfold ccw in *. unfold det in *. lra.
Qed.
Lemma ccw_symm: forall( p q r :Point2D),
ccw p q r -> ~ ccw p r q.
Proof.
intros. unfold ccw in *. unfold det in *. lra.
Qed.
Lemma ccw_inter: forall (p q r t:Point2D),
ccw t q r -> ccw p t r -> ccw p q t -> ccw p q r.
Proof.
intros. unfold ccw in *. unfold det in *. lra.
Qed.

Lemma Q_gt_0_plus : forall (r1 r2 : Q),
  r1 > 0 -> r2 > 0 -> r1 + r2 > 0.
Proof.
intros.
lra.
Qed.
 
Lemma Q_gt_0_mult : forall (r1 r2 : Q),
  r1 > 0 -> r2 > 0 -> r1 * r2 > 0.
Proof. 
intros. assert( 0 * r2 <  r1 * r2).
 apply (Qmult_lt_compat_r 0 r1 r2 ).
- tauto.
- tauto.
- lra.
Qed.
Lemma Q_gt_0_div : forall (r1 r2 : Q),
  r1 > 0 -> r2 > 0 -> r1 * / r2 > 0.
Proof.
intros. 
assert( /r2 > 0).
apply Qinv_lt_0_compat. tauto.
apply Q_gt_0_mult.
tauto. tauto.
Qed.

Lemma Q_mult_div : forall (r1 r2 r3 : Q),
  r1 = r2 * r3 -> r2 > 0 -> (r1 * / r2 = r3).
Proof. 
intros.

assert (r1 * / r2 == r3).
- rewrite H in *. assert(r2*r3 == r3*r2). apply (Qmult_comm ).
  rewrite H1 in *. assert (r2 * / r2 ==1). apply (Qmult_inv_r r2).
  lra. assert(r3 * r2 * / r2 == r3 * (r2 * / r2)).
  lra. rewrite H2 in *. assert (r3 * 1 == r3). lra.
  rewrite H4 in H3. tauto.
- apply Q_equality. tauto.
Qed.

Axiom ccw_trans: forall(p q r t s : Point2D),
(ccw s t p) -> (ccw s t q) -> (ccw s t r) -> (ccw t p q) -> (ccw t q r) -> 
  (ccw t p r).

(*dual transivity for leftdart dl and its next and previous darts dln and dlp
from the point of view p for arbitrary point do*)
Axiom ccw_dual_trans: forall (t s p q r :Point2D),
ccw t s p -> ccw t s r -> ccw t s q -> ccw s p q -> 
ccw s q r -> ccw s p r.
 