Require Import QArith. 
Require Import Arith.
Require Import Reals.
Require Import Psatz.
Require Import QArith.Qminmax.
Require Import Coq.Arith.PeanoNat.
Require Lra.

Structure Point2D := {
first:> Q;
second:> Q;
}.

Inductive dim: Set := zero : dim | one :dim.

Lemma eq_dim_dec : forall (i:dim)(j:dim), (i=j) + (~i=j).
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
Definition default_point : Point2D := {| first:=0 ; second:=0|}.

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
((first p) * second q) - (first q * second p) - (first p * second r) + 
(first r * second p) + (first q * second r) - (first r * second q).

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























