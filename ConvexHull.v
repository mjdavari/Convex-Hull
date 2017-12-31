Require Import QArith. 
Require Import Arith.
Require Import Reals.
Require Import Psatz.
Require Import QArith.Qminmax.
Require Import Coq.Arith.PeanoNat.
Require Import 
Require Lra.
Load Hypermap.

Definition prec_CH (m:Hmap) : Prop :=
inv_hmap m /\ linkless m /\ well_emb m /\ noncollinear m.

Definition black_dart (m:Hmap)(d:dart) : Prop :=
~ has_succ m zero d /\ ~ has_succ m one d /\
~ has_pred m zero d /\ ~ has_pred m one d.
Definition blue_dart (m:Hmap)(d:dart) : Prop :=
has_succ m zero d /\ ~ has_succ m one d /\
~ has_pred m zero d /\ has_pred m one d.
Definition red_dart (m:Hmap)(d:dart) : Prop :=
~ has_succ m zero d /\ has_succ m one d /\
has_pred m zero d /\ ~ has_pred m one d.

Lemma black_dart_dec: forall (m:Hmap)(d:dart) , {black_dart m d} + {~black_dart m d}.
Proof.
intros.
unfold black_dart. case (succ_dec m zero d).
-intro. right.  apply not_and_or.
remember (black_dart m d) as bd.

Qed.

Definition convex (m:fmap) : Prop := forall (x:dart)(y:dart),
exd m x -> exd m y -> blue_dart m x ->
let px := (fpoint m x) in let py := (fpoint m y) in
let x0 := (A m zero x) in let px0 := (fpoint m x0) in
px <> py -> px0 <> py -> ccw px px0 py.

Definition visible (m:fmap)(d:dart)(p:point) : Prop :=
if (blue_dart_dec m d)
then (ccw (fpoint m d) p (fpoint m (A m zero d)))
else (ccw (fpoint m (A_1 m zero d)) p (fpoint m d)).

Definition left_dart (m:fmap)(p:point)(d:dart) : Prop :=
blue_dart m d /\ invisible m (A_1 m one d) p /\ visible m d p.
Definition right_dart (m:fmap)(p:point)(d:dart) : Prop :=
red_dart m d /\ visible m d p /\ invisible m (A m one d) p.

Definition CH (m:fmap) : fmap :=
match m with
V=>V
|IVxp=>IVxp
| I (I m0 x1 t1 p1) x2 t2 p2 =>
CHI m0 (CH2 x1 p1 x2 p2 (max_dart m)) ((max_dart m)+3)
|_=>V
end.

Definition CH2 (x1:dart)(p1:point)
(x2:dart)(p2:point)(max:dart) : fmap :=
let m0 := (I (I V x1 p1) x2 p2) in
let m1 := L (I m0 (max+1) p1) one (max+1) x1 in
let m2 := L (I m1 (max+2) p2) one (max+2) x2 in
L (L m2 zero x1 (max+2)) zero x2 (max+1).

Fixpoint CHI (m1:fmap)(m2:fmap)(max:dart) {struct m1} : fmap :=
match m1 with
V=>m2
| I m0 x p => CHI m0 (CHID m2 m2 x p max) (max+1)
|_=>V
end.

Fixpoint submap (m:fmap)(mr:fmap) {struct m} : Prop :=
match m with
V => True
| I m0 x p => submap m0 mr /\ exd mr x /\ (fpoint mr x) = p
| L m0 k x y => submap m0 mr /\
(A mr k x) = y /\ (A_1 mr k y) = x
end.

FixpointCHID (m:fmap)(mr:fmap)(x:dart)(p:point)
 (max:dart) {structm} : fmap :=
 matchm with
 V=>IVxp
 |Im0x0p0=>
 if(blue_dart_dec mr x0)then
 if(invisible_dec mr x0 p) then
 (I (CHID m0 mr x p max) x0 p0)
else if(left_dart_dec mr p x0)then
 (L (L (I (I (CHID m0 mr x p max) x0 p0)
 max p) one max x) zero x0 max)
 else(I (CHID m0 mr x p max) x0 p0)
 else if(red_dart_dec mr x0)then
 if(invisible_dec mr x0 p)then
 (I (CHID m0 mr x p max) x0 p0)
 else if(right_dart_dec mr p x0)then
 (L (I (CHID m0 mr x p max) x0 p0) zero x x0)
 else(CHID m0 mr x p max)
 else(I (CHID m0 mr x p max) x0 p0)
 | L m0 zero x0 y0 =>
 if(invisible_dec mr x0 p)then
 (L (CHID m0 mr x p max) zero x0 y0)
 else(CHID m0 mr x p max)
 | L m0 one x0 y0 =>
 if(invisible_dec mr x0 p)then
 (L (CHID m0 mr x p max) one x0 y0)
 else if(invisible_dec mr y0 p) then
 (L (CHID m0 mr x p max) one x0 y0)
 else(CHID m0 mr x p max)
 end.










