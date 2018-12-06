Require Import QArith. 
Require Import Arith.
Require Import Psatz.
Require Import QArith.Qminmax.
Require Import Coq.Arith.PeanoNat.
Require Import Coq.Logic.Classical_Prop.
Require Import Bool Basics OrdersTac.
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

Definition inv_poly (m:Hmap) : Prop := forall (d:dart),
exd m d -> black_dart m d \/ blue_dart m d \/ red_dart m d.

Lemma black_dart_dec: forall (m:Hmap)(d:dart) , {black_dart m d} + {~black_dart m d}.
Proof.
intros.
unfold black_dart. case (succ_dec m zero d).
-intro. right. intro. tauto.
-intros. case (succ_dec m one d).
  ++intros. right. intro. tauto.
  ++intros. case (pred_dec m zero d).
      -- intros. tauto.
      -- intros. case (pred_dec m one d) .
          +++ tauto.
          +++  intros. tauto.
Qed. 

Lemma blue_dart_dec: forall (m:Hmap)(d:dart) , {blue_dart m d} + {~blue_dart m d}.
Proof.
intros.
unfold blue_dart. case (succ_dec m zero d).
-intro. case (succ_dec m one d). 
    ++  intros. right. intro. tauto.
    ++  intros. case (pred_dec m zero d).
        -- intros. right.  tauto.
        -- intros. case (pred_dec m one d) .
            +++ intros. left. tauto.
            +++  intros. right. intro. tauto.
-intros. right. intro. tauto.
Qed. 

Lemma red_dart_dec: forall (m:Hmap)(d:dart) , {red_dart m d} + {~red_dart m d}.
Proof.
intros.
unfold red_dart. case (succ_dec m zero d).
-intro. right. intro. tauto.
-intros. case (succ_dec m one d).
  ++intros. case (pred_dec m zero d). 
      -- intros. case (pred_dec m one d) . 
          +++right. intro. tauto.
          +++intros. left. tauto. 
      -- intros. tauto.
  ++ intros. right. intro. tauto.
Qed. 
 Lemma dart_color_dec: forall (m:Hmap) (d:dart),
well_emb m -> exd m d-> {red_dart m d} + {black_dart m d} + {blue_dart m d}.
Proof.
intros.
unfold well_emb in *. apply H in H0. clear H. 
intros. unfold red_dart.

Qed.
Definition convex (m:Hmap) : Prop := forall (x:dart)(y:dart),
exd m x -> exd m y -> blue_dart m x ->
let px := (fpoint m x) in let py := (fpoint m y) in
let x0 := (k_succ m zero x) in let px0 := (fpoint m x0) in
px <> py -> px0 <> py -> ccw px px0 py.

Definition visible (m:Hmap)(d:dart)(p:Point2D) : Prop :=
if (blue_dart_dec m d)
then (ccw (fpoint m d) p (fpoint m (k_succ m zero d)))
else (ccw (fpoint m (k_succ_rev m zero d)) p (fpoint m d)).

Definition invisible (m:Hmap)(d:dart)(p:Point2D) : Prop := ~ visible m d p.

Definition left_dart (m:Hmap)(p:Point2D)(d:dart) : Prop :=
blue_dart m d /\ invisible m (k_succ_rev m one d) p /\ visible m d p.
Definition right_dart (m:Hmap)(p:Point2D)(d:dart) : Prop :=
red_dart m d /\ visible m d p /\ invisible m (k_succ m one d) p.

Lemma visible_dec : forall (m:Hmap)(d:dart)(p:Point2D) ,
 {visible m d p} + {~ visible m d p}.
Proof.
intros.
unfold visible.
case (blue_dart_dec m d).
  -intros. case (ccw_dec (fpoint m d) p (fpoint m (k_succ m zero d))).
    ++ tauto.
    ++ tauto.
  - intros. case (ccw_dec (fpoint m (k_succ_rev m zero d)) p (fpoint m d)). 
    ++ tauto.
    ++ tauto.
Qed.
Lemma invisible_dec : forall (m:Hmap)(d:dart)(p:Point2D) ,
 {invisible m d p} + {~ invisible m d p}.
Proof.
intros.
unfold invisible.
case (visible_dec m d p).
  - intros. tauto.
  - intros. tauto.
Qed.
Lemma exist_link: forall(m:Hmap) (d1 d2 d:dart) (k:dim) , exd (L m zero d1 d2) d -> exd m d.
Proof. 
intros.
unfold exd in H. fold exd in H. tauto.
Qed.
Lemma exist_insert: forall(m:Hmap)  (d d1:dart) (p:Point2D) , exd m d -> exd (I m d1 p) d.
Proof. 
intros.
unfold exd. right. fold exd. tauto.
Qed.
Lemma right_dart_dec : forall (m:Hmap)(p:Point2D)(d:dart) , 
{right_dart m p d} +{~ right_dart m p d}.
Proof.
intros.
unfold right_dart.
case (red_dart_dec m d).
- intros. case (visible_dec m d p).
   ++ intros. case (invisible_dec m (k_succ m one d) p).
      --intros. left. auto.
      --intros. right. tauto.
   ++ intros.  right. tauto. 
- intros. right. tauto.
Qed.

Lemma left_dart_dec : forall (m:Hmap)(p:Point2D)(d:dart) ,
 {left_dart m p d} +{~ left_dart m p d}.
Proof.
intros. unfold left_dart.
case (blue_dart_dec m d).
-intros. case (invisible_dec m (k_succ_rev m one d) p).
   ++intros. case (visible_dec m d p).
       --- intros. left. tauto.
       ---intros. right. tauto.
    ++intros. right. tauto.
- intros. right. tauto.
Qed.
Fixpoint submap (m:Hmap)(mr:Hmap): Prop :=
match m with
V => True
| I m0 x p => submap m0 mr /\ exd mr x /\ (fpoint mr x) = p
| L m0 k x y => submap m0 mr /\
(k_succ mr k x) = y /\ (k_succ_rev mr k y) = x
end.

Fixpoint CHID (m:Hmap)(mr:Hmap)(x:dart)(p:Point2D)
 (max:dart) : Hmap :=
 match m with
  V => I V x p
 | I m0 x0 p0 =>
   if(blue_dart_dec mr x0) then
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

Fixpoint CHI (m1:Hmap)(m2:Hmap)(max:dart) : Hmap :=
match m1 with
V=>m2
| I m0 x p => CHI m0 (CHID m2 m2 x p max) ((max + 1)%nat)
|_=>V
end.

Definition CH2 (x1:dart)(p1:Point2D)
(x2:dart)(p2:Point2D)(max:dart) : Hmap :=
let m0 := (I (I V x1 p1) x2 p2) in
let m1 := L (I m0 (max+1)%nat p1) one (max+1)%nat x1 in
let m2 := L (I m1 (max+2)%nat p2) one (max+2)%nat x2 in
L (L m2 zero x1 (max+2)%nat) zero x2 (max+1)%nat.

Definition CH (m:Hmap) : Hmap :=
match m with
V => V
|I V x p => I V x p
| I (I m0 x1 p1) x2 p2 =>
CHI m0 (CH2 x1 p1 x2 p2 (max_dart m)) (((max_dart m)+3)%nat)
|_=>V
end.

Definition half_blue_succ (m:Hmap)(d:dart) : Prop :=
has_succ m zero d /\ ~ has_succ m one d /\
~ has_pred m zero d /\ ~ has_pred m one d.
Definition half_blue_pred (m:Hmap)(d:dart) : Prop :=
~ has_succ m zero d /\ ~ has_succ m one d /\
~ has_pred m zero d /\ has_pred m one d.

Lemma helper1 : forall (m:Hmap)(d d0: dart)(p :Point2D) ,
exd (I m d0 p) d -> ~ d=d0 -> exd m d.
Proof.
intros. 
unfold exd in H. case H.
-intros. symmetry in H1. tauto.
-intro. fold exd in H1. tauto.
Qed.

Lemma helper2 : forall (m:Hmap)(d : dart)(p :Point2D) ,
exd (I m d p) d .
Proof.
intros.
unfold exd. tauto.
Qed.
Lemma helper3 : forall (m mr:Hmap) (x d d1 d2 max:dart) (d0:dim)(p:Point2D) , 
exd (CHID m mr x p max) d -> exd (CHID (L m d0 d1 d2) mr x p max) d.
Proof.
intros.
induction d0.
- unfold CHID. case (invisible_dec mr d1 p).
  +intro. unfold exd. fold exd. fold CHID. auto.
  +intro. auto.
- unfold CHID. case (invisible_dec mr d1 p). 
  +intro. unfold exd. fold exd. fold CHID. auto.
  +intro. case (invisible_dec mr d2 p). 
    --intro.  unfold exd. fold exd. fold CHID. auto.
    --intro. fold CHID. auto.
Qed.
Lemma submap_insert: forall(m mr:Hmap) (d0:dart) (p:Point2D), submap (I m d0 p) mr -> submap m mr.
Proof.
intros. unfold submap in H.  fold submap in H. tauto.
Qed.
Lemma submap_link: forall(m mr:Hmap) (d1 d2:dart) (d:dim), submap (L m d d1 d2) mr -> submap m mr.
Proof.
intros. unfold submap in H.  fold submap in H. tauto.
Qed.
Lemma submap_insert_rev: forall (m mr:Hmap) (d:dart) (p:Point2D),
~exd m d -> submap m (I mr d p) -> submap m mr.
Proof.
intros. induction m.
- tauto.
- simpl in *. split.
  + apply IHm. 
    -- tauto.
    --  tauto.
  + split.
    --apply proj2 in H0. apply proj1 in H0. case H0.
      ++ intro. apply not_or_and in H. rewrite H1 in H.  tauto.
      ++ intro. auto.
    -- apply not_or_and in H. apply proj2 in H0. apply proj2 in H0.
       case (eq_dart_dec d d0) in H0. 
      ++ rewrite e in H. tauto.
      ++  auto.
 - simpl in *. split.
   + apply IHm. 
     -- auto.
     --  tauto.
   + tauto.
Qed.
Lemma submap_exist_rel: forall (m mr:Hmap) (d:dart),
submap m mr -> exd m d -> exd mr d.
Proof.
intros.
induction m.
-tauto.
- simpl in *. case H0.
  + intro. rewrite H1 in H. tauto.
  + intro. tauto.
- simpl in *. tauto. 
Qed.
Fixpoint distinct_members (m:Hmap): Prop :=
match m with
| V => True
| I m0 d _ => ~ exd m0 d /\ distinct_members m0
| L m0 _ _ _ => distinct_members m0
end.
Lemma dis_mem_ins_rev  :
forall (m:Hmap) (d:dart) (p:Point2D) , 
~exd m d /\ distinct_members m -> distinct_members (I m d p).
Proof.
intros.  simpl in *. tauto.
Qed.
(*Lemma submap_inv_hmap: forall(m mr:Hmap) ,
 distinct_members m -> submap m mr -> inv_hmap mr-> inv_hmap m.
Proof.
intros.
induction m.
-  simpl. tauto.
- assert (exd mr d).
  * simpl in H0. tauto.
  * simpl. split.
      + apply IHm.
        -- simpl in H. tauto.
        -- simpl in *. tauto.
      + assert (submap m mr).
        -- simpl in *. tauto.
        -- unfold prec_I. split.
          ++ clear H H0 IHm H3. induction mr.
             --- tauto.
             --- simpl in *. unfold prec_I in H1. case H2.
                 +++ intro. rewrite H in H1. tauto.
                 +++ intro. apply IHmr.
                    ** tauto.
                    **  tauto.
             --- simpl in *. tauto.
          ++ clear H0 H1 IHm H2 H3. induction m.
             --- tauto.
             --- simpl in* . intro . assert(distinct_members (I m d p)).
                  +++ simpl. tauto. 
                  +++ tauto.
             --- simpl. apply IHm. simpl. tauto.
- assert(exd mr d0).
  + unfold submap 
  +  apply IHm.
    --tauto.
    -- tauto.
  + unfold prec_L. split.
    -- 
     
Qed.*)
Lemma blue_dart_CHID_1 :
forall (m mr:Hmap)(x:dart)(px:Point2D)(max:dart)(d:dart),
blue_dart mr d -> exd m d -> exd (CHID m mr x px max) d.
Proof.
intros.
induction m.
- tauto.
- simpl. case (blue_dart_dec mr d0).
  ++intros. case (invisible_dec mr d0 px).
      -- intros. case (eq_dart_dec d d0).
         +++ intro. rewrite e. apply helper2.
         +++ intro. elim H0. 
             --- intro. symmetry in H1. tauto. 
             --- intro. simpl. right. tauto.
      --intro. case (left_dart_dec mr px d0).
        +++intro. case (eq_dart_dec d d0).
            ---intro. rewrite e. unfold exd. right. auto.
            ---intro. unfold exd. right. right. fold exd.
               apply IHm. apply (helper1 m d d0 p).
               ++++tauto.
               ++++tauto.
        +++ intro. case (eq_dart_dec d d0).
            ---intro. rewrite e. apply helper2.
            ---intro. unfold exd in H0. case H0.
               ++++intro. symmetry in H1. tauto.
               ++++intro. fold exd in H1. clear H0. 
                   unfold exd. right. fold exd. apply IHm. tauto.
  ++ intro. case(red_dart_dec mr d0).
      --intro. case (invisible_dec mr d0 px).
        +++intro. case (eq_dart_dec d0 d).
            ---intro. rewrite e. apply helper2.
            ---intro. unfold exd. right. fold exd.
               apply IHm. apply (helper1 m d d0 p).
               ++++ tauto.
               ++++ auto.
        +++intro. case (eq_dart_dec d0 d).
            ---intro. case (right_dart_dec mr px d0).
                ++++ intro. unfold exd.  tauto.
                ++++ intro. apply IHm. rewrite e in n. tauto.
            ---intro. case (right_dart_dec mr px d0).
                ++++ intro. unfold exd. right. fold exd.
                     apply IHm. apply (helper1 m d d0 p).
                     ---- tauto.
                     ---- auto.
                ++++intro. apply IHm. apply (helper1 m d d0 p).
                     ---- tauto.
                     ---- auto.
    --intro. case (eq_dart_dec d d0).
       +++ intro. rewrite e in H. tauto.
       +++ intro. unfold exd. right. fold exd. apply IHm.
           apply (helper1 m d d0 p).
          --- tauto.
          --- tauto.
- unfold exd. fold exd. apply helper3. apply IHm.
  unfold exd in H0. fold exd in H0. auto.
Qed.

Lemma blue_dart_CHID_11 :
forall (m mr:Hmap)(x:dart)(px:Point2D)(max:dart)(d:dart),
submap m mr -> d <> x -> exd m d -> blue_dart mr d ->
visible mr d px -> invisible mr (k_succ_rev mr one d) px ->
k_succ (CHID m mr x px max) zero d = max.
Proof.
intros.
induction m.
- unfold exd in H1. tauto.
- simpl. case (blue_dart_dec mr d0).
  +intro. case (invisible_dec mr d0 px).
    --intro. unfold k_succ. fold k_succ. apply IHm.
      ++ unfold submap in H. simpl. fold submap in H. tauto.
      ++ apply (helper1 m d d0 p).
         --- tauto.
         --- intro. rewrite H5 in H3. unfold invisible in i. auto.
    --intro. case(left_dart_dec mr px d0).
      ++intro. unfold k_succ. fold k_succ. case (eq_dart_dec d0 d).
            +++intro. case (eq_dim_dec zero one).
                ----intro. discriminate.
                ----intro. case(eq_dim_dec zero zero).
                    ++++intro. auto.
                    ++++intro. apply IHm.
                        ** apply (submap_insert m mr d0 px). tauto.
                        ** tauto.
            +++intro. case (eq_dim_dec zero zero).
               ----intro. case (eq_dim_dec zero one).
                   ++++intro. discriminate.
                   ++++intro. apply IHm.
                       **  apply (submap_insert m mr d0 p). tauto.
                       ** apply (helper1 m d d0 p).
                          ***auto.
                          *** auto.
               ----intro. tauto.
      ++intro. apply IHm.
        --- apply (submap_insert m mr d0 p). tauto.
        --- case(eq_dart_dec d d0).
            +++ intro. unfold left_dart in n0. apply not_and_or in n0.
                case n0.
                * intro. tauto.
                * intro. apply not_and_or in H5. case H5.
                  ** intro. rewrite e in H4. tauto.
                  ** intro. tauto. 
            +++ intro. apply (helper1 m d d0 p).
               * tauto.
               * tauto.
  +intro. case (red_dart_dec mr d0).
    --intro. case (invisible_dec mr d0 px).
       ++ intro. unfold k_succ. fold k_succ. apply IHm.
           --- apply (submap_insert m mr d0 p). tauto.
           --- case (eq_dart_dec d d0).
               +++ intro. rewrite e in H2. tauto.
               +++ intro. apply (helper1 m d d0 p).
                   * tauto.
                   * tauto.
       ++ intro. case (right_dart_dec mr px d0).
          --- intro. case (eq_dart_dec d d0).
              +++ intro. rewrite e in H2. tauto.
              +++ intro. unfold k_succ. fold k_succ. case (eq_dim_dec zero zero).
                  ----intro. case (eq_dart_dec x d).
                      * intro. symmetry in e0. tauto.
                      * intro. apply IHm.
                        **  apply (submap_insert m mr d0 p). tauto.
                        ** apply (helper1 m d d0 p).
                          *** tauto.
                          *** tauto.
                  ----intro. apply IHm.
                      * apply (submap_insert m mr d0 p). tauto.
                      * apply (helper1 m d d0 p).
                        ** tauto.
                        ** tauto.
          --- intro. apply IHm.
              +++ apply (submap_insert m mr d0 p). tauto.
              +++ apply (helper1 m d d0 p).
                  * tauto.
                  * intro. rewrite H5 in H2. tauto.
   -- intro. apply IHm.
      ++ apply (submap_insert m mr d0 p). tauto.
      ++  apply (helper1 m d d0 p).
          ---tauto.
          --- intro. rewrite H5 in H2. tauto.
- simpl. induction d0.
  + case(invisible_dec mr d1 px).
    -- intro. case(eq_dart_dec d d2).
        ++intro. unfold k_succ. fold k_succ. case (eq_dim_dec zero zero). 
             ---intro. case (eq_dart_dec d1 d).
                +++intro. unfold invisible in i. rewrite e1 in i. tauto.
                +++intro. apply IHm.
                    * apply (submap_link m mr d1 d2 zero ). tauto.
                    * apply (exist_link m d1 d2 d zero). tauto.
             ---intro. tauto. 
        ++intro. unfold k_succ. fold k_succ.  case (eq_dim_dec zero zero).
            ---intro. case(eq_dart_dec d1 d).
                * intro. rewrite e0 in i. unfold invisible in i. tauto.
                * intro. apply IHm. 
                  ** apply (submap_link m mr d1 d2 zero ). tauto.
                  ** apply (exist_link m d1 d2 d zero). tauto.
            ---intro. tauto.
     -- intro. apply IHm.  
        ++ apply (submap_link m mr d1 d2 zero ). tauto.
        ++ apply (exist_link m d1 d2 d zero). tauto.
  + case(invisible_dec mr d1 px).
    -- intro. unfold k_succ. fold k_succ. case (eq_dim_dec zero one).
        ++ intro. discriminate.
        ++ intro. apply IHm.
            --- apply (submap_link m mr d1 d2 one ). tauto.
            ---apply (exist_link m d1 d2 d one). tauto.
    -- intro. case (invisible_dec mr d2 px).
        +++ intro. unfold k_succ. fold k_succ. case (eq_dim_dec zero one).
            * intro. discriminate.
            *intro. apply IHm.
               ** apply (submap_link m mr d1 d2 one ). tauto.
               ** apply (exist_link m d1 d2 d one). tauto.
        +++ intro. apply IHm.
            * apply (submap_link m mr d1 d2 one ). tauto.
            * apply (exist_link m d1 d2 d one). tauto.
Qed.
Lemma exd_dec : forall (m:Hmap) (d:dart) ,{exd m d} + {~ exd m d}.
Proof.
intros.
induction m.
- tauto.
- case IHm.
  + intro. left. apply (exist_insert  m d d0 p). auto.
  + intro. case (eq_dart_dec d d0).
    --intro. left. unfold exd. left. auto.
    --intro. right. intro. unfold exd in H. fold exd in H. case H.
       ++ intro. symmetry in H0. auto.
       ++ intro. auto.
- case IHm.
  +intro. auto.
  +intro. auto.
Qed.

Lemma noncolinear_insert: forall (m:Hmap) (x:dart) (p:Point2D),
~ exd m x -> noncollinear (I m x p) -> noncollinear m.
Proof.
intros.
unfold noncollinear. intros. unfold noncollinear in H.
unfold noncollinear in H0. simpl in *.
specialize H0 with d1 d2 d3.
intro.
apply H0.
 - auto.
 - auto.
 - auto.
 - case (eq_dart_dec x d1).
   + intro. rewrite e in H. tauto.
   +  intro. case (eq_dart_dec x d2).
      -- intro. rewrite e in H. tauto.
      -- intro. auto.
 -case (eq_dart_dec x d1).
   + intro. rewrite e in H. tauto.
   +  intro. case (eq_dart_dec x d2).
      -- intro. rewrite e in H. tauto.
      -- intro. case (eq_dart_dec x d3).
         ++ intro. rewrite e in H. tauto.
         ++ intro. tauto.
 -case (eq_dart_dec x d1).
   + intro. rewrite e in H. tauto.
   +  intro. case (eq_dart_dec x d2).
      -- intro. rewrite e in H. tauto.
      -- intro. case (eq_dart_dec x d3).
         ++ intro. rewrite e in H. tauto.
         ++ intro. tauto.
-  case (eq_dart_dec x d1).
   + intro. rewrite e in H. tauto.
   +  intro. case (eq_dart_dec x d2).
      -- intro. rewrite e in H. tauto.
      -- intro. case (eq_dart_dec x d3).
         ++ intro. rewrite e in H. tauto.
         ++ intro. auto.
Qed.
Lemma linkless_inser: forall (m:Hmap) (x:dart) (p:Point2D),
linkless (I m x p) <-> linkless m.
Proof.
intros. split. 
-intro. tauto.
- intro. tauto. 
Qed.
Lemma linkless_exist_succ: forall (m:Hmap) (x:dart) (d:dim), 
linkless m -> ~ has_succ m d x.
Proof.
intros. intro. induction m.
- auto.
- simpl in *. auto.
-  simpl in *. auto.
Qed.
Lemma linkless_exist_pred: forall (m:Hmap) (x:dart) (d:dim), 
linkless m -> ~ has_pred m d x.
Proof.
intros. intro. induction m.
- auto.
- simpl in *. auto.
-  simpl in *. auto.
Qed.
Lemma well_emb_insert: forall (m:Hmap) (d:dart)(p:Point2D),
linkless m -> ~ exd m d -> well_emb( I m d p) -> well_emb (m).
Proof.
intros.
unfold well_emb in *. intros. split.
- intro. specialize H1 with x. case H1.
  + apply exist_insert. auto.
  + intros. simpl in *. clear H1. clear H5. 
    apply (linkless_exist_succ m x zero) in H. auto.
- split. 
  + intro. apply (linkless_exist_succ m x one) in H. tauto.
  + split. 
     -- intro.  apply (linkless_exist_pred m x zero) in H. tauto.
     -- split.
        ++  intro.  apply (linkless_exist_pred m x one) in H. tauto.
        ++ intros. specialize H1 with x. apply proj2 in H1.
           apply proj2 in H1. apply proj2 in H1. apply proj2 in H1.
               specialize H1 with y.  assert( exd (I m d p) y).
           --- apply exist_insert. auto.
           --- apply H1 in H6.
             +++ simpl in *. case(eq_dart_dec d x) in H6.
               * rewrite e in H0. auto.
               * intro. case(eq_dart_dec d y) in H6.
                  ** rewrite e in H0. auto.
                  ** auto. 
            +++ auto.
            +++ auto.
            +++ auto.
          --- apply exist_insert. auto.
Qed.
Lemma prec_insert: forall (m:Hmap)(d:dart)(p:Point2D),
  prec_CH (I m d p) -> prec_CH m .
Proof.
intros. induction m.
- unfold prec_CH in *. simpl in *. split.
  * auto.
  * split.
    ** auto.
    ** split.
        *** unfold well_emb. tauto. 
        *** unfold noncollinear . intros. auto.
- unfold prec_CH. simpl in *. split.
  * unfold prec_CH in *. simpl in *. tauto. 
  * unfold prec_CH in *. simpl in *. split.
    ** tauto.
    ** split. 
       *** apply (well_emb_insert (I m d0 p0) d p).
           + tauto. 
           + unfold prec_I in H. tauto.
           + tauto.
       *** apply (noncolinear_insert (I m d0 p0) d p).
          + unfold prec_I in H. tauto.
          + tauto.
- unfold prec_CH in *. simpl in *. tauto.
Qed.
Lemma inv_hmap_nil: forall(m :Hmap) (d:dart), 
 exd m d -> inv_hmap m  -> d<>nil.
Proof.
intros.
induction m.
- tauto.
- simpl in *. elim H. 
    +intros. elim H0. intros. unfold prec_I in H3. 
      rewrite H1 in H3. tauto.
    +intros. tauto.
- simpl in *. tauto.  
Qed.
Lemma CHID_exd_m: forall (m mr :Hmap) (d:dart) (x:dart)(p:Point2D) (max:nat),
~exd m d -> ~x=d -> (max > d)%nat ->~exd (CHID m mr x p max) d.
Proof.
intros.
induction m.
- simpl in*.  tauto.
- simpl in *. case(blue_dart_dec mr d0).
   + intro. case (invisible_dec mr d0 p).
      -- intro. simpl in *. intro. elim H1.
          tauto. intro. tauto.
      -- intro. case(left_dart_dec mr p d0).
         intro. simpl in *. intro. elim H2.
         intro. rewrite H3 in H1. lia.
         intro. tauto.
         intro. simpl in *. intro.
         tauto. 
   + intro. case(red_dart_dec mr d0).
      -- intro. case(invisible_dec mr d0 p).
          ++ intro. simpl in *. intro. tauto.
          ++ intros.  case(right_dart_dec mr p d0).
             intro. simpl in *. tauto. 
             intro. tauto.
      -- intro. simpl in *. tauto.
- simpl in *.  case d0.
   +case (invisible_dec mr d1 p).  
      --intro. simpl in *. tauto.
      -- intro. tauto.
  + case(invisible_dec mr d1 p).
      --intro. simpl in *. tauto.
      --intro. case (invisible_dec mr d2 p).
          ++ intro. simpl in *. tauto.
          ++ intro. tauto.
Qed.
Lemma max_dart_h1: forall(m: Hmap) (d:dart),
exd m d -> (d > max_dart m)%nat -> False.
Proof.
intros. induction m.
- tauto.
- simpl in H. simpl in H0.  case (lt_dec (max_dart m) d0) in H0.
  + elim H.
    -- intro. rewrite H1 in  *. apply (lt_irrefl d) in H0. tauto.
    -- intro. apply IHm.
       ++ tauto.
       ++ lia.
  + elim H.
    -- intro. rewrite H1 in n. lia.
    -- intro. tauto.
- simpl in *. tauto.  
Qed.
Lemma CHID_point_exd: forall(m mr :Hmap) (d:dart) (x:dart)(p:Point2D) (max:nat) ,
exd (CHID m mr x p max) x.
Proof.
intros.
induction m.
- simpl in *. tauto.
- simpl in *. case(blue_dart_dec mr d0).
  + case(invisible_dec mr d0 p).
    --intros. simpl in *. right. tauto.
    -- intros.  case(left_dart_dec mr p d0).
        ++ intros. simpl in *.  tauto.
        ++ intros. simpl in *.  tauto.
  + intros. case(red_dart_dec mr d0).
    -- intros. case(invisible_dec mr d0 p).
        ++ intros. simpl in *.  tauto.
        ++ intros. case(right_dart_dec mr p d0).
           intros. simpl in *. tauto. intro. tauto.
    -- intro. simpl in *. tauto.
- simpl in *. case d0.
   + case ( invisible_dec mr d1 p).
      -- intro. simpl in *. tauto.
      -- intro.  tauto.
  +case (invisible_dec mr d1 p).
      -- intro. simpl in *. tauto.
      -- intro. case (invisible_dec mr d2 p).
          intro. tauto.
          intro. tauto.
Qed.
(*Lemma CHID_inv_hmap: forall(m mr:Hmap)  (x max :dart) (p:Point2D),
distinct_members m -> ~x = nil ->  ~exd m x -> (max > (max_dart mr))%nat ->
submap m mr -> inv_hmap mr -> inv_hmap (CHID m mr x p max).
Proof. 
intros.
induction m.
- unfold CHID. unfold inv_hmap. unfold prec_I. tauto.
-  simpl. simpl in H.  case (blue_dart_dec mr d).
  + intro. case (invisible_dec mr d p).
    -- intro. simpl. split.
       ++ simpl in H3. simpl in H1. apply IHm. tauto. tauto.
          simpl in H2. tauto.
           
       ++ simpl in H3. unfold prec_I. split.
          --- apply (inv_hmap_nil mr d). tauto. tauto. 
          --- clear IHm. induction m .
              +++ simpl. unfold exd in H1. 
                  intro. elim H1. case H5. intro.
                   symmetry in H6. tauto. intro.  auto.
              +++ simpl in H1. assert( ~ exd (I m d0 p1) d ). tauto.
                  simpl in H5.
                  simpl. case (blue_dart_dec mr d0).
                    *  intro. case(invisible_dec mr d0 p).
                        ** intro. simpl.  apply and_not_or. split.
                           *** apply not_or_and in H5. tauto.
                           *** apply IHm.
                                split. tauto. elim H. intros. simpl in H7. tauto.
                                 simpl. intro. elim H6. intro. tauto.
                                intro. tauto. simpl. 
                                split. simpl in H3. tauto.
                                split. simpl in H3. tauto.
                                simpl in H3. tauto.                               
                        ** intros. case (left_dart_dec mr p d0).
                            *** intros. simpl. intro. unfold left_dart in l.
                                unfold invisible in i.
                                 elim H6. 
                                intros.  unfold invisible in n.
                                rewrite H7 in H2. apply ( max_dart_h1 mr d). tauto. tauto.
                                intro. elim H7.
                                intro. tauto. intros. apply IHm.
                                split. tauto. simpl in H. tauto.
                                simpl. tauto. simpl. split. simpl in H2. simpl in H3.  tauto.
                                split. apply not_or_and in H1. elim H1. intros.
                                simpl in H2. tauto. simpl in H2. tauto. tauto.                               
                            *** intros. simpl. intro. apply IHm.
                                split. tauto. simpl in H. tauto.
                                simpl in H. simpl. tauto. simpl in H3. simpl.
                                tauto. elim H6. intro. tauto. intros. tauto.
                    * intros admit.  case(invisible_dec mr d0 p).
                        ** intro. case(red_dart_dec mr d0 ).
                           *** intro. simpl. apply and_not_or. split.
                                tauto. apply IHm. simpl in H1. split.  tauto.
                                simpl in H. tauto. simpl. apply and_not_or .
                                tauto. simpl. simpl in H3. tauto.
                           *** intro. simpl. apply and_not_or. split.
                                intro. apply not_or_and in H5. tauto.
                                apply IHm. simpl in *. tauto.
                                simpl in *. tauto. simpl in *. tauto.
                        ** intros. case(red_dart_dec mr d0 ). 
                            ***intros. case (right_dart_dec mr p d0). 
                               intros. simpl in *. tauto.
                               intros. simpl in *. tauto.
                            *** intros. simpl in *. tauto.
            +++ simpl in *. case d0. 
                * case (invisible_dec mr d1 p). 
                   ** intros. simpl in *. tauto.
                   ** intros. tauto.
                * case (invisible_dec mr d1 p).
                   ** intros. simpl in *. tauto.
                   ** intros. case(invisible_dec mr d2 p).
                      *** intros. simpl in *. tauto.
                      *** intros. tauto.
    -- intros. case (left_dart_dec mr p d).
       ++intros. simpl in *. split.
          ---  split.
               +++ split.
                   * split.
                     ** tauto. 
                     ** unfold prec_I. split. apply (inv_hmap_nil mr d).
                        tauto. tauto.
                        clear IHm.
                        induction m.
                        *** simpl in *. apply and_not_or. 
                            apply not_or_and in H1. split. intro.
                             symmetry in H5. tauto.  tauto.
                        *** simpl in *.  case(blue_dart_dec mr d0).
                            intros. case(invisible_dec mr d0 p).
                            intros. simpl in *. intro. elim H5.
                            intro. apply proj1 in H . apply not_or_and in H. tauto.
                            intro. tauto.
                            intros. case (left_dart_dec mr p d0).
                            simpl in *. intro. intro. elim H5. 
                            intro.  apply ( max_dart_h1 mr d).
                             tauto. rewrite H6 in H2. tauto.                            
                            intro. tauto.
                            intros. simpl in *. intro. tauto.
                            intros. case (red_dart_dec mr d0).
                            intros. case(invisible_dec mr d0 p).
                            intros. simpl in *. tauto.
                            intros. case(right_dart_dec mr p d0).
                            intros. simpl in *. intro. tauto.
                            intros. tauto.
                            intros. simpl. tauto.
                        *** simpl in *. case d0.
                             case( invisible_dec mr d1 p).
                            intros. simpl in *. tauto.
                            intros. tauto.
                            case (invisible_dec mr d1 p).
                            intro. simpl in *. tauto.
                            intro. case (invisible_dec mr d2 p).
                            intro. tauto.
                            intro. tauto.
                * simpl. unfold prec_I. split. admit. simpl. intro.
                   elim H5. intro. rewrite <- H6 in H2. 
                   apply ( max_dart_h1 mr d). tauto. tauto.
                   intro. admit.
            +++ unfold prec_L. split. simpl. tauto.
                split. simpl. . admit. split. intro.
                unfold has_succ in H4. simpl in H4. admit.
                split. intro. unfold has_succ in H4. simpl in H4.
                admit. admit.
     --- admit.
   ++ admit. 
  + admit.
-admit.
                  
 simpl in H1. assert(submap m mr). tauto.
              apply IHm in H2.
              induction mr.
              +++ simpl.  tauto.
              +++ fold inv_hmap in *. unfold CHID.
Qed.*)
Lemma dart_nil_dec: forall(d:dart) ,
{d=nil} + {(d > nil) %nat}.
Proof.
intro.
induction d.
- apply(zerop nil).
- simpl. case IHd.
  + intro. right. rewrite e. lia.
  + intro. right. assert (S d > d)%nat. lia. 
    apply (gt_trans (S d) d nil). tauto. tauto. 
Qed.
Lemma succ_pred: forall(m:Hmap) (d:dim)(d1:dart),
inv_hmap m -> has_pred m d d1 -> has_succ m d (k_pred m d d1).
Proof.
intros.
induction m.
-tauto.
- simpl in *. unfold has_succ in *. unfold has_pred in *. tauto.
-unfold has_pred in *. simpl in *. case(eq_dim_dec d d0) in *.
  + case(eq_dart_dec d3 d1) in *.
    -- unfold has_succ. simpl. case (eq_dim_dec d d0).
        ++ intro. case(eq_dart_dec d2 d2). intro.
               unfold prec_L in H. intro. rewrite H1 in H. 
              assert(exd m nil). tauto. apply (inv_hmap_nil m nil). tauto.
              tauto. tauto.
           intro. tauto.
        ++ intro. tauto.
    -- unfold has_succ. simpl.  case (eq_dim_dec d d0).
        ++ intro. case (eq_dart_dec d2 (k_pred m d d1)).
           intro.  unfold prec_L in H. intro. rewrite H1 in H. 
              assert(exd m nil). tauto. apply (inv_hmap_nil m nil). tauto.
              tauto. tauto.
           intro. tauto. 
        ++ intro. tauto.
  + unfold has_succ. simpl. case (eq_dim_dec d d0).
    -- intro. case(eq_dart_dec d2 (k_pred m d d1)).
       ++ intro. tauto.
       ++ intro. tauto.
    -- intro. tauto.
Qed.
Lemma pred_fpoint_eq: forall(m:Hmap) (d: dart),
well_emb m -> exd m d -> blue_dart m d -> fpoint m d = fpoint m (k_pred m one d).
Proof.
intros.
unfold well_emb in *.
specialize H with d. apply H in H0.
unfold blue_dart in *. apply proj2 in H1. apply proj2 in H1. apply proj2 in H1.
apply proj2 in H0. apply proj2 in H0. apply proj2 in H0. apply proj1 in H0.
apply H0 in H1. unfold k_succ_rev in *. tauto.
Qed.
Lemma submap_fpoint: forall (m mr :Hmap) (d:dart),
submap m mr -> exd m d-> fpoint m d = fpoint mr d.
Proof.
intros.
induction m.
- tauto.
- simpl in *.
  case (eq_dart_dec d0 d) in *.
  + rewrite e in *. symmetry. tauto.
  + tauto.
- simpl in *. tauto.
Qed. 
Lemma submap_noncollinear: forall (m mr : Hmap),
submap m mr -> noncollinear mr -> noncollinear m.
Proof.
intros.
unfold noncollinear in *.
intros. specialize H0 with d1 d2 d3.
assert (exd mr d1). apply (submap_exist_rel m mr d1 ). tauto. tauto.
assert (exd mr d2). apply (submap_exist_rel m mr d2 ). tauto. tauto.
assert (exd mr d3). apply (submap_exist_rel m mr d3 ). tauto. tauto.
assert (fpoint m d1 = fpoint mr d1).
apply (submap_fpoint m mr d1). tauto. tauto.
assert (fpoint m d2 = fpoint mr d2).
apply (submap_fpoint m mr d2). tauto. tauto.
assert (fpoint m d3 = fpoint mr d3).
apply (submap_fpoint m mr d3). tauto. tauto.

rewrite <- H10 in H0. rewrite <- H11 in H0. rewrite <- H12 in H0.
 tauto.
Qed.
Lemma left_dart_h1: forall(m mr :Hmap) (d1 d2 dnew:dart) ,
inv_hmap m -> well_emb m-> submap m mr-> noncollinear mr -> convex m ->
exd mr dnew -> exd m d1 -> exd m d2 -> left_dart m (fpoint mr dnew) d1 ->
 ccw (fpoint m d1) (fpoint mr dnew) (fpoint m d2).
Proof.
intros.
remember (fpoint mr dnew) as p.
unfold left_dart in *.
elim H7. intro. intro. elim H9. intro. intro.
unfold invisible in *. unfold visible in *. case(blue_dart_dec m (k_succ_rev m one d1)) in *.
- unfold k_succ_rev in *.  unfold blue_dart in *. 
     apply proj2 in b. apply proj1 in b. apply proj2 in H8. apply proj2 in H8. apply proj2 in H8.
      assert (False). apply (succ_pred) in H8.
      tauto.  tauto. tauto.
- case(blue_dart_dec m d1) in *.
  + unfold k_succ_rev in *. simpl in *. 
    remember (fpoint m d1) as pd1. remember (fpoint m d2) as pd2. 
    remember (fpoint m (k_pred m zero (k_pred m one d1))) as pred.
    remember (fpoint m (k_succ m zero d1)) as pnex. 
    
    apply (ccw_dual_trans pred pd1 p pnex pd2).
    -- assert(fpoint m (k_pred m one d1) = pd1).  
        ++ unfold blue_dart in b. symmetry. rewrite Heqpd1. apply (pred_fpoint_eq m d1).  (*fpoint d1 and k_pred one d1 are same from blue_dart*)
           tauto. tauto. tauto.                   
        ++ rewrite  H12 in H7. assert(~ ccw pred p pd1). tauto.
         apply ccw_not_col . tauto.
         unfold noncollinear in *. 
        specialize H2 with (k_pred m zero (k_pred m one d1)) dnew d1.
        
        assert(fpoint m (k_pred m zero (k_pred m one d1)) = fpoint mr (k_pred m zero (k_pred m one d1))).
         apply submap_fpoint. tauto. case (dart_color_dec m (k_pred m one d1)).   
        tauto. 
          admit. 
       rewrite  Heqpred . rewrite Heqpd1 . rewrite Heqp . 
         assert(fpoint m d1 = fpoint mr d1).
          apply submap_fpoint. tauto. tauto. 
          rewrite H15.          apply H2.
         apply(submap_exist_rel m mr (k_pred m zero (k_pred m one d1))).
           tauto. admit.
           tauto. apply (submap_exist_rel m mr d1). tauto. tauto.
           admit.
            admit. admit. 
         
    -- admit. (* results from convexity and blue_dart d1*)
    -- admit. (* results from blue_dart d1*)
    --tauto.
    -- admit. (* results from blue_dart d1*)
  + tauto.      

Lemma left_dart_uniq: forall (mr: Hmap) (d1 d2 :dart) (p:Point2D),
convex mr -> exd mr d1 -> exd mr d2 -> left_dart mr p d1 -> left_dart mr p d2 -> d1 = d2.
Proof. 
intros. unfold convex in *. specialize H with d1 d2. unfold blue_dart in *.  simpl in *. tauto.
-  unfold convex in H. specialize H with d1 d2. 
   simpl in *. case (eq_dart_dec d d1) in *.
    + case (eq_dart_dec d d2) in *.
       -- rewrite e in e0. tauto.
       -- case(eq_dart_dec d (k_succ mr zero d1)).
          ++ intro. admit. (* self loop on d*)
          ++ intro. case(eq_dart_dec d (k_succ mr zero d1)) in *.
             --- admit. (*self loop on d*)
             --- rewrite e in *. unfold left_dart in H0. admit.
    + case(eq_dart_dec d (k_succ mr zero d1)) in *.
        -- case(eq_dart_dec d d2) in *.
           ++ admit.
           ++ admit.
        -- case(eq_dart_dec d d2) in *.
           ++  admit.
           ++ admit.
- admit.
Qed.
Lemma CHID_blue_left_nexd: forall (m mr:Hmap) (d x:dart)(p:Point2D)(max:dart),
blue_dart mr d -> visible mr d p -> left_dart mr p d -> ~ exd m d 
-> submap m mr -> (max > (max_dart mr))%nat /\ (max > x)%nat 
-> ~ exd (CHID m mr x p max) max.
Proof.
intros. induction m.
- simpl. intro. case H5. intro. rewrite H6 in H4. lia. tauto.
-  simpl in *. case (blue_dart_dec mr d0).
   + intro. case(invisible_dec mr d0 p  ).
      -- intro. simpl. intro. elim H5. intro. 
          rewrite <- H6 in H4. apply (max_dart_h1 mr d0).  tauto. 
          tauto.
          intro. tauto.
      -- intro. case (left_dart_dec mr p d0).
          ++ intro. simpl in *. intro. admit.
          ++ intro. simpl. intro. elim H5.  intro.  
             rewrite <- H6 in H4. apply (max_dart_h1 mr d0). tauto.
             tauto. 
             intro. tauto.
    + intro. case (red_dart_dec mr d0).
       -- intro. case (invisible_dec mr d0 p).
          ++ intro. simpl. intro. elim H5.
             intro. apply (max_dart_h1 mr d0). tauto. rewrite <- H6 in H4. tauto.
             intro. tauto.
          ++ intro. case (right_dart_dec mr p d0).
             intro. simpl. intro.  elim H5. intro. rewrite<- H6 in H4.
             apply (max_dart_h1 mr d0). tauto. tauto.
             intro. tauto.
             intro. tauto.
      -- intro. simpl. intro. elim H5. intro. rewrite <- H6 in H4. 
         apply (max_dart_h1 mr d0). tauto. tauto.
         intro. tauto.
- simpl. case d0.
   + case (invisible_dec mr d1 p).
      -- intro. simpl in *.   tauto.
      -- intro. simpl in *. tauto.
   + case (invisible_dec mr d1 p).
      -- intro. simpl in *. tauto.
      -- intro. case (invisible_dec mr d2 p).
          ++ intro. simpl in *. tauto.
          ++  intro. simpl in *. tauto.
Qed.
Lemma CHID_inv_hmap_h1:forall(m mr:Hmap) (x:dart)(p:Point2D)(max:dart) ,
 submap m mr -> inv_hmap mr -> inv_hmap m-> convex mr -> x <> nil -> ~exd mr x 
-> (max > x)%nat /\ (max > max_dart mr)%nat
 ->inv_hmap (CHID m mr x p max).
Proof.
intros. induction m.
-simpl. unfold prec_I. tauto.
-simpl. case (blue_dart_dec mr d).
    + intro. case (invisible_dec mr d p).
        -- intro. simpl. split.
            ++ simpl in H. simpl in H1. tauto.
            ++ unfold prec_I. split. simpl in H. 
               apply (inv_hmap_nil mr d).
               tauto. tauto.
                simpl in H. simpl in H1. unfold prec_I in *|-.
                assert(inv_hmap (CHID m mr x p max)). tauto.
                induction m.
                --- simpl in *. unfold prec_I in *.
                    elim H. intros. intro. case H9. intros.
                     rewrite <- H10 in H. tauto.  tauto.
                --- simpl in *. case(blue_dart_dec mr d0) in *.
                     +++ intro. case (invisible_dec mr d0 p) in *.
                         * simpl in *. tauto. 
                         * simpl in *. case(left_dart_dec mr p d0) in *.
                             simpl in *. elim H7. intro. rewrite H8 in H5.
                             apply proj2 in H5. apply (max_dart_h1 mr d). tauto. 
                             tauto. intro.  tauto. simpl in *. tauto. 
                     +++ intro. case(red_dart_dec mr d0) in *.
                         * case(invisible_dec mr d0 p) in *. 
                            simpl in *. tauto. case(right_dart_dec mr p d0) in *.
                            simpl in *. tauto. tauto.
                         * simpl in *. tauto.
                 --- simpl in *. case d0 in *.
                      +++ case (invisible_dec mr d1 p) in *.
                          * simpl in *. tauto.
                          * tauto.
                      +++ case(invisible_dec mr d1 p) in *.
                          * simpl in *. tauto.
                          * case (invisible_dec mr d2 p) in *.
                                simpl in *. tauto.
                                tauto.
         -- intro. case(left_dart_dec mr p d) in *.
             ++ simpl in *. split. split.  split. split. 
                tauto. unfold prec_I. split.  apply (inv_hmap_nil mr d). tauto.
                tauto. apply (CHID_exd_m m mr d x p max ). 
                unfold prec_I in *. tauto. intro. rewrite H6 in H4. tauto.
                assert(~ max_dart mr < d)%nat. intro. apply (max_dart_h1 mr d).
                tauto. lia. apply not_lt in H6. lia.  
                unfold prec_I. split. intro. rewrite H6 in H5. case(dart_nil_dec  x).
                intro. tauto.  intro. lia.
                
                simpl in *. intro. elim H6.
                intro. admit. 
                intro. unfold prec_I in *. admit.
                unfold prec_L.  simpl in *. split.
                tauto. split. right.  right. apply CHID_point_exd.  tauto.
                split. unfold has_succ. simpl in *. admit. 
                split. unfold has_pred. simpl in *. admit.
                admit. 
                 unfold prec_L. simpl in *. split.
                tauto. split. right.  right. admit.
                split. unfold has_succ. simpl in *. admit. 
                split. unfold has_pred. simpl in *. admit.
                admit. 
             ++ simpl in *. split. tauto. unfold prec_I.
                split. admit. admit.
    + intro. case(red_dart_dec mr d).
       -- intro. case(invisible_dec mr d p).
          ++ intro. simpl in *. split. tauto.
             unfold prec_I. split. admit. admit.
          ++ intro. case(right_dart_dec mr p d).
             intro. simpl in *. split. split. tauto.
             unfold prec_I. split. admit.  admit.
             unfold prec_L. split. simpl. admit. 
             simpl. split.   admit.
             simpl.  split.  unfold has_succ.
             simpl. admit.
             split. unfold has_succ.  admit.
             admit.
            intro. simpl in *.  tauto.
       -- intro. simpl in *. split. tauto .
          unfold prec_I. split. admit. admit.
- simpl in *. case d.
   + case ( invisible_dec mr d0 p). 
      --intro. simpl in *. split. tauto.
        unfold prec_L. split. admit.
        split. admit. split. admit. split. admit. admit.
      -- intro. tauto.
  + case (invisible_dec mr d0 p).
    -- intro. simpl in *. split. tauto.
        admit.
    -- intro. case(invisible_dec mr d1 p).
        ++ intro. simpl in *. split. tauto.
            admit.
        ++ intro. tauto.
Qed.
Lemma CHID_inv_hmap: forall(mr:Hmap) (x:dart)(p:Point2D)(max:dart) ,
convex mr ->x<>nil -> (max > x /\ max > max_dart mr)%nat -> inv_hmap (CHID mr mr x p max).
Proof.
intros.
induction mr.
- simpl. unfold prec_I. tauto.
- simpl. case (blue_dart_dec (I mr d p0) d).
    + intro. case (invisible_dec (I mr d p0) d p).
        -- intro. simpl. split.
           ++ apply CHID_inv_hmap_h1.
Qed.

Lemma CHI_inv_hmap: forall(m mr:Hmap) ,
submap m mr -> inv_hmap mr -> convex mr ->
-> inv_hmap (CHI m mr x p max).
Proof.
intros. 
induction m.
- simpl. auto.
- simpl. case (lt_dec (max_dart m) d). 
  + intros. induction mr.
    -- simpl. admit.
    -- remember (I mr d0 p0) as t in *. simpl. case (blue_dart_dec (I mr d0 p0) d0).
       ++ intro.  case(invisible_dec (I mr d0 p0) d0 p).
            --- intro. unfold CHID. simpl.
  + unfold CHID.  case (blue_dart_dec (I t d0 p0) d0).
  -- intro. case (invisible_dec (I t d0 p0) d0 p).
     ++ intros. fold CHID. case (invisible_dec (I t d p) d p).
        --- intros. case(invisible_dec (I t d p) d p0).
            +++ intros. 
Qed. 
Theorem inv_hmap_CH : forall (m:Hmap),
prec_CH m -> inv_hmap (CH m).
Proof.
intros.
induction m.
- unfold CH. unfold prec_CH in H. tauto.
-  unfold CH. 
    case m in *.
   + simpl.  unfold prec_CH in H. tauto.
    + simpl. case (lt_dec (if lt_dec (max_dart m) d0 then d0 else max_dart m)).
      -- intro.  case (lt_dec (max_dart m)) in l.
          ++ unfold .  admit.
          ++ admit.
      --  intros. case (if lt_dec (max_dart m) d0 then d0 else max_dart m).
          ++ admit.
          ++ intros. admit.
    + admit.
- simpl. tauto.
Qed.
Theorem exd_CH : forall (m:fmap)(d:dart), prec_CH m ->
exd m d -> exd (CH m) d /\ fpoint m d = fpoint (CH m) d.

Theorem one_left : forall (m:fmap)(p:point)(x:dart)(y:dart),
inv_hmap m -> inv_poly m -> well_emb m ->
inv_noncollinear_points m p -> convex m ->
left_dart m p x -> left_dart m p y -> x = y.

Theorem exd_left_dart_exd_right_dart :
forall (m:fmap)(px:point), inv_hmap m -> inv_poly m ->
(exists da:dart, exd m da /\ left_dart m px da) ->
(exists db:dart, exd m db /\ right_dart m px db).

Lemma blue_dart_not_right_dart_until_i_visible_i :
forall (m:fmap)(d:dart)(p:point)(i:nat), inv_hmap m ->
inv_poly m -> exd m d -> blue_dart m d -> visible m d p ->
let iter0 := (A m zero (Iter (cF m) j d)) in
(forall (j:nat), j <= i -> ~ right_dart m p iter0) ->
visible m (Iter (cF m) i d) p.

Theorem well_emb_CH : forall (m:fmap),
prec_CH (m) -> well_emb (CH m).



Theorem inv_poly_CH : forall (m:Hmap),
prec_CH m -> inv_poly (CH m).

Theorem convex_CH : forall (m:fmap),
prec_CH m -> convex (CH m).










