
Require Import Arith.
Require Import Reals.
Require Import Psatz.
Require Import Coq.Init.Nat.
Require Import QArith. 
Require Import QArith.QArith_base.
Require Import Coq.Arith.PeanoNat.
Require Lra.
Require Import Omega.
Require Import Wellfounded.
 Require Import Coq.Arith.Wf_nat. Require Import Coq.Wellfounded.Wellfounded. 
Load CpdtTactics.
Require Import Orders.
Require Import Sorting.
Require Import Sorted.
Require Import Sorting.Mergesort.

Require Import MyQ.
Require Import Point2D.

Section projections.
  Context {A : Type} {B : Type}.

  Definition first (p:A * B) := match p with
                                | (x, y) => x
                              end.
  Definition second (p:A * B) := match p with
                                | (x, y) => y
                              end.
End projections.

(* we use a nat to simplify checking for existance and equality of points
   and prevent numerical error due to equality deciding *)


Inductive ListP : Set := 
Lz : ListP
| LI :  nat -> Point2D -> ListP->ListP.

Fixpoint cnt (l:ListP) : nat :=
match l with
Lz => 0
| LI id p l0 => 1 + (cnt l0)
end.

Fixpoint link (l1:ListP) (l2:ListP) : (ListP) :=
match l2 with
Lz => l1
| LI id pt l0 => LI id pt (link l1 l0)
end.

Fixpoint sublist (l:ListP) (i:nat) (j:nat) : ListP :=
if( eq_nat_dec i 0) then
    if (eq_nat_dec j 0) then
        Lz
    else 
          match l with
          Lz => Lz
          | LI  id pt l0 => LI id pt (sublist l0 i (j-1))
          end
else
  match l with
  Lz => Lz
  |LI id pt l0 => sublist l0 (i-1) j 
  end
.
(* LI 3 ({|fst:=1;snd:=1|}) (LI 2 ({|fst:=1;snd:=1|})
 (LI 1 ({|fst:=1;snd:=1|}) Lz)  )

Compute sublist  (LI 3 ({|fst:=1;snd:=1|}) (LI 2 ({|fst:=1;snd:=1|})
 (LI 1 ({|fst:=1;snd:=1|}) Lz)  )) 0 6.
*)

(*==============================================================*)
(*====================== merge sort by  x-axis  ================*)
(*==============================================================*)

Fixpoint insert_in_list (l:ListP)(id:nat)(pt:Point2D): ListP := 
match l with
Lz => LI id pt Lz
| LI id1 pt1 l0 => 
  if(Qlt_dec (Xp pt1) (Xp pt)) then
    LI id1 pt1 (insert_in_list  l0 id pt)
  else if(Qlt_dec (Xp pt) (Xp pt1)) then
          LI id pt l
        else if(Qlt_dec (Yp pt) (Yp pt1)) then
                           LI id pt l
                     else if(Qlt_dec (Yp pt1) (Yp pt)) then
                         LI id1 pt1 (insert_in_list  l0 id pt)
                          else 
                               LI id pt l
end.

Fixpoint merge (l1:ListP) (l2:ListP) : (ListP) :=
match l1 with
Lz  => l2
| LI id1 pt1 l10 =>
   insert_in_list (merge l10 l2) id1 pt1
end.

Fixpoint break_list (l:ListP)(i j :nat): (ListP) :=
if(eq_nat_dec i 1) then
  match l with 
      Lz => Lz
      | LI id pt l0 => if (eq_nat_dec j 1) then
                          LI id pt Lz
                       else 
                          LI id pt (break_list l0 i (j - 1))
  end
else
    match l with 
      Lz => Lz
      | LI id pt l0 => break_list l0 (i - 1) j
    end.

Fixpoint split (ls : ListP) : ListP * ListP :=
    match ls with
      | Lz => (Lz, Lz)
      | LI id pt Lz => (LI id pt Lz, Lz)
      | LI id1 pt1 (  LI id2 pt2 ls') =>
        let (ls1, ls2) := split ls' in
          (LI id1 pt1 ls1, LI id2 pt2 ls2)
    end.

(*================ Wellformness ================*)
Definition lengthOrder (ls1 ls2 : ListP) :=
    (lt (cnt ls1) (cnt ls2) ).

Hint Constructors Acc.

  Lemma lengthOrder_wf' : forall len, forall ls, ((cnt ls) <= len)%nat -> Acc lengthOrder ls.
    unfold lengthOrder; induction len; crush.
  Defined.

Theorem lengthOrder_wf : well_founded lengthOrder.
    red; intro; eapply lengthOrder_wf'; eauto.
  Defined.


Lemma split_wf : forall len ls, (2 <= cnt ls <= len)%nat
    -> let (ls1, ls2) := split ls in
      lengthOrder ls1 ls /\ lengthOrder ls2 ls.
    unfold lengthOrder; induction len; crush; do 2 (destruct ls; crush);
      destruct (le_lt_dec 2 (cnt ls));
        repeat (match goal with
                  | [ _ : (cnt ?E < 2)%nat |- _ ] => destruct E
                  | [ _ : (S (cnt ?E) < 2)%nat |- _ ] => destruct E
                  | [ IH : _ |- context[split ?L] ] =>
                    specialize (IH L); destruct (split L); destruct IH
                end; crush).
  Defined.
Ltac split_wf := intros ls ?; intros; generalize (@split_wf (cnt ls) ls);
    destruct (split ls); destruct 1; crush.

Lemma split_wf1 : forall ls, (2 <= cnt ls)%nat
    -> lengthOrder (first (split ls)) ls.
    split_wf.
  Defined.

Lemma split_wf2 : forall ls, (2 <= cnt ls)%nat
    -> lengthOrder (second (split ls)) ls.
    split_wf.
  Defined.

  Hint Resolve split_wf1 split_wf2.
(*================ Wellformness ================*)


(*================ MERGE SORT ================*)

Definition mergeSort : ListP -> ListP.
    refine (Fix lengthOrder_wf (fun _ => ListP)
      (fun (ls : ListP)
        (mergeSort : forall ls' : ListP, lengthOrder ls' ls -> ListP) =>
        if le_lt_dec 2 (cnt ls)
          then let lss := split ls in
            merge (mergeSort (first lss) _) (mergeSort (second lss) _)
          else ls)); subst lss; eauto.
  Defined.
(*================ MERGE SORT ================*)

Definition PointOrderByX_le (pt1 pt2 : Point2D) : Prop := 
let x1 := (Xp pt1) in let y1 := (Yp pt1) in let x2 := (Xp pt2) in let y2 := (Yp pt2) in
 if(Qlt_dec  x1 x2) then
    True
  else if(Qlt_dec x2 x1 ) then
          False
        else if(Qlt_dec  y1 y2 ) then
                          True
                     else if(Qlt_dec y2 y1) then
                         False
                          else 
                               True.


Lemma PointOrderByX_le_dec: forall (pt1 pt2: Point2D) , {PointOrderByX_le pt1 pt2}
 + {~PointOrderByX_le pt1 pt2}.
Proof.
intros. 
unfold PointOrderByX_le. 
  case (Qlt_dec (Xp pt1) (Xp pt2)).
    - intros. auto.
    - intros.  case (Qlt_dec (Xp pt2) (Xp pt1)).
        + intros. tauto.  
        + intros. case (Qlt_dec (Yp pt1) (Yp pt2)).
          -- intros. tauto.
          -- intros. case (Qlt_dec (Yp pt2) (Yp pt1)).
             ++ intros. tauto.
             ++ intros. tauto.      
Defined.
Fixpoint is_sorted (ls : ListP) : Prop :=
   match ls with
|Lz => True
| LI id1 pt1 ls1 =>
      match ls1 with
      | Lz => True
      | LI id2 pt2 ls2 =>  if(PointOrderByX_le_dec pt1 pt2) then is_sorted ls1
                           else False    
      end
end.



Lemma single_sort: forall (a:Point2D) (id:nat ), is_sorted (LI id a Lz).
Proof.
intros.
unfold is_sorted.
tauto.
Qed.


Lemma empty_list_is_sorted:is_sorted (Lz).
Proof.
unfold is_sorted.
tauto.
Qed.

Lemma insert_sub :forall (p:Point2D) (id:nat) (ls:ListP), 
is_sorted (LI id p ls)-> is_sorted ls.
Proof.
intros.  unfold is_sorted in *.
induction ls.
- tauto.
-  case (PointOrderByX_le_dec p p0) in *.
  + intros. fold is_sorted in *. tauto.
  + tauto.
Qed.

Lemma sorted_helper1: forall (p:Point2D) (id:nat) (ls:ListP),
is_sorted (LI id p ls) -> is_sorted ls.
Proof. intros. unfold is_sorted in H. fold is_sorted in H.
 simpl in *. induction ls.
  - tauto.
  - case(PointOrderByX_le_dec p p0) in *.
    ++ tauto.
    ++  tauto.
Qed. 

Lemma sorted_helper2: forall (pt1 pt2: Point2D)(id1 id2 :nat) (ls:ListP),
PointOrderByX_le pt1 pt2 -> is_sorted (LI id2 pt2 ls) -> is_sorted(LI id1 pt1 (LI id2 pt2 ls)).
Proof.
intros. simpl. case(PointOrderByX_le_dec pt1 pt2).
- intros. induction ls.
  + tauto.
  + case(PointOrderByX_le_dec pt2 p0). 
    -- intros. apply sorted_helper1 in H0. tauto.
    -- intros. simpl in H0. case (PointOrderByX_le_dec pt2 p0) in *.
       ++  tauto.
       ++  tauto.
- intros. tauto.
Qed.

Lemma insert_works : forall (p:Point2D) (id:nat) (ls:ListP),
 is_sorted ls -> is_sorted(insert_in_list ls id p).
Proof.
intros. induction ls.
  - tauto.
  - induction ls.
    + simpl . case (Qlt_dec  (Xp p0) (Xp p)).
      -- intros. simpl. case (PointOrderByX_le_dec p0 p).
         ++ tauto.
         ++ intros. unfold PointOrderByX_le in *. case (Qlt_dec (Xp p0) (Xp p)) in *. tauto. tauto.
      -- intros. simpl in *.  case (Qlt_dec  (Xp p) (Xp p0)).
         ++ intros. simpl. case(PointOrderByX_le_dec p p0).
            * tauto.
            * intros. unfold PointOrderByX_le in *. case(Qlt_dec (Xp p) (Xp p0)) in *.
              ** tauto.
              ** case(Qlt_dec (Xp p0) (Xp p)) in *. tauto. tauto.
         ++ intros. case(Qlt_dec (Yp p) (Yp p0)).
            * intros. simpl. case(PointOrderByX_le_dec p p0).
              ** intros. tauto. 
              ** intros. unfold PointOrderByX_le in *. case (Qlt_dec (Xp p) (Xp p0)) in *.
                 *** tauto.
                 *** case(Qlt_dec (Xp p0) (Xp p)) in *. tauto.
                     **** case (Qlt_dec (Yp p) (Yp p0)) in *. tauto. tauto.
            * intros. case(Qlt_dec (Yp p0) (Yp p)).
              ** intros. simpl. case (PointOrderByX_le_dec p0 p) in *. tauto.
                 *** unfold PointOrderByX_le in *. case (Qlt_dec (Xp p) (Xp p0)) in *.
                    **** tauto.
                    **** case(Qlt_dec (Xp p0) (Xp p)) in *. tauto.
                        --- case (Qlt_dec (Yp p0) (Yp p)) in *. tauto. tauto.
              ** intros. simpl. case (PointOrderByX_le_dec p p0) in *. tauto.
                 ***  unfold PointOrderByX_le in *. case (Qlt_dec (Xp p) (Xp p0)) in *.
                    **** tauto.
                    **** case (Qlt_dec (Xp p0) (Xp p)) in *. tauto.
                         case(Qlt_dec (Yp p) (Yp p0)) in *. tauto. 
                         case (Qlt_dec (Yp p0) (Yp p)) in *. tauto. tauto.
    + unfold insert_in_list in *. fold insert_in_list in *.
      case(Qlt_dec (Xp p0) (Xp p)) in *.
      -- intros. case(Qlt_dec (Xp p1) (Xp p)) in *.
         ++ unfold is_sorted. fold is_sorted. case(PointOrderByX_le_dec p0 p1). intros.
            --- destruct (insert_in_list ls id p). tauto. case (PointOrderByX_le_dec p1 p3).
                +++ intros. apply sorted_helper1 in H. apply IHls in H.
                    apply sorted_helper1 in H. tauto.
                +++ intros. apply sorted_helper1 in H.  apply IHls in H.
                    simpl in H. case(PointOrderByX_le_dec p1 p3) in *. tauto. tauto.
            ---  intros. simpl in H. case(PointOrderByX_le_dec p0 p1) in *. tauto. tauto.
         ++ unfold is_sorted. fold is_sorted. case(Qlt_dec (Xp p) (Xp p1)) in *.
            --- case (PointOrderByX_le_dec p0 p).
                +++ intros. apply IHls. apply sorted_helper1 in H. tauto.
                +++ intros. unfold PointOrderByX_le in n2. case(Qlt_dec (Xp p0) (Xp p)) in *.
                    * tauto. 
                    * tauto.
            ---  intros. case(Qlt_dec (Yp p) (Yp p1)) in *. 
                +++ case(PointOrderByX_le_dec p0 p). 
                    * intros. apply IHls. apply sorted_helper1 in H. tauto.
                    * intros. unfold PointOrderByX_le in *. case(Qlt_dec (Xp p0) (Xp p)) in *.
                       ** tauto.
                       ** tauto.
                +++ case (Qlt_dec (Yp p1) (Yp p)) in *.
                    * case(PointOrderByX_le_dec p0 p1) in *. 
                      ** apply IHls.  apply sorted_helper1 in H. tauto.
                      ** simpl in H. case (PointOrderByX_le_dec p0 p1) in *.
                         *** tauto.
                         *** tauto.
                   * case (PointOrderByX_le_dec p0 p) in *.
                      ** apply IHls. apply sorted_helper1 in H. tauto.
                      ** unfold PointOrderByX_le in *. case (Qlt_dec (Xp p0) (Xp p)) in *.
                         *** tauto. 
                         *** tauto.
      -- simpl. case(Qlt_dec (Xp p) (Xp p0)) in *.
         ++ apply sorted_helper2. 
            * unfold PointOrderByX_le. case(Qlt_dec (Xp p) (Xp p0)) in *.
              ** tauto.
              ** tauto.
            * tauto.
         ++ case(Qlt_dec (Yp p) (Yp p0)) in *.
            * intros. simpl. case(PointOrderByX_le_dec p p0).
              ** intros. tauto. 
              ** intros. unfold PointOrderByX_le in *. case (Qlt_dec (Xp p) (Xp p0)) in *.
                 *** tauto.
                 *** case(Qlt_dec (Xp p0) (Xp p)) in *. tauto.
                     **** case (Qlt_dec (Yp p) (Yp p0)) in *. tauto. tauto.
              
            * intros. case(Qlt_dec (Yp p0) (Yp p)) in *.
              ** intros. simpl. case (Qlt_dec (Xp p1) (Xp p)) in *. 
                 *** case(PointOrderByX_le_dec p0 p1).
                     **** intros. apply IHls. apply sorted_helper1 in H. tauto.
                     **** intros. simpl in H. case (PointOrderByX_le_dec p0 p1) in *. tauto. tauto.
                 *** case(Qlt_dec (Xp p) (Xp p1)) in *.
                     **** case(PointOrderByX_le_dec p0 p).
                          --- intros. apply IHls. apply sorted_helper1 in H. tauto.
                          --- intros. unfold PointOrderByX_le in*. case(Qlt_dec (Xp p0) (Xp p)) in *.
                             +++ tauto.
                             +++ case(Qlt_dec (Xp p) (Xp p0)) in *. tauto. case(Qlt_dec (Yp p0) (Yp p)) in *. 
                                 tauto. tauto.
                     **** case(Qlt_dec (Yp p) (Yp p1)) in *.
                          --- case(PointOrderByX_le_dec p0 p).
                             +++ intros. apply IHls. apply sorted_helper1 in H. tauto.
                             +++ intros. unfold PointOrderByX_le in*. case(Qlt_dec (Xp p0) (Xp p)) in *.
                                ---- tauto.
                                ---- case(Qlt_dec (Xp p) (Xp p0)) in *. tauto. case(Qlt_dec (Yp p0) (Yp p)) in *. 
                                 tauto. tauto.
                          --- case(Qlt_dec (Yp p1) (Yp p)) in *.
                             +++ case(PointOrderByX_le_dec p0 p1).
                                 ---- intros. apply IHls. apply sorted_helper1 in H. tauto.
                                 ---- intros.  simpl in H. case (PointOrderByX_le_dec p0 p1) in *. tauto.
                                     tauto.                                    
                             +++ case(PointOrderByX_le_dec p0 p).
                                 ---- intros. apply IHls. apply sorted_helper1 in H. tauto.
                                 ---- intros. unfold PointOrderByX_le in *. case(Qlt_dec (Xp p0) (Xp p)) in *.
                                      tauto. case (Qlt_dec (Xp p) (Xp p0)) in *. tauto. 
                                      case(Qlt_dec (Yp p0) (Yp p)) in *. tauto. tauto.
               ** apply sorted_helper2.
                  *** unfold PointOrderByX_le. case (Qlt_dec (Xp p) (Xp p0)).
                     **** tauto.
                     **** intros. case(Qlt_dec (Xp p0) (Xp p)). intros. tauto. intros.
                          case(Qlt_dec (Yp p) (Yp p0)).   intros. tauto. intros.
                          case(Qlt_dec (Yp p0) (Yp p)). intros. tauto. tauto.
                  *** tauto.
Qed.

Lemma merge_keeps_sorted: forall ls1 ls2 , is_sorted ls1 -> is_sorted ls2 -> is_sorted(merge ls1 ls2).
Proof.
intros. induction ls1.
- simpl. tauto.
- simpl. apply sorted_helper1 in H. apply  IHls1 in H.
  apply insert_works. tauto.
Qed.


Module PointOrderByX <: TotalLeBool.
  Definition t := Point2D.
  Definition leb pt1 pt2 := if PointOrderByX_le_dec pt1 pt2 then true else false.
  Theorem leb_total : forall pt1 pt2, leb pt1 pt2 =true\/ leb  pt2 pt1 = true.
Proof. intros. unfold leb. case(PointOrderByX_le_dec pt1 pt2).
  + intros. tauto. + intros. case(PointOrderByX_le_dec pt2 pt1).
    intros. tauto. intros. unfold PointOrderByX_le in *. left.
    case (Qlt_dec (Xp pt1) (Xp pt2)) in *. tauto. case(Qlt_dec (Xp pt2) (Xp pt1)) in *.
    tauto. case(Qlt_dec (Yp pt1) (Yp pt2)) in *. tauto.
    case(Qlt_dec (Yp pt2) (Yp pt1)) in *. tauto. tauto.    Qed.


End PointOrderByX.




(* Module NatOrder: TotalLeBool.
  Definition t := nat.
  Fixpoint leb n1 n2 :=
    match n1, n2 with
    | 0%nat, _ => true
    | _, 0%nat => false
    | S n1', S n2' => leb n1' n2'
    end.
Check leb.
 (* Infix "<=?" := leb (at level 70). *)
 Lemma leble: forall a b , le a b -> leb a b = true.
Proof. intros. unfold leb. 
induction a.  simpl in *. tauto. assert (H' := H). apply le_Sn_le in H. apply IHa in H.
  induction b. simpl in *. lia.
    simpl in *. fold leb in *.
  Theorem leb_total : forall a1 a2,leb a1 a2  = true \/ leb a2 a1 = true.
Proof. intros. assert(lt a1 a2 \/ ~ lt a1 a2). tauto. elim H.
 +  intros. unfold leb.  tauto.  
 + intros. tauto.   omega. 
End NatOrder.  *)


Local Notation "[ ]" := nil.
Local Notation "[ a ; .. ; b ]" := (a :: .. (b :: []) ..).
Module Import Point2DSort := Sort PointOrderByX. 


Fixpoint is_sortedByX (ls : list Point2D) : Prop :=
   match ls with
| [] => True
| pt1 :: ls1 =>
      match ls1 with
      | [] => True
      | pt2 :: ls2 =>  if(PointOrderByX_le_dec pt1 pt2) then is_sortedByX ls1
                           else False    
      end
end.

Check Sorted.
Lemma locallySorted: forall ls:list Point2D , LocallySorted PointOrderByX_le ls -> is_sortedByX ls.
Proof. intros.
induction ls.
- simpl. tauto.
- inversion H.
  + simpl. tauto.
  + rewrite <- H1 in IHls. apply IHls in H2.
    simpl in *. case (PointOrderByX_le_dec a b) in *.
    -- tauto.
    -- tauto.
Qed.
Hint Resolve PointOrderByX.leb_total.
Hint Constructors Sorted.
Hint Constructors HdRel.

(* ============================================ sort theorems
Theorem Sorted_sort : forall l, Sorted (sort l).

Corollary LocallySorted_sort : forall l, Sorted.Sorted leb (sort l).

Theorem Permuted_sort : forall l, Permutation l (sort l).

Corollary StronglySorted_sort : forall l,
  Transitive leb -> StronglySorted leb (sort l).

 Inductive Sorted : list A -> Prop :=
    | Sorted_nil : Sorted []
    | Sorted_cons a l : Sorted l -> HdRel a l -> Sorted (a :: l).

Lemma HdRel_inv : forall a b l, HdRel a (b :: l) -> R a b.

Lemma Sorted_inv :
    forall a l, Sorted (a :: l) -> Sorted l /\ HdRel a l.

Lemma Sorted_rect :
    forall P:list A -> Type,
      P [] ->
      (forall a l, Sorted l -> P l -> HdRel a l -> P (a :: l)) ->
      forall l:list A, Sorted l -> P l.

Lemma Sorted_LocallySorted_iff : forall l, Sorted l <-> LocallySorted l.
Lemma Sorted_cons
     : forall (A : Type) (R : A -> A -> Prop) (a : A) (l : list A),
       Sorted R l -> HdRel R a l -> Sorted R (a :: l)
  ============================================ sort theorems
*)
Check sort. 
Check is_true.
Check LocallySorted_sort.
Check Sorted_cons.
Lemma sort2: forall (ls: list Point2D )  
, LocallySorted PointOrderByX_le(sort ls).
Proof. intros.  pose (LocallySorted_sort ls) as thm.
  inversion thm.
  + simpl. apply LSorted_nil.
  + simpl. rewrite <- H in *.  inversion thm.
    - apply Sorted_LocallySorted_iff .
      apply Sorted_cons.
      ++ clear thm H0 H1 H5 H2 H3 H. induction l.
         -- apply Sorted_nil.
         -- apply Sorted_inv in H4. destruct H4.
            apply IHl in H. apply Sorted_cons.
            * tauto.
            * induction l.  
              ** apply HdRel_nil.
              ** apply HdRel_inv in H0. apply HdRel_cons. 
                 case (PointOrderByX_le_dec a1 a2) in H0. tauto.
               discriminate. 
      ++ clear thm H0  H4 H H5 H2 H3. induction l.
         -- apply HdRel_nil.
         --  apply HdRel_inv in H1. apply HdRel_cons.
             case (PointOrderByX_le_dec a a1) in H1. tauto.
               discriminate. 
Qed.

Lemma sort_works: forall (ls: list Point2D )  
,  is_sortedByX(sort ls).
Proof. intros.
apply locallySorted.
apply sort2.
Qed.

(*=====================================================================*)
(*======================= stack of Point2D   ==========================*)
(*=====================================================================*)

Inductive StackP : Set := 
| stack_nill : StackP
| stack_cons : StackP ->  Point2D -> StackP.

Fixpoint stack_size (s: StackP):nat :=
match s with
stack_nill => 0
| stack_cons s' pt => S (stack_size s')
end.

Fixpoint stack_insert (s:StackP)(pt :Point2D):=
stack_cons s pt.

Fixpoint list_to_stack (ls:list Point2D)(s:StackP) : StackP :=
match ls with
| [] => s
| pt :: ls' =>  list_to_stack ls' (stack_insert s pt) 
end.

Fixpoint stack_to_list (s:StackP): list Point2D :=
match s with
| stack_nill => []
| stack_cons s' pt => pt :: stack_to_list s'
end.

Fixpoint stack_empty (s:StackP):Prop := match s with
stack_nill => True
| stack_cons _ _ => False
end.

Fixpoint stack_pop (s:StackP) : Point2D := 
match s with
stack_nill => {|id:=0 ; x:=0 ; y:= 0|}
| stack_cons s' pt => pt
end.

Fixpoint head_list (ls:list Point2D) : Point2D :=
match ls with
|[] => {|id:=0 ; x:=0 ; y:= 0|}
| pt :: ls => pt
end.

Fixpoint is_in_list (ls:list Point2D ) (pt: Point2D) :Prop :=
match ls with
| [] => False
| pt1 :: ls' => id pt = id pt1 \/ is_in_list ls' pt
end.

Fixpoint next_in_list_h1 (first_point: Point2D)(ls:list Point2D)(pt : Point2D) :Point2D :=
match ls with
| [] => head_list []
| pt1 :: ls' => if(eq_nat_decide (id pt1)  (id pt)) then 
match ls' with |[] => first_point | pt2 :: _ => pt2 end
else next_in_list_h1 first_point ls' pt
end.

Fixpoint next_in_list (ls:list Point2D)(pt : Point2D) :Point2D :=
match ls with
| [] => head_list []
| pt1 :: ls' => next_in_list_h1 pt1 ls pt
end.

Fixpoint distinct_id_list (ls: list Point2D): Prop := 
match ls with
| [] => True
| pt1 :: ls' => ~ is_in_list ls' pt1 /\ distinct_id_list ls' 
end.

Fixpoint distinct_list_helper (ls:list Point2D ) (pt: Point2D) :Prop :=
match ls with
| [] => True
| pt1 :: ls' => ~((x pt) == (x pt1) /\ y pt == y pt1) /\ distinct_list_helper ls' pt
end.

Fixpoint distinct_list (ls: list Point2D): Prop := 
match ls with
| [] => True
| pt1 :: ls' => distinct_list_helper ls' pt1 /\ distinct_list ls' 
end.
(*===============================================================*)
(*======================== to prevenet points with zero id ======*)
(*===============================================================*)
Fixpoint positive_id_list (ls: list Point2D): Prop := 
match ls with
| [] => True
| pt1 :: ls' => ((id pt1) > 0 )%nat /\ positive_id_list ls' 
end.

Fixpoint well_formed_list (ls:list Point2D): Prop := distinct_list ls /\ distinct_id_list ls /\ positive_id_list ls.

Lemma distinct_remove:  forall(ls : list Point2D) (pt : Point2D),
 distinct_list (pt :: ls) -> distinct_list ls.
Proof.
intros. induction ls.
- simpl. tauto.
- simpl.  simpl in H. tauto.
Qed.
Lemma distinct_id_remove:  forall(ls : list Point2D) (pt : Point2D),
    distinct_id_list (pt :: ls) -> distinct_id_list ls.
Proof.
intros. simpl in *. tauto.
Qed.
Lemma positive_id_remove:  forall(ls : list Point2D) (pt : Point2D),
 positive_id_list (pt :: ls)-> positive_id_list ls.
Proof. intros. simpl in H. tauto.
Qed.

Lemma well_formed_remove: forall(ls : list Point2D) (pt : Point2D),
 well_formed_list (pt :: ls) -> well_formed_list (ls).
Proof.
intros. induction ls.
- simpl . tauto.
- simpl in *. tauto.
Qed.

Lemma is_in_list_equality: forall (ls: list Point2D)(pt1 pt2:Point2D),
eq_nat pt1 pt2 -> is_in_list ls pt1 <-> is_in_list ls pt2.
Proof. intros. split.
- induction ls.
  + simpl.  tauto.
  + intros. simpl . unfold is_in_list in H0.
    fold is_in_list in H0. destruct H0.
    -- rewrite H0 in H. apply eq_nat_is_eq in H. symmetry in H. tauto.
    -- tauto.
- intro.  induction ls.
  + simpl.  tauto.
  + intros. simpl . unfold is_in_list in H0.
    fold is_in_list in H0. destruct H0.
    -- rewrite H0 in H. apply eq_nat_is_eq in H. tauto.
    -- tauto.
Qed.

Lemma is_in_list_add: forall (ls: list Point2D)(pt1 pt2:Point2D),
is_in_list ls pt1 -> is_in_list (pt2::ls) pt1.
Proof.
intros. unfold is_in_list. fold is_in_list. 
auto.
Qed.

Lemma next_in_list_exist_h1: forall(ls: list Point2D)(pt1 a:Point2D),
(is_in_list ls pt1) -> next_in_list_h1 a ls pt1 = a \/ is_in_list ls (next_in_list_h1 a ls pt1).
Proof.
intros.
induction ls.
- simpl. tauto.
- unfold next_in_list_h1 . case(eq_nat_decide a0 pt1).
  + intros. simpl. destruct ls.
    -- tauto.
    -- simpl. tauto.
  + intros. fold next_in_list_h1 . unfold is_in_list. fold is_in_list.
    simpl in H. destruct H.
    -- symmetry in H. apply eq_nat_is_eq in H. tauto.
    -- apply IHls in H. tauto.
Qed.

Lemma next_in_list_exist: forall (ls: list Point2D)(pt1 pt2:Point2D),
is_in_list ls pt1 -> is_in_list ls (next_in_list ls pt1).
Proof.
intros.
induction ls. simpl. tauto.
unfold is_in_list. fold is_in_list. simpl in H. destruct H.
- induction ls.
  + simpl in *.  case(eq_nat_decide a pt1).
     -- intros. tauto.
     -- intros. symmetry in H. apply eq_nat_is_eq in H. tauto.
  + right. simpl. case(eq_nat_decide a pt1). intros. tauto.
    intros. symmetry in H. apply eq_nat_is_eq in H. tauto.
- assert(H1:= H). apply IHls in H1. clear IHls.
  apply (next_in_list_exist_h1 ls pt1 a) in H. 
  simpl. fold next_in_list_h1. case(eq_nat_decide a pt1). 
  + intros. destruct ls. tauto. simpl. tauto. 
  + intros. clear H1 n. destruct H. 
    --left. eauto. 
      remember (next_in_list_h1 a ls pt1) as b.
      destruct H. tauto.
    -- tauto.
Qed. 
    
Lemma next_in_list_remove: forall (ls: list Point2D)(pt1 pt2:Point2D),
id pt1 <> id pt2 -> is_in_list ls pt2 -> next_in_list (pt1 :: ls) pt2 = (next_in_list ls pt2) \/ next_in_list (pt1 :: ls) pt2 = pt1.
Proof.
intros.
simpl.
case(eq_nat_decide pt1 pt2).
- intros.  apply eq_nat_is_eq in e.
       rewrite <- e in H. tauto.
- intros. induction ls.
  + tauto.
  + simpl. case(eq_nat_decide a pt2).
    -- intros. destruct ls. tauto. tauto. 
    -- intros. simpl in H0. destruct H0.
       ++ rewrite H0 in n0. destruct n0. apply eq_eq_nat. tauto.
       ++ apply IHls in H0. destruct H0.
          * clear IHls. rewrite H0. induction ls.
            ** tauto.
            ** simpl in *. case(eq_nat_decide a0 pt2) in *.
               intros.  destruct ls. simpl in *. case(eq_nat_decide a0 pt2) in * . 
               rewrite <- H0 in e. tauto. tauto. tauto.
               clear IHls. induction ls. simpl. tauto.
               unfold next_in_list_h1 in *. fold next_in_list_h1 in *.
               case(eq_nat_decide a1 pt2) in *. destruct ls.
               rewrite <- H0 in n1. symmetry in H0. tauto. tauto. tauto.
          * tauto.
Qed.

Lemma well_formed_equity: forall(ls : list Point2D)(pt1 pt2 :Point2D) ,
 well_formed_list ls -> is_in_list ls pt1 -> is_in_list ls pt2 -> eq_nat pt1 pt2 -> pt1 = pt2.
Proof. intros. apply Point2D_eq in H2. tauto. 
Qed.
(*================ Tests  ================*)
Section Test.

Local Definition p1: Point2D := {|id:=1 ; x:=1 ; y:= 1#1|}.
Definition p2: Point2D := {|id:=2 ; x:=5#2 ; y:= 2#1|}.
Definition p3: Point2D := {|id:=3 ; x:=5#2 ; y:= 3#1|}.
Definition p4: Point2D := {|id:=4 ; x:=4#1 ; y:= 2#1|}.
Definition p5: Point2D := {|id:=5 ; x:=5#7 ; y:= 2#1|}.

Definition plist : ListP :=  LI 1 p1 (LI 2%nat p2 (LI 3 p3 (LI 4 p4 (LI 5 p5 Lz)))).

Compute first(split plist).
Compute mergeSort plist.
(*Eval compute in (mergeSort plist).*)
Compute is_sorted(plist).
Compute is_sorted( mergeSort plist).
Compute (sort [p1;p2;p3;p4;p5]).
Compute (list_to_stack [p1;p2;p3;p4;p5] stack_nill). 
Compute (stack_to_list (list_to_stack [p1;p2;p3;p4;p5] stack_nill)).
Check leb.
Check PointOrderByX.leb.

(*Compute (Sorted [p1;p2;p3;p4;p5]).*)
End Test.
(*================ Tests  ================*)