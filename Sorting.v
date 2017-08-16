
Require Import Coq.Bool.Bool.
Require Import Coq.Arith.Arith.
Require Import Coq.Arith.EqNat.
Require Import Coq.omega.Omega.
Require Import Coq.Lists.List.
Require Import QArith.
Import ListNotations.
Require Import Reals.
Require Import Psatz.
Require Import QArith.Qminmax.
Require Import List.
Require Import PeanoNat.


Fixpoint replace_in_list (i :nat)(l : list Q)(b : Q):=
match i,l with
| O , nil => nil
| O ,  _::l' => b :: l'
| S i' , nil =>  nil
| S i' , a::l' => a :: (replace_in_list i' l' b)
end.

Check replace_in_list.
Definition lpoint : list (Q)
  := 1:: 0:: 1 :: 0:: 1 ::  nil.

Eval compute in (replace_in_list 3 lpoint (3#1)).

Definition i_element(i:nat)(l:list Q)(d:Q):=nth i l d.

Definition j_element(j:nat)(l:list Q)(d:Q):=nth j l d.

Definition swap (i j :nat)(l : list Q) :=
replace_in_list i (replace_in_list j l (nth i l 0)) (nth j l 0) .

Eval compute in (swap 1 2 lpoint).

Search Qle.
Check Qle_bool.


Fixpoint insert (n:Q)(ms : list Q) :=
  match ms with
  | nil => n::nil
  | m::ms' => if  Qle_bool n m
              then n::ms
              else m::(insert n ms')
  end.

Eval compute in insert (3#1) (1::0::1::4#1::nil).

Fixpoint sort (ms : list Q) :=
  match ms with
  | nil => nil
  | m::ms' => insert m (sort ms')
  end.

Eval compute in sort (4#1::2#1::3#1::1::nil).

Eval compute in (le 4 1).

Definition is_sorted (l : list Q) :=
forall (i:nat), ( i < ((length l) -1))%nat -> ((nth i l 0) <= (nth (i+1) l 0)).

Lemma single_sort: forall a:Q, is_sorted [a].
Proof.
intros.
unfold is_sorted.
intros.
induction i.
- simpl in *. lia.
- simpl in *. lia.
Qed.
Search Qle.

Lemma empty_list_is_sorted:is_sorted ([]).
Proof.
unfold is_sorted.
intros.
induction i.
- simpl. apply Qle_refl.
- simpl. apply Qle_refl.
Qed.


Lemma sortedlist_sort:forall (a:Q)(l:list Q), is_sorted (a::l)-> is_sorted l.
Proof.
intros. unfold is_sorted in *. intros. specialize (H (S i)). induction i. 
- simpl in *. rewrite <- minus_n_O in H. 
  apply  (lt_O_minus_lt (length l) 1) in H0. auto.
- simpl in *. rewrite <- minus_n_O in H. 
  apply Nat.lt_add_lt_sub_r in H0. rewrite Nat.add_1_r in H0. auto.
Qed.

Lemma insert_sorted_0: forall (a :Q) (l:list Q), is_sorted(l) /\ a <= nth 0 l 0 
-> is_sorted(a::l).
Proof. 
intros. destruct H. unfold is_sorted. intros. induction i.
  - simpl. auto.
  - simpl. unfold is_sorted in H. specialize (H i). simpl in H1.
    rewrite <- Nat.add_1_r in H1. rewrite <- minus_n_O in H1.
    apply Nat.lt_add_lt_sub_r in H1. auto.
Qed.

Lemma Qle_bool_false: forall (a b :Q) , (Qle_bool a b = false) -> a>b.
Proof. 
 intros.
  generalize ((proj2 (Qle_bool_iff a b))). rewrite H.
  destruct (Qlt_le_dec b a); intuition; try discriminate.
Qed.

Lemma list_length: forall(l:list Q) , (length l >= 0)%nat.
Proof.
intro. induction l.
  - simpl. auto.
  - simpl.  rewrite <- Nat.add_1_r. apply le_plus_trans. auto.
Qed.

Lemma succ_pos: forall(n:nat) ,( S n > 0 )%nat.
Proof.
intros. induction n.
  - auto.
  -  auto.
Qed.

Lemma insert_works: forall (l : list Q) (a : Q), (is_sorted l) -> 
(is_sorted (insert a l)).
Proof.
intros.
induction l.
  - simpl in *. apply single_sort.
  - unfold insert. remember (Qle_bool a a0) as res. induction res.
      + symmetry in Heqres. apply Qle_bool_iff in Heqres.
        apply insert_sorted_0. split.
        -- auto.
        -- simpl. auto.
      + fold insert. unfold is_sorted. intros. induction i.
        -- simpl. unfold insert. induction l.
           ++ simpl. symmetry in Heqres. apply Qle_bool_false in Heqres.
              apply Qlt_le_weak. auto.
           ++ simpl in *. remember (Qle_bool a a1) as b. induction b.
              --- simpl. symmetry in Heqres. apply Qle_bool_false in Heqres.
                  apply Qlt_le_weak. auto.
              --- simpl. fold insert in IHl0. unfold is_sorted in H.
                  specialize (H O) . simpl in *. assert ( 0 < S (length l))%nat.
                  +++ apply succ_pos.
                  +++ auto.
        -- simpl. apply sortedlist_sort in H. apply IHl.
           ++ auto.
           ++ simpl in H0. rewrite <- Nat.add_1_r in H0.
              rewrite <- minus_n_O in H0. apply Nat.lt_add_lt_sub_r in H0. auto.
Qed.


Lemma sort_sorts: forall (i:nat)(l: list Q), (i < (length l) - 1)%nat ->
 Qle (nth i (sort l) 0)  (nth (i+1) (sort l) 0).
Proof.
intros.
induction l.
  - simpl in *. induction i.
     + apply Qle_irrefl. 
  - simpl in *. apply Qle_refl.
  - simpl in *. simpl in *. destruct IHl.
    ++ .
unfold insert.

Inductive sort : list Q -> Prop :=
  | nil_sort : sort nil
  | cons_sort :
      forall (a:Q) (l:list A), sort l -> lelistA a l -> sort (a :: l).
Check Sort.