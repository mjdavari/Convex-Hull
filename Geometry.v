Require Import QArith. 
Require Import Reals.
Require Import Psatz.
Require Import QArith.Qminmax.
Require Lra.


Structure Open_Interval := {
lower_bound:Q;
upper_bound:Q;
opennes : lower_bound < upper_bound}.

Definition open_membership ( x :Q )( I : Open_Interval) :=
x < upper_bound I /\ x > lower_bound I.

Definition open_waybelow ( I J :Open_Interval) :=
lower_bound J < lower_bound I /\ upper_bound I < upper_bound J.

Lemma member_transivity : forall x :Q , forall I J : Open_Interval,
open_waybelow I J -> open_membership x I -> open_membership x J.
Proof.
intros.
destruct I as [lower upper prop].
destruct J as [lower' upper' prop'].
unfold open_waybelow, open_membership.
simpl in *.
destruct H as [A1 A2].
split.
apply (Qlt_trans x upper upper').
apply H0.
apply A2.
apply (Qlt_trans lower' lower x).
apply A1.
apply H0.
Qed.

Definition open_separated (I J : Open_Interval):=
upper_bound I <= lower_bound J \/ upper_bound J <= lower_bound I.

Definition totally_open_separated (I J : Open_Interval):=
upper_bound I < lower_bound J \/ upper_bound J < lower_bound I.

Lemma separation_expansion: forall I J : Open_Interval , 
totally_open_separated I J ->
 exists I' J' , totally_open_separated I' J' 
-> open_waybelow I I' -> open_waybelow J J'.
Proof.
intros.
destruct I as [lower_I upper_I prop_I].
destruct J as [lower_J upper_J prop_J].
destruct H as [A1| A2].
simpl in *.
assert (I'_prop: ((3#1)*(lower_I)-(lower_J)+(upper_I))*(1#3)<
((2#1)*(upper_I ) + (lower_J) ) * (1#3)).
lra.
exists{|lower_bound:=((3#1)*(lower_I)-(lower_J)+(upper_I))*(1#3);upper_bound :=
((2#1)*(upper_I ) + (lower_J) ) * (1#3); opennes :=I'_prop|}.
assert(J'_prop: ((2#1)*lower_J + upper_I)*(1#3) < ((3#1)*upper_J + lower_J 
- upper_I)*(1#3)).
lra.
exists{|lower_bound:=((2#1)*lower_J + upper_I)*(1#3) ; upper_bound := ((3#1)*upper_J + lower_J 
- upper_I)*(1#3); opennes :=J'_prop |}.
unfold totally_open_separated.
simpl in *.
unfold open_waybelow.
simpl in *.
lra.
simpl in *.
assert (J'_prop: ((3#1)*(lower_J)-(lower_I)+(upper_J))*(1#3)<
((2#1)*(upper_J ) + (lower_I) ) * (1#3)).
lra.
exists{|lower_bound:=((3#1)*(lower_J)-(lower_I)+(upper_J))*(1#3);upper_bound :=
((2#1)*(upper_J ) + (lower_I) ) * (1#3); opennes :=J'_prop|}.
assert(I'_prop: ((2#1)*lower_I + upper_J)*(1#3) < ((3#1)*upper_I + lower_I 
- upper_J)*(1#3)).
lra.
exists{|lower_bound:=((2#1)*lower_I + upper_J)*(1#3) ; upper_bound := ((3#1)*upper_I + lower_I 
- upper_J)*(1#3); opennes :=I'_prop |}.
unfold totally_open_separated.
simpl in *.
unfold open_waybelow.
simpl in *.
lra.
Qed.

(*Check upper_bound.*)
