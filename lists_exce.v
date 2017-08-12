Require Import List.
Require Import QArith. 

Definition l23 : list Q
  := 2#1 :: 3#1 :: nil.
Definition l123 : list Q
  := 1#1 :: l23.

Eval compute in (hd l123).

FixedPoint sum_list (A: (list Q)):=
match hd A




