Require Import Arith. 

Structure poset := {
poset_carrier:> Set;
poset_relation:> poset_carrier -> poset_carrier -> Prop;
refl: forall x , poset_relation x x ;
transivity: forall x  y z , poset_relation x y /\ poset_relation y z
 -> poset_relation x z;
anti_symmetry: forall x y, poset_relation x y /\ poset_relation y x -> x = y;
}.

Notation "x <= y" := (poset_relation x y) (at level 70, no associativity).

Inductive two := a | b.



Definition ftwo(x y:two):Prop:=
match x with
    |a => True
    | b => (match y with
 | b => True
| a => False
end
)
end.
Eval compute in (ftwo b a).

Definition two_poset : poset.
Proof.
refine {| poset_carrier := two; poset_relation := ftwo |}.
-intros. induction x.
   +  simpl. trivial.
   +  simpl. trivial.
- intros. rename H into Hypoth. induction x.
   ++ simpl. trivial.
   ++ destruct Hypoth.
     *** induction y.
         -- elim H.
         -- apply H0.
- intros. destruct H. induction x.
   + induction y.
     --- trivial.
    --- elim H0.
   + induction y. elim H. trivial.
Qed.

Inductive LiftedBool := T | F | B.

Defnition LiftedBoolRel (x y : LiftedBool): Prop := 
match x with 
    |T => ( match y with 
          |T => True
          |F => False
          |B => False 
           end)
    |F => ( match y with 
          |T => False
          |F => True
          |B => False 
           end)
    |B => True
end

Eval compute in LiftedBoolRel T F
Definition 
