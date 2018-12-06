Require Import QArith. 
(* ================================================================== *)
(* ===== Point2D ==================================================== *)
(* ================================================================== *)
Structure Point2D := {
id:> nat;
x:> Q;
y:> Q;
}.
Definition Xp (pt : Point2D) : Q := x pt.
Definition Yp (pt : Point2D) : Q := y pt.
Axiom Point2D_eq: forall (p q : Point2D), eq_nat (id p)(id q) -> p = q.