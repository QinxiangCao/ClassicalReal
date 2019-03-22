From Coq Require Import Init.Nat.
(**def of total-order-field and metric space**)
Class OrderField (X : Type): Type :={
    lt : X -> X -> Prop;
    HOF1 : forall (x y : X), lt x y \/ lt y x;
    HOF2 : forall (x : X), ~(lt x x);
    HOF3 : forall (x y z : X), lt x y -> lt y z -> lt x z;
}.
Notation "x < y" := (lt x y): metric.
Local Open Scope metric.
(** Maybe using notation to make code more readable. -- Qinxiang *)
Class Field  (X : Type)  :={
    x0 : X;
    plus : X -> X -> X;
    HF1 : forall (x y : X), plus x y = plus y x;
    HF2 : forall (x y z : X), plus (plus x y) z = plus x (plus y z);
    HF3 : forall (x : X), plus x0 x = x;
    HF4 : forall (x : X), (exists ix, plus x ix = x0) ;
}.

Class Metric (A : Type) (X : Type):={
    dist : A -> A -> X;
    HM_F :> Field X;
    HM_OF :> OrderField X;
    HM1 : forall (p1 p2 : A), (lt x0 (dist p1 p2)) \/ (dist p1 p2) = x0;
    HM2 : forall (p1 p2 : A), dist p1 p2 = dist p2 p1;
    HM3 : forall (p : A), dist p p = x0;
    HM4 : forall (p1 p2 p3 : A), (lt (dist p1 p3) (plus (dist p1 p2) (dist p2 p2))) \/ (dist p1 p3) = (plus (dist p1 p2) (dist p2 p2));
}.
(** Putting Type definitions in to type class arguments
are probably better. -- Qinxiang *)
Class CauchySeq (A : Type) (X : Type) :={
    HC_M : Metric A X;
    Cseq : nat -> A;
    HCA : forall (eps : X), lt x0 eps
      -> (exists (N : X -> nat), forall (m n:nat), (m > (N eps))%nat /\ (n > (N eps))%nat
         -> lt (dist (Cseq m) (Cseq n)) eps);
}.
