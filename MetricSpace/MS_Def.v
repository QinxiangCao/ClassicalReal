From Coq Require Import Init.Nat.
(**def of total-order-field and metric space**)
Class OrderField (X : Type) :={
    lt : X -> X -> Prop;
    HOF1 : forall (x y : X), lt x y \/ lt y x;
    HOF2 : forall (x : X), ~(lt x x);
    HOF3 : forall (x y z : X), lt x y -> lt y z -> lt x z;
}.

Class Field  (X : Type)  :={
    x0 : X;
    plus : X -> X -> X;
    HF1 : forall (x y : X), plus x y = plus y x;
    HF2 : forall (x y z : X), plus (plus x y) z = plus x (plus y z);
    HF3 : forall (x : X), plus x0 x = x;
    HF4 : forall (x : X), (exists ix, plus x ix = x0) ;
}.

Class Metric (A : Type) :={
    X : Type;
    dist : A -> A -> X;
    HM_F : Field X;
    HM_OF : OrderField X;
    HM1 : forall (p1 p2 : A), lt (dist p1 p2) x0;
    HM2 : forall (p1 p2 : A), dist p1 p2 = dist p2 p1;
    HM3 : forall (p : A), dist p p = x0;
    HM4 : forall (p1 p2 p3 : A), lt (dist p1 p3) (plus (dist p1 p2) (dist p2 p2));
}.

