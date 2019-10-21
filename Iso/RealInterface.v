Require Import QArith.

Module Type R_Field.
  Parameter R : Type.
  Delimit Scope R_scope with R.
  Bind Scope R_scope with R.
  Local Open Scope R_scope.
  Parameter Req: R -> R -> Prop.
  Parameter R0 : R.
  Parameter R1 : R.
  Parameter Rplus : R -> R -> R.
  Parameter Rmult : R -> R -> R.
  Parameter Ropp : R -> R.
  Parameter Rinv' : {a0 : R | ~(Req a0 R0)} -> R.
  Parameter Rlt : R -> R -> Prop.
  Infix "==" := Req : R_scope.
  Notation "0" := (R0) : R_scope.
  Notation "1" := (R1) : R_scope.
  Infix "+" := Rplus : R_scope.
  Infix "*" := Rmult : R_scope.
  Notation "- x" := (Ropp x) : R_scope.
  Infix "<" := Rlt : R_scope.
  Definition Rgt (r1 r2:R) : Prop := r2 < r1.
  Definition Rle (r1 r2:R) : Prop := r1 < r2 \/ r1 == r2.
  Definition Rge (r1 r2:R) : Prop := Rgt r1 r2 \/ r1 == r2.
  Definition Rminus (r1 r2:R) : R := r1 + - r2.
  Infix "-" := Rminus : R_scope.
  Infix "<=" := Rle : R_scope.
  Infix ">=" := Rge : R_scope.
  Infix ">"  := Rgt : R_scope.

  Axiom R_Setoid: Equivalence Req.
  Axiom Rplus_comp: Proper (Req ==> Req ==> Req) Rplus.
  Axiom Rmult_comp: Proper (Req ==> Req ==> Req) Rmult.
  Axiom Ropp_comp: Proper (Req ==> Req) Ropp.
  Axiom Rdiv'_comp: Proper ((fun x y => proj1_sig x == proj1_sig y) ==> Req) Rinv'.
  Axiom Rlt_comp: Proper (Req ==> Req ==> iff) Rlt.

  Axiom Rplus_comm : forall r1 r2:R, r1 + r2 == r2 + r1.
  Axiom Rplus_assoc : forall r1 r2 r3:R, r1 + r2 + r3 == r1 + (r2 + r3).
  Axiom Rplus_opp_r : forall r:R, r + - r == 0.
  Axiom Rplus_0_l : forall r:R, 0 + r == r.
  Axiom Rmult_comm : forall r1 r2:R, r1 * r2 == r2 * r1.
  Axiom Rmult_assoc : forall r1 r2 r3:R, r1 * r2 * r3 == r1 * (r2 * r3).
  Axiom Rinv_l : forall r, Rinv' r * proj1_sig r == 1.
  Axiom Rmult_1_l : forall r:R, 1 * r == r.
  Axiom R1_neq_R0 : 1 <> 0.
  Axiom Rmult_plus_distr_l : forall r1 r2 r3:R, r1 * (r2 + r3) == r1 * r2 + r1 * r3.
  Axiom total_order_T : forall r1 r2:R, {r1 < r2} + {r1 == r2} + {r1 > r2}.
  Axiom Rlt_asym : forall r1 r2:R, r1 < r2 -> ~ r2 < r1.
  Axiom Rlt_trans : forall r1 r2 r3:R, r1 < r2 -> r2 < r3 -> r1 < r3.
  Axiom Rplus_lt_compat_l : forall r r1 r2:R, r1 < r2 -> r + r1 < r + r2.
  Axiom Rmult_lt_compat_l : forall r r1 r2:R, 0 < r -> r1 < r2 -> r * r1 < r * r2.
  (*Axiom archimed : forall r:R, IZR (up r) > r /\ IZR (up r) - r <= 1.*)
  Definition is_upper_bound (E:R -> Prop) (m:R) := forall x:R, E x -> x <= m.
  Definition bound (E:R -> Prop) :=  exists m : R, is_upper_bound E m.
  Definition is_lub (E:R -> Prop) (m:R) :=
    is_upper_bound E m /\ (forall b:R, is_upper_bound E b -> m <= b).
  Axiom completeness :
    forall E:R -> Prop,
      bound E -> (exists x : R, E x) -> { m:R | is_lub E m }.

End R_Field.
