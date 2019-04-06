(* Third Section: C2D *)

Theorem Dedekind_CSeq :forall (CSeq:nat->Q->Prop),
Cauchy CSeq->Dedekind (fun q=>exists (N:nat),forall (n:nat),(n>N)%nat->(forall(p:Q),CSeq n p->(q<p)%Q)).
Proof.
Admitted.

Definition C2D (A:CReal):DReal :=
match A with
|Real_intro CSeq H =>
Real_cons (fun q=>exists (N:nat),forall (n:nat),(n>N)%nat->(forall(p:Q),CSeq n p->(q<p)%Q)) (Dedekind_CSeq CSeq H) end.

Theorem C2D_properity1:forall (x y:CReal),
  (((C2D x)+(C2D y))%DR==C2D (x+y)%CR)%DR.
Proof.
Admitted.

Theorem C2D_properity2:forall (x y:CReal),
  (((C2D x)*(C2D y))%DR==C2D (x*y)%CR)%DR.
Proof.
Admitted.

Theorem C2D_properity3:forall (x y:CReal),
(x==y)%CR->  ((C2D x)==(C2D y))%DR.
Proof.
Admitted.


(* Fourth Section: D2C *)
Fixpoint psucc(n:positive):positive :=
match n with
| xI p => xO (psucc p)
| xO p => xI p
| xH => xO xH
end.

Fixpoint of_nat(n:nat) : positive :=
 match n with
   | O => 1
   | S O => 1
   | S x => psucc (of_nat x)
 end.
Theorem Cauchy_Dcut :forall (DCut:Q->Prop),
Dedekind DCut->Cauchy (fun n q=>exists N:Z,
DCut (N#(2^(of_nat n)))/\~DCut((N+1)%Z#2^(of_nat n))/\(q==N#2^(of_nat n))%Q).
Proof.
Admitted.

Definition D2C (B:DReal):CReal :=
match B with
|Real_cons DCut H =>
Real_intro (fun n q=>exists N:Z,DCut (N#(2^(of_nat n)))/\~DCut((N+1)%Z#2^(of_nat n))/\(q==N#2^(of_nat n))%Q)
(Cauchy_Dcut DCut H) end.

(* Fifth Section: Bijection *)
Theorem Bijection: forall x y,(D2C x==y)%CR <->(C2D y==x)%DR.
Proof.
Admitted.
