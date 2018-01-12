
Inductive I (A : Type) (x : A) : A -> Type :=
  refl : I A x x.

Arguments refl {_} _.

Notation "x = y" := (I _ x y): type_scope.

Definition J (A:Type) (t:A) (P : forall y:A, t = y -> Type)
           (u : A) (p : t = u) (v:P t (refl t)) : P u p :=
  match p with
  | refl _ => v
  end.

Section J_cbn. 

  Variable A : Type.
  Variable t : A.
  Variable P : forall y:A, t = y -> Type. 
  Variable v : P t (refl t).
  
  Eval cbn in J A t P t (refl t) v.  
  
End J_cbn. 

Inductive nat : Set :=
  O : nat
| S : nat -> nat.

Fixpoint rec (P : nat -> Type) (P0 : P O) (PS: forall n : nat, P n -> P (S n)) (n : nat) : P n :=
  match n with
  | O => P0
  | S n => PS n (rec P P0 PS n)
  end. 

Section nat_cbn. 

  Variable n : nat. 
  Variable P : nat -> Type. 
  Variable P0 : P O.
  Variable PS : forall n : nat, P n -> P (S n).
  
  Eval cbn in rec P P0 PS O.

  Eval cbn in rec P P0 PS (S n).
  
End nat_cbn. 
