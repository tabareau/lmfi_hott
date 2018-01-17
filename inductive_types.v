
Inductive I (A : Type) (x : A) : A -> Type :=
  refl : I A x x.

Arguments refl {_} _.

Notation "x = y" := (I _ x y): type_scope.

Definition subst (A:Type) (t:A) (P : forall y:A, t = y -> Type)
           (u : A) (p : t = u) (v:P t (refl t)) : P u p :=
  match p with
  | refl _ => v (* : P t (refl t) *)
  end.


Section subst_computation. 

  Variable A : Type.
  Variable t : A.
  Variable P : forall y:A, t = y -> Type. 
  Variable v : P t (refl t).
  
  Eval cbn in
      subst A t P t (refl t) v.  
  
End subst_computation. 










Inductive nat : Set :=
  O : nat
| S : nat -> nat.



Fixpoint rec (P : nat -> Type) (P0 : P O) (PS: forall n : nat, P n -> P (S n)) (n : nat) : P n :=
  match n with
  | O => P0
  | S n' => PS n' (rec P P0 PS n')
  end. 

Section nat_computation. 

  Variable n : nat. 
  Variable P : nat -> Type. 
  Variable P0 : P O.
  Variable PS : forall n : nat, P n -> P (S n).
  
  Eval cbn in
      rec P P0 PS O.

  Eval cbn in
      rec P P0 PS (S n).
  
  Eval cbn in
      rec P P0 PS (S (S (S O))).


End nat_computation. 


Fixpoint plus (n : nat) : nat -> nat :=
  fun m =>
    match n with
    | O => m
    | S n' => S (plus n' m)
    end. 

Check (fun m => refl m) : forall m:nat, plus O m = m.

Fail Check (fun n => refl n) : forall n:nat, plus n O = n.

Definition ap {A B:Type} (f:A -> B) {x y:A} (p:x = y) : f x = f y
  := match p with refl _ => refl (f x) end.



Fixpoint plus_O_r (n : nat) : plus n O = n :=
  match n with
  | O => refl O (* : plus O O = O *)
  | S n' => ap S (plus_O_r n') (* S (plus  n' 0) = S n' *)
  end. 


(* Alternative definition of dependent pairs  *)

Inductive sigma (A: Type) (B: A -> Type) : Type :=
  | exist : forall (a:A), B a -> sigma A B. 
