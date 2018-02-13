Set Universe Polymorphism.

Require Import Trunc Hedberg. 

Definition apD {A} {B : A -> Type} (f:forall x, B x) {x y:A} (p:x = y) :
  p # (f x) = f y
  := match p with refl _ => refl _ end.


Module Export Interval.
  Private Inductive Int : Type :=
  | zero : Int
  | one : Int.

  Axiom seg : zero = one. 
  
  Definition Int_ind
             (P: Int -> Type) 
             (b0: P zero)
             (b1: P one)
             (s : seg # b0 = b1)
  : forall i, P i
    := fun i => match i with
                | zero => b0
                | one => b1
                end.

   Axiom Int_ind_seg : forall 
             (P: Int -> Type) 
             (b0: P zero)
             (b1: P one)
             (s : seg # b0 = b1),
  apD (Int_ind P b0 b1 s) seg = s.
   
End Interval.


Section Int_computation. 

  Variable i : Int. 
  Variable P : Int -> Type. 
  Variable b0 : P zero.
  Variable b1 : P one.
  Variable s : seg # b0 = b1.                 
  
  Eval cbn in
      Int_ind P b0 b1 s zero.

  Eval cbn in
      Int_ind P b0 b1 s one.

End Int_computation.

Definition Int_IsContr : IsContr Int.
Proof.
  unshelve econstructor.
  - exact zero.
  - unshelve refine (Int_ind _ _ _ _).
    + exact (refl zero).
    + exact seg.
    + apply transport_paths_r.
Defined. 

Definition transport_const {A B : Type} {x1 x2 : A} (p : x1 = x2) (y : B)
  : transport (fun x => B) p y = y.
Proof.
  destruct p.  exact (refl y).
Defined.

Definition Int_funext (A : Type)  (B :A -> Type) (f g : forall a, B a):
       f == g -> f = g.
Proof.
  intro p.
  pose (pp := fun x => Int_ind (fun _ => B x) (f x) (g x) (transport_const _ _ @ p x)).
  pose (q := (fun i x => pp x i) : Int -> (forall x, B x)).
  exact (ap q seg).
Defined.


Module Export Squash.
  Private Inductive trunc (A : Type) : Type :=
  | tr : A -> trunc A.

  Arguments tr {_} _.
  
  Axiom trunc_hprop : forall A (a b : trunc A), a = b.

  Definition trunc_rec A B
             (f: A -> B)
             (hprop : IsHProp B)
  : trunc A -> B
    := fun a => match a with
                | tr a => f a
                end.

  Axiom trunc_rec_eq : forall A B
                              (f: A -> B)
                              (hprop : IsHProp B)
                              (a a': trunc A),
      ap (trunc_rec A B f hprop) (trunc_hprop A a a') =
      (IsHProp_to_IsIrr _ hprop _ _).
  
End Squash.

Definition trunc_ind A
           (P: trunc A -> Type) 
           (f: forall a, P (tr a))
           (hprop : forall a, IsHProp (P a))
  : forall a, P a.
Proof.
  intro a. refine (trunc_rec A (P a) _ (hprop a) a).
  intro a'. exact ((trunc_hprop _ _ _) # (f a')).
Defined. 


Module Export Circle.
  Private Inductive S1 : Type :=
  | base : S1.

  Axiom loop : base = base.

  Definition S1_ind (P : S1 -> Type)
             (b: P base)
             (l : loop # b = b)
  : forall x, P x
    := fun x => match x with
                | base => b
                end.

  Axiom S1_ind_eq : forall (P : S1 -> Type)
             (b: P base)
             (l : loop # b = b),
      apD (S1_ind P b l) loop = l.

  Definition S1_rec (B : Type)
             (b: B)
             (l : b = b)
  : S1 -> B
    := fun x => match x with
                | base => b
                end.

  Axiom S1_rec_eq : forall B
             (b: B)
             (l : b = b),
      ap (S1_rec B b l) loop = l.

End Circle.

Variable notS: Type.
Variable notSet : not (IsHSet notS).

Definition loop_not_refl : not (loop = refl base).
Proof.
  intro e.
  apply notSet. apply StreicherK_HSet. intros x p. 
  pose (S1_rec_eq notS x  p). rewrite e in i. apply inverse. exact i.
Defined.



Module Export Suspension.

  Private Inductive Susp (A:Type) : Type :=
  | N : Susp A
  | S : Susp A.
             
  Axiom merid : forall A, A -> (N A) = (S A).

  Arguments N {_}.
  Arguments S {_}.
  Arguments merid {_} _.
  
  Definition Susp_rec A (B : Type)
             (n s: B) 
             (m : A -> n = s)
  : Susp A -> B
    := fun x => match x with
                | N => n
                | S => s
                end.

  Axiom Susp_rec_eq : forall A (B : Type)
             (n s: B) 
             (m : A -> n = s) a,
      ap (Susp_rec A B n s m) (merid a) = m a.
  
  Definition Susp_ind A (P : Susp A -> Type)
             (n : P N)
             (s : P S)
             (m : forall a, (merid a) # n = s)
  : forall x, P x
    := fun x => match x with
                | N => n
                | S => s
                end.

  Axiom Susp_ind_eq : forall A (P : Susp A -> Type)
             (n : P N)
             (s : P S)
             (m : forall a, (merid a) # n = s) a,
      apD (Susp_ind A P n s m) (merid a) = m a.

End Suspension.


Definition Susp_bool_S1 : Susp bool ≃ S1.
Proof.
  unshelve econstructor.
  - unshelve refine (Susp_rec bool S1 _ _ _).
    + exact base.
    + exact base.
    + intro b. destruct b.
      * exact (refl _).
      * exact loop.
  - unshelve refine (isequiv_adjointify _ _ _ _).
    + unshelve refine (S1_rec (Susp bool) _ _).
      * exact N.
      * exact (merid false @ (merid true)^).
    + unshelve refine (Susp_ind bool _ _ _ _); cbn. 
      * reflexivity.
      * exact (merid true).
      * intro b; destruct b; cbn.
        ** rewrite (transport_paths_Fl (g := id) (merid true) (refl N)).
           rewrite ap_id.
           rewrite ap_compose. rewrite Susp_rec_eq.
           cbn. reflexivity. 
        ** rewrite (transport_paths_Fl (g := id) (merid false) (refl N)).
           rewrite ap_id.
           rewrite ap_compose. rewrite Susp_rec_eq.
           rewrite S1_rec_eq. rewrite concat_V. rewrite concat_p1.
           rewrite <- concat_p_pp. rewrite concat_Vp.
           rewrite concat_p1. apply inv2.
    + unshelve refine (S1_ind _ _ _); cbn. 
      * reflexivity.
      * rewrite (transport_paths_Fl (g := id) loop (refl base)).
        cbn. rewrite ap_id.
        rewrite ap_compose. rewrite S1_rec_eq.
        repeat rewrite ap_pp. rewrite ap_V. 
        rewrite Susp_rec_eq. cbn. rewrite concat_p1.
        rewrite concat_V. 
        rewrite inv2. rewrite Susp_rec_eq. 
        rewrite <- concat_p_pp. cbn. apply concat_Vp.
Defined.

Module Export CylinderHIT.
  Private Inductive Cyl {X Y} (f: X -> Y) : Y -> Type :=
    | top : forall x, Cyl f (f x)
    | base : forall y, Cyl f y.

  Axiom cyl_eq : forall {X Y} {f: X -> Y}, (base f) ∘ f == (top f).

  Global Arguments top {X Y f} x.
  Global Arguments base {X Y f} y.
  
  Definition Cyl_ind {X Y} {f: X -> Y}
             (P: forall y, Cyl f y -> Type) 
             (top': forall x, P (f x) (top x))
             (base': forall y, P y (base y))
             (cyl_eq' : forall x, (cyl_eq x) # (base' (f x)) = top' x)
  : forall y (w: Cyl f y), P y w
    := fun y w => match w with
                  | top x => top' x
                  | base x => base' x
                end.
End CylinderHIT.