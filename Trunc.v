Set Universe Polymorphism.

(* To avoid dependencies with the hott library, we will not 
   prove some technical lemmas *)
Axiom admit : forall X, X.
Ltac cheat := apply admit.

Inductive sigT {A:Type} (P:A -> Type) : Type :=
    existT : forall x:A, P x -> sigT P.

Definition projT1 {A} {P:A -> Type} (x:sigT P) : A := match x with
                                      | existT _ a _ => a
                                      end.

Definition projT2  {A} {P:A -> Type} (x:sigT P) : P (projT1 x) :=
  match x return P (projT1 x) with
  | existT _ _ h => h
  end.

Notation "{ x : A & P }" := (sigT (A:=A) (fun x => P)) : type_scope.
Notation "x .1" := (projT1 x) (at level 3).
Notation "x .2" := (projT2 x) (at level 3).
Notation " ( x ; p ) " := (existT _ x p).

Notation id := (fun x => x). 

Notation compose := (fun g f x => g (f x)).

Notation "g ∘ f" := (compose g%function f%function) (at level 1): function_scope.

(* Definition of equality *)

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


Definition concat {A : Type} {x y z : A} (p : x = y) (q : y = z) : x = z.
  destruct p; exact q.
Defined.

Notation "p @ q" := (concat p q) (at level 20).

Definition inverse {A : Type} {x y : A} (p : x = y) : y = x
    := match p with refl _ => refl _ end.

Notation "p ^" := (inverse p) (at level 3, format "p '^'").

Notation "f == g" := (forall x, f x = g x) (at level 3).

Definition apD10 {A} {B:A->Type} {f g : forall x, B x} (h:f=g)
  : f == g
  := fun x => match h with refl _ => refl _  end.

Definition transport {A : Type} (P : A -> Type) {x y : A} (p : x = y) (u : P x) : P y :=
  match p with refl _ => u end.

Notation "p # x" := (transport _ p x) (right associativity, at level 65, only parsing).

Definition concat_p1 A (x y :A) (e: x = y) : e @ refl _ = e.
Proof.
  destruct e; reflexivity.
Defined. 

Definition ap {A B:Type} (f:A -> B) {x y:A} (p:x = y) : f x = f y
  := match p with refl _ => refl _ end.

Definition ap_V {A B : Type} (f : A -> B) {x y : A} (p : x = y) :
  ap f (p^) = (ap f p)^.
Proof.
  destruct p; reflexivity.
Defined.

Definition concat_Vp {A : Type} {x y : A} (p : x = y) : p^ @ p = refl _.
  destruct p; reflexivity.
Defined. 

Definition concat_pV {A : Type} {x y : A} (p : x = y) : p @ p^ = refl _.
  destruct p; reflexivity.
Defined. 

Definition inv2 A (x y :A) (e: x = y) : e^ ^= e.
Proof.
  destruct e; reflexivity.
Defined.

Definition ap_pp {A B : Type} (f : A -> B) {x y z : A} (p : x = y) (q : y = z) :
  ap f (p @ q) = (ap f p) @ (ap f q).
  destruct p; reflexivity. 
Defined.

(* Structure of equality  *)

Definition path_sigma_uncurried {A : Type} (P : A -> Type) (u v : {x:A & P x})
           (pq : {p : u.1 = v.1 & u.2 = p^# v.2})
: u = v.
Proof.
  destruct pq as [p q].
  destruct u as [u1 u2], v as [v1 v2]. cbn in p. cbn in q.
  destruct p. cbn in q. 
  destruct q. exact  (refl (u1;u2)). 
Defined.

Definition pr1_path {A} `{P : A -> Type} {u v : sigT P} (p : u = v) : u.1 = v.1 := ap projT1 p.

Notation "p ..1" := (pr1_path p) (at level 50).

Definition pr2_path {A} `{P : A -> Type} {u v : sigT P} (p : u = v)
  : u.2 = p..1^ # v.2.
  destruct p. reflexivity. 
Defined.
    
Notation "p ..2" := (pr2_path p) (at level 50). 


Definition transport_ap {A B : Type} (P : B -> Type) (f : A -> B) {x y : A}
           (p : x = y) (z : P (f x)) : transport P (ap f p) z =
                                       transport (fun x => P (f x)) p z.
Proof.
  destruct p; reflexivity.
Defined.

Definition transport_paths_l {A : Type} {x1 x2 y : A} (p : x1 = x2) (q : x1 = y)
  : transport (fun x => x = y) p q = p^ @ q.
Proof.
  destruct p, q; reflexivity.
Defined.

Definition transport_paths_r {A : Type} {x y1 y2 : A} (p : y1 = y2) (q : x = y1)
  : transport (fun y => x = y) p q = q @ p.
Proof.
  destruct p. apply (concat_p1 _ _ _ _)^.
Defined.


Definition moveR_M1 {A : Type} {x y : A} (p q : x = y) :
  refl _ = p^ @ q -> p = q.
Proof.
  destruct p. exact id. 
Defined.

Definition concat_1p {A : Type} {x y : A} (p : x = y) :
  refl _ @ p = p := refl _.

Definition moveL_M1 {A : Type} {x y : A} (p q : x = y) :
  refl _ = q @ p^ -> p = q.
Proof.
  destruct p.
  intro h. exact (h @ (concat_p1 _ _ _  _)).
Defined.

Definition moveL_M1' {A : Type} {x y : A} (p q : x = y) :
  q^ @ p = refl _ -> p = q.
Proof.
  destruct p. intro e. rewrite concat_p1 in e.
  rewrite <- inv2. rewrite e. reflexivity.
Defined.

Definition concat_A1p {A : Type} {f : A -> A} (p : forall x, f x = x) {x y : A} (q : x = y) :
  (ap f q) @ (p y) = (p x) @ q.
  destruct q. cbn. apply inverse. apply concat_p1.
Defined.

Definition moveL_Vp {A : Type} {x y z : A} (p : x = z) (q : y = z) (r : x = y) :
  r @ q = p -> r = p @ q ^.
Proof.
  destruct r. cbn in *. destruct 1. destruct q. reflexivity. 
Defined.

Definition concat_p_pp {A : Type} {x y z t : A} (p : x = y) (q : y = z) (r : z = t) :
  p @ (q @ r) = (p @ q) @ r.
  destruct p, q; reflexivity.
Defined.

Definition ap_compose {A B C : Type} (f : A -> B) (g : B -> C) {x y : A} (p : x = y) :
  ap (g ∘ f) p = ap g (ap f p).
  destruct p. reflexivity. Defined. 

Definition concat_pA1 {A : Type} {f : A -> A} (p : forall x, x = f x) {x y : A} (q : x = y) :
  (p x) @ (ap f q) =  q @ (p y).
  destruct q; simpl. apply concat_p1.
Defined.

Definition ap2 {A A' B:Type} (f:A -> A' -> B) {x y:A} (p:x = y)
  {x' y':A'} (q:x' = y') : f x x' = f y y'
  := match p with refl _ => match q with refl _ => refl _ end end.


Class IsEquiv {A : Type} {B : Type} (f : A -> B) := BuildIsEquiv {
  e_inv :> B -> A ;
  e_sect : forall x, e_inv (f x) = x;
  e_retr : forall y, f (e_inv y) = y;
  e_adj : forall x : A, e_retr (f x) = ap f (e_sect x);
}.

Arguments e_inv {_ _} _ {_} _.
Arguments e_sect {_ _} _ {_} _.
Arguments e_retr {_ _} _ {_} _.
Arguments e_adj {_ _} _ {_} _.

Definition Funext := forall (A : Type) (P : A -> Type) f g, IsEquiv (@apD10 A P f g).


Theorem other_adj A B (f:A->B) {H : IsEquiv f} (b : B):
  e_sect f (IsEquiv := H) (e_inv f b) = ap (e_inv f) (e_retr f b).
Proof.
  cheat.
Defined. 

Instance isequiv_inverse A B (f:A->B) {H : IsEquiv f} : IsEquiv (e_inv f) 
    := BuildIsEquiv _ _ (e_inv f) f (e_retr f) (e_sect f) (other_adj _ _ _).

Definition ap_inv_equiv {A B} (f : A -> B) `{IsEquiv _ _ f} x y : f x = f y -> x = y.
Proof.
  intro X. exact ((e_sect f x)^@ ap (e_inv f) X @ e_sect f y).
Defined.

Definition ap_inv_equiv' {A B} (f : A -> B) `{IsEquiv _ _ f} x y : e_inv f x = e_inv f y -> x = y.
Proof.
  intro X. exact ((e_retr f x)^@ ap f X @ e_retr f y).
Defined.


Definition ap_id A (x y:A) (e:x = y) : ap id e = e.
Proof.
  destruct e; reflexivity.
Defined.

Instance IsEquiv_ap_transport A (P : A -> Type) {x y : A} (p : x = y) (u v : P x)
  : IsEquiv (@ap _ _ (fun (X : P x) => p # X) u v).
Proof. 
  unshelve econstructor; cbn. 
  - intros. destruct p. exact X.
  - intro e. destruct p. cbn. apply ap_id.
  - intro e. destruct p. cbn. apply ap_id.
  - intro e; destruct e. destruct p. reflexivity. 
Defined. 

(* can be found in theories/Basics/Equivalences.v *)

Instance isequiv_ap A B {x y : A} (f:A->B) {H:IsEquiv f}
  : IsEquiv (@ap _ _ f x y).
Proof. 
  unshelve econstructor; cbn. 
  - apply ap_inv_equiv. auto. 
  - intro e. destruct e. unfold ap_inv_equiv. cbn. rewrite concat_p1.
    apply concat_Vp.
  - cheat.
  - cheat. 
Defined. 

(* Axiom funext : Funext.  *)

(* Level of homotopy of types *)

Definition IsContr (A:Type) := { x : A & forall y, x = y}.
Existing Class IsContr. 

Definition path_contr {A} `{IsContrA : IsContr A} (x y : A) : x = y
  := let contr := IsContrA.2 in (contr x)^ @ (contr y).

Definition path2_contr {A} `{IsContr A} {x y : A} (p q : x = y) : p = q.
Proof.
  assert (K : forall (r : x = y), r = path_contr x y).
  intro r; destruct r. unfold path_contr.
  symmetry. apply concat_Vp.
  transitivity (path_contr x y). apply K. symmetry; apply
                                                      K. 
Defined.

Definition contr_paths_contr A `{IsContr A} (x y : A) : IsContr (x = y).
  unshelve econstructor.
  exact (path_contr x y).
  exact (path2_contr _).
Defined.


Fixpoint IsTrunc n A := match n with
                           | O => IsContr A
                           | S n => forall x y:A, IsTrunc n (x = y)
                           end.



Definition IsHProp A := IsTrunc 1 A.

Definition IsIrr A := forall x y : A, x = y. 

Definition IsIrr_inhab_IsContr A (H: IsIrr A) : A -> IsContr A :=
  fun x => existT _ x (H x).
  
Definition IsHProp_to_IsIrr A : IsHProp A -> IsIrr A :=
  fun H x y => (H x y).1. 

Definition IsIrr_to_IsHProp A : IsIrr A -> IsHProp A.
  unshelve econstructor.
  apply X.
  intro e. unshelve eapply path2_contr. apply IsIrr_inhab_IsContr; auto.
Defined. 




Definition singleton A (x:A) := {y : A & x = y}.





Definition singleton_IsContr A x : IsContr (singleton A x).
Proof.
  unshelve econstructor.
  unfold singleton. exists x. apply refl.
  intros [y e].
  apply path_sigma_uncurried. cbn. exists e.
   symmetry. eapply concat. apply (transport_paths_r e^ e).
      apply concat_pV.
Defined. 


(* Preservation of homotopy level *)

Definition contr_equiv A B (f : A -> B)
  `{IsContr A} `{IsEquiv A B f}
  : IsContr B.
Proof.
  unshelve econstructor.
  - exact (f H.1).
  - intro b. eapply concat; try exact (e_retr f b).
    apply ap. apply H.2.
Defined. 


Definition trunc_equiv n A B (f : A -> B)
  `{IsTrunc n A} `{IsEquiv A B f}
  : IsTrunc n B.
Proof.
  generalize dependent B; generalize dependent A.
  induction n; cbn ; intros.
  - apply (contr_equiv A B f).
  - unshelve eapply (IHn ((e_inv f x = e_inv f y)) _ (x = y)).
    + apply IsTrunc0.
    + apply ap_inv_equiv. apply isequiv_inverse. 
    + exact (@isequiv_inverse _ _ (ap (e_inv f)) (isequiv_ap B A (e_inv f))).
Defined.

Definition IsTrunc_Forall {funext:Funext} A (B : A -> Type) n
           (H : forall x, IsTrunc n (B x)) : IsTrunc n (forall x, B x).
Proof.
  revert A B H. induction n; intros; cbn.
  - unshelve econstructor.
    + intro a. apply (H a).1.
    + intro f. apply funext. intro a. apply (H a).2.
  - intros f g. unshelve eapply (trunc_equiv _ _ _ (e_inv (apD10))).
    + auto.
    + apply IHn. cbn in H. intro a. exact (H a (f a) (g a)). 
    + apply isequiv_inverse.
Defined. 

(* IsTrunc is a mere proposition *)

Definition IsHProp_IsTrunc n A {funext : Funext} : IsHProp (IsTrunc n A).
Proof.
  apply IsIrr_to_IsHProp; revert A. 
  induction n; cbn in *; intros A H H'. 
  - apply path_sigma_uncurried.  unshelve econstructor.
    apply H.2. apply funext. intro x. unshelve eapply path2_contr.
  - apply funext. intro x. apply funext. intro y.
    eapply IHn.
Defined.



Class Equiv A B := BuildEquiv {
  e_fun :> A -> B ;
  e_isequiv :> IsEquiv e_fun
}.

Notation "A ≃ B" := (Equiv A B) (at level 20).


Arguments e_fun {_ _} _ _.
Arguments e_isequiv {_ _ _}.

Typeclasses Transparent e_fun e_inv.

Coercion e_fun : Equiv >-> Funclass.

Definition e_inv' {A B : Type} (e : A ≃ B) : B -> A := e_inv (e_fun e).
Definition e_sect' {A B : Type} (e : A ≃ B) := e_sect (e_fun e).
Definition e_retr' {A B : Type} (e : A ≃ B) := e_retr (e_fun e).
Definition e_adj' {A B : Type} (e : A ≃ B) := e_adj (e_fun e).


Definition issect'  {A B : Type} (f : A -> B) (g : B -> A)
           (issect : g ∘ f == id) (isretr : f  ∘ g == id) :=
  fun x =>
    ap g (ap f (issect x)^)  @  ap g (isretr (f x))  @  issect x.

Definition is_adjoint' {A B : Type} (f : A -> B) (g : B -> A)
           (issect : g∘ f == id) (isretr : f  ∘ g == id) (a : A) : isretr (f a) = ap f (issect' f g issect isretr a).
Proof.
  unfold issect'.
  apply moveL_M1.
  repeat rewrite ap_pp. rewrite <- concat_p_pp; rewrite <- ap_compose.
  pose  (concat_pA1 (fun b => (isretr b)^) (ap f (issect a))). cbn in i. 
  eapply concat. Focus 2. apply ap2. reflexivity. exact i. cbn. clear i. 
  rewrite <- concat_p_pp.
  pose (concat_A1p (fun b => (isretr b)) (isretr (f a))). cbn in i. 
  apply moveL_Vp in i.
  rewrite <- concat_p_pp in i. rewrite concat_pV in i.
  rewrite concat_p1 in i.
  rewrite ap_compose in i.
  eapply concat. Focus 2. apply ap2. reflexivity.
  rewrite concat_p_pp. eapply concat. Focus 2.
  apply ap2. eapply concat. Focus 2.
  apply ap2. symmetry. apply i. reflexivity.
  symmetry. apply concat_pV. reflexivity. reflexivity.
  repeat rewrite <- ap_compose. cbn. 
  cbn. symmetry. eapply concat. refine (ap_pp ((f ∘ g) ∘f) _ _)^.
  rewrite concat_Vp. reflexivity.
Defined.

Definition isequiv_adjointify {A B : Type} (f : A -> B) (g : B -> A)
           (issect : g∘ f == id) (isretr : f  ∘ g == id)  : IsEquiv f
  := BuildIsEquiv A B f g (issect' f g issect isretr) isretr 
                  (is_adjoint' f g issect isretr).


Definition hfiber {A B : Type} (f : A -> B) (y : B) := { x : A & f x = y }.

Definition hfiber_canonical {A B : Type} (f : A -> B) (x : A) : hfiber f (f x)
  := (x ; refl _).

Definition IsEquiv_hfiber_IsContr {A B : Type} (f : A -> B) :
  IsEquiv f -> forall y, IsContr (hfiber f y).
Proof.
  intros H y. unshelve econstructor.
  - exists (e_inv f y). exact (e_retr f y).
  - intros [x e]. apply path_sigma_uncurried. unshelve econstructor; cbn.
    + destruct e. exact (e_sect f x).
    + destruct e. rewrite <- (transport_ap (fun X => X = f x) f). 
      rewrite (e_adj f). rewrite transport_paths_l. rewrite concat_p1.
      repeat rewrite ap_V. apply (inv2 _ _ _ _)^.
Defined.

Definition hfiber_IsEquiv_IsContr {A B : Type} (f : A -> B) :
  (forall y, IsContr (hfiber f y)) -> IsEquiv f.
Proof.
  intros fib.
  unshelve econstructor.
  - intro y. exact (fib y).1.1.
  - intro x. exact ((fib (f x)).2 (hfiber_canonical f x)..1).    
  - intro y. cbn. apply (fib y).1.2.
  - intro x. cbn. 
    pose ((fib (f x)).2 (hfiber_canonical f x)..2). cbn in i.
    eapply concat; try exact i. rewrite <- (transport_ap (fun X => X = f x) f).
    rewrite transport_paths_l. rewrite concat_p1.
    repeat rewrite ap_V. apply (inv2 _ _ _ _).
Defined.

Definition IsEquiv_compose {funext:Funext} {A B C: Type} (f : A -> B) (H:IsEquiv f)
           : IsEquiv (fun (g:C -> A) => f ∘ g).
Proof.
  simple refine (isequiv_adjointify _ _ _ _).
  - exact (fun g => (e_inv f) ∘ g).
  - cbn. intro g. apply funext. intro b. apply e_sect.
  - cbn. intro g. apply funext. intro a. apply e_retr.
Defined. 
    
Definition IsHProp_inhab_isContr A {H:A -> IsContr A} : IsHProp A.
  apply IsIrr_to_IsHProp. intros x y.
  exact (@path_contr _ (H x) _ _).
Defined.

Definition functor_forall {A B} `{P : A -> Type} `{Q : B -> Type}
    (f : B -> A) (g : forall b:B, P (f b) -> Q b)
  : (forall a:A, P a) -> (forall b:B, Q b) := fun H b => g b (H (f b)).

Instance isequiv_functor_forall {funext : Funext} {A B} {P : A -> Type} {Q : B -> Type}
         (f : B -> A) `{!IsEquiv f} (g : forall b, P (f b) -> Q b) `{!forall b, IsEquiv (g b)}
  : IsEquiv (functor_forall f g).
Proof.
  simple refine (isequiv_adjointify _ _ _ _).
  - refine (functor_forall (e_inv f) _).
    intros a y. generalize (e_inv (g _) y). 
    exact (transport P (e_retr f a)).
  - intros h. apply funext. intro a. unfold functor_forall.
    destruct (e_retr f a). cbn. apply e_sect. 
  - intros h;apply funext. unfold functor_forall. intros b.
    rewrite e_adj. destruct (e_sect f b).
    cbn. apply e_retr.
Defined.

Definition Equiv_inverse {A B : Type} (e: A ≃ B) : B ≃ A := BuildEquiv _ _ (e_inv (e_fun e)) (isequiv_inverse _ _ _).  

Typeclasses Transparent e_fun e_inv.

Instance Equiv_forall (A A' : Type)  (B : A -> Type) (B' : A' -> Type)
         (eA : A ≃ A') (eB : forall x, B (e_inv eA x) ≃ B' x )
         {funext : Funext}
         : (forall x:A , B x) ≃ (forall x:A', B' x).
Proof.
  unshelve refine (BuildEquiv _ _ (functor_forall (e_inv eA) (fun x => e_fun (eB x))) _).
  unshelve eapply isequiv_functor_forall. auto. apply isequiv_inverse.
  intro a'. exact (@e_isequiv _ _ (eB a')). 
Defined.

Fixpoint sigma_map {A B P Q} (f: A -> B) (g : forall a, P a -> Q (f a)) (l : sigT P) : sigT Q :=
  match l with
  | existT _ a l => existT _ (f a) (g a l)
  end. 

Definition sigma_map_compose {A B C P Q R } (f: A -> B) (f' : B -> C)
           (g : forall a, P a -> Q (f a)) (g' : forall b, Q b -> R (f' b))
           (l : sigT P):
  sigma_map f' g' (sigma_map f g l) = sigma_map (f' ∘ f) (fun a l => g' (f a) (g a l)) l.
Proof.
  destruct l; reflexivity.
Defined.

Definition sigma_map_eq {A P} (f: A -> A) (g : forall a, P a -> P (f a))
           (H : forall x, f x = x) (H' : forall a (l : P a), (H a)^ # l = g a l) (l : sigT P) :
 sigma_map f g l = l.
Proof.
  induction l. apply path_sigma_uncurried. unshelve econstructor; cbn; auto.
  symmetry. apply H'. 
Defined.

Definition naturality'  {A B} `{P : A -> Type} `{Q : B -> Type}
           (f : A -> B) 
           (e' : forall a, P a -> Q (f a)) a b (e : a = b) z:
  transport (Q ∘ f) e (e' _ z) = e' _ (e # z).
Proof.
  destruct e. reflexivity.
Defined.

Definition Equiv_Sigma (A A':Type) (B: A -> Type) (B': A' -> Type)
           (eA: A ≃ A') (eB : forall x, B x ≃ B' (e_fun eA x) ) :
  (sigT B) ≃ (sigT B').
Proof.
  unshelve refine (BuildEquiv _ _ _ (isequiv_adjointify _ _ _ _)).
  - unshelve refine (sigma_map eA (fun x => e_fun (eB x))). 
  - pose (sigma_map (e_inv eA) (fun a => e_inv (eB (e_inv eA a)))).
    intro x. apply s. exists x.1.
    apply (transport B' (e_retr eA _)^). exact x.2.
  - intros [a b]. cbn. apply path_sigma_uncurried.
    unshelve econstructor; cbn. apply e_sect.
    rewrite e_adj. rewrite <- ap_V, transport_ap.
    rewrite (naturality' (e_fun eA) eB). 
    apply e_sect.
  - intros [a b].
    cbn. apply path_sigma_uncurried. cbn. 
    unshelve econstructor; apply e_retr. 
Defined. 
