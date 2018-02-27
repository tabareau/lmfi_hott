Set Implicit Arguments.
Generalizable All Variables.

Notation idmap := (fun x => x).
Notation "g 'o' f"  := (fun x => g (f x)) (at level 40, left associativity).

Set Primitive Projections.
Record sigT {A} (P : A -> Type) := exist { π1 : A ; π2 : P π1 }.
Arguments exist {_} _ _ _.
Scheme sigT_rect := Induction for sigT Sort Type.

Notation "{ x & P }" := (sigT (fun x => P)) (only parsing) : type_scope.
Notation "{ x : A & P }" := (sigT (A:=A) (fun x => P)) (only parsing) : type_scope.
Notation "'exists' x .. y , P"
  := (sigT (fun x => .. (sigT (fun y => P)) ..))
       (at level 200, x binder, y binder, right associativity) : type_scope.
Notation "∃ x .. y , P"
  := (sigT (fun x => .. (sigT (fun y => P)) ..))
       (at level 200, x binder, y binder, right associativity) : type_scope.
Notation "( x ; y )" := (exist _ x y) : core_scope.
Notation "( x ; y ; z )" := (x ; (y ; z)) : core_scope.
(* Notation "( x ; y ; .. ; z )" := (exist _ .. (exist _ x y) .. z) : core_scope. *)
Notation pr1 := (@π1 _ _).
Notation pr2 := (@π2 _ _).
Notation "x .1" := (@π1 _ _ x) (at level 3, format "x '.1'") : core_scope.
Notation "x .2" := (@π2 _ _ x) (at level 3, format "x '.2'") : core_scope.

Definition prod A B := sigT (fun _ : A => B).
Notation "A * B" := (prod A B) (at level 40, left associativity) : type_scope.
Notation "A × B" := (prod A B) (at level 90, right associativity) : type_scope.
Definition pair {A B} : A -> B -> A × B := fun x y => (x; y).
Notation "( x , y , .. , z )" := (pair .. (pair x y) .. z) : core_scope.
Definition fst {A B} : A × B -> A := pr1.
Definition snd {A B} : A × B -> B := pr2.

Definition iff (A B : Type) := (A -> B) × (B -> A).
Notation "A <-> B" := (iff A B)%type : type_scope.

Definition transitive_iff {A B C}
  : A <-> B -> B <-> C -> A <-> C.
Proof.
  intros H1 H2. split; firstorder.
Defined.


Open Scope type_scope.

(* ********* Strict Eq ********* *)
Delimit Scope eq_scope with eq.
Open Scope eq_scope.

Local Unset Elimination Schemes.

Inductive Eq {A: Type} (a: A) : A -> Type :=
  refl : Eq a a.

Arguments refl {A a} , [A] a.

Scheme Eq_ind := Induction for Eq Sort Type.
Arguments Eq_ind [A] a P f y e.
Scheme Eq_rec := Minimality for Eq Sort Type.
Arguments Eq_rec [A] a P f y e.

Notation "x ≡ y :> A"
  := (@Eq A x y) (at level 70, y at next level, no associativity) : type_scope.
Notation "x ≡ y"
  := (@Eq _ x y) (at level 70, no associativity) : type_scope.

Axiom Eq_UIP : forall {A: Type} {x y: A} (p q: x ≡ y), p ≡ q.

Lemma Eq_rew A a y P (X : P a) (H : a ≡ y :> A) : P y.
Proof. rewrite <- H. assumption. Defined.

Lemma Eq_rew_r A a y P (X : P y) (H : a ≡ y :> A) : P a.
Proof. rewrite H. assumption. Defined.

Bind Scope eq_scope with Eq.

Definition Einverse {A : Type} {x y : A} (p : x ≡ y) : y ≡ x.
  symmetry; assumption.
Defined.
Arguments Einverse {A x y} p : simpl nomatch.

Definition Econcat {A : Type} {x y z : A} (p : x ≡ y) (q : y ≡ z) : x ≡ z :=
  match p, q with refl, refl => refl end.
Arguments Econcat {A x y z} p q : simpl nomatch.

Notation "'E1'" := refl : eq_scope.
Notation "p E@ q" := (Econcat p%eq q%eq) (at level 20) : eq_scope.
Notation "p ^E" := (Einverse p%eq) (at level 3, format "p '^E'") : eq_scope.

Definition Etransport {A : Type} (P : A -> Type) {x y : A} (p : x ≡ y) (u : P x) : P y :=
  match p with refl => u end.
Arguments Etransport {A}%type_scope P {x y} p%eq_scope u : simpl nomatch.

Notation "p E# x"
  := (Etransport _ p x) (right associativity, at level 65, only parsing) : eq_scope.

Notation "f ≡≡ g" := (forall x, f x ≡ g x) (at level 70, no associativity) : type_scope.

Definition Eap {A B:Type} (f:A -> B) {x y:A} (p:x ≡ y) : f x ≡ f y
  := match p with refl => refl end.
Global Arguments Eap {A B}%type_scope f {x y} p%eq_scope.

Definition EapD10 {A} {B: A -> Type} {f g: forall x, B x} (h: f ≡ g)
  : f ≡≡ g
  := fun x => match h with refl => E1 end.
Global Arguments EapD10 {A%type_scope B} {f g} h%eq_scope _.

Definition Eap10 {A B} {f g: A -> B} (h: f ≡ g) : f ≡≡ g
  := EapD10 h.
Global Arguments Eap10 {A B}%type_scope {f g} h%eq_scope _.

Axiom eq_funext: forall {A: Type} {P : A -> Type} {f g : forall x : A, P x},
    f ≡≡ g -> f ≡ g.

Definition EapD {A:Type} {B:A->Type} (f:forall a:A, B a) {x y:A} (p:x≡y):
  p E# (f x) ≡ f y
  :=
  match p with refl => refl end.
Arguments EapD {A%type_scope B} f {x y} p%eq_scope : simpl nomatch.

Definition Etransport_Vp {A: Type} (P: A -> Type) {x y: A} (p: x ≡ y) (z: P x)
  : p^E E# p E# z ≡ z.
Proof.
  destruct p; reflexivity.
Defined.

Definition Etransport_compose {A B : Type} {x y : A} (P : B -> Type) (f : A -> B)
           (p : x ≡ y) (z : P (f x)) :
  Etransport (fun x0 : A => P (f x0)) p z ≡ Etransport P (Eap f p) z.
destruct p. reflexivity.
Defined.


Definition eq_sigma {A: Type} (P: A -> Type) {x x': A} {y: P x} {y': P x'}
           (p: x ≡ x') (q: p E# y ≡ y')
  : (x; y) ≡ (x'; y').
Proof.
  destruct p, q; reflexivity.
Defined.

Definition Etransport_sigma' {A B : Type} {C : A -> B -> Type}
           {x1 x2 : A} (p : x1 ≡ x2) yz
: Etransport (fun x => sigT (C x)) p yz ≡
  (yz.1 ; Etransport (fun x => C x yz.1) p yz.2).
Proof.
  destruct p. destruct yz. reflexivity.
Defined.

Definition pr1_eq {A : Type} `{P : A -> Type} {u v : sigT P} (p : u ≡ v)
  : u.1 ≡ v.1
  := Eap pr1 p.

Notation "p ..1E" := (pr1_eq p) (at level 3).

Definition pr2_eq {A : Type} `{P : A -> Type} {u v : sigT P} (p : u ≡ v)
  : p..1E E# u.2 ≡ v.2
  := (Etransport_compose P pr1 p u.2)^E
     E@ (@EapD { x & P x} _ pr2 _ _ p).

Notation "p ..2E" := (pr2_eq p) (at level 3).



(* inverse and composition *)
Definition Einv_V {A} {x y : A} (p : x ≡ y)
  : (p^E)^E ≡ p.
  now destruct p.
Defined.

Definition Econcat_Vp {A} {x y : A} (p : x ≡ y)
  : p^E E@ p ≡ E1.
Proof.
  now destruct p.
Defined.

Definition Econcat_pV {A} {x y : A} (p : x ≡ y)
  : p E@ p^E ≡ E1.
Proof.
  now destruct p.
Defined.

Definition Econcat_1p {A} {x y : A} (p : x ≡ y)
  : E1 E@ p ≡ p.
Proof.
  now destruct p.
Defined.

Definition Econcat_p1 {A} {x y : A} (p : x ≡ y)
  : p E@ E1 ≡ p.
Proof.
  now destruct p.
Defined.

Definition Econcat_p_pp {A} {x y z t : A} (p : x ≡ y)
           (q : y ≡ z) (r : z ≡ t)
  : p E@ (q E@ r) ≡ (p E@ q) E@ r.
  now destruct p, q, r.
Defined.

Definition Econcat_pp_p {A} {x y z t : A} (p : x ≡ y)
           (q : y ≡ z) (r : z ≡ t)
  : (p E@ q) E@ r ≡ p E@ (q E@ r).
  now destruct p, q, r.
Defined.


(* Eap *)
Definition Eap_pp {A B} (f : A -> B) {x y z} (p : x ≡ y) (q : y ≡ z)
  : Eap f (p E@ q) ≡ Eap f p E@ Eap f q.
  now destruct p, q.
Defined.

Definition Eap_V {A B} (f : A -> B) {x y : A} (p : x ≡ y)
  : Eap f p^E ≡ (Eap f p)^E.
Proof.
  now destruct p.
Defined.

Definition Eap_const {A B} {x y : A} (p : x ≡ y) (z : B)
  : Eap (fun _ => z) p ≡ E1.
Proof.
  now destruct p.
Defined.

Definition Eap_compose {A B C} (f : A -> B) (g : B -> C) {x y}
           (p : x ≡ y)
  : Eap (g o f) p ≡ Eap g (Eap f p).
  now destruct p.
Defined.



Delimit Scope morphism_scope with morphism.
Delimit Scope category_scope with category.
Delimit Scope object_scope with object.

Local Open Scope morphism_scope.

Reserved Notation "f ∘ g" (at level 40, left associativity).

Record Category : Type :=
  Build_Category {
      object :> Type;
      morphism : object -> object -> Type;

      identity : forall x, morphism x x;
      compose : forall s d d',
          morphism d d'
          -> morphism s d
          -> morphism s d'
      where "f ∘ g" := (compose f g);

      associativity : forall x1 x2 x3 x4
                             (m1 : morphism x1 x2)
                             (m2 : morphism x2 x3)
                             (m3 : morphism x3 x4),
          (m3 ∘ m2) ∘ m1 ≡ m3 ∘ (m2 ∘ m1);

      left_identity : forall a b (f : morphism a b), identity b ∘ f ≡ f;
      right_identity : forall a b (f : morphism a b), f ∘ identity a ≡ f;
    }.

Bind Scope category_scope with Category.
Bind Scope object_scope with object.
Bind Scope morphism_scope with morphism.

Arguments object !C%category / : rename.
Arguments morphism !C%category / s d : rename.
Arguments identity {!C%category} / x%object : rename.
Arguments compose {!C%category} / {s d d'}%object (m1 m2)%morphism : rename.


Global Infix "∘" := compose : morphism_scope.
Global Notation "x --> y" := (morphism _ x y) (at level 99, right associativity, y at level 200) : type_scope.
Global Notation "1" := (identity _) : morphism_scope.

Definition TYPE : Category.
Proof.
  unshelve refine (Build_Category _ _ _ _ _ _).
  - exact Type.
  - exact (fun A B => A -> B).
  - exact (fun A => idmap).
  - exact (fun A B C g f => (fun x => g (f x))).
  - reflexivity.
  - reflexivity.
  - reflexivity.
Defined.

(* Lifting property between f and g *)
Definition LP {C: Category} {x y: C} (f: x --> y) {x' y': C} (g: x' --> y')
  := forall (F: x --> x') (G: y --> y'), g ∘ F ≡ G ∘ f -> ∃ (Ɣ: y --> x'), (Ɣ ∘ f ≡ F) × (g ∘ Ɣ ≡ G).

Definition LLP {C: Category} (R: forall {x y: C}, (x --> y) -> Type) {x y: C} (f: x --> y)
  := forall x' y' (g: x' --> y'), R g -> LP f g.

Definition RLP {C: Category} (L: forall {x y: C}, (x --> y) -> Type) {x' y': C} (g: x' --> y')
  := forall x y (f: x --> y), L f -> LP f g.

Definition LLP_functor {C: Category} (R R': forall {x y: C}, (x --> y) -> Type)
           (RR': forall x y (f: x --> y), R f -> R' f)
           {x y: C} (f: x --> y)
  : LLP (@R') f -> LLP (@R) f.
Proof.
  intros H x' y' g Hg. apply H. apply RR'; assumption.
Defined.

Definition RLP_functor {C: Category} (L L': forall {x y: C}, (x --> y) -> Type)
           (LL': forall x y (f: x --> y), L f -> L' f)
           {x y: C} (f: x --> y)
  : RLP (@L') f -> RLP (@L) f.
Proof.
  intros H x' y' g Hg. apply H. apply LL'; assumption.
Defined.

Record weak_factorization_system {C: Category} (L R: forall {x y: C}, (x --> y) -> Type) :=
  { facto: forall (x z: C) (f: x --> z),
      ∃ y (g: x --> y) (h: y --> z), (h ∘ g ≡ f) × L g × R h;
    LLP_R: forall (x y: C) (f: x --> y), L f <-> LLP (@R) f;
    RLP_L: forall (x y: C) (f: x --> y), R f <-> RLP (@L) f
  }.

Definition wfs_iff_R {C: Category} (L R R': forall {x y: C}, (x --> y) -> Type)
           (H: forall x y (f: x --> y), R f <-> R' f)
           (W: weak_factorization_system (@L) (@R))
  : weak_factorization_system (@L) (@R').
Proof.
  destruct W. eapply Build_weak_factorization_system.
  - intros x z f. destruct (facto0 x z f) as [y [g [h [H1 [H2 H3]]]]].
    refine (y; (g; h; (H1, (H2, _)))). now apply H.
  - intros x y f; split; intro H1.
    + eapply LLP_functor. apply H.
      apply LLP_R0. assumption.
    + apply LLP_R0. eapply LLP_functor.
      apply H. assumption.
  - intros x y f; split; intro H1.
    + apply RLP_L0. apply H. assumption.
    + apply H. eapply RLP_L0. assumption.
Defined.      

Definition wfs_iff_L {C: Category} (L L' R: forall {x y: C}, (x --> y) -> Type)
           (H: forall x y (f: x --> y), L f <-> L' f)
           (W: weak_factorization_system (@L) (@R))
  : weak_factorization_system (@L') (@R).
Proof.
  destruct W. eapply Build_weak_factorization_system.
  - intros x z f. destruct (facto0 x z f) as [y [g [h [H1 [H2 H3]]]]].
    refine (y; (g; h; (H1, (_, H3)))). now apply H.
  - intros x y f; split; intro H1.
    + apply LLP_R0. apply H. assumption.
    + apply H. eapply LLP_R0. assumption.
  - intros x y f; split; intro H1.
    + eapply RLP_functor. apply H.
      apply RLP_L0. assumption.
    + apply RLP_L0. eapply RLP_functor.
      apply H. assumption.
Defined.      


Definition two_out_of_three {C: Category} (W: forall {x y: C}, (x --> y) -> Type)
  := forall (x y z: C) (f: x --> y) (g: y --> z),
    (W f -> W g -> W (g ∘ f)) ×
    (W g -> W (g ∘ f) -> W f) ×
    (W (g ∘ f) -> W f -> W g).

Record model_structure (C: Category) :=
  { W: forall {x y: C}, (x --> y) -> Type;
    F: forall {x y: C}, (x --> y) -> Type;
    C: forall {x y: C}, (x --> y) -> Type;
    tot: two_out_of_three (@W);
    C_AF: weak_factorization_system (@C) (fun x y f => W f × F f);
    AC_F: weak_factorization_system (fun x y f => W f × C f) (@F)
  }.

(* Addition of fibrant types and fibrant equality *)

Axiom Fibrant : Type -> Type.
Existing Class Fibrant.

Notation "'FibrantF' P" := (forall x, Fibrant (P x)) (at level 10) : Fib_scope.
Notation "'FibrantF2' P" := (forall x y, Fibrant (P x y)) (at level 10) : Fib_scope.
Open Scope Fib_scope.

Record TypeF := {
  TypeF_T : Type;
  TypeF_F : Fibrant TypeF_T
}.

Arguments Build_TypeF _ {_}.

Coercion TypeF_T : TypeF >-> Sortclass.
Global Existing Instance TypeF_F.


Axiom Fibrant_forall
  : forall A (B: A -> Type), Fibrant A -> (forall x, Fibrant (B x)) -> Fibrant (forall x, B x).

Axiom Fibrant_sigma
  : forall A (B: A -> Type), Fibrant A -> (forall x, Fibrant (B x)) -> Fibrant (sigT B).

Axiom Fibrant_unit : Fibrant unit.

Module Export Paths.
  Private Inductive paths {A : Type} (a : A) : A -> Type :=
    idpath : paths a a.

  Arguments idpath {A a} , [A] a.

  Definition paths_ind (A : Type) {FibA: Fibrant A} (a : A)
             (P : forall a0 : A, paths a a0 -> Type) {FibP: FibrantF2 P}
             (f: P a idpath) (y : A) (p : paths a y) : P y p
    := match p as p0 in (paths _ y0) return (P y0 p0) with
       | idpath => f
       end.
  Arguments paths_ind [A _] a P [_] f y p.

  Definition paths_rec (A : Type) {FibA: Fibrant A} (a : A) (P : A -> Type)
             {FibP: FibrantF P} (f : P a) (y : A) (p : paths a y)
    : P y :=
    match p in (paths _ y0) return (P y0) with
    | idpath => f
    end.

  Axiom Fibrant_paths : forall (A: Type) {FibA: Fibrant A} (x y: A), Fibrant (paths x y).


  (** The inverse of a path. *)
  Definition inverse {A : Type} {FibA: Fibrant A} {x y : A} (p : paths x y) : paths y x
    := @paths_rec A FibA x (fun y => paths y x) _ idpath y p.

  Definition paths_rec' A {FibA: Fibrant A} a y P {FibP: FibrantF P} (X : P y)
             (H : @paths A a y) : P a
    := @paths_rec A FibA y P FibP X _ (inverse H).

End Paths.

Arguments paths_rec [A _] a P [_] f y p.

Notation "x = y :> A" := (@paths A x y) : type_scope.
Notation "x = y" := (x = y :> _) : type_scope.

Notation "f == g" := (forall x, f x = g x) (at level 70, no associativity) : type_scope.

(* Properties of fibrant equality *)

Definition Eq_to_paths {A : Type} {FibA: Fibrant A} {x y : A} (p : x ≡ y) : x = y :=
  match p with
    | refl => idpath
  end.

Definition concat {A : Type} {FibA: Fibrant A} {x y z : A} (p : x = y) (q : y = z) : x = z.
Proof.
  refine (@paths_rec A _ y (fun z => x = z) _
                  (@paths_rec A _ x (fun y => x = y)_ idpath y p) z q).
Defined.

Arguments concat {A FibA x y z} !p !q.

Delimit Scope path_scope with path.
Open Scope path_scope.

Notation "p @ q" := (concat p%path q%path) (at level 20) : path_scope.
Notation "p ^" := (inverse p%path) (at level 3, format "p '^'") : path_scope.
Notation "1" := idpath : path_scope.

Definition transport {A : Type} {FibA: Fibrant A} (P : A -> Type)
           {FibP: FibrantF P}  {x y : A} (p : x = y) (u : P x) : P y
  := paths_rec x P u y p.

Arguments transport {A}%type_scope {FibA} P {FibP} {x y} p%path_scope u : simpl nomatch.

Notation "p # x"
  := (transport _ p x) (right associativity, at level 65, only parsing) : path_scope.


Record Contr (A: Type) {FibA: Fibrant A} :=
  { center : A;
    contr : forall x, center = x }.

Arguments Contr _ {_}.
Arguments contr _ {_} _ _.


Definition ap {A B: Type} {FibA: Fibrant A} {FibB: Fibrant B} (f: A -> B) {x y: A} (p: x = y)
  : f x = f y
  := paths_rec x (fun y => f x = f y) idpath y p.

Arguments ap {A B}%type_scope {FibA FibB} f {x y} p%path_scope.

Definition apD {A: Type} {FibA: Fibrant A} {B: A -> Type} {FibB: FibrantF B}
           (f: forall a: A, B a) {x y: A} (p: x = y)
  : p # (f x) = f y
  := paths_ind x (fun y p => transport B p (f x) = f y) 1 y p.

Arguments apD {A%type_scope FibA B FibB} f {x y} p%path_scope : simpl nomatch.


Definition ap_pp {A B} {FibA: Fibrant A} {FibB: Fibrant B} (f : A -> B) {x y z : A} (p : x = y) (q : y = z) :
  ap f (p @ q) = (ap f p) @ (ap f q).
Proof.
  revert y p q. unshelve refine (paths_ind _ _ _).
  revert z. unshelve refine (paths_ind _ _ _).
  exact 1.
Defined.

Definition ap_V {A B} {FibA: Fibrant A} {FibB: Fibrant B} (f : A -> B) {x y : A} (p : x = y) :
  ap f (p^) = (ap f p)^.
Proof.
  revert y p. unshelve refine (paths_ind _ _ _).
  exact 1.
Defined.

Definition inv_pp {A} {FibA: Fibrant A} {x y z : A} (p : x = y) (q : y = z) :
  (p @ q)^ = q^ @ p^.
Proof.
  revert y p q. unshelve refine (paths_ind _ _ _).
  revert z. unshelve refine (paths_ind _ _ _).
  exact 1.
Defined.

Definition inv_V {A} {FibA: Fibrant A} {x y : A} (p : x = y) :
  p^^ = p.
Proof.
  revert y p. unshelve refine (paths_ind _ _ _).
  exact 1.
Defined.

Definition ap_compose {A B C} {FibA: Fibrant A} {FibB: Fibrant B} {FibC: Fibrant C} (f : A -> B) (g : B -> C) {x y : A} (p : x = y) :
  ap (fun x => g (f x)) p = ap g (ap f p).
Proof.
  revert y p. unshelve refine (paths_ind _ _ _).
  exact 1.
Defined.

Definition concat_p_pp {A} {FibA: Fibrant A} {x y z t : A} (p : x = y) (q : y = z) (r : z = t) :
  p @ (q @ r) = (p @ q) @ r.
Proof.
  revert y p q r. unshelve refine (paths_ind _ _ _).
  revert z. unshelve refine (paths_ind _ _ _).
  revert t. unshelve refine (paths_ind _ _ _).
  exact 1.
Defined.

Definition concat_pp_p {A} {FibA: Fibrant A} {x y z t : A} (p : x = y) (q : y = z) (r : z = t) :
  (p @ q) @ r = p @ (q @ r).
Proof.
  revert y p q r. unshelve refine (paths_ind _ _ _).
  revert z. unshelve refine (paths_ind _ _ _).
  revert t. unshelve refine (paths_ind _ _ _).
  exact 1.
Defined.

Definition concat_1p {A} {FibA: Fibrant A} {x y: A} (p: x = y)
  : 1 @ p = p.
Proof.
  revert y p. unshelve refine (paths_ind _ _ _).
  exact 1.
Defined.

Definition concat_p1 {A} {FibA: Fibrant A} {x y: A} (p: x = y)
  : p @ 1 = p.
Proof.
  revert y p. unshelve refine (paths_ind _ _ _).
  exact 1.
Defined.

Definition concat_pV {A} {FibA: Fibrant A} {x y : A} (p : x = y) :
  p @ p^ = 1
  := paths_ind x (fun y p => p @ p^ = 1) 1 _ _.

Definition concat_Vp {A} {FibA: Fibrant A} {x y : A} (p : x = y) :
  p^ @ p = 1
  := paths_ind x (fun y p => p^ @ p = 1) 1 _ _.

Definition moveR_Vp {A} {FibA: Fibrant A} {x y z : A} (p : x = z) (q : y = z) (r : x = y) :
  p = r @ q -> r^ @ p = q.
Proof.
  revert y r q. unshelve refine (paths_ind _ _ _). intro q. 
  intro h. exact (concat_1p _ @ h @ concat_1p _).
Defined.

Definition moveL_Vp {A} {FibA: Fibrant A} {x y z : A} (p : x = z) (q : y = z) (r : x = y) :
  r @ q = p -> q = r^ @ p.
Proof.
  revert y r q. unshelve refine (paths_ind _ _ _). intro q. 
  intro h. exact ((concat_1p _)^ @ h @ (concat_1p _)^).
Defined.

Definition moveR_M1 {A} {FibA: Fibrant A} {x y : A} (p q : x = y) :
  1 = p^ @ q -> p = q.
Proof.
  revert y p q. unshelve refine (paths_ind _ _ _). intro q. 
  intro h. exact (h @ (concat_1p _)).
Defined.

Definition concat_pA1 {A} {FibA: Fibrant A} {f : A -> A} (p : forall x, x = f x) {x y : A} (q : x = y) :
  (p x) @ (ap f q) =  q @ (p y)
    := paths_ind x (fun y q => (p x) @ (ap f q) = q @ (p y))
               (concat_p1 _ @ (concat_1p _)^) y q.


Definition path_sigma {A: Type} {FibA: Fibrant A}
           (P: A -> Type) {FibP: FibrantF P}
           {x x': A} {y: P x} {y': P x'}
           (p: x = x') (q: p # y = y')
  : (x; y) = (x'; y').
Proof.
  revert x' p y' q. unshelve refine (paths_ind _ _ _). 
  unshelve refine (paths_ind _ _ _).
  exact 1.
Defined.

Definition path_contr {A} {FibA: Fibrant A} {HA: Contr A} (x y : A)
  : x = y.
Proof.
  exact ((contr _ _ _)^ @ contr _ HA _).
Defined.

Definition transport_compose {A B} {FibA: Fibrant A} {FibB: Fibrant B}
           {x y: A} (P: B -> Type) {FibP : FibrantF P}
           (f : A -> B) (p : x = y) (z : P (f x))
  : transport (fun x => P (f x)) p z = transport P (ap f p) z.
Proof.
  revert y p. unshelve refine (paths_ind _ _ _). 
  exact 1.
Defined.

Definition transport_const {A B} {FibA: Fibrant A} {FibB: Fibrant B}
           {x1 x2 : A} (p : x1 = x2) (y : B)
  : transport (fun x => B) p y = y.
Proof.
  refine (paths_ind x1 (fun x2 p => p # y = y) 1 x2 p).
Defined.

Definition transport_paths_r A {FibA: Fibrant A} {x y1 y2: A}
           (p : y1 = y2) (q : x = y1)
  : transport (fun y : A => x = y) p q = q @ p.
Proof.
  revert y2 p. unshelve refine (paths_ind _ _ _). 
  revert y1 q. unshelve refine (paths_ind _ _ _). 
  exact 1.
Defined.

Definition transport_paths_Fl {A B} {FibA: Fibrant A} {FibB: Fibrant B} 
           (f: A -> B) {x1 x2: A} {y: B} (p: x1 = x2) (q: f x1 = y)
  : transport (fun x : A => f x = y) p q = (ap f p)^ @ q.
Proof.
  revert x2 p. unshelve refine (paths_ind _ _ _). 
  revert y q. unshelve refine (paths_ind _ _ _). 
  exact 1.
Defined.

Definition transport_paths_Fr {A B} {FibA: Fibrant A} {FibB: Fibrant B} 
           (f: A -> B) {x1 x2: A} {y: B} (p: x1 = x2) (q: y = f x1)
  : transport (fun x : A => y = f x) p q = q @ ap f p.
Proof.
  revert x2 p. unshelve refine (paths_ind _ _ _). 
  exact (concat_p1 _)^.
Defined.

Definition concat_Ep {A} {FibA: Fibrant A} {x y z : A} (e: x ≡ y) (p: y = z) : x = z
  := Etransport (fun u => u = z) e^E p.

Definition concat_EVp {A} {FibA: Fibrant A} {x y z : A} (e: y ≡ x) (p: y = z) : x = z
  := Etransport (fun u => u = z) e p.

Definition concat_pE {A} {FibA: Fibrant A} {x y z : A} (p: x = y) (e: y ≡ z) : x = z
  := Etransport (fun v => x = v) e p.

Definition concat_Ep_ETP {A} {FibA: Fibrant A} {x y z: A} (e: x ≡ y :> A) (p: y ≡ z)
  : concat_Ep e (Eq_to_paths p) ≡ Eq_to_paths (e E@ p).
Proof.
  now destruct e, p.
Defined.

Definition concat_EVp_ETP {A} {FibA: Fibrant A} {x y z: A} (e: y ≡ x :> A) (p: y ≡ z)
  : concat_EVp e (Eq_to_paths p) ≡ Eq_to_paths (e^E E@ p).
Proof.
  now destruct e, p.
Defined.

Definition concat_pE_ETP {A} {FibA: Fibrant A} {x y z: A} (p: x ≡ y) (e: y ≡ z)
  : concat_pE (Eq_to_paths p) e ≡ Eq_to_paths (p E@ e).
Proof.
  now destruct e, p.
Defined.

Definition ap_concat_Ep {A B} {FibA: Fibrant A}  {FibB: Fibrant B} (f: A -> B)
           {x y z: A} (e: x ≡ y :> A) (p: y = z)
  : ap f (concat_Ep e p) ≡ concat_Ep (Eap f e) (ap f p).
Proof.
    now destruct e.
Defined.

Definition ap_concat_EVp {A B} {FibA: Fibrant A} {FibB: Fibrant B} (f: A -> B)
           {x y z: A} (e: y ≡ x) (p: y = z)
  : ap f (concat_EVp e p) ≡ concat_EVp (Eap f e) (ap f p).
Proof.
    now destruct e.
Defined.

Definition ap_concat_pE {A B} {FibA: Fibrant A} {FibB: Fibrant B} (f: A -> B)
           {x y z: A} (p: x = y) (e: y ≡ z)
  : ap f (concat_pE p e) ≡ concat_pE (ap f p) (Eap f e).
Proof.
    now destruct e.
Defined.

Definition Etransport_paths_FlFrE {A B} {FibB: Fibrant B} {f g: A -> B} {x1 x2: A} (p: x1 ≡ x2) (q: f x1 ≡ g x1)
  : Etransport (fun x => f x = g x) p (Eq_to_paths q) ≡ Eq_to_paths ((Eap f p^E) E@ q E@ (Eap g p)).
Proof.
  destruct p; simpl. apply Eap. now destruct q.
Defined.



(* Equivalences for univalent equality *)

Record IsEquiv {A B} {FibA: Fibrant A} {FibB: Fibrant B} (f: A -> B) :=
  { equiv_inv : B -> A ;
    eisretr : f o equiv_inv == idmap;
    eissect : equiv_inv o f == idmap;
    eisadj :  forall x : A, eisretr (f x) = ap f (eissect x) }.

Arguments equiv_inv {_ _ _ _ _} _ _.
Arguments eisretr {_ _ _ _ _} _ _.
Arguments eissect {_ _ _ _ _} _ _.
Arguments eisadj {_ _ _ _ _} _ _.

Definition isequiv_adjointify {A B} {FibA: Fibrant A} {FibB: Fibrant B} {f: A -> B}
           (g: B -> A) : f o g == idmap -> g o f == idmap -> IsEquiv f.
Proof.
  intros isretr issect. unshelve eapply Build_IsEquiv.
  exact g. exact isretr.
  exact (fun x => ap g (ap f (issect x)^) @ ap g (isretr (f x)) @ issect x).
  intro a; cbn.
  apply moveR_M1.
  repeat (rewrite ap_pp; rewrite concat_p_pp); rewrite (ap_compose _ _ _)^.
  rewrite (concat_pA1 (fun b => (isretr b)^) (ap f (issect a)^)).
  repeat rewrite concat_pp_p; rewrite ap_V; apply moveL_Vp; rewrite concat_p1.
  rewrite concat_p_pp; rewrite (ap_compose _ _ _)^.
  rewrite (concat_pA1 (fun b => (isretr b)^) (isretr (f a))).
  rewrite concat_pV; rewrite concat_1p.
  exact 1.
Defined.

Definition isequiv_compose {A B C} {FibA: Fibrant A} {FibB: Fibrant B} {FibC: Fibrant C}
           {f: A -> B} (Hf: IsEquiv f) {g: B -> C} (Hg: IsEquiv g)
  : IsEquiv (g o f).
Proof.
  unshelve eapply isequiv_adjointify.
  exact ((equiv_inv Hf) o (equiv_inv Hg)).
  exact (fun c => ap g (eisretr _ (equiv_inv Hg c)) @ eisretr _ c).
  exact (fun a => ap _ (eissect _ (f a)) @ eissect _ a).
Defined.

Definition cancelR_isequiv {A B C} {FibA: Fibrant A} {FibB: Fibrant B} {FibC: Fibrant C}
           (f : A -> B) {g : B -> C}
           {Hf: IsEquiv f} {Hgf: IsEquiv (g o f)}
  : IsEquiv g.
Proof.
  unshelve eapply isequiv_adjointify.
  exact (f o (equiv_inv Hgf)).
  intro x; cbn. exact (eisretr Hgf x).
  intro x; cbn.
  refine (ap (fun x => f (equiv_inv Hgf (g x))) (eisretr Hf x)^ @ _).
  refine (ap f (eissect Hgf _) @ _).
  apply eisretr.
Defined.

Definition cancelL_isequiv {A B C} {FibA: Fibrant A} {FibB: Fibrant B} {FibC: Fibrant C}
           (g : B -> C) {f : A -> B}
           {Hg: IsEquiv g} {Hgf: IsEquiv (g o f)}
  : IsEquiv f.
Proof.
  unshelve eapply isequiv_adjointify.
  exact ((equiv_inv Hgf) o g).
  intro x; cbn.
  refine ((eissect Hg _)^ @ _).
  refine (ap (equiv_inv Hg) (eisretr Hgf _) @ _).
  apply eissect.
  intro x; cbn. exact (eissect Hgf x).
Defined.


(* FType is category *) 

Definition FTYPE : Category.
Proof.
  unshelve eapply Build_Category.
  - exact TypeF.
  - exact (fun A B => A -> B).
  - exact (fun A => idmap). 
  - exact (fun A B C g f => fun x => g (f x)).
  - reflexivity.
  - reflexivity.
  - reflexivity.
Defined.


Record Retract {A B} (g : A -> B) {A' B'} (f : A' -> B') :=
  { ret_s : A -> A' ;
    ret_r : A' -> A ;
    ret_s' : B -> B' ;
    ret_r' : B' -> B ;
    ret_sr : ret_r o ret_s ≡≡ idmap ;
    ret_sr' : ret_r' o ret_s' ≡≡ idmap;
    ret_H1 : f o ret_s ≡≡ ret_s' o g ;
    ret_H2 : ret_r' o f ≡≡ g o ret_r }.
Unset Implicit Arguments.

Global Arguments Build_Retract {A B g A' B' f} s r s' r' sr sr' H1 H2 : rename.

Infix "RetractOf" := Retract (at level 30).

Lemma LP_Retract {A A' B' B C C' D D'}
      {f: A -> A'} {g: B' -> B} {f': C -> C'} {g': D' -> D}
      (Hf : f' RetractOf f) (Hg : g' RetractOf g)
  : LP (C:=TYPE) f g -> LP (C:=TYPE) f' g'.
Proof.
  intros H F G H1; cbn in *.
  assert (X: g o (ret_s Hg o F o ret_r Hf) ≡≡ ret_s' Hg o G o ret_r' Hf o f). {
    intro. refine (ret_H1 Hg _ E@ _). apply Eap.
    refine (Eap10 H1 _ E@ _). apply Eap.
    exact (ret_H2 Hf _)^E. }
  specialize (H ((ret_s Hg) o F o (ret_r Hf)) ((ret_s' Hg) o G o (ret_r' Hf)) (eq_funext X)).
  destruct H as [h [H2 H3]]; cbn in *.
  exists ((ret_r Hg) o h o (ret_s' Hf)). split; apply eq_funext; intro x; simpl.
  - transitivity (ret_r Hg (h (f (ret_s Hf x)))).
    repeat apply Eap. exact (ret_H1 Hf _)^E.
    transitivity (ret_r Hg (ret_s Hg (F (ret_r Hf (ret_s Hf x))))).
    apply Eap. apply (Eap10 H2).
    transitivity (F (ret_r Hf (ret_s Hf x))).
    apply (ret_sr Hg). apply Eap. apply (ret_sr Hf).
  - refine ((ret_H2 Hg _)^E E@ _).
    refine (Eap _ (Eap10 H3 _) E@ _).
    refine (ret_sr' Hg _ E@ _).
    apply Eap. exact (ret_sr' Hf _).
Defined.


Definition retract_id {A B} (f: A -> B) : f RetractOf f.
Proof.
  unshelve eapply Build_Retract; intro; cbn; try reflexivity.
Defined.

Definition LP_TYPE_FTYPE {A B A' B': TypeF} {f: A -> B} {g: A' -> B'}
  : LP (C:=TYPE) f g -> LP (C:=FTYPE) f g.
  auto.
Defined.

(* Definition of Fibrations *)

Record IsFibration {A B} (f : A -> B) := 
  { fib_A : Type ;
    fib_P : fib_A -> Type ;
    fib_Fib : FibrantF fib_P;
    fib_H : f RetractOf (@π1 _ fib_P) }.

Global Arguments Build_IsFibration {A B f B'} P {FibP} H : rename.

Notation Fib := @IsFibration.

Definition fiber {A B} (f: A -> B) := fun y => ∃ x, f x = y.

Let inf_fib {A B} (f: A -> B) : A -> ∃ y, fiber f y
  := fun x => (f x ; x ; 1).

Notation "` A" := (Build_TypeF A) (at level 10).



Definition LP_inf_fib_F {A B: TypeF} (f: A -> B)
  : LLP (C:=FTYPE) Fib (inf_fib f : `_ -> `_).
Proof.
  intros A'' B'' g [B' P HP Hg]. apply LP_TYPE_FTYPE.
  refine(LP_Retract (retract_id _) Hg _).
  intros F G H; cbn in *.
  unshelve refine (let α : ((∃ y, fiber f y) -> ∃ y, P (G y)) := _ in _). {
    refine (fun y => (y; _)).
    destruct y as [y [x p]].
    pose proof (Etransport P (Eap10 H x) (@π2 _ _ (F x))); cbn in X.
    revert y p ; unshelve refine (paths_ind _ _ _). exact X. }
  unshelve refine (let β: ((∃ y, P (G y)) -> sigT P) := _ in _). {
    exact (fun w => (G (@π1 _ _ w); @π2 _ _ w)). }
  exists (β o α). split; [|reflexivity].
  apply eq_funext; intro x.
  unshelve eapply eq_sigma; cbn. exact (Eap10 H _)^E.
  now rewrite Etransport_Vp.
Defined.

Definition wfs_AC_F : weak_factorization_system (@LLP FTYPE (@IsFibration)) (@IsFibration).
Proof.
  unshelve eapply Build_weak_factorization_system; cbn.
  - intros A B f. exists (` (∃ y, fiber f y)).
    exists (inf_fib f). exists (@π1 _ _).
    split; [reflexivity|]. split.
    (* + apply LP_inf_fib_F.  bug?? *)
    + apply (LP_inf_fib_F _).
    + refine (Build_IsFibration _ (retract_id _)).
  - intros A B f; split; auto.
  - intros A B f; split; intros Hf.
    + intros A' B' g Hg. now apply Hg.
    + assert (LP (C:=FTYPE) (inf_fib f: `_ -> `_) f). {
        apply Hf. apply LP_inf_fib_F. }
      cbn in X. unfold LP in X. 
      specialize (X idmap (@π1 _ _) E1); cbn in X. destruct X as [g [Hg1 Hg2]].
      refine (Build_IsFibration (fiber f) _).
      refine (Build_Retract (inf_fib f) g idmap idmap _ _ _ _);
        intro; try reflexivity; cbn.
      exact (Eap10 Hg1 _). exact (Eap10 Hg2^E _).
Defined.


Record AFib A B (f : A -> B) := (* F *)
  { afib_A : TypeF ;
    afib_P : afib_A -> Type ;
    afib_Fib : FibrantF afib_P ;
    afib_H1 : forall y, Contr (afib_P y) ;
    afib_H2 : f RetractOf (@π1 _ afib_P) }.

Global Arguments Build_AFib {A B f B'} P {FibP} HP H : rename.

Definition AFib_Fib {A B} (f: A -> B)
  : AFib _ _ f -> Fib _ _ f.
Proof.
  intros [B' P FibP HP H].
  exact (Build_IsFibration _ H).
Defined.


Module Export CylinderHIT.
  Private Inductive Cyl {X Y} (f: X -> Y) : Y -> Type :=
    | top : forall x, Cyl f (f x)
    | base : forall y, Cyl f y.

  Axiom cyl_eq : forall {X Y} {f: X -> Y}, (base f) o f == top f.

  Global Arguments top {X Y f} x.
  Global Arguments base {X Y f} y.
  
  Axiom Fibrant_Cyl : forall {X Y} {FibX: Fibrant X} {FibY: Fibrant Y} {f: X -> Y}, FibrantF (Cyl f).

  Definition Cyl_ind {X Y} {FibX: Fibrant X} {FibY: Fibrant Y} {f: X -> Y}
             (P: forall y, Cyl f y -> Type) {FibP: FibrantF2 P}
             (top': forall x, P (f x) (top x))
             (base': forall y, P y (base y))
             (cyl_eq' : forall x, (cyl_eq x) # (base' (f x)) = top' x)
  : forall y (w: Cyl f y), P y w
    := fun y w => match w with
                  | top x => top' x
                  | base x => base' x
                end.
End CylinderHIT.


Section Cylinder.
  Context {X Y} {FibX: Fibrant X} {FibY: Fibrant Y} {f: X -> Y}.

  Definition Cyl_Contr (y: Y) : Contr (Cyl f y).
  Proof.
    exists (base y).
    revert y. unshelve refine (Cyl_ind (fun y x => base y = x) _ _ _).
    - exact cyl_eq.
    - intro. exact 1.
    - intros x; cbn.
      refine (transport_paths_r (x:= base (f x)) (cyl_eq x) 1 @ _).
      exact (concat_1p _).
  Defined.

  (* ∃ y, Cyl f y  is the homotopy pushout of f and idmap *)
  Definition sig_cyl_ind (P: sigT (Cyl f) -> Type) {FibP: FibrantF P}
             (top': forall x, P (f x; top x))
             (base': forall y, P (y; base y))
             (cyl_eq': forall x,
                 transport (fun w => P (f x; w)) (cyl_eq x) (base' (f x)) = top' x)
    : forall w, P w.
  Proof.
    intros [y w].
    exact (Cyl_ind (fun y w => P (y; w)) top' base' cyl_eq' y w).
  Defined.

  Definition sig_cyl_rec P {FibP: Fibrant P}
             (top': X -> P) (base': Y -> P)
             (cyl_eq': forall x, base' (f x) = top' x)
    : (sigT (Cyl f)) -> P.
  Proof.
    intros [y w].
    refine (Cyl_ind (fun y w => P) top' base' _ y w); cbn.
    intro x. exact (transport_const _ _ @ cyl_eq' _).
  Defined.

  Definition top' : X -> exists y, Cyl f y := fun x => (f x; top x).
  Definition base' : Y -> exists y, Cyl f y := fun y => (y; base y).

End Cylinder.

Definition LP_top'_AF {A B: TypeF} (f: A -> B)
  : LLP (C:=FTYPE) AFib (top' (f:=f): `_ -> `_).
Proof.
  intros A'' B'' g [B' P FibP HP Hg].
  refine (LP_Retract (g:=_:`_ -> `_) (retract_id _) Hg _).
  clear g Hg. intros F G H; cbn in *.
  unshelve eexists.
  - intro w. exists (G w). revert w.
    unshelve eapply sig_cyl_ind; cbn.
    + intro x. exact ((Eap10 H x) E# (F x).2).
    + intro y. eapply center. apply HP.
    + intro; cbn. unshelve eapply path_contr. apply HP. 
  - split; cbn. 2: reflexivity.
    apply eq_funext; intro x. unshelve eapply eq_sigma. exact (Eap10 H x)^E.
    rewrite Etransport_Vp. reflexivity.
Defined.

Definition wfs_C_AF : weak_factorization_system (@LLP FTYPE AFib) AFib.
Proof.
  eapply Build_weak_factorization_system; cbn.
  - intros A B f. exists (` (sigT (Cyl f))).
    exists top'. exists (@π1 _ _).
    split; [reflexivity|]. split.
    + exact (LP_top'_AF _).
    + refine(Build_AFib _ _ (retract_id _)); cbn.
      apply Cyl_Contr.
  - intros; split; auto.
  - intros A B f; split; intros Hf.
    + intros A' B' g Hg. now apply Hg.
    + assert (LP (C:=FTYPE) (top' (f:=f): `_ -> `_) f). {
        apply Hf. apply LP_top'_AF. }
      specialize (X idmap (@π1 _ _) E1); cbn in X. destruct X as [g [Hg1 Hg2]].
      refine(Build_AFib (Cyl f) _ _); cbn.
      apply Cyl_Contr.
      refine (Build_Retract top' g idmap idmap _ _ _ _);
        intro; try reflexivity; cbn.
      exact (Eap10 Hg1 _). exact (Eap10 Hg2^E _). 
Defined.


Definition weak_eq_retract {A B A' B': TypeF}
           (f: A -> B) (inf_fib: A' -> B')
           (Hinf_fib: inf_fib RetractOf f) (Hf: IsEquiv f)
  : IsEquiv inf_fib.
Proof.
  destruct Hf as [g Hg1 Hg2].
  destruct Hinf_fib as [s r s' r' sr sr' Hf1 Hf2].
  refine (isequiv_adjointify (r o g o s') _ _); intro.
  - rewrite <- Hf2. refine(ap _ (Hg1 _) @ _). apply Eq_to_paths, sr'.
  - rewrite <- Hf1. refine(ap _ (Hg2 _) @ _). apply Eq_to_paths, sr.
Defined.

Definition two_out_of_three_weak_equiv
  : @two_out_of_three FTYPE (fun _ _ f => IsEquiv f).
Proof.
  intros A B C f g; cbn in *. repeat split; intros H1 H2.
  - now apply isequiv_compose.
  - refine(cancelL_isequiv (g:=g)); assumption. 
  - refine(cancelR_isequiv (f:=f)); assumption. 
Defined.

Definition AFib_aux {B: TypeF} {P: B -> Type} {FibP: FibrantF P} (H: IsEquiv (@π1 _ P))
  : forall y, Contr (P y).
Proof.
  destruct H as [g Hg1 Hg2 Hg3]. intro y.
  unshelve eapply Build_Contr.
  - refine ((Hg1 y) # (g y).2).
  - intro w.
    specialize (Hg3 (y; w)); cbn in Hg3. rewrite Hg3; clear Hg3.
    rewrite (transport_compose P (@π1 _ _) (Hg2 (y; w)) _)^.
    exact (apD _ (Hg2 (y; w))).
Defined.

Definition AFib_ok {A B: TypeF} (f: A -> B)
  : AFib _ _ f  <->  (IsEquiv f × Fib _ _ f).
Proof.
  split; intro H.
  - split.
    + destruct H as [B' P FibP HP Hf].
      refine(weak_eq_retract (_ : ` _ -> ` _) _ Hf _). clear f Hf; cbn.
      unshelve eapply isequiv_adjointify.
      * intro x; exists x; apply HP.
      * intro; exact 1.
      * intros [x w]; cbn.
        rewrite (contr _ _ w). exact 1.
    + destruct H as [B' P FibP H1 H2]. econstructor. eassumption. exact H2.
  - refine(Build_AFib (fiber f) _ _).
    + pose proof (two_out_of_three_weak_equiv _ _ _ (inf_fib f: `_ -> `_) (pr1: `_ -> `_)); cbn in X.
      destruct X as [_ [_ H2]]. specialize (H2 (fst H)).
      refine (AFib_aux (P:=fiber f) (H2 _)).
      clear H2 H. destruct A, B.
      unshelve eapply isequiv_adjointify.
      * exact (fun w => w.2.1).
      * intros [y [x p]]; cbn. unfold inf_fib.
        revert y p. unshelve refine (paths_ind _ _ _).
        exact 1.
      * intro; exact 1.
    + assert (LP (C:=FTYPE) (inf_fib f: `_ -> `_) f). {
        apply LP_inf_fib_F. apply H. }
      specialize (X idmap pr1 E1); cbn in X. destruct X as [g [Hg1 Hg2]].
      refine (Build_Retract (inf_fib f) g idmap idmap _ _ _ _);
        intro; try reflexivity; cbn.
      exact (Eap10 Hg1 _). exact (Eap10 Hg2^E _).
Defined.

Definition LLPAFib_ok {A B: TypeF} (f: A -> B)
  : LLP (C:=FTYPE) Fib f  <->  (IsEquiv f × LLP (C:=FTYPE) AFib f).
Proof.
  split.
  - intro H; split.
    + unshelve refine(let X := H _ B (pr1: `_ -> `_) _ (inf_fib f) idmap E1 in _).
      refine (Build_IsFibration _ (retract_id _)).
      destruct X as [g [Hg1 Hg2]]; cbn in *.
      destruct A, B. unshelve eapply isequiv_adjointify.
      * exact (fun w => (g w).2.1).
      * intro x; pose (g x).2.2. cbn in *.
        rewrite p. apply Eq_to_paths. exact (Eap10 Hg2 _).
      * intro x; cbn. rewrite (Eap10 Hg1 x). exact 1.
    + intros A' B' F Hf. apply H. now apply AFib_Fib.
  - intros [H2 H1] A' B' g Hg.
    refine(LP_Retract (f:=inf_fib f: `_ -> `_) _ (retract_id _) _).
    +  clear A' B' g Hg.
       assert (X : AFib (sigT (fiber f)) B pr1). {
         destruct H2 as [g Hg1 Hg2 Hg3].
         refine(Build_AFib _ _ (retract_id _)).
         intro y; cbn. exists (g y; Hg1 _).
         intros [x p].
         refine(path_sigma _ ((ap g p)^ @ Hg2 _) _).
         rewrite transport_paths_Fl. rewrite ap_pp. rewrite (Hg3 _)^.
         rewrite ap_V. rewrite inv_pp. rewrite inv_V.
         rewrite (ap_compose g f _)^.
         rewrite concat_pp_p. refine (moveR_Vp _ _ _).
         revert y p. unshelve refine (paths_ind _ _ _).
         cbn. exact (concat_1p _ @ (concat_p1 _)^). }
       specialize (H1 (` (sigT (fiber f))) B pr1 X (inf_fib f) idmap E1); clear X.
       destruct H1 as [Ɣ [H H']]; cbn in *.
       unshelve refine (Build_Retract idmap idmap Ɣ pr1 _ _ _ _); intro; try reflexivity.
       exact (Eap10 H' _). exact (Eap10 H^E _).
    + now refine(LP_inf_fib_F _ _ _ _ _).
Defined.


Definition fibrant_types_give_fibrations {A: Type} {FibA: Fibrant A}
  : IsFibration (fun _:A => tt).
Proof.
  unshelve refine(Build_IsFibration (fun _:`unit => A) _).
  unshelve refine(Build_Retract (fun x => (tt; x)) (@π2 _ (fun _:unit => A)) idmap idmap _ _ _ _);
    intro; try reflexivity; cbn.
  destruct x as [[] y]; reflexivity.
Defined.


Definition type_model_structure : model_structure FTYPE.
Proof.
  unshelve eapply Build_model_structure.
  - exact (fun _ _ f => IsEquiv f).
  - exact Fib. 
  - exact (@LLP FTYPE AFib).
  - apply two_out_of_three_weak_equiv.
  - eapply wfs_iff_R. apply @AFib_ok.
    exact wfs_C_AF.
  - eapply wfs_iff_L. apply @LLPAFib_ok. exact wfs_AC_F.
Defined.
