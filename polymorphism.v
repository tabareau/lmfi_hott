Set Printing Universes.

(* a basic example *)

Definition identity {A : Type} (a : A) := a.

Fail Definition selfid := identity (@identity).

Polymorphic Definition pidentity {A : Type} (a : A) := a.

Definition selfpid := pidentity (pidentity).

Print selfpid.


(* A more interesting example *)

Record _PreCategory :=
  { _obj :> Type;
    _hom : forall a b : _obj, Type ; 
    _id : forall a, _hom a a ;
    _comp : forall a b c, _hom b c -> _hom a b -> _hom a c }.

Record _PreFunctor (C D : _PreCategory) :=
  { _fun_obj : C.(_obj) -> D.(_obj);
    _fun_hom : forall c c' : C.(_obj), _hom _ c c' -> _hom _ (_fun_obj c) (_fun_obj c') }.

Definition category_of_category: _PreCategory.
Proof.
  Fail unshelve refine (@Build__PreCategory _PreCategory _PreFunctor _ _).
Abort.

(* Now with polymorphic definitions *)

Polymorphic Record PreCategory :=
  { obj :> Type;
    hom : forall a b : obj, Type ; 
    id : forall a, hom a a ;
    comp : forall a b c, hom b c -> hom a b -> hom a c }.

Print PreCategory.

Arguments hom {_} _ _.

Polymorphic Record PreFunctor (C D : PreCategory) :=
  { fun_obj : C.(obj) -> D.(obj);
    fun_hom : forall c c' : C.(obj), hom c c' -> hom (fun_obj c) (fun_obj c') }.

Arguments fun_obj {_ _} _ _.
Arguments fun_hom {_ _} _ {_ _} _.

Polymorphic Definition category_of_category: PreCategory.
Proof.
  unshelve refine (@Build_PreCategory PreCategory PreFunctor _ _).
  - intro C. unshelve econstructor. exact (fun c => c). exact (fun c c' e => e).
  - intros C D E g f. unshelve econstructor. exact (fun c => g.(fun_obj) (f.(fun_obj) c)).
    exact (fun c c' e => g.(fun_hom) (f.(fun_hom) e)).
Defined.

