Set Universe Polymorphism.


Inductive I (A : Type) (x : A) : A -> Type :=
  refl : I A x x.

Arguments refl {_} _.

Notation "x = y" := (I _ x y): type_scope.

Definition subst (A:Type) (t:A) (P : forall y:A, t = y -> Type)
           (u : A) (p : t = u) (v:P t (refl t)) : P u p :=
  match p with
  | refl _ => v
  end.


Variable set : Type.
Variable name : Type -> set.
Variable El : set -> Type.
Axiom reflect : forall A:Type, A = El (name A).

Inductive Tree : Type :=
span : forall a : set, (El a -> Tree) -> Tree.

Definition elem (t : Tree) (u : Tree) : Type
:= match u with
| span A us => { a : El A & t = us a}
end.

Definition Bad (t : Tree) : Type
:= elem t t.

Definition is_good : forall t, Bad t -> False.
  induction t. cbn. intros [x ex].
  unfold not in H. apply (H x).
  rewrite <- ex. cbn. 
  exists x. exact ex.
Qed.

Definition tree := name Tree.

Definition getTree : El tree (* El (name Tree) = Tree  *) -> Tree :=
  subst Type Tree (fun A _ => A -> Tree) (El tree) (reflect Tree) (fun x => x).

Definition Russell := span tree getTree.

Lemma is_bad : Bad Russell.
  cbn. 
  pose (a := subst Type Tree (fun T _ => T) (El tree) (reflect Tree) Russell).
  cbn in a.
  exists a.
  unfold getTree, a. clear a. 
  exact (subst Type Tree (fun T e => Russell =
  subst Type Tree (fun (A : Type) (_ : Tree = A) => A -> Tree) 
    T e (fun x : Tree => x)
    (subst Type Tree (fun (T : Type) (_ : Tree = T) => T) 
       T e Russell)) (El tree) (reflect Tree) (refl _)).
Defined.

Definition paradox : False := (is_good _ is_bad).