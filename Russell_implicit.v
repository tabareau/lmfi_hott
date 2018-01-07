Set Printing Universes. 

Inductive Tree : Type :=
span : forall A : Type, (A -> Tree) -> Tree.

Definition elem (t : Tree) (u : Tree) : Prop
:= match u with
| span A us => exists a : A , t = us a
end.

Definition Bad (t : Tree) : Prop := elem t t.

Lemma is_good {t : Tree} : ~Bad t.
induction t. intros [x ex]. apply (H x).
rewrite <- ex. cbn. 
exists x; exact ex.
Qed.

Fail Definition Russell : Tree := span Tree (fun x => x).
