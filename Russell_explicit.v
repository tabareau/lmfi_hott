Set Universe Polymorphism.

Inductive Tree@{i j} : Type@{j} :=
span : forall A : Type@{i}, (A -> Tree) -> Tree.

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

Fail Definition Russell@{i j k} : Tree@{i j} := span@{i j} Tree@{k i} (fun x => x).

Set Printing Universes.

Fail Definition Russell@{i} : Tree@{i i} := span@{i i} Tree@{i i} (fun x => x).
