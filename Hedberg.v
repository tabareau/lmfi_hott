Set Universe Polymorphism.

Require Import Trunc. 


Definition naturality {A} `{P : A -> Type} `{Q : A -> Type}
           (f : forall a, P a -> Q a) a b (e : a = b) (z:P a):
  transport Q e (f a z) = f b (transport P e z).
Proof.
  destruct e. reflexivity.
Defined.

Definition reflexiveRelation_hprop_aux X (R : X -> X -> Type)
           (Rcompat : forall x y, R x y -> x = y) :
  forall x y z (p:x=y) (r:R x z),
    transport (fun X => X = _) p (Rcompat x z r) =
    Rcompat y z (transport (fun X => R X _) p r).
  intros.
  apply (@naturality _ (fun x => R x z) (fun x => x = z) (fun x => Rcompat x z)).
Defined. 

Definition IsHSet A := IsTrunc 2 A.

Definition StreicherK X := forall (x:X) (p:x=x), p = refl x.

Definition StreicherK_HSet X : StreicherK X -> IsHSet X. 
Proof.
  intros H x y. apply IsIrr_to_IsHProp. intros e e'. destruct e'.
  apply H. 
Defined.

Definition reflexiveRelation_hprop X (R : X -> X -> Type) (HR : forall x y, IsHProp (R x y))
           (Rrefl : forall x, R x x) (Rcompat : forall x y, R x y -> x = y) :
  IsHSet X. 
Proof.
  
  apply StreicherK_HSet. intros x p.
  pose (reflexiveRelation_hprop_aux _ _ Rcompat _ _ _ p (Rrefl x)).
  rewrite transport_paths_l in i.
  assert (transport (fun X : X => R X x) p (Rrefl x) = Rrefl x).
  apply HR. rewrite X0 in i. clear X0. 
  apply moveL_Vp in i. rewrite concat_pV in i.
  rewrite <- (concat_1p p^) in i. apply inverse in i. apply moveL_M1 in i.
  exact i.
Defined.

Definition IsHProp_False: IsHProp False.
Proof. 
  apply IsIrr_to_IsHProp. intro e. destruct e.
Defined.

Definition not (A:Type) := A -> False. 

Definition IsHProp_double_neg {funext:Funext} A : IsHProp (not (not A)).
Proof.
  unshelve eapply IsTrunc_Forall; auto.
  intros; apply IsHProp_False.
Defined.

Definition Decidable_classical P (dec_P : P + not P)
  : not (not P) -> P. 
Proof. 
  intros n. destruct dec_P.
  - exact p. 
  - destruct (n n0).
Defined. 

Definition Hedberg {funext:Funext}  A (dec_paths_ : forall a b : A, ((a = b) + not (a = b))%type)
  : IsHSet A.
Proof.
  unshelve eapply reflexiveRelation_hprop.
  Focus 4. intros a b. apply Decidable_classical; auto. 
  - intros. unshelve eapply IsHProp_double_neg; auto.
  - intros a n. apply (n (refl a)).
Defined.

Definition Hedberg_alt A (dec_paths_ : forall a b : A, (a = b) + not (a = b)%type)
  : IsHSet A.
Proof.
  intros a b.

  assert (lemma: forall p: a = b,  
             match dec_paths_ a a, dec_paths_ a b with
             | inl r, inl s => p = r^ @ s
             | _, _ => False
             end).
  {
    destruct p.
    destruct (dec_paths_ a a) as [pr | f].
    - apply inverse. apply concat_Vp.
    - exact (f (refl a)).
  }

  apply IsIrr_to_IsHProp; intros p q.
 assert (p_given_by_dec := lemma p).
  assert (q_given_by_dec := lemma q).
  destruct (dec_paths_ a b); destruct (dec_paths_ a a); try contradiction.
  apply (p_given_by_dec @ q_given_by_dec ^).
Defined.

Definition neq_true_false : not (true = false).
Proof.
  intro e.
  assert (forall b (e:true = b), match b with
                                    | true => True
                                    | false => False
                                    end).
  clear. intros b e. destruct e. auto.
  specialize (H false e). cbn in H. exact H.
Defined. 

Definition Decidable_eq_bool : forall (x y : bool),  (x = y) + not (x = y).
Proof.
  destruct x, y.
  - left. reflexivity. 
  - right.
    (* intro e. inversion e. *)
    apply neq_true_false.
  - right. intro e; apply neq_true_false. exact e^.
  - left. reflexivity.
Defined.

Definition S_inv : forall (x y : nat),  S x = S y -> x = y.
Proof.
  inversion 1. reflexivity.
Defined. 

Definition Decidable_eq_nat : forall (x y : nat),  (x = y) + not (x = y).
induction x.
- destruct y.
 + left ;reflexivity.
 + right. intro H; inversion H.
- destruct y.
  + right; intro H; inversion H.
  + case (IHx y). intro H. left. exact (ap S H).
    intro H; right. intro e. apply (H (S_inv _ _ e)).
Defined.
