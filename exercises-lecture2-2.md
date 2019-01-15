A. We define natural numbers as indicated in file ITT.pdf using the
following syntactic constructions:

A ::= ... | N
t,u,v ::= ... | 0 | succ t | rec [0 ↦ t | succ n ↦_b u] v

Give definitions for

- addition on Peano natural numbers
- multiplication on Peano natural numbers

Give a proof term for a proof of associativity of addition

B. We define equality, as an identity type, as indicated in file
ITT.pdf using the following syntactic constructions:

A ::= ... | t =_A u
t,u,v ::= ... | refl t | subst p in v

Remark: another, type-annotated notation for "subst p in v" is
"J_a.b.P p v" (where p has type t =_A u, v has type P[t/a][refl t/b],
and the whole expression has type P[u/a][p/b]).

Give proof terms showing:
- the symmetry of equality
- the transitivity of equality

Next, seeing the proof of symmetry has a function from "t =_A u" to "u
=_A t" for all A, t, u, and, similarly for transitivity, show that 
- symmetry is involutive
  (i.e. "symmetry A t u (symmetry A u t p) =_{t =_A u} p" for any proof p of "t =_A u")
- transitivity is associative
  (i.e. "transitivity A t v w (transitivity A t u v p q) r = transitivity A t u w p (transitivity A u v w q r)"
   for any proofs of equality p, q, r)
- reflexivity is a neutral element for transitivity
  (i.e. "transitivity A t t u (refl t) p = p" and "transitivity A t u u p (refl t) = p")

