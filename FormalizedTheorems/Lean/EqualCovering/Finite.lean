import EqualCovering.Covering

universe u

axiom order_subgroup {α : Type u} {G : Group α} : Subgroup G → Nat
axiom exp {α : Type u} : Group α → Nat
axiom order_elem {α : Type u} (G : Group α) : α → Nat

axiom lagrange {α : Type u} {G : Group α} (H : Subgroup G) (x : α) :
  H.subset x → order_elem G x ∣ order_subgroup H

axiom exp_multiple {α : Type u} {G : Group α} (x : α) :
  order_elem G x ∣ exp G

axiom exp_divides {α : Type u} {G : Group α} (N : Nat) :
  (∀ x : α, order_elem G x ∣ N) → exp G ∣ N

structure FiniteEqualCovering {α : Type u} (G : Group α) (I : Type u) where
  cov : Covering G I
  equalSz : ∀ i j : I, order_subgroup (cov.sub i) = order_subgroup (cov.sub j)
