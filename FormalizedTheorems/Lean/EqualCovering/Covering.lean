import EqualCovering.Group

universe u

structure Covering {α : Type u} (G : Group α) (I : Type u) where
  sub : I → Subgroup G
  proper : ∀ i, IsProper (sub i)
  covers : ∀ x : α, ∃ i, (sub i).subset x

axiom Size {α : Type u} {G : Group α} : Subgroup G → Type u

structure EqualCovering {α : Type u} (G : Group α) (I : Type u) where
  cov : Covering G I
  equalSz : ∀ i j : I, Size (cov.sub i) = Size (cov.sub j)
