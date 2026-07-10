import EqualCovering.Group

universe u

structure Homomorphism {α β : Type u} (G : Group α) (Q : Group β) where
  func : α → β
  map_mul : ∀ x y, func (G.mul x y) = Q.mul (func x) (func y)

axiom map_one {α β : Type u} {G : Group α} {Q : Group β} (f : Homomorphism G Q) :
  f.func G.one = Q.one

axiom map_inv {α β : Type u} {G : Group α} {Q : Group β} (f : Homomorphism G Q) (x : α) :
  f.func (G.inv x) = Q.inv (f.func x)

def Surjective {α β : Type u} (f : α → β) : Prop :=
  ∀ y, ∃ x, f x = y

def PreimageSubgroup {α β : Type u} {G : Group α} {Q : Group β} (f : Homomorphism G Q) (H : Subgroup Q) : Subgroup G := {
  subset := fun g => H.subset (f.func g),
  isSubgroup := {
    mul_mem := fun {x y} hx hy =>
      (f.map_mul x y).symm ▸ H.isSubgroup.mul_mem hx hy,
    inv_mem := fun {x} hx =>
      (map_inv f x).symm ▸ H.isSubgroup.inv_mem hx,
    one_mem :=
      (map_one f).symm ▸ H.isSubgroup.one_mem
  }
}
