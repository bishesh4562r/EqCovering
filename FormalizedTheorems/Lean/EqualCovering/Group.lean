universe u

structure Group (α : Type u) where
  mul : α → α → α
  one : α
  inv : α → α
  mul_assoc : ∀ x y z : α, mul (mul x y) z = mul x (mul y z)
  one_mul : ∀ x : α, mul one x = x
  mul_one : ∀ x : α, mul x one = x
  inv_mul : ∀ x : α, mul (inv x) x = one
  mul_inv : ∀ x : α, mul x (inv x) = one

structure IsSubgroup {α : Type u} (G : Group α) (H : α → Prop) : Prop where
  mul_mem : ∀ {x y}, H x → H y → H (G.mul x y)
  inv_mem : ∀ {x}, H x → H (G.inv x)
  one_mem : H G.one

structure Subgroup {α : Type u} (G : Group α) where
  subset : α → Prop
  isSubgroup : IsSubgroup G subset

def IsProper {α : Type u} {G : Group α} (H : Subgroup G) : Prop :=
  ∃ g : α, ¬ H.subset g
