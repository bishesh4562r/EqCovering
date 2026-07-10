import EqualCovering.Group

universe u

def DirectProduct {α β : Type u} (G : Group α) (H : Group β) : Group (α × β) := {
  mul := fun (g1, h1) (g2, h2) => (G.mul g1 g2, H.mul h1 h2),
  one := (G.one, H.one),
  inv := fun (g, h) => (G.inv g, H.inv h),
  mul_assoc := by
    intro x y z
    rcases x with ⟨g1, h1⟩
    rcases y with ⟨g2, h2⟩
    rcases z with ⟨g3, h3⟩
    simp [G.mul_assoc, H.mul_assoc]
  one_mul := by
    intro x
    rcases x with ⟨g, h⟩
    simp [G.one_mul, H.one_mul]
  mul_one := by
    intro x
    rcases x with ⟨g, h⟩
    simp [G.mul_one, H.mul_one]
  inv_mul := by
    intro x
    rcases x with ⟨g, h⟩
    simp [G.inv_mul, H.inv_mul]
  mul_inv := by
    intro x
    rcases x with ⟨g, h⟩
    simp [G.mul_inv, H.mul_inv]
}

def ProdSubgroup {α β : Type u} {G : Group α} (S : Subgroup G) (H : Group β) : Subgroup (DirectProduct G H) := {
  subset := fun (g, _h) => S.subset g,
  isSubgroup := {
    mul_mem := fun h1 h2 => S.isSubgroup.mul_mem h1 h2,
    inv_mem := fun hx => S.isSubgroup.inv_mem hx,
    one_mem := S.isSubgroup.one_mem
  }
}
