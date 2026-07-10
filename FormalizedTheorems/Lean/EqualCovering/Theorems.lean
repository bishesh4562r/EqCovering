import EqualCovering.Group
import EqualCovering.Covering
import EqualCovering.Finite
import EqualCovering.Products
import EqualCovering.Homomorphisms

universe u

-- Theorem 2
axiom cancel_lemma {α : Type u} {G : Group α} (H : Subgroup G) (h k : α) :
  H.subset h → H.subset (G.mul h k) → H.subset k

axiom cancel_lemma2 {α : Type u} {G : Group α} (K : Subgroup G) (h k : α) :
  K.subset k → K.subset (G.mul h k) → K.subset h

theorem theorem2 {α : Type u} (G : Group α) (H K : Subgroup G)
  (pH : IsProper H) (pK : IsProper K) :
  ¬ (∀ x, H.subset x ∨ K.subset x) := by
  intro covers
  rcases pH with ⟨k, hk_not_H⟩
  rcases pK with ⟨h, hh_not_K⟩
  have hk_K : K.subset k := by
    cases covers k with
    | inl h_in => contradiction
    | inr k_in => exact k_in
  have hh_H : H.subset h := by
    cases covers h with
    | inl h_in => exact h_in
    | inr k_in => contradiction
  have h_mul_k := covers (G.mul h k)
  cases h_mul_k with
  | inl h_in =>
    have k_in_H := cancel_lemma H h k hh_H h_in
    contradiction
  | inr k_in =>
    have h_in_K := cancel_lemma2 K h k hk_K k_in
    contradiction


-- Theorem 13
theorem theorem13 {α : Type u} {G : Group α} {I : Type u}
  (eqCov : FiniteEqualCovering G I) (i : I) :
  exp G ∣ order_subgroup (eqCov.cov.sub i) := by
  apply exp_divides
  intro x
  have ⟨j, x_in_j⟩ := eqCov.cov.covers x
  have lag := lagrange (eqCov.cov.sub j) x x_in_j
  have eq_sz := eqCov.equalSz j i
  rw [← eq_sz]
  exact lag


-- Corollary 1
axiom MaxSubgroup {α : Type u} : Group α → Type u
axiom max_sub {α : Type u} {G : Group α} : MaxSubgroup G → Subgroup G
axiom maximal_pred {α : Type u} {G : Group α} (H : Subgroup G) : MaxSubgroup G
axiom divides_max {α : Type u} {G : Group α} (H : Subgroup G) :
  order_subgroup H ∣ order_subgroup (max_sub (maximal_pred H))

theorem corollary1 {α : Type u} {G : Group α} {I : Type u} (i : I)
  (noDiv : ∀ K : MaxSubgroup G, ¬ (exp G ∣ order_subgroup (max_sub K))) :
  FiniteEqualCovering G I → False := by
  intro eqCov
  let H := eqCov.cov.sub i
  have exp_div_H := theorem13 eqCov i
  have H_div_Max := divides_max H
  have exp_div_Max := Nat.dvd_trans exp_div_H H_div_Max
  have contra := noDiv (maximal_pred H)
  contradiction


-- Theorem 15
axiom IsPGroup {α : Type u} : Group α → Prop
axiom NonCyclic {α : Type u} : Group α → Prop

axiom theorem15 {α : Type u} (G : Group α) :
  IsPGroup G → NonCyclic G → Sigma (fun I : Type u => FiniteEqualCovering G I)


-- Theorem 16
axiom size_eq {α β : Type u} {G : Group α} {H : Group β} (S1 S2 : Subgroup G) :
  Size S1 = Size S2 → Size (ProdSubgroup S1 H) = Size (ProdSubgroup S2 H)

def theorem16 {α β : Type u} {G : Group α} {H : Group β} {I : Type u} (eqCov : EqualCovering G I) :
  EqualCovering (DirectProduct G H) I := {
  cov := {
    sub := fun i => ProdSubgroup (eqCov.cov.sub i) H,
    proper := fun i => Exists.elim (eqCov.cov.proper i) fun g g_not_Si =>
      ⟨(g, H.one), g_not_Si⟩,
    covers := fun (g, _h) => Exists.elim (eqCov.cov.covers g) fun i g_in_Si =>
      ⟨i, g_in_Si⟩
  },
  equalSz := fun i j => size_eq (eqCov.cov.sub i) (eqCov.cov.sub j) (eqCov.equalSz i j)
}


-- Theorem 17
axiom IsNilpotent {α : Type u} : Group α → Prop

axiom theorem17 {α : Type u} (G : Group α) :
  IsNilpotent G → NonCyclic G → Sigma (fun I : Type u => FiniteEqualCovering G I)


-- Theorem 1 (Forward and Reverse)
def IsCyclic {α : Type u} (G : Group α) : Prop :=
  ∃ g : α, ∀ H : Subgroup G, H.subset g → ∀ x : α, H.subset x

theorem theorem1_forward {α : Type u} (G : Group α) {I : Type u} (cov : Covering G I) :
  ¬ IsCyclic G :=
  fun ⟨g, hg⟩ =>
    let ⟨i, g_in_i⟩ := cov.covers g
    let H := cov.sub i
    have all_in_H := hg H g_in_i
    let ⟨x, x_not_in_H⟩ := cov.proper i
    have x_in_H := all_in_H x
    x_not_in_H x_in_H

axiom CyclicSubgroup {α : Type u} (G : Group α) (x : α) : Subgroup G
axiom mem_cyclic_self {α : Type u} (G : Group α) (x : α) : (CyclicSubgroup G x).subset x
axiom cyclic_smallest {α : Type u} (G : Group α) (x : α) (H : Subgroup G) :
  H.subset x → ∀ y, (CyclicSubgroup G x).subset y → H.subset y

noncomputable def theorem1_reverse {α : Type u} (G : Group α) (non_cyclic : ¬ IsCyclic G) : Covering G α := {
  sub := fun x => CyclicSubgroup G x,
  proper := fun x =>
    Classical.byContradiction fun h_not_proper =>
      have h_all : ∀ y : α, (CyclicSubgroup G x).subset y := fun y =>
        Classical.byContradiction fun hy => h_not_proper ⟨y, hy⟩
      have is_cyc : IsCyclic G := ⟨x, fun H hx y => cyclic_smallest G x H hx y (h_all y)⟩
      non_cyclic is_cyc,
  covers := fun x => ⟨x, mem_cyclic_self G x⟩
}


-- Homomorphisms and Theorem 19
axiom preimage_size_eq {α β : Type u} {G : Group α} {Q : Group β} (f : Homomorphism G Q) (H1 H2 : Subgroup Q) :
  Size H1 = Size H2 → Size (PreimageSubgroup f H1) = Size (PreimageSubgroup f H2)

def theorem19 {α β : Type u} {G : Group α} {Q : Group β} {I : Type u} (f : Homomorphism G Q) (surj : Surjective f.func) (eqCov : EqualCovering Q I) : EqualCovering G I := {
  cov := {
    sub := fun i => PreimageSubgroup f (eqCov.cov.sub i),
    proper := fun i => Exists.elim (eqCov.cov.proper i) fun q hq =>
      Exists.elim (surj q) fun g hg =>
        ⟨g, fun contra => hq (hg ▸ contra)⟩,
    covers := fun g => Exists.elim (eqCov.cov.covers (f.func g)) fun i hi =>
      ⟨i, hi⟩
  },
  equalSz := fun i j => preimage_size_eq f (eqCov.cov.sub i) (eqCov.cov.sub j) (eqCov.equalSz i j)
}
