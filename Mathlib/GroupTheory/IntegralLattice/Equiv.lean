/-
Copyright (c) 2024 Erik van der Plas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik van der Plas
-/
import Mathlib.GroupTheory.IntegralLattice.Basic

open IntegralLattice

structure IntegralLatticeEquiv (Λ₁ Λ₂ : Type*)
  [IntegralLattice Λ₁] [IntegralLattice Λ₂]
  extends Λ₁ ≃+ Λ₂ where
  (preserves_inner' : ∀ x y: Λ₁, ⟪toFun x, toFun y⟫_ℤ = ⟪x, y⟫_ℤ)

infixl:25 " ≃ₗ " => IntegralLatticeEquiv

namespace IntegralLatticeEquiv

variable {Λ₁ Λ₂ Λ₃ : Type*} [IntegralLattice Λ₁] [IntegralLattice Λ₂] [IntegralLattice Λ₃]

def refl (Λ : Type*) [IntegralLattice Λ] : Λ ≃ₗ Λ where
  __ := AddEquiv.refl Λ
  preserves_inner' _ _ := rfl

def symm (f : Λ₁ ≃ₗ Λ₂) : Λ₂ ≃ₗ Λ₁ where
  __ := f.toAddEquiv.symm
  preserves_inner' x y := by
    rw [← f.preserves_inner']
    simp

def trans (f : Λ₁ ≃ₗ Λ₂) (g : Λ₂ ≃ₗ Λ₃) : Λ₁ ≃ₗ Λ₃ where
  __ := f.toAddEquiv.trans g.toAddEquiv
  preserves_inner' x y := by
    rw [← f.preserves_inner', ← g.preserves_inner']
    simp

instance : EquivLike (Λ₁ ≃ₗ Λ₂) Λ₁ Λ₂ where
  coe := fun x => x.toFun
  inv := fun x ↦ x.invFun
  left_inv := fun x ↦ x.left_inv
  right_inv := fun x ↦ x.right_inv
  coe_injective' := by
    intros f g h
    cases f
    simp_all

instance : AddEquivClass (Λ₁ ≃ₗ Λ₂) Λ₁ Λ₂ where
  map_add f a b := f.map_add a b

lemma preserves_inner (f : Λ₁ ≃ₗ Λ₂) (x y : Λ₁) : ⟪f x, f y⟫_ℤ = ⟪x, y⟫_ℤ :=
  f.preserves_inner' x y

end IntegralLatticeEquiv
