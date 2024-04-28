/-
Copyright (c) 2024 Erik van der Plas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik van der Plas
-/
import Mathlib.GroupTheory.IntegralLattice.Basic
import Mathlib.GroupTheory.IntegralLattice.Equiv

variable (Λ : Type*) [IntegralLattice Λ]

/-- The group of integral lattice automorphisms -/
@[reducible]
def IntegralLatticeAut := IntegralLatticeEquiv Λ Λ

namespace IntegralLatticeAut

instance : Group (IntegralLatticeAut Λ) where
  mul f g := IntegralLatticeEquiv.trans g f
  one := IntegralLatticeEquiv.refl Λ
  inv := IntegralLatticeEquiv.symm
  mul_assoc := by intros; rfl
  one_mul := by intros; rfl
  mul_one := by intros; rfl
  mul_left_inv := IntegralLatticeEquiv.self_trans_symm

@[simp]
lemma one_apply (x : Λ) : (1 : IntegralLatticeAut Λ) x = x :=
  rfl

@[simp]
lemma mul_apply (f g : IntegralLatticeAut Λ) (x : Λ) : (f * g) x = f (g x) :=
  rfl

end IntegralLatticeAut
