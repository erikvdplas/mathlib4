/-
Copyright (c) 2024 Erik van der Plas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik van der Plas
-/
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.LinearAlgebra.FreeModule.Basic
import Mathlib.LinearAlgebra.Matrix.Determinant

open Module
open FiniteDimensional

/-- An *integral lattice* is a finitely generated free abelian group
of finite rank `n` with a bilinear form that takes integer values. -/
class IntegralLattice (Λ : Type*) extends Inner ℤ Λ, AddCommGroup Λ where
  [free : Free ℤ Λ]
  [finite : Finite ℤ Λ]
  (add_inner : ∀ x y z: Λ, ⟪(x + y), z⟫_ℤ = ⟪x, z⟫_ℤ + ⟪y, z⟫_ℤ)
  (inner_sym : ∀ x y: Λ, ⟪x, y⟫_ℤ = ⟪y, x⟫_ℤ)
  (inner_self : ∀ x: Λ, ⟪x, x⟫_ℤ ≥ 0)
  (inner_self_eq_zero : ∀ x: Λ, ⟪x, x⟫_ℤ = 0 → x = 0)

attribute [instance] IntegralLattice.free IntegralLattice.finite

namespace IntegralLattice

variable (Λ : Type*) [IntegralLattice Λ]

def IsEven : Prop := ∀ x y: Λ, Even ⟪x, y⟫_ℤ

def gramMatrix {Λ ι : Type*} [IntegralLattice Λ] (v : ι → Λ) :=
  Matrix.of (fun i j ↦ ⟪v i, v j⟫_ℤ)

/-- The determinant of a lattice is defined as the determinant
of the Gram matrix of its basis. -/
noncomputable
def determinant : ℤ :=
  (gramMatrix (Free.chooseBasis ℤ Λ)).det

def IsUnimodular : Prop := determinant Λ = 1

end IntegralLattice
