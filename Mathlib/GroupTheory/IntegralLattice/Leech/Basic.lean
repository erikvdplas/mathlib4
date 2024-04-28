/-
Copyright (c) 2024 Erik van der Plas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik van der Plas
-/
import MathLib.GroupTheory.IntegralLattice.Equiv
import Mathlib.LinearAlgebra.Dimension.Finrank

universe u

open IntegralLattice
open FiniteDimensional

/-- The Leech lattice is the unique even, unimodular integral lattice of rank 24. -/
class LeechLattice (Λ : Type*) extends IntegralLattice Λ where
  (even : IsEven Λ)
  (unimodular : IsUnimodular Λ)
  (rank_eq_24 : finrank ℤ Λ = 24)

namespace LeechLattice

variable (Λ : Type*) [LeechLattice Λ]

theorem unique (Λ₁ Λ₂ : Type*) [LeechLattice Λ₁] [LeechLattice Λ₂]:
  Nonempty (IntegralLatticeEquiv Λ₁ Λ₂) := sorry

theorem exists_leech : Prop := ∃ (Λ : Type u), Nonempty (LeechLattice Λ)

end LeechLattice
