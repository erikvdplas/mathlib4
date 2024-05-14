/-
Copyright (c) 2024 Erik van der Plas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik van der Plas
-/
import Mathlib.GroupTheory.IntegralLattice.Leech.Basic
import Mathlib.GroupTheory.IntegralLattice.Aut
import Mathlib.LinearAlgebra.FreeModule.Basic

open Module

variable (Λ : Type*) [LeechLattice Λ]

-- TODO: Help needed, helpppppp
-- The Conway-0 group is the automorphism group of the Leech lattice.
-- We use the IntegralLatticeAut structure to construct the variable.
variable (C₀ : Type*) [IntegralLatticeAut Λ]

instance : Nontrivial C₀ where
  exists_pair_ne := by
    let ι := Free.ChooseBasisIndex ℤ Λ
    let b : Basis ι ℤ Λ := Free.chooseBasis _ _
    haveI : Fintype ι := inferInstance
    let b₀ := Classical.choose b
    sorry
