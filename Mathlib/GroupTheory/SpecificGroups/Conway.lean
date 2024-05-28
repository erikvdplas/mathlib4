/-
Copyright (c) 2024 Erik van der Plas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik van der Plas
-/
import Mathlib.GroupTheory.IntegralLattice.Leech.Basic
import Mathlib.GroupTheory.IntegralLattice.Aut
import Mathlib.GroupTheory.Subgroup.Center

open IntegralLatticeAut

variable (Λ : Type*) [LeechLattice Λ]

-- The Conway-0 group is the automorphism group of the Leech lattice.
-- We use the IntegralLatticeAut structure to construct the variable.
abbrev Conway₀ := IntegralLatticeAut Λ

-- The Conway-1 group is the Conway-0 group modulo its center.
abbrev Conway₁ := Conway₀ Λ ⧸ (Subgroup.center (Conway₀ Λ))

-- The Conway-1 group is a simple group.
instance Conway₁.simple : IsSimpleGroup (Conway₁ Λ) := sorry
