/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.AnabelianGeometry.WeightFiltration.TorsionCoefficientMaps
import Mathlib.LinearAlgebra.FreeModule.Finite.Matrix
import Mathlib.RingTheory.LocalRing.Module

/-!
# Finite torsion over field-valued coefficients

At every invertible index the actual torsion kernel is finite étale over
the local base. Its section algebra is finite free, hence has only finitely
many algebra maps to a field. No algebraic-closedness assumption is needed.
-/

noncomputable section

open AlgebraicGeometry AlgebraicGeometry.FiniteEtale

namespace GoodReductionJacobian.RelativeGroupLaw

variable {H : Type} [CommRing H] [IsLocalRing H]
  {A : Scheme} {f : A ⟶ Spec (.of H)} [IsProper f] [Smooth f]
  (G : RelativeGroupLaw H f) (hc : G.IsCommutative)

/-- Every unit-index torsion level over field-valued coefficients is finite. -/
theorem finite_torsionLevel_of_isUnit
    (L : Type) [Field L] [Algebra H L] (n : ℕ+) (hn : IsUnit ((n : ℕ) : H)) :
    Finite (ProCGroups.torsionLevel (G.AlgPoints hc L) n) := by
  let X := G.unitTorsionCover hc n hn
  have : Module.Finite H Γ(X.left, ⊤) := sections_moduleFinite H X
  have : Module.Free H Γ(X.left, ⊤) := Module.free_of_flat_of_isLocalRing
  exact Finite.of_injective (G.torsionLevelEquivKernelSections hc L n hn)
    (G.torsionLevelEquivKernelSections hc L n hn).injective

end GoodReductionJacobian.RelativeGroupLaw
