/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.AbelianVarieties.Tate.FullTateModule
import Nyll.EtaleFundamentalGroups.GeometricFiber.AbelianUnitMultiplicationCover
import Nyll.EtaleFundamentalGroups.GeometricFiber.HenselianSpecialization

/-!
# Actual prime-to-residue torsion specialization

The multiplication kernel over a smooth proper local-ring group is finite
étale at every invertible index. Its actual generic and residue points are
identified by the existing normal henselian specialization. The group and
Tate transition compatibilities are separate from this point comparison.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra
open AlgebraicGeometry.FiniteEtale

namespace GoodReductionJacobian.RelativeGroupLaw

variable {H : Type} [CommRing H] [IsLocalRing H]
  {A : Scheme} {f : A ⟶ Spec (.of H)} [IsProper f] [Smooth f]
  (G : RelativeGroupLaw H f) (hc : G.IsCommutative)

include hc in
/-- The actual multiplication kernel at an invertible index is finite étale. -/
theorem isFiniteEtale_schemeKerStr_of_isUnit (n : ℕ) (hn : IsUnit (n : H)) :
    IsFiniteEtale (G.schemeKerStr n) := by
  have : IsFiniteEtale (G.schemeNsmul n) :=
    G.isFiniteEtale_schemeNsmul_of_isUnit hc n hn
  have : IsFinite (G.schemeKerStr n) := inferInstance
  have : Etale (G.schemeKerStr n) := inferInstance
  exact IsFiniteEtale.mk

/-- The existing multiplication kernel bundled over the original local ring. -/
def unitTorsionCover (n : ℕ+) (hn : IsUnit ((n : ℕ) : H)) :
    FiniteEtale (Spec (.of H)) := by
  have : IsFiniteEtale (G.schemeKerStr (n : ℕ)) :=
    G.isFiniteEtale_schemeKerStr_of_isUnit hc (n : ℕ) hn
  exact FiniteEtale.mk (G.schemeKerStr (n : ℕ))

/-- Torsion points over any coefficient algebra are actual points of this cover. -/
def torsionLevelEquivUnitKernelPoints (T : Type) [CommRing T] [Algebra H T]
    (n : ℕ+) (hn : IsUnit ((n : ℕ) : H)) :
    ProCGroups.torsionLevel (G.AlgPoints hc T) n ≃
      (Over.mk (Spec.algebraMap H T) ⟶ (G.unitTorsionCover hc n hn).toComma) :=
  (G.torsionLevelEquivAlgSchemeKerPoints hc T n).trans
    (schemeHomOverEquivOverHom (Spec.algebraMap H T) (G.schemeKerStr (n : ℕ)))

variable (R L : Type) [CommRing R] [HenselianLocalRing R] [IsIntegrallyClosed R]
  [Field L] [Algebra H R] [Algebra R L] [IsFractionRing R L]
  [Algebra H L] [IsScalarTower H R L]

/-- Specialize actual torsion points using their unique integral lift and reduction. -/
def torsionLevelSpecialization (n : ℕ+) (hn : IsUnit ((n : ℕ) : H)) :
    ProCGroups.torsionLevel (G.AlgPoints hc L) n ≃
      ProCGroups.torsionLevel (G.AlgPoints hc (IsLocalRing.ResidueField R)) n :=
  (G.torsionLevelEquivUnitKernelPoints hc L n hn).trans
    ((henselianSpecializationOverEquiv H R L (G.unitTorsionCover hc n hn)).trans
      (G.torsionLevelEquivUnitKernelPoints hc (IsLocalRing.ResidueField R) n hn).symm)

/-- The constructed torsion comparison is the actual specialization of kernel points. -/
theorem torsionLevelEquivUnitKernelPoints_specialization
    (n : ℕ+) (hn : IsUnit ((n : ℕ) : H))
    (x : ProCGroups.torsionLevel (G.AlgPoints hc L) n) :
    G.torsionLevelEquivUnitKernelPoints hc (IsLocalRing.ResidueField R) n hn
        (G.torsionLevelSpecialization hc R L n hn x) =
      henselianSpecializationOverEquiv H R L (G.unitTorsionCover hc n hn)
        (G.torsionLevelEquivUnitKernelPoints hc L n hn x) :=
  Equiv.apply_symm_apply _ _

end GoodReductionJacobian.RelativeGroupLaw
