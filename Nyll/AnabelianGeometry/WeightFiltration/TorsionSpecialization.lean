/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.AbelianVarieties.Tate.FiniteTorsion
public import Nyll.AbelianVarieties.Tate.FullTateModule
public import Nyll.EtaleFundamentalGroups.GeometricFiber.AbelianUnitMultiplicationCover
public import Nyll.EtaleFundamentalGroups.GeometricFiber.HenselianSpecialization
public import Nyll.ProCGroups.Abelian.FullTateModule

/-!
# Actual prime-to-residue torsion specialization

The multiplication kernel over a smooth proper local-ring group is finite
étale at every invertible index. Its actual generic and residue points are
identified by the existing normal henselian specialization. The group and
Tate transition compatibilities are separate from this point comparison.
-/

@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra
open AlgebraicGeometry.FiniteEtale

namespace GoodReductionJacobian.RelativeGroupLaw

variable {H : Type} [CommRing H] [IsLocalRing H]
  {A : Scheme} {f : A ⟶ Spec (.of H)} [IsProper f] [Smooth f]
  (G : RelativeGroupLaw H f) (hc : G.IsCommutative)

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
