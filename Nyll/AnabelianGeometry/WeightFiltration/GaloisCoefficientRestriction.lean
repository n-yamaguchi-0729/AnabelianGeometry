/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.AnabelianGeometry.WeightFiltration.TorsionCoefficientExtension
import Mathlib.FieldTheory.Normal.Defs

/-!
# Actual normal restriction and torsion coefficient extension

The same automorphism on the larger coefficient field restricts normally
to the smaller field. The original coefficient maps intertwine these
actual actions at each torsion level and on the full Tate family.
-/

noncomputable section

open CategoryTheory AlgebraicGeometry ProCGroups

namespace GoodReductionJacobian.RelativeGroupLaw

variable {K Ω L : Type} [Field K] [Field Ω] [Field L]
  [Algebra K Ω] [Algebra K L] [Algebra Ω L]
  [IsScalarTower K Ω L] [Normal K Ω]
  {A : Scheme} {f : A ⟶ Spec (.of K)}
  (G : RelativeGroupLaw K f) (hc : G.IsCommutative)

/-- Normal restriction supplies the coefficient-action compatibility
without a separately chosen automorphism on the smaller field. -/
theorem torsionCoefficientMap_normalRestriction
    (σ : L ≃ₐ[K] L) (n : ℕ+) (x : torsionLevel (G.AlgPoints hc Ω) n) :
    G.torsionCoefficientMap hc (IsScalarTower.toAlgHom K Ω L) n
        (G.torsionCoefficientMap hc (σ.restrictNormal Ω).toAlgHom n x) =
      G.torsionCoefficientMap hc σ.toAlgHom n
        (G.torsionCoefficientMap hc (IsScalarTower.toAlgHom K Ω L) n x) :=
  G.torsionCoefficientMap_equivariant hc (IsScalarTower.toAlgHom K Ω L)
    (σ.restrictNormal Ω) σ (fun z => σ.restrictNormal_commutes Ω z) n x

/-- The actual coefficient extension intertwines the original full Tate
actions coordinate by coordinate. -/
theorem fullTateCoefficientMap_normalRestriction
    (σ : L ≃ₐ[K] L) (x : FullTateModule (G.AlgPoints hc Ω)) :
    FullTateModule.map (AlgPoints.map (L := G) (hc := hc) (IsScalarTower.toAlgHom K Ω L))
        (FullTateModule.map (AlgPoints.map (L := G) (hc := hc)
          (σ.restrictNormal Ω).toAlgHom) x) =
      FullTateModule.map (AlgPoints.map (L := G) (hc := hc) σ.toAlgHom)
        (FullTateModule.map (AlgPoints.map (L := G) (hc := hc)
          (IsScalarTower.toAlgHom K Ω L)) x) := by
  apply FullTateModule.ext
  intro n
  exact congrArg Subtype.val
    (G.torsionCoefficientMap_normalRestriction hc σ n (FullTateModule.projection _ n x))

/-- The very same normal restriction inherits a finite root-power formula
from the larger coefficient field. -/
theorem normalRestriction_pow_of_pow
    (σ : L ≃ₐ[K] L) (n q : ℕ)
    (hσ : ∀ z : L, z ^ n = 1 → σ z = z ^ q)
    (z : Ω) (hz : z ^ n = 1) : (σ.restrictNormal Ω) z = z ^ q := by
  apply (algebraMap Ω L).injective
  rw [σ.restrictNormal_commutes, map_pow]
  apply hσ
  rw [← map_pow, hz, map_one]

end GoodReductionJacobian.RelativeGroupLaw
