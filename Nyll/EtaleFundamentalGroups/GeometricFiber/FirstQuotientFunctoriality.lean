/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.EtaleFundamentalGroups.GeometricFiber.ArithmeticKernelNaturality
public import Nyll.ProCGroups.Topologies.QuotientMaps
public import Nyll.ProCGroups.Abelian.ArithmeticFirstQuotient
public import Nyll.ProCGroups.Topologies.TopologicallyCharacteristicSubgroups

/-!
# Original scheme morphisms on the first arithmetic quotient

The actual map of geometric fundamental groups preserves the embedded closed
geometric commutator. It therefore induces a continuous map on the original
first quotients, with both the representatives and arithmetic labels retained.
This applies in particular to an open curve's original compactification map.
-/

@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.PreGaloisCategory
open ProCGroups.Abelian

namespace AlgebraicGeometry.FiniteEtale

universe u

variable (k L : Type u) [Field k] [Field L] [Algebra k L] [IsSepClosure k L]
  {X Y : Scheme.{u}} (j : X ⟶ Y) (f : Y ⟶ Spec (CommRingCat.of k))
  {Ω : Type u} [Field Ω] [IsSepClosed Ω] (xi : Spec (CommRingCat.of Ω) ⟶ X)

local notation "DX" =>
  MonoidHom.ker (ContinuousMonoidHom.toMonoidHom
    (arithmeticFundamentalGroupHom k L (j ≫ f) xi))
local notation "DY" =>
  MonoidHom.ker (ContinuousMonoidHom.toMonoidHom
    (arithmeticFundamentalGroupHom k L f (xi ≫ j)))

/-- The original scheme map preserves the actual embedded geometric commutator. -/
theorem arithmeticFirstKernel_le_comap_fundamentalGroupHom :
    arithmeticFirstKernel DX ≤
      (arithmeticFirstKernel DY).comap (fundamentalGroupHom j xi).toMonoidHom := by
  rintro g ⟨d, hd, rfl⟩
  exact ⟨arithmeticKernelHom k L j f xi d,
    Subgroup.closedCommutator_map_le (arithmeticKernelHom k L j f xi) ⟨d, hd, rfl⟩,
    rfl⟩

/-- The first arithmetic quotient map induced by the original scheme morphism. -/
def arithmeticFirstFundamentalGroupHom :
    ArithmeticFirstQuotient DX →ₜ* ArithmeticFirstQuotient DY :=
  ProCGroups.QuotientGroup.mapₜ (arithmeticFirstKernel DX) (arithmeticFirstKernel DY)
    (fundamentalGroupHom j xi)
    (arithmeticFirstKernel_le_comap_fundamentalGroupHom k L j f xi)

/-- Passage to the first quotient retains the original pointed representative. -/
@[simp] theorem arithmeticFirstFundamentalGroupHom_apply_mk (g : π₁ᵉᵗ(xi)) :
    arithmeticFirstFundamentalGroupHom k L j f xi (arithmeticFirstMk DX g) =
      arithmeticFirstMk DY (fundamentalGroupHom j xi g) := rfl

/-- Equality in the original open first quotient is preserved by its actual
map to the target first quotient, including the compactification case. -/
theorem arithmeticFirstMk_eq_of_source_eq (g h : π₁ᵉᵗ(xi))
    (heq : arithmeticFirstMk DX g = arithmeticFirstMk DX h) :
    arithmeticFirstMk DY (fundamentalGroupHom j xi g) =
      arithmeticFirstMk DY (fundamentalGroupHom j xi h) :=
  congrArg (arithmeticFirstFundamentalGroupHom k L j f xi) heq

/-- The induced map commutes with the same original arithmetic projections. -/
theorem arithmeticFirstFundamentalGroupHom_arithmetic (g : ArithmeticFirstQuotient DX) :
    arithmeticFirstProjection (arithmeticFundamentalGroupHom k L f (xi ≫ j))
        (arithmeticFirstFundamentalGroupHom k L j f xi g) =
      arithmeticFirstProjection (arithmeticFundamentalGroupHom k L (j ≫ f) xi) g := by
  obtain ⟨a, rfl⟩ := QuotientGroup.mk'_surjective (arithmeticFirstKernel DX) g
  exact arithmeticFundamentalGroupHom_comp k L j f xi a

/-- The image of any original subgroup, in particular a decomposition
subgroup, is transported by precisely the original pointed map. -/
theorem arithmeticFirstFundamentalGroupHom_map_subgroup (D : Subgroup π₁ᵉᵗ(xi)) :
    (D.map (arithmeticFirstMk DX).toMonoidHom).map
        (arithmeticFirstFundamentalGroupHom k L j f xi).toMonoidHom =
      (D.map (fundamentalGroupHom j xi).toMonoidHom).map
        (arithmeticFirstMk DY).toMonoidHom := by
  rw [Subgroup.map_map, Subgroup.map_map]
  rfl

end AlgebraicGeometry.FiniteEtale
