/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.AlgebraicCurves.Models.Divisors.CartierModulus
public import Nyll.AlgebraicCurves.Geometry.IsClosedSingletonNeGenericPoint
public import Mathlib.AlgebraicGeometry.FunctionField
public import Mathlib.Topology.Sheaves.Stalks

/-!
# Full modulus congruence is restriction to one

For a rational function represented by a unit on a neighbourhood of the actual
Cartier modulus, the function-field congruence is equivalent to restriction to
one on the original closed subscheme. Stalk detection retains every nilpotent
order; it needs no reduced-support replacement or decomposition assumption.
-/

@[expose] public section

noncomputable section

universe u v

open AlgebraicGeometry

namespace AlgebraicCurve.CurveModel

attribute [local instance] CurveModel.isIntegral CurveModel.isProper CurveModel.smooth

variable {K : Type u} [Field K] {F : Type v} [Field F] [Algebra K F]
  (M : CurveModel K F) (I : M.C.IdealSheafData) (hI : I.IsInvertible)

include hI in
/-- Points of an actual Cartier modulus on the model are closed points of the curve. -/
theorem isClosed_cartierPoint (z : I.subscheme) :
    IsClosed ({I.subschemeι z} : Set M.C) := by
  apply AlgebraicCurve.isClosed_singleton_of_ne_genericPoint M.toBase
  have hz : I.subschemeι z ∈ I.support := by
    change I.subschemeι z ∈ (I.support : Set M.C)
    rw [← I.range_subschemeι]
    exact ⟨z, rfl⟩
  intro h
  have htop : I.stalkIdeal (genericPoint M.C) = ⊤ := by
    let J : Ideal M.C.functionField := I.stalkIdeal (genericPoint M.C)
    exact (Ideal.eq_bot_or_top J).resolve_left (hI.stalkIdeal_ne_bot (genericPoint M.C))
  exact (I.stalkIdeal_eq_top_iff_notMem_support (genericPoint M.C)).mp htop (h ▸ hz)

/-- The modulus coefficient at a point is its constructed Cartier multiplicity. -/
theorem cartierModulus_placeOfPoint (x : closedPoints M.C) :
    M.cartierModulus I hI (M.placeOfPoint x) = M.cartierMultiplicity I hI x := by
  change M.cartierMultiplicity I hI (M.placeEquiv.symm (M.placeEquiv x)) = _
  rw [M.placeEquiv.symm_apply_apply]

/-- Congruence at a modulus point is the actual germ of the restricted unit. -/
theorem congruentOne_sectionUnit_iff
    (U : M.C.Opens) [Nonempty U] (a : Γ(M.C, U)ˣ)
    (z : I.subscheme) (hz : I.subschemeι z ∈ U) :
    (M.placeOfPoint ⟨I.subschemeι z, M.isClosed_cartierPoint I hI z⟩).CongruentOne
        (M.cartierMultiplicity I hI ⟨I.subschemeι z, M.isClosed_cartierPoint I hI z⟩)
        (M.ffEquiv.symm (M.C.germToFunctionField U a)) ↔
      I.subscheme.presheaf.germ (I.subschemeι ⁻¹ᵁ U) z hz
        (I.subschemeι.app U (a : Γ(M.C, U))) = 1 := by
  let b : (M.C.presheaf.stalk (I.subschemeι z))ˣ :=
    Units.map (M.C.presheaf.germ U (I.subschemeι z) hz).hom.toMonoidHom a
  have h := M.congruentOne_iff_modulusStalk_eq_one I hI z
    (M.isClosed_cartierPoint I hI z) b
  change (M.placeOfPoint ⟨I.subschemeι z, M.isClosed_cartierPoint I hI z⟩).CongruentOne
      (M.cartierMultiplicity I hI ⟨I.subschemeι z, M.isClosed_cartierPoint I hI z⟩)
      (M.ffEquiv.symm (algebraMap (M.C.presheaf.stalk (I.subschemeι z)) M.C.functionField
        (M.C.presheaf.germ U (I.subschemeι z) hz (a : Γ(M.C, U))))) ↔
    I.subschemeι.stalkMap z
      (M.C.presheaf.germ U (I.subschemeι z) hz (a : Γ(M.C, U))) = 1 at h
  rw [M.C.algebraMap_germ_eq_germToFunctionField hz,
    I.subschemeι.germ_stalkMap_apply U z hz] at h
  exact h

/-- The full function-field modulus congruence is precisely restriction to one
under the original closed immersion, on any neighbourhood of its support. -/
theorem cartierModulus_congruentOne_iff_restriction_eq_one
    (U : M.C.Opens) [Nonempty U] (hU : (I.support : Set M.C) ⊆ U)
    (a : Γ(M.C, U)ˣ) :
    (M.cartierModulus I hI).CongruentOne
        (M.ffEquiv.symm (M.C.germToFunctionField U a)) ↔
      I.subschemeι.app U (a : Γ(M.C, U)) = 1 := by
  constructor
  · intro hf
    apply TopCat.Presheaf.section_ext I.subscheme.sheaf (I.subschemeι ⁻¹ᵁ U)
    intro z hz
    have hzI : I.subschemeι z ∈ I.support := by
      change I.subschemeι z ∈ (I.support : Set M.C)
      rw [← I.range_subschemeι]
      exact ⟨z, rfl⟩
    let x : closedPoints M.C := ⟨I.subschemeι z, M.isClosed_cartierPoint I hI z⟩
    have hx : M.cartierModulus I hI (M.placeOfPoint x) ≠ 0 := by
      rw [M.cartierModulus_placeOfPoint I hI x]
      intro hzero
      exact (M.cartierMultiplicity_eq_zero_iff I hI x).mp hzero hzI
    have hc := hf.2 (M.placeOfPoint x) hx
    rw [M.cartierModulus_placeOfPoint I hI x] at hc
    exact ((M.congruentOne_sectionUnit_iff I hI U a z hz).mp hc).trans
      (map_one (I.subscheme.presheaf.germ (I.subschemeι ⁻¹ᵁ U) z hz).hom).symm
  · intro ha
    refine ⟨(a.isUnit.map
      (M.ffEquiv.symm.toRingHom.comp (M.C.germToFunctionField U).hom)).ne_zero, ?_⟩
    intro w hw
    let x := M.placeEquiv.symm w
    have hxI : x.1 ∈ I.support := by
      by_contra hx
      exact hw ((M.cartierModulus_eq_zero_iff I hI w).mpr hx)
    have hxrange : x.1 ∈ Set.range I.subschemeι := by
      rw [I.range_subschemeι]
      exact hxI
    obtain ⟨z, hzx⟩ := hxrange
    have hzU : I.subschemeι z ∈ U := hzx.symm ▸ hU hxI
    have hz : I.subscheme.presheaf.germ (I.subschemeι ⁻¹ᵁ U) z hzU
        (I.subschemeι.app U (a : Γ(M.C, U))) = 1 := by
      rw [ha]
      exact map_one (I.subscheme.presheaf.germ (I.subschemeι ⁻¹ᵁ U) z hzU).hom
    have hc := (M.congruentOne_sectionUnit_iff I hI U a z hzU).mpr hz
    have he : (⟨I.subschemeι z, M.isClosed_cartierPoint I hI z⟩ : closedPoints M.C) = x :=
      Subtype.ext hzx
    have hwx : M.placeOfPoint x = w := M.placeEquiv.apply_symm_apply w
    rw [he, hwx] at hc
    exact hc

end AlgebraicCurve.CurveModel
