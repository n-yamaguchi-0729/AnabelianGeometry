/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/
import Nyll.EtaleFundamentalGroups.GaloisCategories.CoverTransportFiber
import Nyll.EtaleFundamentalGroups.GeometricFiber.EquivariantFiberCoverIso
import Nyll.ProCGroups.Topologies.ArithmeticInnerCorrectionFiberTransport

/-! # Actual cover comparison for the explicit inner correction

The changed transport functor is compared to the original transport by the
specified translation on its actual finite fibres. Composing with any original
cover isomorphism keeps that original named target cover, while retaining the
exact corrected fibre formula. No target model or coordinate is reselected.
-/
noncomputable section
open CategoryTheory
open scoped FintypeCatDiscrete

namespace ProCGroups

/-- Inverse of the actual corrected group map, with conjugation displayed. -/
theorem innerCorrectedGroupEquiv_symm_apply
    {A B : Type*} [Group A] [Group B]
    [TopologicalSpace A] [TopologicalSpace B] [IsTopologicalGroup B]
    (α : A ≃ₜ* B) (c g : B) :
    (innerCorrectedGroupEquiv α c).symm g = α.symm (c⁻¹ * g * c) := by
  apply (innerCorrectedGroupEquiv α c).injective
  rw [(innerCorrectedGroupEquiv α c).apply_symm_apply,
    innerCorrectedGroupEquiv_apply, α.apply_symm_apply]
  simp only [mul_assoc, mul_inv_cancel_left, mul_inv_cancel, mul_one]

end ProCGroups

namespace CategoryTheory.PreGaloisCategory

universe u₁ v₁ u₂ v₂ w

variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]
  [GaloisCategory C] [GaloisCategory D]
  (F : C ⥤ FintypeCat.{w}) [FiberFunctor F]
  (G : D ⥤ FintypeCat.{w}) [FiberFunctor G]
  (α : Aut F ≃ₜ* Aut G) (c : Aut G) (U : C)

/-- The actual fibre comparison: e1, then e0 inverse, then translation by c. -/
def innerCorrectedCoverTransportFiberEquiv :
    G.obj ((coverTransportOfAutEquiv F G (ProCGroups.innerCorrectedGroupEquiv α c)).functor.obj U) ≃
      G.obj ((coverTransportOfAutEquiv F G α).functor.obj U) :=
  (coverTransportFiberEquiv F G (ProCGroups.innerCorrectedGroupEquiv α c) U).trans
    (((coverTransportFiberEquiv F G α U).symm).trans (MulAction.toPerm c))

@[simp] theorem innerCorrectedCoverTransportFiberEquiv_apply
    (x : G.obj
      ((coverTransportOfAutEquiv F G (ProCGroups.innerCorrectedGroupEquiv α c)).functor.obj U)) :
    innerCorrectedCoverTransportFiberEquiv F G α c U x =
      c • (coverTransportFiberEquiv F G α U).symm
        (coverTransportFiberEquiv F G (ProCGroups.innerCorrectedGroupEquiv α c) U x) := rfl

/-- The displayed fibre comparison is equivariant for the unchanged target group. -/
theorem innerCorrectedCoverTransportFiberEquiv_smul
    (g : Aut G)
    (x : G.obj
      ((coverTransportOfAutEquiv F G (ProCGroups.innerCorrectedGroupEquiv α c)).functor.obj U)) :
    innerCorrectedCoverTransportFiberEquiv F G α c U (g • x) =
      g • innerCorrectedCoverTransportFiberEquiv F G α c U x := by
  change c • (coverTransportFiberEquiv F G α U).symm
      (coverTransportFiberEquiv F G (ProCGroups.innerCorrectedGroupEquiv α c) U (g • x)) =
    g • (c • (coverTransportFiberEquiv F G α U).symm
      (coverTransportFiberEquiv F G (ProCGroups.innerCorrectedGroupEquiv α c) U x))
  rw [coverTransportFiberEquiv_smul, ProCGroups.innerCorrectedGroupEquiv_symm_apply,
    coverTransportFiberEquiv_symm_smul]
  simp only [mul_smul, smul_inv_smul]

/-- Full faithfulness realizes that exact fibre comparison as an actual
isomorphism from corrected transport to the original transported cover. -/
def innerCorrectedCoverTransportIso :
    (coverTransportOfAutEquiv F G (ProCGroups.innerCorrectedGroupEquiv α c)).functor.obj U ≅
      (coverTransportOfAutEquiv F G α).functor.obj U :=
  coverIsoOfEquivariantFiberEquiv G
    (innerCorrectedCoverTransportFiberEquiv F G α c U)
    (innerCorrectedCoverTransportFiberEquiv_smul F G α c U)

/-- Evaluation of the actual comparison retains the specified translation. -/
theorem innerCorrectedCoverTransportIso_hom_apply
    (x : G.obj
      ((coverTransportOfAutEquiv F G (ProCGroups.innerCorrectedGroupEquiv α c)).functor.obj U)) :
    G.map (innerCorrectedCoverTransportIso F G α c U).hom x =
      c • (coverTransportFiberEquiv F G α U).symm
        (coverTransportFiberEquiv F G (ProCGroups.innerCorrectedGroupEquiv α c) U x) :=
  coverIsoOfEquivariantFiberEquiv_hom_apply G
    (innerCorrectedCoverTransportFiberEquiv F G α c U)
    (innerCorrectedCoverTransportFiberEquiv_smul F G α c U) x

variable {V : D}

/-- Keep any original named target cover and its original isomorphism. Only
precompose with the actual comparison for the corrected transport. -/
def innerCorrectedNamedCoverIso
    (J : (coverTransportOfAutEquiv F G α).functor.obj U ≅ V) :
    (coverTransportOfAutEquiv F G (ProCGroups.innerCorrectedGroupEquiv α c)).functor.obj U ≅ V :=
  innerCorrectedCoverTransportIso F G α c U ≪≫ J

/-- Naturality of the target-group action moves the same translation through
the original named isomorphism, without changing the target cover V. -/
theorem innerCorrectedNamedCoverIso_hom_apply
    (J : (coverTransportOfAutEquiv F G α).functor.obj U ≅ V)
    (x : G.obj
      ((coverTransportOfAutEquiv F G (ProCGroups.innerCorrectedGroupEquiv α c)).functor.obj U)) :
    G.map (innerCorrectedNamedCoverIso F G α c U J).hom x =
      c • G.map J.hom ((coverTransportFiberEquiv F G α U).symm
        (coverTransportFiberEquiv F G (ProCGroups.innerCorrectedGroupEquiv α c) U x)) := by
  change G.map ((innerCorrectedCoverTransportIso F G α c U).hom ≫ J.hom) x = _
  rw [G.map_comp]
  change G.map J.hom (G.map (innerCorrectedCoverTransportIso F G α c U).hom x) = _
  rw [innerCorrectedCoverTransportIso_hom_apply]
  exact (ConcreteCategory.congr_hom (c.hom.naturality J.hom)
    ((coverTransportFiberEquiv F G α U).symm
      (coverTransportFiberEquiv F G (ProCGroups.innerCorrectedGroupEquiv α c) U x))).symm

/-- In the original source-fibre coordinate, the corrected named fibre map
is exactly the original named fibre map translated by c. -/
theorem innerCorrectedNamedCoverIso_hom_sourceFiber
    (J : (coverTransportOfAutEquiv F G α).functor.obj U ≅ V) (x : F.obj U) :
    G.map (innerCorrectedNamedCoverIso F G α c U J).hom
        ((coverTransportFiberEquiv F G (ProCGroups.innerCorrectedGroupEquiv α c) U).symm x) =
      c • G.map J.hom ((coverTransportFiberEquiv F G α U).symm x) := by
  rw [innerCorrectedNamedCoverIso_hom_apply, Equiv.apply_symm_apply]

end CategoryTheory.PreGaloisCategory
