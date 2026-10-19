/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.AlgebraicCurves.Models.Ramification.OpenBoundary
import Nyll.AlgebraicCurves.Models.Construction.Transport
import Nyll.AlgebraicCurves.Models.Rational.PuncturedProjectiveLineBoundaryPlaces

/-! # Boundary labels under an actual isomorphism of curve models

The comparison uses the images of closed points under the specified ambient
isomorphism. In particular, passing to a rational-configuration model preserves
the number of geometric punctures.
-/

noncomputable section

open CategoryTheory AlgebraicGeometry AlgebraicCurve
open AlgebraicGeometry.ProjSpace

namespace AnabelianGeometry.GeometricFundamentalGroup

universe u v w

variable {K : Type u} [Field K]
  {F : Type v} [Field F] [Algebra K F]
  {L : Type w} [Field L] [Algebra K L]

/-- The boundary bijection of a commuting pair of actual scheme isomorphisms. -/
def boundaryPlaceEquivOfModelIso
    (M : CurveModel K F) (N : CurveModel K L)
    {X Y : Scheme.{u}} (jX : X ⟶ M.C) (jY : Y ⟶ N.C)
    (e : M.C ≅ N.C) (i : X ≅ Y)
    (hi : i.hom ≫ jY = jX ≫ e.hom) :
    M.openBoundaryPlaces jX ≃ N.openBoundaryPlaces jY := by
  let P : Place K F ≃ Place K L :=
    M.placeEquiv.symm.trans ((CurveModel.closedPointsEquivOfIso e).symm.trans N.placeEquiv)
  refine P.subtypeEquiv ?_
  intro V
  have hcenter : (N.placeEquiv.symm (P V)).val = e.hom (M.placeEquiv.symm V).val := by
    change (N.placeEquiv.symm (N.placeEquiv
      ((CurveModel.closedPointsEquivOfIso e).symm (M.placeEquiv.symm V)))).val = _
    exact congrArg Subtype.val (N.placeEquiv.symm_apply_apply _)
  change (M.placeEquiv.symm V).val ∉ Set.range jX ↔
    (N.placeEquiv.symm (P V)).val ∉ Set.range jY
  rw [hcenter]
  apply not_congr
  constructor
  · rintro ⟨x, hx⟩
    refine ⟨i.hom x, ?_⟩
    calc
      jY (i.hom x) = e.hom (jX x) :=
        congrArg (fun a : X ⟶ N.C => a x) hi
      _ = e.hom (M.placeEquiv.symm V).val := congrArg e.hom hx
  · rintro ⟨y, hy⟩
    refine ⟨i.inv y, ?_⟩
    apply e.hom.isOpenEmbedding.injective
    calc
      e.hom (jX (i.inv y)) = jY (i.hom (i.inv y)) :=
        (congrArg (fun a : X ⟶ N.C => a (i.inv y)) hi).symm
      _ = jY y := congrArg jY (congrArg (fun a : Y ⟶ Y => a y) i.inv_hom_id)
      _ = e.hom (M.placeEquiv.symm V).val := hy

/-- The boundary bijection retains its actual center in the target model. -/
theorem boundaryPlaceEquivOfModelIso_center
    (M : CurveModel K F) (N : CurveModel K L)
    {X Y : Scheme.{u}} (jX : X ⟶ M.C) (jY : Y ⟶ N.C)
    (e : M.C ≅ N.C) (i : X ≅ Y)
    (hi : i.hom ≫ jY = jX ≫ e.hom) (V : M.openBoundaryPlaces jX) :
    (N.placeEquiv.symm (boundaryPlaceEquivOfModelIso M N jX jY e i hi V).val).val =
      e.hom (M.placeEquiv.symm V.val).val := by
  change (N.placeEquiv.symm (N.placeEquiv
    ((CurveModel.closedPointsEquivOfIso e).symm (M.placeEquiv.symm V.val)))).val = _
  exact congrArg Subtype.val (N.placeEquiv.symm_apply_apply _)

/-- A literal configuration obtained by an actual geometric model isomorphism
has exactly the original number of geometric boundary places. -/
theorem rationalConfiguration_card_eq_boundary_card
    {k κ : Type} [Field k] [Field κ] [Algebra k κ]
    {F : Type} [Field F] [Algebra κ F]
    (M : CurveModel κ F) {X : Scheme} (j : X ⟶ M.C)
    (s : Finset (Projectivization k (k × k)))
    (e : M.C ≅ (projectiveLineRatFuncModel κ).C)
    (i : X ≅ CategoryTheory.Limits.pullback
      (Spec.map (CommRingCat.ofHom (algebraMap k κ)))
      ((rationalConfigurationOpen s).ι ≫ π k 1))
    (hi : i.hom ≫ rationalConfigurationBaseChangeChart k κ s = j ≫ e.hom) :
    s.card = Nat.card (M.openBoundaryPlaces j) := by
  rw [← rationalConfigurationBoundaryPlaces_card k κ s]
  exact (Nat.card_congr (boundaryPlaceEquivOfModelIso M (projectiveLineRatFuncModel κ)
    j (rationalConfigurationBaseChangeChart k κ s) e i hi)).symm

end AnabelianGeometry.GeometricFundamentalGroup
