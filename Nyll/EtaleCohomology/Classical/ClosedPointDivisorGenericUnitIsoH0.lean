/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.EtaleCohomology.Classical.AbelianRestrictionPullback
public import Nyll.EtaleCohomology.Classical.ClosedPointDivisorGenericUnitIsoNaturality
public import Nyll.EtaleCohomology.Classical.ClosedPointDivisorIsoGlobalSections
public import Nyll.EtaleCohomology.Classical.GenericUnitOpenCohomology
public import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic

/-!
# Original divisor coordinates of the native generic-unit pullback

The proved sheaf square is applied to the original cohomology pullback.
In degree zero, the original inverse-global-comparison section is exactly
the original divisor restriction section. Its closed-point coefficients
therefore undergo the actual closed-point permutation of the isomorphism.
-/

@[expose] public section

noncomputable section

universe u

open AlgebraicGeometry CategoryTheory Limits Opposite TopologicalSpace

namespace EtaleCohomology

variable {kX kY : Type u} [Field kX] [Field kY]
  {Y X : Scheme.{u}} [IsIntegral Y] [IsIntegral X]
  (fX : X ⟶ Spec (CommRingCat.of kX)) [SmoothOfRelativeDimension 1 fX]
  (fY : Y ⟶ Spec (CommRingCat.of kY)) [SmoothOfRelativeDimension 1 fY]
  (e : Y ≅ X)

/-- The inverse of the original global divisor comparison also retains
the actual quotient restriction map under a scheme isomorphism. -/
theorem smoothCurveClosedPointDivisorGenericUnitIso_inv_iso_naturality :
    (etaleRestrictionGenericUnitQuotientIso e.hom).hom ≫
        (smoothCurveClosedPointDivisorGenericUnitIso fY).inv =
      (etaleRestriction e.hom AddCommGrpCat.{u}).map
          (smoothCurveClosedPointDivisorGenericUnitIso fX).inv ≫
        (closedPointDivisorIsoRestrictionIso e).hom := by
  let R := etaleRestriction e.hom AddCommGrpCat.{u}
  let EX := smoothCurveClosedPointDivisorGenericUnitIso fX
  let EY := smoothCurveClosedPointDivisorGenericUnitIso fY
  apply (cancel_epi (R.map EX.hom)).mp
  calc
    _ = ((closedPointDivisorIsoRestrictionIso e).hom ≫ EY.hom) ≫ EY.inv := by
      rw [← Category.assoc,
        smoothCurveClosedPointDivisorGenericUnitIso_iso_naturality fX fY e]
    _ = (closedPointDivisorIsoRestrictionIso e).hom := by
      rw [Category.assoc, EY.hom_inv_id, Category.comp_id]
    _ = R.map EX.hom ≫ R.map EX.inv ≫ (closedPointDivisorIsoRestrictionIso e).hom := by
      rw [← Category.assoc, ← R.map_comp, EX.hom_inv_id, R.map_id, Category.id_comp]

/-- Actual inverse divisor coordinates of the native quotient pullback
are the native restriction of the original divisor cohomology class. -/
theorem smoothCurveClosedPointDivisorGenericUnitIso_inv_cohomology_pullback
    (i : ℕ) (a : Sheaf.H.{u} (etaleGenericUnitQuotient X) i) :
    Sheaf.H.map (smoothCurveClosedPointDivisorGenericUnitIso fY).inv i
        (etaleGenericUnitQuotientCohomologyPullback e.hom i a) =
      Sheaf.H.map (closedPointDivisorIsoRestrictionIso e).hom i
        (etaleAbelianRestrictionCohomologyPullback e.hom
          (closedPointDivisorSheaf X) i
          (Sheaf.H.map (smoothCurveClosedPointDivisorGenericUnitIso fX).inv i a)) := by
  rw [etaleGenericUnitQuotientCohomologyPullback_restriction,
    etaleAbelianRestrictionCohomologyPullback_naturality,
    ← Sheaf.H.map_comp_apply, ← Sheaf.H.map_comp_apply]
  exact congrArg
    (fun φ => Sheaf.H.map φ i
      (etaleAbelianRestrictionCohomologyPullback e.hom (etaleGenericUnitQuotient X) i a))
    (smoothCurveClosedPointDivisorGenericUnitIso_inv_iso_naturality fX fY e)

/-- Degree zero uses the actual original global divisor section map,
with the original terminal representatives on both small étale sites. -/
theorem smoothCurveClosedPointDivisorGenericUnitIso_inv_zero_sections
    (a : Sheaf.H.{u} (etaleGenericUnitQuotient X) 0) :
    Sheaf.H.equiv₀ (closedPointDivisorSheaf Y)
        (MorphismProperty.Over.mkIdTerminal
          (show MorphismProperty Scheme.{u} from @Etale) Y)
        (Sheaf.H.map (smoothCurveClosedPointDivisorGenericUnitIso fY).inv 0
          (etaleGenericUnitQuotientCohomologyPullback e.hom 0 a)) =
      closedPointDivisorIsoGlobalSectionsMap e
        (Sheaf.H.equiv₀ (closedPointDivisorSheaf X)
          (MorphismProperty.Over.mkIdTerminal
            (show MorphismProperty Scheme.{u} from @Etale) X)
          (Sheaf.H.map (smoothCurveClosedPointDivisorGenericUnitIso fX).inv 0 a)) := by
  let hX : IsTerminal (Scheme.Etale.mk (𝟙 X)) := MorphismProperty.Over.mkIdTerminal
    (show MorphismProperty Scheme.{u} from @Etale) X
  let hY : IsTerminal (Scheme.Etale.mk (𝟙 Y)) := MorphismProperty.Over.mkIdTerminal
    (show MorphismProperty Scheme.{u} from @Etale) Y
  have he : e.hom ≫ (Scheme.Etale.mk (𝟙 X)).hom =
      (Scheme.Etale.mk (𝟙 Y)).hom ≫ e.hom := by
    change e.hom ≫ 𝟙 X = 𝟙 Y ≫ e.hom
    exact (Category.comp_id e.hom).trans (Category.id_comp e.hom).symm
  have hm :
      (MorphismProperty.Over.homMk
        (P := show MorphismProperty Scheme.{u} from @Etale) (Q := ⊤)
        (A := (etalePostcompose e.hom).obj (Scheme.Etale.mk (𝟙 Y)))
        (B := Scheme.Etale.mk (𝟙 X)) e.hom he) =
      hX.from ((etalePostcompose e.hom).obj (Scheme.Etale.mk (𝟙 Y))) :=
    hX.hom_ext _ _
  change _ = (closedPointDivisorIsoRestrictionIso e).hom.hom.app
    (op (Scheme.Etale.mk (𝟙 Y)))
    ((closedPointDivisorSheaf X).obj.map
      (hX.from ((etalePostcompose e.hom).obj (Scheme.Etale.mk (𝟙 Y)))).op
      (Sheaf.H.equiv₀ (closedPointDivisorSheaf X) hX
        (Sheaf.H.map (smoothCurveClosedPointDivisorGenericUnitIso fX).inv 0 a)))
  rw [smoothCurveClosedPointDivisorGenericUnitIso_inv_cohomology_pullback fX fY e 0 a]
  have hn := Sheaf.H.equiv₀_naturality hY (closedPointDivisorIsoRestrictionIso e).hom
    (etaleAbelianRestrictionCohomologyPullback e.hom (closedPointDivisorSheaf X) 0
      (Sheaf.H.map (smoothCurveClosedPointDivisorGenericUnitIso fX).inv 0 a))
  have hz := etaleAbelianRestrictionCohomologyPullback_zero_sections e.hom
    (closedPointDivisorSheaf X) hX hY e.hom he
    (Sheaf.H.map (smoothCurveClosedPointDivisorGenericUnitIso fX).inv 0 a)
  dsimp +instances only [hX, hY] at hn hz hm ⊢
  rw [← hn, hz, hm]
  rfl

end EtaleCohomology
