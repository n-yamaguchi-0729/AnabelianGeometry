/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.EtaleCohomology.Classical.ClosedPointDivisorGenericUnitArbitraryChart
public import Nyll.EtaleCohomology.Classical.ClosedPointDivisorGenericUnitCharts
public import Mathlib.AlgebraicGeometry.OpenImmersion

/-!
# Original affine comparisons along an open immersion

An affine open immersion is an isomorphism onto its actual open range.
Transporting the existing chart comparison along that proved factorization
allows the same affine ring to be used on both sides of a scheme isomorphism.
All residue-fiber coefficients remain the original ones.
-/

@[expose] public section

noncomputable section

universe u

open AlgebraicGeometry CategoryTheory Limits Opposite TopologicalSpace

namespace EtaleCohomology.DivisorGenericUnitGlobal

section Divisors

variable (R : Type u) [CommRing R] {X : Scheme.{u}} [JacobsonSpace X]

/-- The original chart comparison along its specified, equal, open
immersion. This only transports the source along the factorization equality. -/
def affineChartDivisorIsoAlong (U : X.Opens)
    (e : Spec (CommRingCat.of R) ≅ (U : Scheme))
    (q : Spec (CommRingCat.of R) ⟶ X) [IsOpenImmersion q]
    (hq : e.hom ≫ U.ι = q) :
    (etaleRestriction q AddCommGrpCat.{u}).obj (closedPointDivisorSheaf X) ≅
      closedPointDivisorSheaf (Spec (CommRingCat.of R)) := by
  subst q
  exact affineChartDivisorIso R U e

/-- The transported original chart map preserves every original
coefficient at any specified image closed point. -/
theorem affineChartDivisorIsoAlong_coefficient (U : X.Opens)
    (e : Spec (CommRingCat.of R) ≅ (U : Scheme))
    (q : Spec (CommRingCat.of R) ⟶ X) [IsOpenImmersion q]
    (hq : e.hom ≫ U.ι = q)
    (y : closedPoints (Spec (CommRingCat.of R))) (x : closedPoints X)
    (hx : q y.1 = x.1) (V : (Spec (CommRingCat.of R)).Etale)
    (s : (closedPointDivisorSheaf X).obj.obj (op ((etalePostcompose q).obj V)))
    (z : closedPointResidueFiber (Spec (CommRingCat.of R)) y V) :
    closedPointDivisorSummandSectionsAddEquiv (Spec (CommRingCat.of R)) y V
      ((closedPointDivisorSheafComponentProjection (Spec (CommRingCat.of R)) y).hom.app
        (op V) ((affineChartDivisorIsoAlong R U e q hq).hom.hom.app (op V) s)) z =
    closedPointDivisorSummandSectionsAddEquiv X x ((etalePostcompose q).obj V)
      ((closedPointDivisorSheafComponentProjection X x).hom.app
        (op ((etalePostcompose q).obj V)) s)
      ⟨z.1, (congrArg q z.2).trans hx⟩ := by
  subst q
  let yU : closedPoints (U : Scheme) :=
    (e.hom.homeomorph.sets e.hom.isClosedEmbedding.preimage_closedPoints.symm).toEquiv y
  let x₀ : closedPoints X := ((closedPointsOpenEquiv U) yU).1
  have hxx : x₀ = x := Subtype.ext hx
  subst x
  exact affineChartDivisorIso_coefficient R U e y V s z

/-- The actual isomorphism from an affine open immersion to its open range. -/
def affineOpenRangeIso (q : Spec (CommRingCat.of R) ⟶ X) [IsOpenImmersion q] :
    Spec (CommRingCat.of R) ≅ (q.opensRange : Scheme) :=
  IsOpenImmersion.isoOfRangeEq q q.opensRange.ι Subtype.range_val.symm

omit [JacobsonSpace X] in
/-- The range isomorphism has the original affine open immersion as
its composite with the open inclusion. -/
theorem affineOpenRangeIso_hom_fac
    (q : Spec (CommRingCat.of R) ⟶ X) [IsOpenImmersion q] :
    (affineOpenRangeIso R q).hom ≫ q.opensRange.ι = q :=
  IsOpenImmersion.isoOfRangeEq_hom_fac q q.opensRange.ι Subtype.range_val.symm

/-- Restriction of the original divisor sheaf along an actual affine
open immersion, using its actual open range. -/
def affineOpenDivisorIso (q : Spec (CommRingCat.of R) ⟶ X) [IsOpenImmersion q] :
    (etaleRestriction q AddCommGrpCat.{u}).obj (closedPointDivisorSheaf X) ≅
      closedPointDivisorSheaf (Spec (CommRingCat.of R)) :=
  affineChartDivisorIsoAlong R q.opensRange (affineOpenRangeIso R q) q
    (affineOpenRangeIso_hom_fac R q)

/-- The actual image closed point of an affine open immersion into a
Jacobson scheme. -/
def affineOpenClosedPoint (q : Spec (CommRingCat.of R) ⟶ X) [IsOpenImmersion q]
    (y : closedPoints (Spec (CommRingCat.of R))) : closedPoints X :=
  ((closedPointsOpenEquiv q.opensRange)
    (((affineOpenRangeIso R q).hom.homeomorph.sets
      (affineOpenRangeIso R q).hom.isClosedEmbedding.preimage_closedPoints.symm).toEquiv y)).1

/-- The closed-point image has the original map on its underlying point. -/
theorem affineOpenClosedPoint_coe
    (q : Spec (CommRingCat.of R) ⟶ X) [IsOpenImmersion q]
    (y : closedPoints (Spec (CommRingCat.of R))) :
    q y.1 = (affineOpenClosedPoint R q y).1 :=
  (congrArg (fun m => m y.1) (affineOpenRangeIso_hom_fac R q)).symm

/-- Every original residue-fiber coefficient survives the actual
affine open-restriction comparison. -/
theorem affineOpenDivisorIso_coefficient
    (q : Spec (CommRingCat.of R) ⟶ X) [IsOpenImmersion q]
    (y : closedPoints (Spec (CommRingCat.of R))) (x : closedPoints X)
    (hx : q y.1 = x.1) (V : (Spec (CommRingCat.of R)).Etale)
    (s : (closedPointDivisorSheaf X).obj.obj (op ((etalePostcompose q).obj V)))
    (z : closedPointResidueFiber (Spec (CommRingCat.of R)) y V) :
    closedPointDivisorSummandSectionsAddEquiv (Spec (CommRingCat.of R)) y V
      ((closedPointDivisorSheafComponentProjection (Spec (CommRingCat.of R)) y).hom.app
        (op V) ((affineOpenDivisorIso R q).hom.hom.app (op V) s)) z =
    closedPointDivisorSummandSectionsAddEquiv X x ((etalePostcompose q).obj V)
      ((closedPointDivisorSheafComponentProjection X x).hom.app
        (op ((etalePostcompose q).obj V)) s)
      ⟨z.1, (congrArg q z.2).trans hx⟩ :=
  affineChartDivisorIsoAlong_coefficient R q.opensRange (affineOpenRangeIso R q) q
    (affineOpenRangeIso_hom_fac R q) y x hx V s z

end Divisors

section GenericUnits

variable (R : Type u) [CommRing R] [IsDedekindDomain R]
  {k : Type u} [Field k] {X : Scheme.{u}} [IsIntegral X] [JacobsonSpace X]
  (f : X ⟶ Spec (CommRingCat.of k)) [SmoothOfRelativeDimension 1 f]

private theorem global_hom_affineChart_along (U : X.Opens)
    (e : Spec (CommRingCat.of R) ≅ (U : Scheme))
    (q : Spec (CommRingCat.of R) ⟶ X) [IsOpenImmersion q]
    (hq : e.hom ≫ U.ι = q) (hR : ¬ IsField R) :
    let _ : HasColimitsOfShape (Discrete (closedPoints (Spec (CommRingCat.of R))))
        (Sheaf (Spec (CommRingCat.of R)).smallEtaleTopology AddCommGrpCat.{u}) :=
      closedPointDivisorSheafHasColimitsOfShape (Spec (CommRingCat.of R))
    (etaleRestriction q AddCommGrpCat.{u}).map
        (smoothCurveClosedPointDivisorGenericUnitIso f).hom ≫
      (affineChartGenericUnitQuotientIso R q).hom =
    (affineChartDivisorIsoAlong R U e q hq).hom ≫
      (affineClosedPointDivisorGenericUnitSheafIso R hR).hom ≫
      (affineGenericPointUnitQuotientFractionRingIso R).hom := by
  intro hShape
  subst q
  rw [smoothCurveClosedPointDivisorGenericUnitIso_hom_affineChart f R U e hR]
  exact affineChartDivisorGenericUnitIso_hom_comp R U e hR

/-- Normalizing the actual global comparison along any affine open
immersion gives the original affine comparison over that same ring. -/
theorem smoothCurveClosedPointDivisorGenericUnitIso_hom_affineOpen
    (q : Spec (CommRingCat.of R) ⟶ X) [IsOpenImmersion q] (hR : ¬ IsField R) :
    let _ : HasColimitsOfShape (Discrete (closedPoints (Spec (CommRingCat.of R))))
        (Sheaf (Spec (CommRingCat.of R)).smallEtaleTopology AddCommGrpCat.{u}) :=
      closedPointDivisorSheafHasColimitsOfShape (Spec (CommRingCat.of R))
    (etaleRestriction q AddCommGrpCat.{u}).map
        (smoothCurveClosedPointDivisorGenericUnitIso f).hom ≫
      (affineChartGenericUnitQuotientIso R q).hom =
    (affineOpenDivisorIso R q).hom ≫
      (affineClosedPointDivisorGenericUnitSheafIso R hR).hom ≫
      (affineGenericPointUnitQuotientFractionRingIso R).hom :=
  global_hom_affineChart_along R f q.opensRange (affineOpenRangeIso R q) q
    (affineOpenRangeIso_hom_fac R q) hR

end GenericUnits

end EtaleCohomology.DivisorGenericUnitGlobal
