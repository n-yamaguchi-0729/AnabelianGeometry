/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.EtaleCohomology.Classical.ClosedPointDivisorGenericUnitGlobal
public import Nyll.EtaleCohomology.Classical.ClosedPointDivisorGenericUnitCharts
public import Nyll.EtaleCohomology.Sites.EtaleRestrictionGluing
public import Nyll.EtaleCohomology.Sites.EtaleSlice
public import Mathlib.AlgebraicGeometry.AffineScheme

/-!
# The original global comparison on any affine chart

The global comparison was glued using the canonical coordinate rings of
affine opens. The proved overlap identity identifies its restriction with
the original comparison for every actual Dedekind affine chart, including
a chart carried along a scheme isomorphism.
-/

@[expose] public section

noncomputable section

universe u

open AlgebraicGeometry CategoryTheory Limits Opposite TopologicalSpace

namespace EtaleCohomology

open DivisorGenericUnitGlobal

private theorem etaleRestriction_map_eq_of_slice_overlap
    {X : Scheme.{u}} (F G : Sheaf X.smallEtaleTopology AddCommGrpCat.{u})
    (U W : X.Etale) (m : U ⟶ W)
    (a : (etaleRestriction U.hom AddCommGrpCat.{u}).obj F ⟶
      (etaleRestriction U.hom AddCommGrpCat.{u}).obj G)
    (b : (etaleRestriction W.hom AddCommGrpCat.{u}).obj F ⟶
      (etaleRestriction W.hom AddCommGrpCat.{u}).obj G)
    (g : F ⟶ G) (hW : (etaleRestriction W.hom AddCommGrpCat.{u}).map g = b)
    (h : ∀ (Y : X.Etale) (nR : Y ⟶ U) (nB : Y ⟶ W),
      (etaleRestrictionHomToSlice U a).app (op (Over.mk nR)) =
        (etaleRestrictionHomToSlice W b).app (op (Over.mk nB))) :
    (etaleRestriction U.hom AddCommGrpCat.{u}).map g = a := by
  apply etaleRestrictionHomToSlice_injective U
  rw [etaleRestrictionHomToSlice_map]
  apply NatTrans.ext
  funext T0
  obtain ⟨T⟩ := T0
  obtain ⟨Y, nR, rfl⟩ := Over.mk_surjective T
  have hb := congr_app
    (congrArg (etaleRestrictionHomToSlice W) hW) (op (Over.mk (nR ≫ m)))
  have hmap := congr_app (etaleRestrictionHomToSlice_map W g)
    (op (Over.mk (nR ≫ m)))
  exact hmap.symm.trans (hb.trans (h Y nR (nR ≫ m)).symm)

/-- Restriction of the actual global comparison to an arbitrary affine
chart is the original comparison constructed from that same chart. -/
theorem smoothCurveClosedPointDivisorGenericUnitIso_hom_affineChart
    {k : Type u} [Field k] {X : Scheme.{u}} [IsIntegral X] [JacobsonSpace X]
    (f : X ⟶ Spec (CommRingCat.of k)) [SmoothOfRelativeDimension 1 f]
    (R : Type u) [CommRing R] [IsDedekindDomain R]
    (U : X.Opens) (e : Spec (CommRingCat.of R) ≅ (U : Scheme))
    (hR : ¬ IsField R) :
    (etaleRestriction (e.hom ≫ U.ι) AddCommGrpCat.{u}).map
        (smoothCurveClosedPointDivisorGenericUnitIso f).hom =
      (affineChartDivisorGenericUnitIso R U e hR).hom := by
  have hSmooth : Smooth f := SmoothOfRelativeDimension.smooth 1 f
  have hU : IsAffineOpen U := IsAffine.of_isIso e.inv
  have hNonempty : Nonempty U := by
    obtain ⟨x⟩ := (inferInstance : Nonempty (Spec (CommRingCat.of R)))
    exact ⟨e.hom x⟩
  have hDedekind : IsDedekindDomain Γ(X, U) :=
    SmoothOfRelativeDimension.isDedekindDomain_sections f hU
  let A : NonemptyAffineOpen X := ⟨U, hU, hNonempty⟩
  let CR : X.Etale := Scheme.Etale.mk (e.hom ≫ U.ι)
  let d : Spec (CommRingCat.of Γ(X, U)) ≅ (U : Scheme) := hU.isoSpec.symm
  let CB : X.Etale := Scheme.Etale.mk (d.hom ≫ U.ι)
  let m : CR ⟶ CB := MorphismProperty.Over.homMk
    (e.hom ≫ hU.isoSpec.hom) (by
      change (e.hom ≫ hU.isoSpec.hom) ≫ (hU.isoSpec.inv ≫ U.ι) = e.hom ≫ U.ι
      simp only [Category.assoc, Iso.hom_inv_id_assoc])
  let g := (smoothCurveClosedPointDivisorGenericUnitIso f).hom
  have hB := smoothCurveClosedPointDivisorGenericUnitIso_hom_restrict f A
  dsimp only [A, nonemptyAffineEtaleChart, smoothCurveChartDivisorGenericUnitIso] at hB
  have hlocal := fun (Y : X.Etale)
      (nR : Y ⟶ Scheme.Etale.mk (e.hom ≫ U.ι))
      (nB : Y ⟶ Scheme.Etale.mk (d.hom ≫ U.ι)) =>
    affineChartDivisorGenericUnitIso_overlap R Γ(X, U) U U e d
      hR (SmoothOfRelativeDimension.not_isField_sections f hU) Y nR nB
  exact etaleRestriction_map_eq_of_slice_overlap
    (closedPointDivisorSheaf X) (etaleGenericUnitQuotient X)
    (Scheme.Etale.mk (e.hom ≫ U.ι)) (Scheme.Etale.mk (d.hom ≫ U.ι)) m
    (affineChartDivisorGenericUnitIso R U e hR).hom
    (affineChartDivisorGenericUnitIso Γ(X, U) U d
      (SmoothOfRelativeDimension.not_isField_sections f hU)).hom g hB hlocal

end EtaleCohomology
