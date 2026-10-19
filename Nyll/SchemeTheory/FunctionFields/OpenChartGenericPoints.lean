/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_AlgebraicCurve_CurveModel_exists_hom_of_algHom.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

The shared structural-map proof is extracted from the NYLL adaptation of
that file and maintained in SchemeTheory.FunctionFields.StructureMorphism.
The open-chart point constructions and their point-compatibility proofs
are local additions.

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/
import Nyll.SchemeTheory.FunctionFields.OpenImmersion
import Nyll.SchemeTheory.FunctionFields.GenericFieldSourceNaturality
import Nyll.SchemeTheory.Normalization.FiniteSeparable

/-! # Generic points from the actual function-field coordinate of an open chart

The point is defined from the inverse of the specified field coordinate.
All point equalities are proved. Compatibility between arithmetic and geometric
open charts is deduced from the already proved proper field-coordinate equation
and the actual scheme square. It is not a new naturality hypothesis.
-/

noncomputable section
open CategoryTheory AlgebraicGeometry TopologicalSpace
open EtaleFundamentalGroups

namespace AlgebraicGeometry.Scheme

universe u

/-- The literal generic point with source the chosen coordinate field. -/
def functionFieldChartPoint {F : Type u} [Field F]
    (X : Scheme.{u}) [IsIntegral X] (E : F ≃+* X.functionField) :
    Spec (.of F) ⟶ X :=
  Spec.map (CommRingCat.ofHom E.symm.toRingHom) ≫
    X.fromSpecStalk (genericPoint X)

/-- Transporting the coordinate field to the original ambient field reproduces
exactly the original generic-extension morphism. -/
theorem functionFieldChartPoint_extend {F Ω : Type u} [Field F] [Field Ω]
    (X : Scheme.{u}) [IsIntegral X] (E : F ≃+* X.functionField)
    [Algebra X.functionField Ω] :
    Spec.map (CommRingCat.ofHom
        ((algebraMap X.functionField Ω).comp E.toRingHom)) ≫
      X.functionFieldChartPoint E = X.genericExtensionMorphism Ω := by
  have hcancel : ((algebraMap X.functionField Ω).comp E.toRingHom).comp
      E.symm.toRingHom = algebraMap X.functionField Ω := by
    ext a
    change algebraMap X.functionField Ω (E (E.symm a)) = _
    rw [E.apply_symm_apply]
  unfold functionFieldChartPoint
  rw [← Category.assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp, hcancel]
  rfl

/-- The exact chart-point equation, including the identity morphism in its
statement, for the canonical coordinate algebra and its induced ambient algebra. -/
theorem functionFieldChartPoint_hchartpoint {F Ω : Type u} [Field F] [Field Ω]
    (X : Scheme.{u}) [IsIntegral X] (E : F ≃+* X.functionField)
    [Algebra X.functionField Ω] :
    letI : Algebra F X.functionField := E.toRingHom.toAlgebra
    letI : Algebra F Ω :=
      ((algebraMap X.functionField Ω).comp E.toRingHom).toAlgebra
    X.genericExtensionMorphism Ω ≫ 𝟙 X =
      Spec.map (CommRingCat.ofHom (algebraMap F Ω)) ≫ X.functionFieldChartPoint E := by
  rw [Category.comp_id]
  exact (functionFieldChartPoint_extend X E).symm

/-- The same hchartpoint equation for ambient algebras already constructed
by the caller. The only compatibility input is the caller's existing hfield. -/
theorem functionFieldChartPoint_hchartpoint_of_hfield
    {F Ω : Type u} [Field F] [Field Ω]
    (X : Scheme.{u}) [IsIntegral X] (E : F ≃+* X.functionField)
    [Algebra F X.functionField] [Algebra X.functionField Ω] [Algebra F Ω]
    [IsScalarTower F X.functionField Ω]
    (hfield : algebraMap F X.functionField = E.toRingHom) :
    X.genericExtensionMorphism Ω ≫ 𝟙 X =
      Spec.map (CommRingCat.ofHom (algebraMap F Ω)) ≫ X.functionFieldChartPoint E := by
  have hmap : algebraMap F Ω = (algebraMap X.functionField Ω).comp E.toRingHom := by
    rw [IsScalarTower.algebraMap_eq F X.functionField Ω, hfield]
  rw [Category.comp_id, hmap]
  exact (functionFieldChartPoint_extend X E).symm

/-- Passing to an actual open chart does not change the specified generic point
in the proper ambient scheme. -/
theorem functionFieldChartPoint_comp_openImmersion
    {F : Type u} [Field F] {X U : Scheme.{u}}
    [IsIntegral X] [IsIntegral U] (E : F ≃+* X.functionField)
    (j : U ⟶ X) [IsOpenImmersion j] :
    U.functionFieldChartPoint (E.trans j.functionFieldRingEquivOfIsOpenImmersion) ≫ j =
      X.functionFieldChartPoint E := by
  let hj : DenseRange j :=
    j.isOpenEmbedding.isOpenMap.denseRange_of_isPreirreducibleSpace j
  have hcancel : (E.trans j.functionFieldRingEquivOfIsOpenImmersion).symm.toRingHom.comp
      (j.functionFieldMap hj) = E.symm.toRingHom := by
    ext a
    change E.symm (j.functionFieldRingEquivOfIsOpenImmersion.symm
      (j.functionFieldRingEquivOfIsOpenImmersion a)) = E.symm a
    rw [RingEquiv.symm_apply_apply]
  unfold functionFieldChartPoint
  rw [Category.assoc, ← Spec_functionFieldMap_fromSpecStalk j hj,
    ← Category.assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp, hcancel]

/-- An already proved field-coordinate equation for a dense proper morphism
implies the corresponding equality of its literal generic-point morphisms. -/
theorem functionFieldChartPoint_comp_of_functionFieldMap
    {F G : Type u} [Field F] [Field G]
    {C D : Scheme.{u}} [IsIntegral C] [IsIntegral D]
    (E : F ≃+* C.functionField) (E' : G ≃+* D.functionField)
    (π : D ⟶ C) (hπ : DenseRange π) (a : F →+* G)
    (hchart : ∀ x : F, π.functionFieldMap hπ (E x) = E' (a x)) :
    D.functionFieldChartPoint E' ≫ π =
      Spec.map (CommRingCat.ofHom a) ≫ C.functionFieldChartPoint E := by
  have hmap : E'.symm.toRingHom.comp (π.functionFieldMap hπ) =
      a.comp E.symm.toRingHom := by
    ext x
    apply E'.injective
    change E' (E'.symm (π.functionFieldMap hπ x)) = E' (a (E.symm x))
    rw [E'.apply_symm_apply]
    simpa only [E.apply_symm_apply] using hchart (E.symm x)
  unfold functionFieldChartPoint
  rw [Category.assoc, ← Spec_functionFieldMap_fromSpecStalk π hπ,
    ← Category.assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp, hmap,
    CommRingCat.ofHom_comp, Spec.map_comp, Category.assoc]

/-- Generic-point compatibility of actual open charts follows by cancellation
of the arithmetic open immersion, using the actual proper square. -/
theorem functionFieldChartPoint_comp_openSquare
    {F G : Type u} [Field F] [Field G]
    {C D X Y : Scheme.{u}}
    [IsIntegral C] [IsIntegral D] [IsIntegral X] [IsIntegral Y]
    (E : F ≃+* C.functionField) (E' : G ≃+* D.functionField)
    (i : X ⟶ C) [IsOpenImmersion i] (j : Y ⟶ D) [IsOpenImmersion j]
    (π : D ⟶ C) (hπ : DenseRange π) (u : Y ⟶ X)
    (hsquare : j ≫ π = u ≫ i) (a : F →+* G)
    (hchart : ∀ x : F, π.functionFieldMap hπ (E x) = E' (a x)) :
    Y.functionFieldChartPoint (E'.trans j.functionFieldRingEquivOfIsOpenImmersion) ≫ u =
      Spec.map (CommRingCat.ofHom a) ≫
        X.functionFieldChartPoint (E.trans i.functionFieldRingEquivOfIsOpenImmersion) := by
  apply (cancel_mono i).mp
  rw [Category.assoc, ← hsquare, ← Category.assoc,
    functionFieldChartPoint_comp_openImmersion,
    functionFieldChartPoint_comp_of_functionFieldMap E E' π hπ a hchart,
    Category.assoc, functionFieldChartPoint_comp_openImmersion]

/-- Extending the preceding exact open-point square to a common ambient field
gives the hpoint equation used by actual rational cusp recognition. -/
theorem functionFieldChartPoint_ambient_openSquare
    {F G Ω : Type u} [Field F] [Field G] [Field Ω]
    [Algebra F G] [Algebra G Ω] [Algebra F Ω] [IsScalarTower F G Ω]
    {C D X Y : Scheme.{u}}
    [IsIntegral C] [IsIntegral D] [IsIntegral X] [IsIntegral Y]
    (E : F ≃+* C.functionField) (E' : G ≃+* D.functionField)
    (i : X ⟶ C) [IsOpenImmersion i] (j : Y ⟶ D) [IsOpenImmersion j]
    (π : D ⟶ C) (hπ : DenseRange π) (u : Y ⟶ X)
    (hsquare : j ≫ π = u ≫ i)
    (hchart : ∀ x : F,
      π.functionFieldMap hπ (E x) = E' (algebraMap F G x)) :
    (Spec.map (CommRingCat.ofHom (algebraMap G Ω)) ≫
        Y.functionFieldChartPoint (E'.trans j.functionFieldRingEquivOfIsOpenImmersion)) ≫ u =
      Spec.map (CommRingCat.ofHom (algebraMap F Ω)) ≫
        X.functionFieldChartPoint (E.trans i.functionFieldRingEquivOfIsOpenImmersion) := by
  rw [Category.assoc,
    functionFieldChartPoint_comp_openSquare E E' i j π hπ u hsquare
      (algebraMap F G) hchart,
    ← Category.assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp,
    ← IsScalarTower.algebraMap_eq F G Ω]

end AlgebraicGeometry.Scheme
