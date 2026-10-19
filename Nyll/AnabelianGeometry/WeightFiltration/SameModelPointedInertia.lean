/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.AnabelianGeometry.WeightFiltration.NamedModelPointedInertia
import Nyll.AnabelianGeometry.WeightFiltration.GenericPlaceInertiaChartImage
import Nyll.AnabelianGeometry.WeightFiltration.BoundaryInertiaMap
import Nyll.SchemeTheory.FunctionFields.OpenChartGenericPoints
import Nyll.AlgebraicCurves.Models.Construction.Basic

/-! # The same place inertia in two actual charts of one geometric model

A commuting square of open charts gives the generic-point equality. The
resulting pointed map carries the inertia of the same normalization prime
exactly, before abelianization. This applies to the actual constant-field
tower comparison and does not choose a new boundary correspondence.
-/

noncomputable section
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.FiniteEtale
open AlgebraicCurve SchemeTheory EtaleFundamentalGroups.Inertia ProCGroups.Abelian

namespace AnabelianGeometry.WeightFiltration

attribute [local instance] CurveModel.isIntegral normalizationCommAlgGaloisAction

private theorem pointed_subgroup_image_of_equal_target
    {X Y : Scheme} {Ω : Type} [Field Ω] [IsSepClosed Ω] [ConnectedSpace Y]
    (f : X ⟶ Y) (x : Spec (.of Ω) ⟶ X) (y z : Spec (.of Ω) ⟶ Y)
    (h : z = y) (hf : x ≫ f = z) (hy : y ≫ 𝟙 Y = z)
    (I : Subgroup π₁ᵉᵗ(x)) (J : Subgroup π₁ᵉᵗ(y)) (K : Subgroup π₁ᵉᵗ(z))
    (hI : I.map (pointedFundamentalGroupHom f x z hf).toMonoidHom = K)
    (hJ : J.map (pointedFundamentalGroupHom (𝟙 Y) y z hy).toMonoidHom = K) :
    I.map (pointedFundamentalGroupHom f x y (hf.trans h)).toMonoidHom = J := by
  subst z
  rw [pointedFundamentalGroupHom_id] at hJ
  have hJ' : J.map (MonoidHom.id _) = K := hJ
  rw [Subgroup.map_id] at hJ'
  exact hI.trans hJ'.symm

/-- A morphism compatible with the supplied generic points carries the same
original place inertia to itself in the target chart. Both chart fields are
identified with the same F by their actual, surjective algebra maps. -/
theorem genericPlaceInertia_pointed_sameField_image
    {K F Ω : Type} [Field K] [Field F] [Algebra K F] [Field Ω]
    (X Y : Scheme) [IsIntegral X] [IsIntegral Y]
    [Algebra F X.functionField] [Algebra F Y.functionField]
    [Algebra X.functionField Ω] [Algebra Y.functionField Ω] [Algebra F Ω]
    [IsScalarTower F X.functionField Ω] [IsScalarTower F Y.functionField Ω]
    [IsSepClosed Ω] [IsSepClosure X.functionField Ω]
    [IsSepClosure Y.functionField Ω] [IsSepClosure F Ω]
    (f : X ⟶ Y)
    (hpoint : X.genericExtensionMorphism Ω ≫ f = Y.genericExtensionMorphism Ω)
    (hsX : Function.Surjective (algebraMap F X.functionField))
    (hsY : Function.Surjective (algebraMap F Y.functionField))
    (p : Place K F) [Algebra p.toValuationSubring Ω]
    [IsScalarTower p.toValuationSubring F Ω]
    (Q : Ideal (normalizationCommAlgCat p.toValuationSubring Ω)) :
    (genericPlaceInertia X p Q).map
      (pointedFundamentalGroupHom f (X.genericExtensionMorphism Ω)
        (Y.genericExtensionMorphism Ω) hpoint).toMonoidHom =
      genericPlaceInertia Y p Q := by
  let EY : F ≃+* Y.functionField :=
    RingEquiv.ofBijective (algebraMap F Y.functionField)
      ⟨(algebraMap F Y.functionField).injective, hsY⟩
  have hY := Scheme.functionFieldChartPoint_hchartpoint_of_hfield (Ω := Ω) Y EY
    (show algebraMap F Y.functionField = EY.toRingHom from rfl)
  have hYpoint : ξ F Ω ≫ Y.functionFieldChartPoint EY =
      Y.genericExtensionMorphism Ω := hY.symm.trans (Category.comp_id _)
  have hXpoint : X.genericExtensionMorphism Ω ≫ f =
      ξ F Ω ≫ Y.functionFieldChartPoint EY := hpoint.trans hYpoint.symm
  have hXimage := genericPlaceInertia_pointed_morphism_chart_image X Y f p Q hsX
    (Y.functionFieldChartPoint EY) hXpoint
  have hYimage := genericPlaceInertia_pointed_chart_image Y p Q hsY
    (Y.functionFieldChartPoint EY) hY
  exact pointed_subgroup_image_of_equal_target f _ _ _ hYpoint hXpoint hY
    _ _ _ hXimage hYimage

/-- The pointed comparison of two actual open charts in the same model is
forced by their commuting square and the supplied coordinate algebras. -/
theorem sameModel_genericPoint_comp
    {K F Ω : Type} [Field K] [Field F] [Algebra K F] [Field Ω]
    (M : CurveModel K F) {X Y : Scheme} [IsIntegral X] [IsIntegral Y]
    (jX : X ⟶ M.C) (jY : Y ⟶ M.C) [IsOpenImmersion jX] [IsOpenImmersion jY]
    (hjX : DenseRange jX) (hjY : DenseRange jY)
    [Algebra F X.functionField] [Algebra F Y.functionField]
    (hfieldX : algebraMap F X.functionField =
      (jX.functionFieldMap hjX).comp M.ffEquiv.toRingHom)
    (hfieldY : algebraMap F Y.functionField =
      (jY.functionFieldMap hjY).comp M.ffEquiv.toRingHom)
    [Algebra X.functionField Ω] [Algebra Y.functionField Ω] [Algebra F Ω]
    [IsScalarTower F X.functionField Ω] [IsScalarTower F Y.functionField Ω]
    (f : X ⟶ Y) (hsquare : f ≫ jY = jX) :
    X.genericExtensionMorphism Ω ≫ f = Y.genericExtensionMorphism Ω := by
  let EX := M.ffEquiv.trans jX.functionFieldRingEquivOfIsOpenImmersion
  let EY := M.ffEquiv.trans jY.functionFieldRingEquivOfIsOpenImmersion
  have hX := Scheme.functionFieldChartPoint_hchartpoint_of_hfield (Ω := Ω) X EX hfieldX
  have hY := Scheme.functionFieldChartPoint_hchartpoint_of_hfield (Ω := Ω) Y EY hfieldY
  have hXpoint : X.genericExtensionMorphism Ω = ξ F Ω ≫ X.functionFieldChartPoint EX :=
    (Category.comp_id _).symm.trans hX
  have hYpoint : Y.genericExtensionMorphism Ω = ξ F Ω ≫ Y.functionFieldChartPoint EY :=
    (Category.comp_id _).symm.trans hY
  apply (cancel_mono jY).mp
  calc
    (X.genericExtensionMorphism Ω ≫ f) ≫ jY = X.genericExtensionMorphism Ω ≫ jX := by
      rw [Category.assoc, hsquare]
    _ = ξ F Ω ≫ M.C.functionFieldChartPoint M.ffEquiv := by
      rw [hXpoint, Category.assoc, Scheme.functionFieldChartPoint_comp_openImmersion]
    _ = Y.genericExtensionMorphism Ω ≫ jY := by
      rw [hYpoint, Category.assoc, Scheme.functionFieldChartPoint_comp_openImmersion]

/-- Actual inertia and its abelian image are unchanged by a commuting change
of open chart in one geometric model. No inertia-preservation equation or
independently chosen point comparison is an input. -/
theorem sameModel_pointed_inertia_image
    {K F Ω : Type} [Field K] [Field F] [Algebra K F] [Field Ω]
    (M : CurveModel K F) {X Y : Scheme} [IsIntegral X] [IsIntegral Y]
    (jX : X ⟶ M.C) (jY : Y ⟶ M.C) [IsOpenImmersion jX] [IsOpenImmersion jY]
    (hjX : DenseRange jX) (hjY : DenseRange jY)
    [Algebra F X.functionField] [Algebra F Y.functionField]
    (hfieldX : algebraMap F X.functionField =
      (jX.functionFieldMap hjX).comp M.ffEquiv.toRingHom)
    (hfieldY : algebraMap F Y.functionField =
      (jY.functionFieldMap hjY).comp M.ffEquiv.toRingHom)
    [Algebra X.functionField Ω] [Algebra Y.functionField Ω] [Algebra F Ω]
    [IsScalarTower F X.functionField Ω] [IsScalarTower F Y.functionField Ω]
    [IsSepClosed Ω] [IsSepClosure X.functionField Ω]
    [IsSepClosure Y.functionField Ω] [IsSepClosure F Ω]
    (f : X ⟶ Y) (hsquare : f ≫ jY = jX)
    (p : Place K F) [Algebra p.toValuationSubring Ω]
    [IsScalarTower p.toValuationSubring F Ω]
    (Q : Ideal (normalizationCommAlgCat p.toValuationSubring Ω)) :
    let hpoint := sameModel_genericPoint_comp M jX jY hjX hjY hfieldX hfieldY f hsquare
    let ψ := pointedFundamentalGroupHom f (X.genericExtensionMorphism Ω)
      (Y.genericExtensionMorphism Ω) hpoint
    (genericPlaceInertia X p Q).map ψ.toMonoidHom = genericPlaceInertia Y p Q ∧
      ((genericPlaceInertia X p Q).map
        (TopologicalAbelianization.mk π₁ᵉᵗ(X.genericExtensionMorphism Ω))).map
          (TopologicalAbelianization.map ψ).toMonoidHom =
        (genericPlaceInertia Y p Q).map
          (TopologicalAbelianization.mk π₁ᵉᵗ(Y.genericExtensionMorphism Ω)) := by
  intro hpoint ψ
  have hsX : Function.Surjective (algebraMap F X.functionField) := by
    rw [hfieldX]
    exact jX.functionFieldRingEquivOfIsOpenImmersion.surjective.comp M.ffEquiv.surjective
  have hsY : Function.Surjective (algebraMap F Y.functionField) := by
    rw [hfieldY]
    exact jY.functionFieldRingEquivOfIsOpenImmersion.surjective.comp M.ffEquiv.surjective
  have hI := genericPlaceInertia_pointed_sameField_image X Y f hpoint hsX hsY p Q
  refine ⟨hI, ?_⟩
  let IX : Subgroup π₁ᵉᵗ(X.genericExtensionMorphism Ω) := genericPlaceInertia X p Q
  let IY : Subgroup π₁ᵉᵗ(Y.genericExtensionMorphism Ω) := genericPlaceInertia Y p Q
  have hIX : IX.map ψ.toMonoidHom = IY := hI
  change (IX.map (TopologicalAbelianization.mk π₁ᵉᵗ(X.genericExtensionMorphism Ω))).map
    (TopologicalAbelianization.map ψ).toMonoidHom =
      IY.map (TopologicalAbelianization.mk π₁ᵉᵗ(Y.genericExtensionMorphism Ω))
  calc
    _ = IX.map ((TopologicalAbelianization.map ψ).toMonoidHom.comp
        (TopologicalAbelianization.mk π₁ᵉᵗ(X.genericExtensionMorphism Ω))) :=
      Subgroup.map_map _ _ _
    _ = IX.map ((TopologicalAbelianization.mk π₁ᵉᵗ(Y.genericExtensionMorphism Ω)).comp
        ψ.toMonoidHom) :=
      congrArg (fun q => IX.map q) (TopologicalAbelianization.map_comp_mk ψ)
    _ = (IX.map ψ.toMonoidHom).map
        (TopologicalAbelianization.mk π₁ᵉᵗ(Y.genericExtensionMorphism Ω)) :=
      (Subgroup.map_map _ _ _).symm
    _ = IY.map (TopologicalAbelianization.mk π₁ᵉᵗ(Y.genericExtensionMorphism Ω)) :=
      congrArg (fun J : Subgroup π₁ᵉᵗ(Y.genericExtensionMorphism Ω) =>
        J.map (TopologicalAbelianization.mk π₁ᵉᵗ(Y.genericExtensionMorphism Ω))) hIX

end AnabelianGeometry.WeightFiltration
