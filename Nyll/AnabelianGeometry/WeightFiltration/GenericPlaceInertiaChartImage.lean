/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/
import Nyll.EtaleFundamentalGroups.Inertia.GenericPlaceInertiaHom
import Nyll.EtaleFundamentalGroups.GeometricFiber.FieldSourceGaloisNaturality
import Nyll.EtaleFundamentalGroups.GeometricFiber.CanonicalPointedMaps

/-! # Original place inertia in the prescribed field chart -/

noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.PreGaloisCategory AlgebraicCurve
open AlgebraicGeometry.FiniteEtale SchemeTheory EtaleFundamentalGroups.Inertia

namespace AnabelianGeometry.WeightFiltration
attribute [local instance] normalizationCommAlgGaloisAction

private theorem pointedHom_equality_conjugation
    {X Y : Scheme} {Ω : Type} [Field Ω]
    (f : Y ⟶ X) (y : Spec (.of Ω) ⟶ Y) (x : Spec (.of Ω) ⟶ X)
    (h : y ≫ f = x) (a : π₁ᵉᵗ(y)) :
    pointedFundamentalGroupHom f y x h a =
      continuousConjAut (eqToIso (congrArg fiber h)) (fundamentalGroupHom f y a) := by
  subst x
  rfl

/-- The same original place inertia, expressed at a prescribed field chart.
The point equality is retained explicitly; no arbitrary base-point conjugator
or inertia-identification assumption is introduced. -/
theorem genericPlaceInertia_pointed_chart_image
    {k F : Type} [Field k] [Field F] [Algebra k F]
    (Y : Scheme) [IsIntegral Y] [Algebra F Y.functionField]
    {Ω : Type} [Field Ω] [Algebra Y.functionField Ω] [Algebra F Ω]
    [IsScalarTower F Y.functionField Ω]
    [IsSepClosed Ω] [IsSepClosure Y.functionField Ω] [IsSepClosure F Ω]
    (p : Place k F) [Algebra p.toValuationSubring Ω]
    [IsScalarTower p.toValuationSubring F Ω]
    (Q : Ideal (normalizationCommAlgCat p.toValuationSubring Ω))
    (hsurj : Function.Surjective (algebraMap F Y.functionField))
    (jF : Spec (.of F) ⟶ Y)
    (hpoint : (ξ Y.functionField Ω ≫ Y.fromSpecStalk (genericPoint Y)) ≫ 𝟙 Y =
      ξ F Ω ≫ jF) :
    let xi := ξ Y.functionField Ω ≫ Y.fromSpecStalk (genericPoint Y)
    let i := (pointedFundamentalGroupHom (𝟙 Y) xi (ξ F Ω ≫ jF) hpoint).toMonoidHom
    (genericPlaceInertia Y p Q).map i =
      (Q.inertia Gal(Ω/F)).map (fieldSourceAbsoluteGaloisHom F Ω jF).toMonoidHom := by
  intro xi i
  let e := AlgEquiv.extendScalarsHomOfSurjective (A := Ω) hsurj
  have hval (τ : (actualNormalizationInertiaGroup p.toValuationSubring F Ω Q).carrier) :
      i (genericPlaceInertiaHom Y p Q hsurj τ) =
        fieldSourceAbsoluteGaloisHom F Ω jF τ.val := by
    have h := fieldSourceAbsoluteGaloisHom_naturality F Y.functionField Ω
      (𝟙 Y) (Y.fromSpecStalk (genericPoint Y)) jF hpoint (e τ.val)
    have he : (e τ.val).restrictScalars F = τ.val := by
      apply AlgEquiv.ext
      intro z
      rfl
    rw [he] at h
    change pointedFundamentalGroupHom (𝟙 Y) xi (ξ F Ω ≫ jF) hpoint
      (genericPlaceInertiaHom Y p Q hsurj τ) = _
    rw [pointedHom_equality_conjugation]
    exact h
  rw [← genericPlaceInertiaHom_range Y p Q hsurj]
  apply Subgroup.ext
  intro z
  constructor
  · rintro ⟨w, ⟨τ, rfl⟩, rfl⟩
    exact ⟨τ.val, τ.property, (hval τ).symm⟩
  · rintro ⟨σ, hσ, rfl⟩
    let τ : (actualNormalizationInertiaGroup p.toValuationSubring F Ω Q).carrier := ⟨σ, hσ⟩
    exact ⟨genericPlaceInertiaHom Y p Q hsurj τ, ⟨τ, rfl⟩, hval τ⟩

end AnabelianGeometry.WeightFiltration
