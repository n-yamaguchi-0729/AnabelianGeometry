/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.EtaleFundamentalGroups.Inertia.AbsoluteDivisorialFiniteQuotientCompatibility
import Nyll.EtaleFundamentalGroups.Inertia.GenericPlaceInertiaHom

/-!
# The same generic Galois map in the place-inertia and finite-cover constructions

Equality transport removes the redundant identity map of the function field.
No new geometric base point or conjugating element is selected.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.PreGaloisCategory
open AlgebraicGeometry.FiniteEtale AlgebraicCurve SchemeTheory

namespace EtaleFundamentalGroups.Inertia

universe u

private theorem symm_eqToIso_of_eq
    {C : Type*} [Category C] {X Y : C} (p : Y = X) (q : X = Y) :
    (eqToIso p).symm = eqToIso q := by
  cases q
  rfl

private theorem fundamentalGroupHom_eqToIso_congr
    {S T : Scheme.{u}}
    {Ω : Type u} [Field Ω] [IsSepClosed Ω]
    (f g : S ⟶ T) (h : f = g)
    (x : Spec (.of Ω) ⟶ S) (a : π₁ᵉᵗ(x)) :
    (eqToIso (congrArg fiber
      (congrArg (fun q : S ⟶ T => x ≫ q) h))).conjAut
        (fundamentalGroupHom f x a) =
      fundamentalGroupHom g x a := by
  subst g
  apply Iso.ext
  change 𝟙 _ ≫ (fundamentalGroupHom f x a).hom ≫ 𝟙 _ =
    (fundamentalGroupHom f x a).hom
  simp only [Category.id_comp, Category.comp_id]

private theorem absoluteGaloisToFiberAutMulEquiv_eq_toAut
    (K Ω : Type u) [Field K] [Field Ω] [Algebra K Ω]
    [IsSepClosure K Ω] [IsSepClosed Ω] (σ : Gal(Ω/K)) :
    absoluteGaloisToFiberAutMulEquiv K Ω (IsSepClosure.sep_closed K) σ =
      toAut (fib K Ω) Gal(Ω/K) σ := by
  rw [absoluteGaloisToFiberAutMulEquiv, toAutMulEquiv_apply]

private theorem fieldSourceAbsoluteGaloisHom_apply_toAut
    (K Ω : Type u) [Field K] [Field Ω] [Algebra K Ω]
    [IsSepClosure K Ω] [IsSepClosed Ω]
    {U : Scheme.{u}} [IsIntegral U] (j : Spec (.of K) ⟶ U)
    (σ : Gal(Ω/K)) :
    fieldSourceAbsoluteGaloisHom K Ω j σ =
      fundamentalGroupHom j (ξ K Ω) (toAut (fib K Ω) Gal(Ω/K) σ) := by
  change fundamentalGroupHom j (ξ K Ω) (toAutHomeo (fib K Ω) Gal(Ω/K) σ) = _
  rw [toAutHomeo_apply]

/-- The two existing constructions are literally the same generic Galois map. -/
theorem absoluteGenericGaloisToFundamentalGroup_eq_fieldSourceAbsoluteGaloisHom
    (U : Scheme.{u}) [IsIntegral U]
    (Ω : Type u) [Field Ω] [Algebra U.functionField Ω]
    [IsSepClosure U.functionField Ω] [IsSepClosed Ω] :
    absoluteGenericGaloisToFundamentalGroup U Ω =
      (fieldSourceAbsoluteGaloisHom U.functionField Ω
        (U.fromSpecStalk (genericPoint U))).toMonoidHom := by
  apply MonoidHom.ext
  intro σ
  have hgen : U.genericExtensionMorphism U.functionField =
      U.fromSpecStalk (genericPoint U) := by
    simp [Scheme.genericExtensionMorphism]
  have hiso : absoluteGenericFiberIso U Ω =
      eqToIso (congrArg fiber
        (congrArg (fun q : Spec (.of U.functionField) ⟶ U =>
          ξ U.functionField Ω ≫ q) hgen)) := by
    exact symm_eqToIso_of_eq _ _
  rw [absoluteGenericGaloisToFundamentalGroup_apply,
    absoluteGaloisToFiberAutMulEquiv_eq_toAut, hiso]
  change _ = fieldSourceAbsoluteGaloisHom U.functionField Ω
    (U.fromSpecStalk (genericPoint U)) σ
  rw [fieldSourceAbsoluteGaloisHom_apply_toAut]
  exact fundamentalGroupHom_eqToIso_congr
    (U.genericExtensionMorphism U.functionField)
    (U.fromSpecStalk (genericPoint U)) hgen (ξ U.functionField Ω)
    (toAut (fib U.functionField Ω) Gal(Ω/U.functionField) σ)

end EtaleFundamentalGroups.Inertia

namespace AnabelianGeometry.WeightFiltration

open EtaleFundamentalGroups.Inertia

/-- For the literal function field, the actual place-inertia map is the
restriction of the same absolute generic Galois map. -/
theorem genericPlaceInertiaHom_eq_absoluteGenericGalois
    {k : Type} [Field k] (U : Scheme) [IsIntegral U]
    [Algebra k U.functionField]
    {Ω : Type} [Field Ω] [Algebra U.functionField Ω]
    [IsSepClosure U.functionField Ω] [IsSepClosed Ω]
    (p : Place k U.functionField) [Algebra p.toValuationSubring Ω]
    [IsScalarTower p.toValuationSubring U.functionField Ω]
    (Q : Ideal (normalizationCommAlgCat p.toValuationSubring Ω))
    (τ : (actualNormalizationInertiaGroup p.toValuationSubring U.functionField Ω Q).carrier) :
    genericPlaceInertiaHom U p Q Function.surjective_id τ =
      absoluteGenericGaloisToFundamentalGroup U Ω
        (actualNormalizationInertiaElement p.toValuationSubring U.functionField Ω Q τ) := by
  rw [absoluteGenericGaloisToFundamentalGroup_eq_fieldSourceAbsoluteGaloisHom]
  have hscalar :
      AlgEquiv.extendScalarsHomOfSurjective
        (R := U.functionField) (S := U.functionField) (A := Ω)
        Function.surjective_id
        (actualNormalizationInertiaElement p.toValuationSubring U.functionField Ω Q τ) =
      actualNormalizationInertiaElement p.toValuationSubring U.functionField Ω Q τ := by
    apply AlgEquiv.ext
    intro a
    rfl
  have h := genericPlaceInertiaHom_apply U p Q Function.surjective_id τ
  change genericPlaceInertiaHom U p Q Function.surjective_id τ =
    fieldSourceAbsoluteGaloisHom U.functionField Ω
      (U.fromSpecStalk (genericPoint U))
      (actualNormalizationInertiaElement p.toValuationSubring U.functionField Ω Q τ)
  rw [fieldSourceAbsoluteGaloisHom_apply_toAut]
  simpa only [hscalar] using h

end AnabelianGeometry.WeightFiltration
