/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.AlgebraicCurves.Divisors.Correspondences.Correspondences
public import Nyll.AlgebraicCurves.Divisors.Maps.Maps
public import Nyll.AlgebraicCurves.FunctionFields.Transcendence.CurveOver
public import Nyll.AlgebraicCurves.Geometry.FundamentalIdentityAlong
public import Nyll.AlgebraicCurves.Models.Construction.Basic
public import Nyll.AlgebraicCurves.Models.Construction.CurveIsIntegral
public import Nyll.AlgebraicCurves.Models.Construction.LiteralArithmeticCurveModel
public import Nyll.AlgebraicCurves.Models.Ramification.RamificationIndexPointPlaceEqOne
public import Nyll.AlgebraicCurves.Models.Sections.RationalSectionBoundaryPlace
public import Nyll.AlgebraicCurves.Places.Restriction.RestrictEqMem
public import Nyll.EtaleFundamentalGroups.FiniteEtale.FunctionField
public import Nyll.EtaleFundamentalGroups.FiniteEtale.Integral
public import Nyll.SchemeTheory.FunctionFields.GenericFieldSourceNaturality
public import Nyll.SchemeTheory.FunctionFields.ScalarFunctoriality
public import Mathlib.AlgebraicGeometry.Morphisms.FormallyUnramified
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.FieldTheory.Separable
public import Mathlib.LinearAlgebra.Dimension.Finrank
public import Mathlib.RingTheory.Finiteness.Basic

/-!
# The literal model and divisor degree of a finite étale cover

A connected finite étale cover remains the original scheme, with its own
function field and structural map. Its field embedding is the canonical
function-field pullback composed with the specified field coordinate of
the base model. Finiteness, separability and the divisor degree multiplier
are proved for this same embedding, in every characteristic.
-/

@[expose] public section

universe w

noncomputable section

universe u v

open AlgebraicGeometry CategoryTheory
open CategoryTheory.PreGaloisCategory EtaleFundamentalGroups

namespace AlgebraicCurve.CurveModel

attribute [local instance] CurveModel.isIntegral CurveModel.isProper CurveModel.smooth

variable {K : Type u} [Field K] {F : Type v} [Field F] [Algebra K F]
  (M : CurveModel K F) [IsNormalIntegral M.C]
  (Y : FiniteEtale M.C) [IsConnected Y]

/-- The cover itself is a smooth proper curve model of its actual
function field. No replacement scheme or function-field isomorphism is chosen. -/
def finiteEtaleModel :
    let _ : IsIntegral Y.left := isIntegral_left_of_isConnected_finiteEtale Y
    let _ : Algebra K Y.left.functionField :=
      (baseToFunctionField ((show Y.left ⟶ M.C from Y.hom) ≫ M.toBase)).toAlgebra
    CurveModel K Y.left.functionField := by
  intro hY algKY
  have : IsFiniteEtale (show Y.left ⟶ M.C from Y.hom) := Y.prop
  have : IsProper ((show Y.left ⟶ M.C from Y.hom) ≫ M.toBase) := inferInstance
  have : SmoothOfRelativeDimension 1 ((show Y.left ⟶ M.C from Y.hom) ≫ M.toBase) :=
    smoothOfRelativeDimension_comp 0 1 (show Y.left ⟶ M.C from Y.hom) M.toBase
  exact literalCurveModel ((show Y.left ⟶ M.C from Y.hom) ≫ M.toBase)

/-- The original base-model field coordinate followed by the actual
map of function fields, with its original ground-field algebra structure. -/
def finiteEtaleModelFieldMap :
    let _ : IsIntegral Y.left := isIntegral_left_of_isConnected_finiteEtale Y
    let _ : Algebra K Y.left.functionField :=
      (baseToFunctionField ((show Y.left ⟶ M.C from Y.hom) ≫ M.toBase)).toAlgebra
    F →ₐ[K] Y.left.functionField := by
  intro hY algKY
  let _ : Algebra K M.C.functionField := M.functionFieldAlgebra
  exact (Scheme.Hom.functionFieldAlgHomOver M.toBase (show Y.left ⟶ M.C from Y.hom)
    (finiteEtale_hom_denseRange_of_isConnected Y)).comp M.ffAlgEquiv.toAlgHom

/-- The field map evaluates through the canonical generic-point pullback. -/
theorem finiteEtaleModelFieldMap_apply :
    let _ : IsIntegral Y.left := isIntegral_left_of_isConnected_finiteEtale Y
    let _ : Algebra K Y.left.functionField :=
      (baseToFunctionField ((show Y.left ⟶ M.C from Y.hom) ≫ M.toBase)).toAlgebra
    ∀ a : F, M.finiteEtaleModelFieldMap Y a =
      (show Y.left ⟶ M.C from Y.hom).functionFieldMap
        (finiteEtale_hom_denseRange_of_isConnected Y) (M.ffEquiv a) := by
  intro hY algKY a
  rfl

/-- The specified field embedding is finite separable, and its degree
is exactly the degree of the canonical extension of scheme function fields. -/
theorem finiteEtaleModelFieldMap_properties :
    let _ : IsIntegral Y.left := isIntegral_left_of_isConnected_finiteEtale Y
    let _ : Algebra K Y.left.functionField :=
      (baseToFunctionField ((show Y.left ⟶ M.C from Y.hom) ≫ M.toBase)).toAlgebra
    let φ := M.finiteEtaleModelFieldMap Y
    FiniteAlong K φ ∧ SeparableAlong K φ ∧
      finrankAlong K φ =
        (let _ : Algebra M.C.functionField Y.left.functionField := finiteEtaleFunctionFieldAlgebra Y
         Module.finrank M.C.functionField Y.left.functionField) := by
  intro hY algKY φ
  let _ : Algebra F Y.left.functionField := algebraAlong φ
  let _ : Algebra M.C.functionField Y.left.functionField := finiteEtaleFunctionFieldAlgebra Y
  have hfinite : FiniteDimensional M.C.functionField Y.left.functionField :=
    finiteDimensional_functionField_of_finiteEtale_isConnected Y
  have hsep : Algebra.IsSeparable M.C.functionField Y.left.functionField :=
    isSeparable_functionField_of_finiteEtale_isConnected Y
  have hforward : (algebraMap M.C.functionField Y.left.functionField).comp M.ffEquiv.toRingHom =
      (RingEquiv.refl Y.left.functionField).toRingHom.comp
        (algebraMap F Y.left.functionField) := by
    ext a
    rfl
  have hback : (algebraMap F Y.left.functionField).comp M.ffEquiv.symm.toRingHom =
      (RingEquiv.refl Y.left.functionField).toRingHom.comp
        (algebraMap M.C.functionField Y.left.functionField) := by
    ext a
    change (show Y.left ⟶ M.C from Y.hom).functionFieldMap
        (finiteEtale_hom_denseRange_of_isConnected Y)
        (M.ffEquiv (M.ffEquiv.symm a)) =
      (show Y.left ⟶ M.C from Y.hom).functionFieldMap
        (finiteEtale_hom_denseRange_of_isConnected Y) a
    rw [M.ffEquiv.apply_symm_apply]
  exact ⟨Module.Finite.of_equiv_equiv M.ffEquiv.symm (RingEquiv.refl _) hback,
    Algebra.IsSeparable.of_equiv_equiv M.ffEquiv.symm (RingEquiv.refl _) hback,
    Algebra.finrank_eq_of_equiv_equiv M.ffEquiv (RingEquiv.refl _) hforward⟩

/-- Actual divisor pullback through the cover multiplies degree by the
canonical function-field extension degree. The required principal-divisor
and fundamental-identity properties come from the same literal curve model. -/
theorem degree_finiteEtaleModel_pullback [PerfectField K] :
    let _ : IsIntegral Y.left := isIntegral_left_of_isConnected_finiteEtale Y
    let _ : Algebra K Y.left.functionField :=
      (baseToFunctionField ((show Y.left ⟶ M.C from Y.hom) ≫ M.toBase)).toAlgebra
    let φ := M.finiteEtaleModelFieldMap Y
    let _ : Algebra F Y.left.functionField := algebraAlong φ
    let _ : IsScalarTower K F Y.left.functionField := isScalarTower_along φ
    let _ : FiniteDimensional F Y.left.functionField :=
      (M.finiteEtaleModelFieldMap_properties Y).1
    let _ : Algebra.IsIntegral F Y.left.functionField := Algebra.IsIntegral.of_finite F _
    let _ : HasPrincipalDivisors K Y.left.functionField :=
      (isCurveOver_of_isIntegral_of_smoothOfRelativeDimension_one
        (M.finiteEtaleModel Y).toBase (M.finiteEtaleModel Y).ffEquiv
          (M.finiteEtaleModel Y).ffEquiv_algebraMap).toHasPrincipalDivisors
    ∀ D : Divisor K F, Divisor.degree (Divisor.pullback Y.left.functionField D) =
      ((let _ : Algebra M.C.functionField Y.left.functionField := finiteEtaleFunctionFieldAlgebra Y
        Module.finrank M.C.functionField Y.left.functionField) : ℤ) * Divisor.degree D := by
  intro hY algKY φ algFY hTower hFinite hIntegral hPrincipal D
  have hsep : Algebra.IsSeparable F Y.left.functionField :=
    (M.finiteEtaleModelFieldMap_properties Y).2.1
  have hφ : φ.toRingHom.IsIntegral := fun a => Algebra.IsIntegral.isIntegral a
  have hfundamental : FundamentalIdentity K F Y.left.functionField :=
    fundamentalIdentityAlong φ hφ hFinite hsep
  rw [Divisor.degree_pullback]
  have hdegree := (M.finiteEtaleModelFieldMap_properties Y).2.2
  change Module.finrank F Y.left.functionField = _ at hdegree
  rw [hdegree]

/-- The place of an original closed point upstairs restricts to the
place of its image under the cover. This uses the original stalk map,
with the same field embedding as the degree formula. -/
theorem restrict_placeOfPoint_finiteEtaleModel
    {K₀ F₀ : Type w} [Field K₀] [Field F₀] [Algebra K₀ F₀]
    (M₀ : CurveModel K₀ F₀) [IsNormalIntegral M₀.C]
    (Y₀ : FiniteEtale M₀.C) [IsConnected Y₀] :
    let _ : IsIntegral Y₀.left := isIntegral_left_of_isConnected_finiteEtale Y₀
    let _ : Algebra K₀ Y₀.left.functionField :=
      (baseToFunctionField ((show Y₀.left ⟶ M₀.C from Y₀.hom) ≫ M₀.toBase)).toAlgebra
    let φ := M₀.finiteEtaleModelFieldMap Y₀
    let _ : Algebra F₀ Y₀.left.functionField := algebraAlong φ
    let _ : IsScalarTower K₀ F₀ Y₀.left.functionField := isScalarTower_along φ
    let _ : FiniteDimensional F₀ Y₀.left.functionField :=
      (M₀.finiteEtaleModelFieldMap_properties Y₀).1
    let _ : Algebra.IsIntegral F₀ Y₀.left.functionField := Algebra.IsIntegral.of_finite F₀ _
    ∀ (y : closedPoints Y₀.left)
      (hy : IsClosed ({(show Y₀.left ⟶ M₀.C from Y₀.hom) y.val} : Set M₀.C)),
      ((M₀.finiteEtaleModel Y₀).placeOfPoint y).restrict F₀ =
        M₀.placeOfPoint ⟨(show Y₀.left ⟶ M₀.C from Y₀.hom) y.val, hy⟩ := by
  intro hY algKY φ algFY hTower hFinite hIntegral y hy
  have hfield : ∀ z : F₀,
      (show Y₀.left ⟶ M₀.C from Y₀.hom).functionFieldMap
          (finiteEtale_hom_denseRange_of_isConnected Y₀)
          (M₀.ffEquiv z) =
        (M₀.finiteEtaleModel Y₀).ffEquiv (algebraMap F₀ Y₀.left.functionField z) := by
    intro z
    exact (M₀.finiteEtaleModelFieldMap_apply Y₀ z).symm
  have hle := M₀.placeOfPoint_le_comap_of_functionFieldMap
    (M₀.finiteEtaleModel Y₀) (show Y₀.left ⟶ M₀.C from Y₀.hom)
    (finiteEtale_hom_denseRange_of_isConnected Y₀) hfield y hy
  exact Place.restrict_eq_of_forall_mem _ _ (fun z hz => hle hz)

/-- Every place is unramified for the canonical field embedding of the
original finite étale cover. The generic-point comparison is supplied by
the actual function-field map. -/
theorem ramificationIndex_finiteEtaleModelFieldMap
    {K₀ F₀ : Type w} [Field K₀] [IsAlgClosed K₀] [Field F₀] [Algebra K₀ F₀]
    (M₀ : CurveModel K₀ F₀) [IsNormalIntegral M₀.C]
    (Y₀ : FiniteEtale M₀.C) [IsConnected Y₀] :
    let _ : IsIntegral Y₀.left := isIntegral_left_of_isConnected_finiteEtale Y₀
    let _ : Algebra K₀ Y₀.left.functionField :=
      (baseToFunctionField ((show Y₀.left ⟶ M₀.C from Y₀.hom) ≫ M₀.toBase)).toAlgebra
    ∀ w : Place K₀ Y₀.left.functionField,
      Place.ramificationIndexAlong (M₀.finiteEtaleModelFieldMap Y₀) w = 1 := by
  intro hY algKY w
  let N := M₀.finiteEtaleModel Y₀
  let φ := M₀.finiteEtaleModelFieldMap Y₀
  let _ : Algebra F₀ Y₀.left.functionField := algebraAlong φ
  have : FiniteDimensional F₀ Y₀.left.functionField :=
    (M₀.finiteEtaleModelFieldMap_properties Y₀).1
  have : Algebra.IsIntegral F₀ Y₀.left.functionField := Algebra.IsIntegral.of_finite F₀ _
  have hφ : φ.toRingHom.IsIntegral := fun a => Algebra.IsIntegral.isIntegral (R := F₀) a
  have : IsFiniteEtale (show Y₀.left ⟶ M₀.C from Y₀.hom) := Y₀.prop
  have heq : N.ffEquiv.toRingHom.comp (φ.toRingHom.comp M₀.ffEquiv.symm.toRingHom) =
      (show Y₀.left ⟶ M₀.C from Y₀.hom).functionFieldMap
          (finiteEtale_hom_denseRange_of_isConnected Y₀) := by
    ext z
    change (show Y₀.left ⟶ M₀.C from Y₀.hom).functionFieldMap
      (finiteEtale_hom_denseRange_of_isConnected Y₀)
      (M₀.ffEquiv (M₀.ffEquiv.symm z)) = _
    exact congrArg
      ((show Y₀.left ⟶ M₀.C from Y₀.hom).functionFieldMap
        (finiteEtale_hom_denseRange_of_isConnected Y₀))
      (M₀.ffEquiv.apply_symm_apply z)
  have hgen : N.C.fromSpecStalk (genericPoint N.C) ≫ (show Y₀.left ⟶ M₀.C from Y₀.hom) =
      Spec.map (CommRingCat.ofHom (N.ffEquiv.toRingHom.comp
        (φ.toRingHom.comp M₀.ffEquiv.symm.toRingHom))) ≫
          M₀.C.fromSpecStalk (genericPoint M₀.C) := by
    rw [heq]
    exact (Spec_functionFieldMap_fromSpecStalk (show Y₀.left ⟶ M₀.C from Y₀.hom)
      (finiteEtale_hom_denseRange_of_isConnected Y₀)).symm
  have htop : FormallyUnramified
      ((⊤ : Y₀.left.Opens).ι ≫ (show Y₀.left ⟶ M₀.C from Y₀.hom)) :=
    MorphismProperty.comp_mem (@FormallyUnramified) _ _
      (inferInstanceAs (FormallyUnramified (⊤ : Y₀.left.Opens).ι))
      (inferInstanceAs (FormallyUnramified (show Y₀.left ⟶ M₀.C from Y₀.hom)))
  have h := CurveModel.ramificationIndexAlong_pointEquivPlace_eq_one_of_formallyUnramified
    N M₀ φ hφ (show Y₀.left ⟶ M₀.C from Y₀.hom) rfl hgen
      (N.pointEquivPlace.symm w) ⊤ trivial htop
  simpa only [N.pointEquivPlace.apply_symm_apply] using h

end AlgebraicCurve.CurveModel
