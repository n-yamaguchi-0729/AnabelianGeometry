/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/
import Nyll.SchemeTheory.FunctionFields.OpenChartGenericPoints
import Nyll.AlgebraicCurves.Models.Charts.OpenChartGenericPoints
import Nyll.SchemeTheory.ProjectiveSpace.ProjectiveLineRatFuncBaseChange
import Nyll.AlgebraicCurves.Models.Rational.PuncturedProjectiveLineBoundaryPlaces

/-! # The actual arithmetic and geometric generic points of punctured P1

The source objects are the original finite-configuration open and its literal
pullback. All three point equalities needed by ActualRationalCuspRecognition
are constructed from the actual function-field coordinates. No point equality
or new field-map naturality equation is an input.
-/

noncomputable section
open CategoryTheory AlgebraicGeometry AlgebraicCurve TopologicalSpace
open scoped RatFunc

namespace AlgebraicGeometry.ProjSpace

attribute [local instance] MvPolynomial.gradedAlgebra Polynomial.algebra

local instance (priority := 2000) genericPointsSMulRatFunc
    {A E : Type*} [CommSemiring A] [Field E]
    [Algebra A (RatFunc E)] : SMul A (RatFunc E) :=
  (inferInstance : Algebra A (RatFunc E)).toSMul

local instance genericPoints_projectiveLine_integral (F : Type) [Field F] :
    IsIntegral (projectiveLineScheme F) := projectiveSpace_isIntegral F 1

local instance genericPoints_configurationOpen_nonempty (k : Type) [Field k] [Infinite k]
    (s : Finset (Projectivization k (k × k))) :
    Nonempty (rationalConfigurationOpen s : Scheme) :=
  rationalConfigurationOpen_nonempty k s

local instance genericPoints_configurationOpen_integral (k : Type) [Field k] [Infinite k]
    (s : Finset (Projectivization k (k × k))) :
    IsIntegral (rationalConfigurationOpen s : Scheme) :=
  isIntegral_of_isOpenImmersion (rationalConfigurationOpen s).ι

local instance genericPoints_configurationBaseChange_nonempty (k κ : Type)
    [Field k] [Field κ] [Algebra k κ] [Infinite k]
    (s : Finset (Projectivization k (k × k))) :
    Nonempty (Limits.pullback (Spec.map (CommRingCat.ofHom (algebraMap k κ)))
      ((rationalConfigurationOpen s).ι ≫ π k 1) : Scheme) :=
  rationalConfigurationBaseChange_nonempty k κ s

local instance genericPoints_configurationBaseChange_integral (k κ : Type)
    [Field k] [Field κ] [Algebra k κ] [Infinite k]
    (s : Finset (Projectivization k (k × k))) :
    IsIntegral (Limits.pullback (Spec.map (CommRingCat.ofHom (algebraMap k κ)))
      ((rationalConfigurationOpen s).ι ≫ π k 1) : Scheme) :=
  isIntegral_of_isOpenImmersion (rationalConfigurationBaseChangeChart k κ s)

variable (k κ : Type) [Field k] [Field κ] [Algebra k κ] [Infinite k]

/-- The arithmetic coordinate of the actual finite-configuration open. -/
def rationalConfigurationArithmeticFunctionFieldEquiv
    (s : Finset (Projectivization k (k × k))) :
    RatFunc k ≃+* (rationalConfigurationOpen s : Scheme).functionField :=
  (projectiveLineRatFuncModel k).ffEquiv.trans
    (rationalConfigurationOpen s).ι.functionFieldRingEquivOfIsOpenImmersion

/-- The geometric coordinate of the literal base-changed open. -/
def rationalConfigurationGeometricFunctionFieldEquiv
    (s : Finset (Projectivization k (k × k))) :
    RatFunc κ ≃+*
      (Limits.pullback (Spec.map (CommRingCat.ofHom (algebraMap k κ)))
        ((rationalConfigurationOpen s).ι ≫ π k 1) : Scheme).functionField :=
  (projectiveLineRatFuncModel κ).ffEquiv.trans
    (rationalConfigurationBaseChangeChart k κ s).functionFieldRingEquivOfIsOpenImmersion

/-- The arithmetic generic point jarith in the actual arithmetic open. -/
def rationalConfigurationArithmeticGenericPoint
    (s : Finset (Projectivization k (k × k))) :
    Spec (.of (RatFunc k)) ⟶ (rationalConfigurationOpen s : Scheme) :=
  Scheme.functionFieldChartPoint _ (rationalConfigurationArithmeticFunctionFieldEquiv k s)

/-- The geometric generic point jgeom in the literal pullback open. -/
def rationalConfigurationGeometricGenericPoint
    (s : Finset (Projectivization k (k × k))) :
    Spec (.of (RatFunc κ)) ⟶
      Limits.pullback (Spec.map (CommRingCat.ofHom (algebraMap k κ)))
        ((rationalConfigurationOpen s).ι ≫ π k 1) :=
  Scheme.functionFieldChartPoint _ (rationalConfigurationGeometricFunctionFieldEquiv k κ s)

/-- The exact hfield equation for the coordinate algebra induced by the actual
geometric open immersion. -/
theorem rationalConfigurationGeometricFunctionFieldEquiv_hfield
    (s : Finset (Projectivization k (k × k))) :
    let U := (Limits.pullback (Spec.map (CommRingCat.ofHom (algebraMap k κ)))
      ((rationalConfigurationOpen s).ι ≫ π k 1) : Scheme)
    letI : Algebra (RatFunc κ) U.functionField :=
      (rationalConfigurationGeometricFunctionFieldEquiv k κ s).toRingHom.toAlgebra
    algebraMap (RatFunc κ) U.functionField =
      ((rationalConfigurationBaseChangeChart k κ s).functionFieldMap
        (rationalConfigurationBaseChangeChart_denseRange k κ s)).comp
          (projectiveLineRatFuncModel κ).ffEquiv.toRingHom := by
  rfl

/-- The exact hchartpoint equation. The RatFunc-to-ambient algebra is
constructed by transport through the actual open-chart coordinate. -/
theorem rationalConfigurationGenericPoint_hchartpoint
    (s : Finset (Projectivization k (k × k)))
    {Ω : Type} [Field Ω]
    [Algebra (Limits.pullback (Spec.map (CommRingCat.ofHom (algebraMap k κ)))
      ((rationalConfigurationOpen s).ι ≫ π k 1) : Scheme).functionField Ω] :
    let U := (Limits.pullback (Spec.map (CommRingCat.ofHom (algebraMap k κ)))
      ((rationalConfigurationOpen s).ι ≫ π k 1) : Scheme)
    let E := rationalConfigurationGeometricFunctionFieldEquiv k κ s
    letI : Algebra (RatFunc κ) U.functionField := E.toRingHom.toAlgebra
    letI : Algebra (RatFunc κ) Ω :=
      ((algebraMap U.functionField Ω).comp E.toRingHom).toAlgebra
    U.genericExtensionMorphism Ω ≫ 𝟙 U =
      Spec.map (CommRingCat.ofHom (algebraMap (RatFunc κ) Ω)) ≫
        rationalConfigurationGeometricGenericPoint k κ s := by
  exact Scheme.functionFieldChartPoint_hchartpoint _
    (rationalConfigurationGeometricFunctionFieldEquiv k κ s)

/-- The hchartpoint equation with the already constructed coordinate/ambient
algebras, retaining only the same hfield used by the recognition theorem. -/
theorem rationalConfigurationGenericPoint_hchartpoint_of_hfield
    (s : Finset (Projectivization k (k × k)))
    {Ω : Type} [Field Ω]
    [Algebra (RatFunc κ)
      (Limits.pullback (Spec.map (CommRingCat.ofHom (algebraMap k κ)))
        ((rationalConfigurationOpen s).ι ≫ π k 1) : Scheme).functionField]
    [Algebra (Limits.pullback (Spec.map (CommRingCat.ofHom (algebraMap k κ)))
      ((rationalConfigurationOpen s).ι ≫ π k 1) : Scheme).functionField Ω]
    [Algebra (RatFunc κ) Ω]
    [IsScalarTower (RatFunc κ)
      (Limits.pullback (Spec.map (CommRingCat.ofHom (algebraMap k κ)))
        ((rationalConfigurationOpen s).ι ≫ π k 1) : Scheme).functionField Ω]
    (hfield : algebraMap (RatFunc κ)
        (Limits.pullback (Spec.map (CommRingCat.ofHom (algebraMap k κ)))
          ((rationalConfigurationOpen s).ι ≫ π k 1) : Scheme).functionField =
      ((rationalConfigurationBaseChangeChart k κ s).functionFieldMap
        (rationalConfigurationBaseChangeChart_denseRange k κ s)).comp
          (projectiveLineRatFuncModel κ).ffEquiv.toRingHom) :
    (Limits.pullback (Spec.map (CommRingCat.ofHom (algebraMap k κ)))
        ((rationalConfigurationOpen s).ι ≫ π k 1) : Scheme).genericExtensionMorphism Ω ≫
        𝟙 (Limits.pullback (Spec.map (CommRingCat.ofHom (algebraMap k κ)))
          ((rationalConfigurationOpen s).ι ≫ π k 1)) =
      Spec.map (CommRingCat.ofHom (algebraMap (RatFunc κ) Ω)) ≫
        rationalConfigurationGeometricGenericPoint k κ s := by
  exact Scheme.functionFieldChartPoint_hchartpoint_of_hfield _
    (rationalConfigurationGeometricFunctionFieldEquiv k κ s) hfield

/-- The exact hpoint equation, derived from the actual proper coefficient map
and the actual base-changed open square. -/
theorem rationalConfigurationGenericPoint_hpoint
    (s : Finset (Projectivization k (k × k)))
    {Ω : Type} [Field Ω] [Algebra (RatFunc κ) Ω] [Algebra (RatFunc k) Ω]
    [IsScalarTower (RatFunc k) (RatFunc κ) Ω] :
    (Spec.map (CommRingCat.ofHom (algebraMap (RatFunc κ) Ω)) ≫
        rationalConfigurationGeometricGenericPoint k κ s) ≫
      Limits.pullback.snd (Spec.map (CommRingCat.ofHom (algebraMap k κ)))
        ((rationalConfigurationOpen s).ι ≫ π k 1) =
      Spec.map (CommRingCat.ofHom (algebraMap (RatFunc k) Ω)) ≫
        rationalConfigurationArithmeticGenericPoint k s := by
  let i : (rationalConfigurationOpen s : Scheme) ⟶ (projectiveLineRatFuncModel k).C :=
    (rationalConfigurationOpen s).ι
  let : IsOpenImmersion i :=
    inferInstanceAs (IsOpenImmersion (rationalConfigurationOpen s).ι)
  let j : (Limits.pullback (Spec.map (CommRingCat.ofHom (algebraMap k κ)))
      ((rationalConfigurationOpen s).ι ≫ π k 1) : Scheme) ⟶
        (projectiveLineRatFuncModel κ).C := rationalConfigurationBaseChangeChart k κ s
  let : IsOpenImmersion j :=
    inferInstanceAs (IsOpenImmersion (rationalConfigurationBaseChangeChart k κ s))
  exact Scheme.functionFieldChartPoint_ambient_openSquare
    (projectiveLineRatFuncModel k).ffEquiv (projectiveLineRatFuncModel κ).ffEquiv
    i j
    (map k κ 1) (projectiveLineMap_denseRange k κ)
    (Limits.pullback.snd (Spec.map (CommRingCat.ofHom (algebraMap k κ)))
      ((rationalConfigurationOpen s).ι ≫ π k 1))
    (rationalConfigurationBaseChangeChart_comp_map k κ s)
    (projectiveLineRatFuncEquiv_coefficientMap k κ)

/-- The exact hbasearith equation, derived from the proper model's structural
coefficient compatibility. -/
theorem rationalConfigurationGenericPoint_hbasearith
    (s : Finset (Projectivization k (k × k)))
    {Ω : Type} [Field Ω] [Algebra (RatFunc k) Ω] [Algebra k Ω]
    [IsScalarTower k (RatFunc k) Ω] :
    (Spec.map (CommRingCat.ofHom (algebraMap (RatFunc k) Ω)) ≫
        rationalConfigurationArithmeticGenericPoint k s) ≫
      ((rationalConfigurationOpen s).ι ≫ π k 1) =
        Spec.map (CommRingCat.ofHom (algebraMap k Ω)) := by
  let i : (rationalConfigurationOpen s : Scheme) ⟶ (projectiveLineRatFuncModel k).C :=
    (rationalConfigurationOpen s).ι
  let : IsOpenImmersion i :=
    inferInstanceAs (IsOpenImmersion (rationalConfigurationOpen s).ι)
  exact CurveModel.functionFieldChartPoint_open_ambient_comp_toBase
    (projectiveLineRatFuncModel k) i

end AlgebraicGeometry.ProjSpace
