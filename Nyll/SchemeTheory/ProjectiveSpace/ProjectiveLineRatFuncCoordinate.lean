/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Definitions/Def_AlgebraicCurve_CurveModelConstruction.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/
import Nyll.SchemeTheory.ProjectiveSpace.ProjectiveSpaceIntegral
import Nyll.SchemeTheory.ProjectiveSpace.ProjectiveLineSmooth
import Nyll.SchemeTheory.FunctionFields.ScalarFunctoriality
import Nyll.SchemeTheory.FunctionFields.StructureMorphism
import Nyll.SchemeTheory.FunctionFields.OpenImmersion
import Mathlib.Algebra.MvPolynomial.Equiv
import Mathlib.FieldTheory.RatFunc.Basic
import Mathlib.Tactic.FinCases

/-! # The literal projective-line model of RatFunc

Chart 1 has coordinate x0/x1. Its canonical open-immersion function-field map
identifies the actual Proj function field with RatFunc, and the constant map
is proved from the actual structure morphism. Reparametrization preserves
the literal scheme and its structure morphism.

The arithmetic-to-geometric coefficient-extension compatibility of this
coordinate is a separate remaining lemma; it is not asserted here.
-/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry AlgebraicCurve TopologicalSpace
open HomogeneousLocalization
open AlgebraicCurves.Geometry.Projective.Proofs.ProjSpace_isPullback_map.AlgebraicGeometry.ProjSpace

local instance projectiveLineAffineFunctionFieldAlgebra
    (R : Type u) [CommRing R] [IsDomain R] :
    Algebra R (Spec (CommRingCat.of R)).functionField :=
  RingHom.toAlgebra
    ((StructureSheaf.toStalk R
        (show PrimeSpectrum.Top R from genericPoint (Spec (CommRingCat.of R)))) :
      CommRingCat.of R ⟶ (Spec (CommRingCat.of R)).functionField).hom

namespace AlgebraicCurve

/-- The actual structural map on an affine domain agrees with the canonical
map through that domain into its function field. -/
theorem baseToFunctionField_specMap_algebraMap
    {k A : Type u} [Field k] [CommRing A] [IsDomain A] [Algebra k A] (a : k) :
    baseToFunctionField (Spec.map (CommRingCat.ofHom (algebraMap k A))) a =
      algebraMap A (Spec (CommRingCat.of A)).functionField (algebraMap k A a) := by
  change (Spec (CommRingCat.of A)).presheaf.germ ⊤
      (genericPoint (Spec (CommRingCat.of A))) trivial
      ((Spec.map (CommRingCat.ofHom (algebraMap k A))).appTop
        ((Scheme.ΓSpecIso (CommRingCat.of k)).inv a)) = _
  have h : (Spec.map (CommRingCat.ofHom (algebraMap k A))).appTop
      ((Scheme.ΓSpecIso (CommRingCat.of k)).inv a) =
      (Scheme.ΓSpecIso (CommRingCat.of A)).inv (algebraMap k A a) := by
    have hn := congrArg (fun f : CommRingCat.of k ⟶
        Γ(Spec (CommRingCat.of A), ⊤) => f a)
      (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom (algebraMap k A)))
    exact hn.symm
  rw [h]
  rfl

end AlgebraicCurve

namespace AlgebraicGeometry.ProjSpace

attribute [local instance] MvPolynomial.gradedAlgebra

private instance chartOne_unique : Unique {i : Fin 2 // i ≠ 1} where
  default := ⟨0, by decide⟩
  uniq := by
    rintro ⟨i, hi⟩
    apply Subtype.ext
    fin_cases i
    · rfl
    · exact (hi rfl).elim

variable (k : Type u) [Field k]

/-- The chart x1 ≠ 0, with polynomial coordinate x0/x1. -/
def projectiveLinePolynomialChartEquiv :
    Polynomial k ≃ₐ[k] Away (MvPolynomial.homogeneousSubmodule (Fin (1 + 1)) k)
      (MvPolynomial.X (1 : Fin 2) : MvPolynomial (Fin 2) k) :=
  (MvPolynomial.uniqueAlgEquiv k {i : Fin 2 // i ≠ 1}).symm.trans
    (awayChartEquiv (S := k) 1 1)

theorem projectiveLinePolynomialChartEquiv_X :
    projectiveLinePolynomialChartEquiv k Polynomial.X = ratio k 1 1 0 := by
  change awayChartEquiv (S := k) 1 1
    (Polynomial.eval₂ MvPolynomial.C
      (MvPolynomial.X (default : {i : Fin 2 // i ≠ 1})) Polynomial.X) = _
  rw [Polynomial.eval₂_X]
  exact awayChartEquiv_X (S := k) 1 1 ⟨0, by decide⟩

/-- The literal standard affine-line chart into the actual Proj scheme. -/
def projectiveLinePolynomialChart :
    (Spec (CommRingCat.of (Polynomial k)) : Scheme) ⟶
      (Proj (MvPolynomial.homogeneousSubmodule (Fin (1 + 1)) k) : Scheme) :=
  Spec.map (CommRingCat.ofHom (projectiveLinePolynomialChartEquiv k).symm.toRingHom) ≫
    Proj.awayι (MvPolynomial.homogeneousSubmodule (Fin (1 + 1)) k)
      (MvPolynomial.X (1 : Fin 2) : MvPolynomial (Fin 2) k) (X_mem_one k 1 1) one_pos

instance projectiveLinePolynomialChart_isOpenImmersion :
    IsOpenImmersion (projectiveLinePolynomialChart k) := by
  unfold projectiveLinePolynomialChart
  have : IsIso
      (Spec.map (CommRingCat.ofHom (projectiveLinePolynomialChartEquiv k).symm.toRingHom)) :=
    inferInstanceAs (IsIso (Spec.map
      (projectiveLinePolynomialChartEquiv k).symm.toRingEquiv.toCommRingCatIso.hom))
  infer_instance

theorem projectiveLinePolynomialChart_comp_π :
    projectiveLinePolynomialChart k ≫ π k 1 =
      Spec.map (CommRingCat.ofHom (algebraMap k (Polynomial k))) := by
  unfold projectiveLinePolynomialChart
  rw [Category.assoc, awayι_comp_π, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
  apply congrArg (fun f => Spec.map (CommRingCat.ofHom f))
  exact RingHom.ext fun a => (projectiveLinePolynomialChartEquiv k).symm.commutes a

local instance projectiveLine_integral :
    IsIntegral (Proj (MvPolynomial.homogeneousSubmodule (Fin (1 + 1)) k) : Scheme) :=
  projectiveSpace_isIntegral k 1
local instance projectiveLine_smooth : SmoothOfRelativeDimension 1 (π k 1) :=
  projectiveLine_smoothOfRelativeDimension k

/-- The canonical affine function-field localization, supplied by its actual owner. -/
local instance polynomialFunctionField_isFractionRing :
    IsFractionRing (Polynomial k)
      (Spec (CommRingCat.of (Polynomial k)) : Scheme).functionField :=
  AlgebraicGeometry.functionField_isFractionRing_of_affine
    (CommRingCat.of (Polynomial k))

/-- The canonical fraction-field equivalence for the polynomial chart. -/
def polynomialFunctionFieldEquiv :
    RatFunc k ≃ₐ[Polynomial k] (Spec (CommRingCat.of (Polynomial k)) : Scheme).functionField :=
  IsLocalization.algEquiv (nonZeroDivisors (Polynomial k)) (RatFunc k) _

/-- The rational function coordinate transported through the actual chart. -/
def projectiveLineRatFuncEquiv :
    RatFunc k ≃+*
      (Proj (MvPolynomial.homogeneousSubmodule (Fin (1 + 1)) k) : Scheme).functionField :=
  (polynomialFunctionFieldEquiv k).toRingEquiv.trans
    (projectiveLinePolynomialChart k).functionFieldRingEquivOfIsOpenImmersion.symm

/-- This equivalence preserves the actual structural coefficient map. -/
theorem projectiveLineRatFuncEquiv_algebraMap (a : k) :
    projectiveLineRatFuncEquiv k (algebraMap k (RatFunc k) a) =
      baseToFunctionField (π k 1) a := by
  change (projectiveLinePolynomialChart k).functionFieldRingEquivOfIsOpenImmersion.symm
      (polynomialFunctionFieldEquiv k (algebraMap k (RatFunc k) a)) = _
  rw [RingEquiv.symm_apply_eq]
  have hd : DenseRange (projectiveLinePolynomialChart k) :=
    (projectiveLinePolynomialChart k).isOpenEmbedding.isOpenMap.denseRange_of_isPreirreducibleSpace
      (projectiveLinePolynomialChart k)
  have hscalar := Scheme.Hom.functionFieldMap_baseToFunctionField
    (π k 1) (projectiveLinePolynomialChart k) hd a
  change (projectiveLinePolynomialChart k).functionFieldRingEquivOfIsOpenImmersion
      (baseToFunctionField (π k 1) a) =
    baseToFunctionField (projectiveLinePolynomialChart k ≫ π k 1) a at hscalar
  rw [projectiveLinePolynomialChart_comp_π, baseToFunctionField_specMap_algebraMap] at hscalar
  rw [IsScalarTower.algebraMap_apply k (Polynomial k) (RatFunc k) a, AlgEquiv.commutes]
  exact hscalar.symm

/-- The same function-field coordinate as an equivalence over k. -/
def projectiveLineRatFuncAlgEquiv :
    letI : Algebra k
      (Proj (MvPolynomial.homogeneousSubmodule (Fin (1 + 1)) k) : Scheme).functionField :=
        (baseToFunctionField (π k 1)).toAlgebra
    RatFunc k ≃ₐ[k]
      (Proj (MvPolynomial.homogeneousSubmodule (Fin (1 + 1)) k) : Scheme).functionField := by
  let : Algebra k
      (Proj (MvPolynomial.homogeneousSubmodule (Fin (1 + 1)) k) : Scheme).functionField :=
    (baseToFunctionField (π k 1)).toAlgebra
  exact AlgEquiv.ofRingEquiv (f := projectiveLineRatFuncEquiv k)
    (projectiveLineRatFuncEquiv_algebraMap k)

end AlgebraicGeometry.ProjSpace
