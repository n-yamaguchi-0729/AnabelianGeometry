/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.SchemeTheory.GroupSchemes.RelativeGroupLaw.AlgebraicPoints
public import Nyll.AlgebraicCurves.Geometry.Curves.SmoothProductIntegral
public import Nyll.AlgebraicCurves.Geometry.Picard.Functor.Functor
public import Nyll.AlgebraicCurves.Geometry.Picard.Poincare.PicardRepresentabilityPoincarePullbackOneIso
public import Nyll.AlgebraicCurves.Geometry.Picard.Representability.RepresentsRelSubPicGroup
public import Nyll.AlgebraicCurves.Geometry.Sheaves.Tensor.InvertibleTensor
public import Nyll.EtaleCohomology.Classical.InvertibleCycleClass
public import Nyll.EtaleCohomology.Classical.InvertibleCycleTensor
public import Nyll.EtaleCohomology.Classical.MultiplicativeGroup
public import Nyll.JacobianVarieties.Picard.GroupLaw.PicardRepresentabilityPullbackMulIso
public import Nyll.SchemeTheory.CategoryTheory.SchemeHomOver
public import Nyll.SchemeTheory.Modules.Invertible.Invertible
public import Mathlib.Algebra.Algebra.Defs

/-!
# The native Poincaré class of actual Picard points

The original Poincaré family defines an additive map from the actual
algebraic points of its Picard representative to native H¹(Gm). The source
point is transported from the self coefficient map to the identity base
without changing its underlying scheme map. The actual Poincaré unit and
multiplication isomorphisms prove additivity of the native class.
-/

@[expose] public section

universe u

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory
open NeronModelInfra GoodReductionJacobian EtaleCohomology

namespace AlgebraicGeometry.RelPicard.RepresentsRelSubPic

variable {K : Type u} [Field K] {C : Scheme.{u}}
  {c : C ⟶ Spec (.of K)} {ε : SchemeHomOver (𝟙 (Spec (.of K))) c}
  {P : SubPicGroupCondition c ε} {D : RelativePic0Designation K c}
  (h : RepresentsRelSubPic c ε P.toSubPicCondition D)

local notation "G" => h.relativeGroupLaw
local notation "hc" => h.relativeGroupLaw_isCommutative
local notation "s" => Spec.map (CommRingCat.ofHom (algebraMap K K))
local notation "C₀" => pullback c (𝟙 (Spec (CommRingCat.of K)))

/-- The spectrum map of the field's self algebra structure is the identity. -/
theorem selfCoefficientSpecMap_eq_id :
    s = 𝟙 (Spec (.of K)) := by
  rw [Algebra.algebraMap_self, CommRingCat.ofHom_id, Spec.map_id]

/-- Regard the same actual algebraic point as a point over the identity
base, using the original self coefficient map. -/
def poincareIdentityPoint (a : (G).AlgPoints hc K) :
    SchemeHomOver (𝟙 (Spec (.of K))) D.toBase :=
  GoodReductionJacobian.schemeHomOverComp (𝟙 (Spec (.of K)))
    ((Category.id_comp s).trans (selfCoefficientSpecMap_eq_id (K := K)))
    (RelativeGroupLaw.AlgPoints.toPoint a)

/-- Changing the presentation of the base retains the original
underlying scheme point. -/
theorem poincareIdentityPoint_coe (a : (G).AlgPoints hc K) :
    (h.poincareIdentityPoint a).1 = (RelativeGroupLaw.AlgPoints.toPoint a).1 :=
  Category.id_comp _

/-- The transported algebraic zero is the original identity section. -/
theorem poincareIdentityPoint_zero :
    h.poincareIdentityPoint 0 = (G).one (𝟙 (Spec (.of K))) := by
  rw [poincareIdentityPoint, RelativeGroupLaw.AlgPoints.toPoint_zero]
  exact (G).one_natural s (𝟙 _) (𝟙 _)
    ((Category.id_comp s).trans (selfCoefficientSpecMap_eq_id (K := K)))

/-- Transport of the original algebraic points preserves the actual
relative group law. -/
theorem poincareIdentityPoint_add (a b : (G).AlgPoints hc K) :
    h.poincareIdentityPoint (a + b) =
      (G).mul (𝟙 (Spec (.of K))) (h.poincareIdentityPoint a) (h.poincareIdentityPoint b) := by
  rw [poincareIdentityPoint, RelativeGroupLaw.AlgPoints.toPoint_add]
  exact (G).mul_natural s (𝟙 _) (𝟙 _)
    ((Category.id_comp s).trans (selfCoefficientSpecMap_eq_id (K := K)))
    (RelativeGroupLaw.AlgPoints.toPoint a) (RelativeGroupLaw.AlgPoints.toPoint b)

variable [IsAlgClosed K] [IsIntegral C] [Smooth c]

local instance : IsIntegral C₀ := isIntegral_pullback_of_smooth_of_isAlgClosed c (𝟙 _)

/-- The original native H¹(Gm) class of the Poincaré family is an
additive homomorphism on the actual Picard algebraic points. -/
def poincareNativeH1Hom : (G).AlgPoints hc K →+
    Sheaf.H.{u} (etaleMultiplicativeGroupSheaf C₀) 1 where
  toFun a := invertibleModuleMultiplicativeGroupH1
    (h.poincare.pullbackAlong (h.poincareIdentityPoint a)).isInvertible
  map_zero' := by
    rw [poincareIdentityPoint_zero]
    obtain ⟨e⟩ : Nonempty
        ((h.poincare.pullbackAlong ((G).one (𝟙 (Spec (.of K))))).L ≅ 𝟙_ _) := by
      let _ : GrpObj (Over.mk D.toBase) := h.grpObj
      exact h.nonempty_poincare_pullbackAlong_one_iso (Over.mk (𝟙 (Spec (.of K))))
    exact (invertibleModuleMultiplicativeGroupH1_iso
      (h.poincare.pullbackAlong ((G).one (𝟙 (Spec (.of K))))).isInvertible
      (Scheme.Modules.isInvertible_unit C₀) e).trans
        (invertibleModuleMultiplicativeGroupH1_unit C₀)
  map_add' a b := by
    rw [poincareIdentityPoint_add]
    obtain ⟨e⟩ := h.nonempty_pullbackAlong_mul_iso (𝟙 (Spec (.of K)))
      (h.poincareIdentityPoint a) (h.poincareIdentityPoint b)
    exact (invertibleModuleMultiplicativeGroupH1_iso
      (h.poincare.pullbackAlong
        ((G).mul (𝟙 (Spec (.of K)))
          (h.poincareIdentityPoint a) (h.poincareIdentityPoint b))).isInvertible
      ((h.poincare.pullbackAlong (h.poincareIdentityPoint a)).isInvertible.tensor
        (h.poincare.pullbackAlong (h.poincareIdentityPoint b)).isInvertible) e).trans
      (invertibleModuleMultiplicativeGroupH1_tensor
        (h.poincare.pullbackAlong (h.poincareIdentityPoint a)).isInvertible
        (h.poincare.pullbackAlong (h.poincareIdentityPoint b)).isInvertible)

/-- The homomorphism evaluates to the original native class of the
actual Poincaré pullback on the original identity base change. -/
theorem poincareNativeH1Hom_apply (a : (G).AlgPoints hc K) :
    h.poincareNativeH1Hom a = invertibleModuleMultiplicativeGroupH1
      (h.poincare.pullbackAlong (h.poincareIdentityPoint a)).isInvertible := rfl

/-- Equality of the original underlying points identifies the native
Poincaré class, independently of the presentation of the base map. -/
theorem poincareNativeH1Hom_apply_of_pointEq (a : (G).AlgPoints hc K)
    (τ : SchemeHomOver (𝟙 (Spec (.of K))) D.toBase)
    (hτ : (RelativeGroupLaw.AlgPoints.toPoint a).1 = τ.1) :
    h.poincareNativeH1Hom a =
      invertibleModuleMultiplicativeGroupH1 (h.poincare.pullbackAlong τ).isInvertible := by
  have hp : h.poincareIdentityPoint a = τ :=
    Subtype.ext ((h.poincareIdentityPoint_coe a).trans hτ)
  rw [poincareNativeH1Hom_apply, hp]

end AlgebraicGeometry.RelPicard.RepresentsRelSubPic
