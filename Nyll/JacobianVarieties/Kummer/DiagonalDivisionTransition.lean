/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.AlgebraicCurves.Geometry.Picard.DivisionPullback
public import Nyll.AlgebraicCurves.Geometry.Picard.DivisionPullbackCocycle
public import Nyll.AlgebraicCurves.Geometry.Picard.Functor.Functor
public import Nyll.AlgebraicCurves.Geometry.Picard.Poincare.PicardRepresentabilityPoincarePullbackMulIso
public import Nyll.AlgebraicCurves.Geometry.Picard.Poincare.PicardRepresentabilityPoincarePullbackOneIso
public import Nyll.JacobianVarieties.Kummer.DiagonalDivisionRoot
public import Nyll.JacobianVarieties.Picard.Poincare.PicardRepresentabilityPoincarePullbackPowIsoTensorPow
public import Nyll.SchemeTheory.Modules.Tensor.TensorPowers
public import Mathlib.AlgebraicGeometry.Modules.Sheaf

/-!
# The original Poincaré transition families on the division cover

The difference of the two original division points classifies an actual
Poincaré family on their overlap. Tensoring this family with the first
root family gives the second root family on the whole product. Its nth
tensor power is trivial, because the original difference is n-torsion.

The point-valued cocycle also gives a tensor-product isomorphism for
successive transition families. These are actual bundle comparisons;
they do not assert a comparison with the cohomological cup product.
-/

@[expose] public section

noncomputable section

universe u

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory
open NeronModelInfra GoodReductionJacobian

namespace AlgebraicGeometry.RelPicard.RepresentsRelSubPic

variable {R : Type u} [CommRing R] {C : Scheme.{u}}
  {c : C ⟶ Spec (.of R)} {ε : SchemeHomOver (𝟙 (Spec (.of R))) c}
  {P : SubPicGroupCondition c ε} {D : RelativePic0Designation R c}
  (h : RepresentsRelSubPic c ε P.toSubPicCondition D)
  {T : Scheme.{u}} {t : T ⟶ Spec (.of R)}
  (a : SchemeHomOver t D.toBase) (n : ℕ)

local notation "s" => h.divisionStructure a n
local notation "b" => h.divisionPoint a n
local notation "G" => h.relativeGroupLaw

/-- The actual Poincaré family classified by the difference of two
original division points. -/
def divisionTransitionFamily {W : Scheme.{u}} {w : W ⟶ Spec (.of R)}
    (x y : SchemeHomOver w s) : RigidifiedLineBundle c ε w :=
  h.poincare.pullbackAlong (h.divisionDifference a n x y)

/-- Restricting the original root family is the Poincaré family
of the same original restricted division point, on the whole product. -/
def divisionRootFamilyPullbackIso {W : Scheme.{u}} {w : W ⟶ Spec (.of R)}
    (x : SchemeHomOver w s) :
    (Scheme.Modules.pullback (baseChangeSnd c x)).obj (h.divisionRootFamily a n).L ≅
      (h.poincare.pullbackAlong (postComp b x)).L :=
  (Scheme.Modules.pullbackComp (baseChangeSnd c x) (baseChangeSnd c b)).app h.poincare.L ≪≫
    (Scheme.Modules.pullbackCongr (baseChangeSnd_comp c b x)).app h.poincare.L

/-- The transition family commutes with an actual further base change,
using the already proved naturality of the original point difference. -/
def divisionTransitionFamilyPullbackIso {W W' : Scheme.{u}}
    {w : W ⟶ Spec (.of R)} {w' : W' ⟶ Spec (.of R)}
    (x y : SchemeHomOver w s) (v : SchemeHomOver w' w) :
    (Scheme.Modules.pullback (baseChangeSnd c v)).obj
        (h.divisionTransitionFamily a n x y).L ≅
      (h.divisionTransitionFamily a n (postComp x v) (postComp y v)).L :=
  (Scheme.Modules.pullbackComp (baseChangeSnd c v)
      (baseChangeSnd c (h.divisionDifference a n x y))).app h.poincare.L ≪≫
    (Scheme.Modules.pullbackCongr
      ((baseChangeSnd_comp c (h.divisionDifference a n x y) v).trans
        (congrArg (fun z => baseChangeSnd c z)
          (h.divisionDifference_pullback a n x y v)))).app h.poincare.L

/-- The transition family takes the first actual root family to
the second actual root family, before passing to any pointwise fibers. -/
theorem divisionTransitionFamily_tensor_rootIso
    {W : Scheme.{u}} {w : W ⟶ Spec (.of R)}
    (x y : SchemeHomOver w s) :
    Nonempty
      ((h.divisionTransitionFamily a n x y).L ⊗
          (Scheme.Modules.pullback (baseChangeSnd c x)).obj (h.divisionRootFamily a n).L ≅
        (Scheme.Modules.pullback (baseChangeSnd c y)).obj (h.divisionRootFamily a n).L) := by
  let : Group (SchemeHomOver w D.toBase) := (G).pointGroup w
  have hdiff : h.divisionDifference a n x y * postComp b x = postComp b y := by
    change (postComp b y * (postComp b x)⁻¹) * postComp b x = postComp b y
    rw [mul_assoc, inv_mul_cancel, mul_one]
  have hmul : Nonempty
      ((h.poincare.pullbackAlong
          (h.divisionDifference a n x y * postComp b x)).L ≅
        (h.divisionTransitionFamily a n x y).L ⊗
          (h.poincare.pullbackAlong (postComp b x)).L) := by
    let := h.grpObj
    exact h.nonempty_poincare_pullbackAlong_mul_iso (T := Over.mk w)
      (schemeHomOverToOverHom (h.divisionDifference a n x y))
      (schemeHomOverToOverHom (postComp b x))
  rw [hdiff] at hmul
  obtain ⟨eMul⟩ := hmul
  exact ⟨(Iso.refl _ ⊗ᵢ h.divisionRootFamilyPullbackIso a n x) ≪≫
    eMul.symm ≪≫ (h.divisionRootFamilyPullbackIso a n y).symm⟩

/-- Over two lifts of the same parameter, the actual transition
family has trivial nth tensor power. -/
theorem divisionTransitionFamily_tensorPowIso_unit
    {W : Scheme.{u}} {w : W ⟶ Spec (.of R)}
    (x y : SchemeHomOver w s)
    (hxy : postComp (h.divisionBaseMap a n) x =
      postComp (h.divisionBaseMap a n) y) :
    Nonempty ((h.divisionTransitionFamily a n x y).L.tensorPow n ≅ 𝟙_ _) := by
  let : Group (SchemeHomOver w D.toBase) := (G).pointGroup w
  obtain ⟨ePow⟩ := h.nonempty_poincare_pullbackAlong_pow_iso_tensorPow w
    (h.divisionDifference a n x y) n
  rw [h.divisionDifference_pow a n x y hxy] at ePow
  have hone : Nonempty ((h.poincare.pullbackAlong (1 : SchemeHomOver w D.toBase)).L ≅
      𝟙_ _) := by
    let := h.grpObj
    exact h.nonempty_poincare_pullbackAlong_one_iso (Over.mk w)
  obtain ⟨eOne⟩ := hone
  exact ⟨ePow.symm ≪≫ eOne⟩

/-- The actual point cocycle gives the tensor-product comparison
between successive original transition families. -/
theorem divisionTransitionFamily_tensorIso
    {W : Scheme.{u}} {w : W ⟶ Spec (.of R)}
    (x y z : SchemeHomOver w s) :
    Nonempty
      ((h.divisionTransitionFamily a n y z).L ⊗
          (h.divisionTransitionFamily a n x y).L ≅
        (h.divisionTransitionFamily a n x z).L) := by
  let : Group (SchemeHomOver w D.toBase) := (G).pointGroup w
  have hmul : Nonempty
      ((h.poincare.pullbackAlong
          (h.divisionDifference a n y z * h.divisionDifference a n x y)).L ≅
        (h.divisionTransitionFamily a n y z).L ⊗
          (h.divisionTransitionFamily a n x y).L) := by
    let := h.grpObj
    exact h.nonempty_poincare_pullbackAlong_mul_iso (T := Over.mk w)
      (schemeHomOverToOverHom (h.divisionDifference a n y z))
      (schemeHomOverToOverHom (h.divisionDifference a n x y))
  change Nonempty ((h.poincare.pullbackAlong
      ((G).mul w (h.divisionDifference a n y z) (h.divisionDifference a n x y))).L ≅
    (h.divisionTransitionFamily a n y z).L ⊗
      (h.divisionTransitionFamily a n x y).L) at hmul
  rw [h.divisionDifference_cocycle a n x y z] at hmul
  obtain ⟨e⟩ := hmul
  exact ⟨e.symm⟩

/-- The two universal lifts on the actual overlap give a transition
family with trivial nth tensor power, without an extra equality input. -/
theorem divisionOverlapTransitionFamily_tensorPowIso_unit :
    Nonempty
      ((h.divisionTransitionFamily a n
        (h.divisionOverlapFirst a n) (h.divisionOverlapSecond a n)).L.tensorPow n ≅ 𝟙_ _) :=
  h.divisionTransitionFamily_tensorPowIso_unit a n _ _ (h.divisionOverlap_projection_eq a n)

end AlgebraicGeometry.RelPicard.RepresentsRelSubPic
