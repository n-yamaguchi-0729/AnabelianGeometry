/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.AlgebraicCurves.Geometry.Picard.AbelJacobi.AbelJacobiFamily
public import Nyll.AlgebraicCurves.Geometry.Picard.AbelJacobi.AjFamilyFibreIso
public import Nyll.AlgebraicCurves.Geometry.Picard.AlgebraicEquivalence.AlgEquivZeroCut
public import Nyll.AlgebraicCurves.Geometry.Picard.AlgebraicEquivalence.RelativeDivisorAlgebraicEquivalenceTwistModuleFibre
public import Nyll.AlgebraicCurves.Geometry.Picard.Functor.Functor
public import Nyll.AlgebraicCurves.Geometry.Picard.Representability.Designation
public import Nyll.AlgebraicCurves.Geometry.Picard.Representability.Representation
public import Nyll.AlgebraicCurves.Geometry.Sheaves.Divisors.InvertibleIdealIsoPullbackModuleComparison
public import Nyll.AlgebraicCurves.Geometry.Sheaves.Tensor.InvertibleIsoTensorUnitLocalRing
public import Nyll.AlgebraicCurves.RelativeDivisors.BaseChange.InvertibleTwistModulePullbackIso
public import Nyll.EtaleCohomology.Classical.DiagonalDivisorBundle
public import Nyll.EtaleCohomology.Classical.DiagonalRigidifiedBundle
public import Nyll.EtaleCohomology.Classical.GraphCartierCycleClass

public import Nyll.SchemeTheory.Modules.Tensor.PullbackMonoidal

/-!
# The original Poincaré family of the normalized diagonal

The original relative diagonal twist has algebraically trivial geometric
fibres by the relative Cartier-divisor theorem. Applying the original
representing property to that actual family gives a morphism from the
curve to the Picard carrier and an isomorphism on the entire product.
The isomorphism identifies the pulled-back Poincaré family with the
original signed divisor bundle of the normalized diagonal.
-/

@[expose] public section

noncomputable section

universe u

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory
open NeronModelInfra GoodReductionJacobian

namespace EtaleCohomology

variable {K : Type u} [Field K] {X : Scheme.{u}}
  (f : X ⟶ Spec (.of K)) [SmoothOfRelativeDimension 1 f]
  (p : Spec (.of K) ⟶ X) (hp : p ≫ f = 𝟙 _)

section

variable [IsSeparated f]

/-- The actual relative diagonal twist, with its original rigidification. -/
def diagonalRigidifiedLineBundle : RelPicard.RigidifiedLineBundle f ⟨p, hp⟩ f where
  L := (RelPicard.diagDiv (a := f)).twistModule f ⟨p, hp⟩
  isInvertible :=
    (RelEffCartierDiv.isInvertible_twistModule_and_nonempty_pullback_iso
      f ⟨p, hp⟩ (RelPicard.diagDiv (a := f))).1
  rigidified :=
    (RelEffCartierDiv.isInvertible_twistModule_and_nonempty_pullback_iso
      f ⟨p, hp⟩ (RelPicard.diagDiv (a := f))).2

end

variable [IsProper f] [GeometricallyIntegral f]

/-- The original relative Cartier theorem supplies the Picard condition
for every geometric fibre of the actual diagonal family. -/
theorem diagonalRigidifiedLineBundle_fibrewise :
    RelPicard.FibrewiseAlgEquivZero (diagonalRigidifiedLineBundle f p hp) := by
  intro k _ _ s
  exact RelEffCartierDiv.isAlgEquivZero_twistModule_fibre
    f ⟨p, hp⟩ (RelPicard.diagDiv (a := f)) k s

variable (D : RelativePic0Designation K f)
  (h : RelPicard.RepresentsRelSubPic f ⟨p, hp⟩ (RelPicard.algEquivZeroCut f ⟨p, hp⟩) D)

/-- The original representing morphism of the actual rigidified
diagonal family. -/
def diagonalPicardClassifyingMap : SchemeHomOver f D.toBase :=
  h.classify f (diagonalRigidifiedLineBundle f p hp)
    (diagonalRigidifiedLineBundle_fibrewise f p hp)

/-- The original Poincaré family pulled back along the actual
classifying morphism is the original normalized diagonal bundle on the
whole self-product. -/
theorem diagonalPicardClassifyingMap_poincareIso :
    Nonempty
      ((h.poincare.pullbackAlong (diagonalPicardClassifyingMap f p hp D h)).L ≅
        (graphEffectiveCartierDivisor f f (𝟙 X) (Category.id_comp f)).1.invModule ⊗
          (diagonalEdgeEffectiveCartierDivisor f p hp).1.module) := by
  obtain ⟨e⟩ := h.classify_spec f (diagonalRigidifiedLineBundle f p hp)
    (diagonalRigidifiedLineBundle_fibrewise f p hp)
  obtain ⟨d⟩ := diagonalTwistModule_iso_middleDivisorBundle f p hp
  exact ⟨e ≪≫ d⟩

/-- Every field-valued point of the same diagonal classifying map
classifies its actual point-minus-base-point line bundle. The extra
normalizing factor is pulled back from the parameter field, where the
original invertible module is trivial. -/
theorem diagonalPicardClassifyingMap_fieldPointIso
    (L : Type u) [Field L] (t : Spec (.of L) ⟶ Spec (.of K))
    (x : SchemeHomOver t f) :
    Nonempty ((h.poincare.pullbackAlong
      ⟨x.1 ≫ (diagonalPicardClassifyingMap f p hp D h).1,
        (Category.assoc _ _ _).trans
          ((congrArg (x.1 ≫ ·) (diagonalPicardClassifyingMap f p hp D h).2).trans x.2)⟩).L ≅
      (RelEffCartierDiv.ofPoint f x.1 x.2).lineBundle ⊗
        (RelEffCartierDiv.ofPoint f (t ≫ p)
          ((Category.assoc _ _ _).trans
            ((congrArg (t ≫ ·) hp).trans (Category.comp_id t)))).idealModule) := by
  let aj := diagonalPicardClassifyingMap f p hp D h
  let ψ := RelPicard.baseChangeSnd f x
  let A := RelPicard.ajFamily (a := f) ⟨p, hp⟩
  let B := productPointSndEffectiveCartierDivisor f p hp
  let V := (RelEffCartierDiv.ofPoint f x.1 x.2).lineBundle ⊗
    (RelEffCartierDiv.ofPoint f (t ≫ p)
      ((Category.assoc _ _ _).trans
        ((congrArg (t ≫ ·) hp).trans (Category.comp_id t)))).idealModule
  obtain ⟨eClassify⟩ := diagonalPicardClassifyingMap_poincareIso f p hp D h
  obtain ⟨eMiddle⟩ := diagonalMiddleDivisorBundle_iso_ajFamily f p hp
  obtain ⟨ePoint⟩ := RelPicard.nonempty_ajFamily_pullbackAlong_iso ⟨p, hp⟩ t x
  have hP : p.ker.IsInvertible := (sectionEffectiveCartierDivisor f p hp).2.isInvertible
  let c : (Scheme.Modules.pullback (pullback.snd f f)).obj p.ker.module ⟶ B.1.module :=
    p.ker.pullbackModuleComparison (pullback.snd f f)
  have : IsIso c :=
    hP.isIso_pullbackModuleComparison (pullback.snd f f) B.2.isInvertible
  let eB : (Scheme.Modules.pullback (pullback.snd f f)).obj p.ker.module ≅ B.1.module :=
    asIso c
  obtain ⟨eField⟩ :=
    (hP.isInvertible_module.pullback x.1).nonempty_iso_tensorUnit_of_isLocalRing
  have hψ : ψ ≫ pullback.snd f f = pullback.snd f t ≫ x.1 := by
    change RelPicard.baseChangeSnd f x ≫ pullback.snd f f = _
    unfold RelPicard.baseChangeSnd
    exact pullback.lift_snd _ _ _
  let eUnit : (Scheme.Modules.pullback ψ).obj B.1.module ≅ 𝟙_ (pullback f t).Modules :=
    (Scheme.Modules.pullback ψ).mapIso eB.symm ≪≫
      (Scheme.Modules.pullbackComp ψ (pullback.snd f f)).app p.ker.module ≪≫
      (Scheme.Modules.pullbackCongr hψ).app p.ker.module ≪≫
      ((Scheme.Modules.pullbackComp (pullback.snd f t) x.1).app p.ker.module).symm ≪≫
      (Scheme.Modules.pullback (pullback.snd f t)).mapIso eField ≪≫
      Scheme.Modules.pullbackTensorUnitObjIso (pullback.snd f t)
  let eComp : (h.poincare.pullbackAlong (RelPicard.postComp aj x)).L ≅
      (Scheme.Modules.pullback ψ).obj (h.poincare.pullbackAlong aj).L :=
    (Scheme.Modules.pullbackCongr (RelPicard.baseChangeSnd_comp f aj x).symm).app
        h.poincare.L ≪≫
      ((Scheme.Modules.pullbackComp ψ (RelPicard.baseChangeSnd f aj)).app h.poincare.L).symm
  exact ⟨eComp ≪≫ (Scheme.Modules.pullback ψ).mapIso (eClassify ≪≫ eMiddle) ≪≫
    Scheme.Modules.pullbackTensorObjIso ψ A B.1.module ≪≫ (ePoint ⊗ᵢ eUnit) ≪≫ ρ_ V⟩

end EtaleCohomology
