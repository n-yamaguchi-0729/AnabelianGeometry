/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.AlgebraicCurves.Geometry.Picard.AbelJacobi.AbelJacobiFamily
public import Nyll.AlgebraicCurves.Geometry.Sheaves.Divisors.IdealSheafModuleMaps
public import Nyll.AlgebraicCurves.Geometry.Sheaves.Divisors.InvertibleIdealInvertibleModule
public import Nyll.AlgebraicCurves.Geometry.Sheaves.Divisors.InvertibleIdealIsoPullbackModuleComparison
public import Nyll.AlgebraicCurves.Geometry.Sheaves.Divisors.InvertibleIdealModuleTensorInvModuleIso
public import Nyll.AlgebraicCurves.Geometry.Sheaves.Divisors.InvertibleIdealPullbackInvModuleIso
public import Nyll.AlgebraicCurves.Geometry.Sheaves.Tensor.InvertibleDual
public import Nyll.AlgebraicCurves.Geometry.Sheaves.Tensor.InvertibleIsoTensorUnitField
public import Nyll.AlgebraicCurves.RelativeDivisors.Cartier.EffectiveCartierInvertibility
public import Nyll.AlgebraicCurves.RelativeDivisors.LineBundles.RelEffCartierDivTwist2
public import Nyll.AlgebraicCurves.RelativeDivisors.PointSums.PointKernelPullback
public import Nyll.EtaleCohomology.Classical.DiagonalDivisorBundle
public import Nyll.EtaleCohomology.Classical.DiagonalPointSectionIdeals
public import Nyll.EtaleCohomology.Classical.GraphCartierCycleClass
public import Nyll.EtaleCohomology.Classical.RationalKunnethSections
public import Nyll.SchemeTheory.CategoryTheory.MonoidalCategoryIsoTensorIsoTensorUnit
public import Nyll.SchemeTheory.Modules.Invertible.Rigidify
public import Nyll.SchemeTheory.Modules.Tensor.PullbackMonoidal

/-!
# The actual rigidified diagonal bundle

Restriction of the Abel–Jacobi family to its original rigidifying
section is the original point line bundle. The other factor restricts
to a pullback of a line over the ground field and is therefore trivial.
Uniqueness of actual tensor inverses identifies the rigidifying twist
with the original second point ideal. Thus the existing relative
diagonal twist is the exact signed divisor bundle of the normalized
original diagonal.
-/

@[expose] public section

noncomputable section

universe u

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory
open EtaleCohomology.Classical

namespace EtaleCohomology

variable {K : Type u} [Field K] {X : Scheme.{u}}
  (f : X ⟶ Spec (.of K)) [IsSeparated f] [SmoothOfRelativeDimension 1 f]
  (p : Spec (.of K) ⟶ X) (hp : p ≫ f = 𝟙 _)

/-- The original Abel–Jacobi family's restriction to its actual
rigidifying section is the original point line bundle. -/
theorem ajFamily_rigSection_iso_pointLineBundle :
    Nonempty
      ((Scheme.Modules.pullback (RelPicard.rigSection f f ⟨p, hp⟩)).obj
          (RelPicard.ajFamily (a := f) ⟨p, hp⟩) ≅ p.ker.invModule) := by
  let σ := RelPicard.rigSection f f ⟨p, hp⟩
  let D := graphEffectiveCartierDivisor f f (𝟙 X) (Category.id_comp f)
  let A := productPointFstEffectiveCartierDivisor f p hp
  have hP : p.ker.IsInvertible := (sectionEffectiveCartierDivisor f p hp).2.isInvertible
  have hD : D.1.IsInvertible := D.2.isInvertible
  have hA : A.1.IsInvertible := A.2.isInvertible
  have hσD : D.1.comap σ = p.ker :=
    diagonalIdeal_comap_kunnethSectionRight f p hp
  have hσDinv : (D.1.comap σ).IsInvertible := hσD.symm ▸ hP
  obtain ⟨d⟩ := hD.nonempty_pullback_invModule_iso σ hσDinv
  let eD : (Scheme.Modules.pullback σ).obj D.1.invModule ≅ p.ker.invModule :=
    d ≪≫ eqToIso (congrArg Scheme.IdealSheafData.invModule hσD)
  have hF : IsIso (p.ker.pullbackModuleComparison (pullback.fst f f)) :=
    hP.isIso_pullbackModuleComparison (pullback.fst f f) hA
  let eF : (Scheme.Modules.pullback (pullback.fst f f)).obj p.ker.module ≅ A.1.module :=
    @asIso _ _ _ _ (p.ker.pullbackModuleComparison (pullback.fst f f)) hF
  have hσfst : σ ≫ pullback.fst f f = f ≫ p :=
    kunnethSectionRight_fst f f p hp
  let eConst : (Scheme.Modules.pullback σ).obj A.1.module ≅
      (Scheme.Modules.pullback f).obj ((Scheme.Modules.pullback p).obj p.ker.module) :=
    (Scheme.Modules.pullback σ).mapIso eF.symm ≪≫
      (Scheme.Modules.pullbackComp σ (pullback.fst f f)).app p.ker.module ≪≫
      (Scheme.Modules.pullbackCongr hσfst).app p.ker.module ≪≫
      ((Scheme.Modules.pullbackComp f p).app p.ker.module).symm
  obtain ⟨eK⟩ := Scheme.Modules.IsInvertible.nonempty_iso_tensorUnit_of_field K
    ((Scheme.Modules.pullback p).obj p.ker.module) (hP.isInvertible_module.pullback p)
  let eUnit : (Scheme.Modules.pullback σ).obj A.1.module ≅ 𝟙_ X.Modules :=
    eConst ≪≫ (Scheme.Modules.pullback f).mapIso eK ≪≫
      Scheme.Modules.pullbackTensorUnitObjIso f
  let eA : A.1.module ≅ (RelPicard.constDiv (a := f) ⟨p, hp⟩).idealModule :=
    eqToIso (congrArg (fun I : (pullback f f).IdealSheafData => I.module)
      (pointKernel_comap_fst f f p hp))
  exact ⟨(Scheme.Modules.pullback σ).mapIso (Iso.refl D.1.invModule ⊗ᵢ eA.symm) ≪≫
    Scheme.Modules.pullbackTensorObjIso σ D.1.invModule A.1.module ≪≫
      (eD ⊗ᵢ eUnit) ≪≫ ρ_ p.ker.invModule⟩

/-- The actual rigidification of the Abel–Jacobi family is the signed
divisor bundle of the actual normalized diagonal. -/
theorem rigidify_ajFamily_iso_middleDivisorBundle :
    Nonempty
      (Scheme.Modules.rigidify (RelPicard.rigSection f f ⟨p, hp⟩) (pullback.snd f f)
          (RelPicard.ajFamily (a := f) ⟨p, hp⟩) ≅
        (graphEffectiveCartierDivisor f f (𝟙 X) (Category.id_comp f)).1.invModule ⊗
          (diagonalEdgeEffectiveCartierDivisor f p hp).1.module) := by
  let σ := RelPicard.rigSection f f ⟨p, hp⟩
  let L := RelPicard.ajFamily (a := f) ⟨p, hp⟩
  let B := productPointSndEffectiveCartierDivisor f p hp
  have hP : p.ker.IsInvertible := (sectionEffectiveCartierDivisor f p hp).2.isInvertible
  have hB : B.1.IsInvertible := B.2.isInvertible
  have hL : Scheme.Modules.IsInvertible L := RelPicard.isInvertible_ajFamily ⟨p, hp⟩
  obtain ⟨eσ⟩ := ajFamily_rigSection_iso_pointLineBundle f p hp
  obtain ⟨eDual⟩ := nonempty_iso_of_tensor_iso_tensorUnit eσ
    (hL.pullback σ).dual.2 hP.nonempty_module_tensor_invModule_iso.2
  have hBiso : IsIso (p.ker.pullbackModuleComparison (pullback.snd f f)) :=
    hP.isIso_pullbackModuleComparison (pullback.snd f f) hB
  let eB : (Scheme.Modules.pullback (pullback.snd f f)).obj p.ker.module ≅ B.1.module :=
    @asIso _ _ _ _ (p.ker.pullbackModuleComparison (pullback.snd f f)) hBiso
  obtain ⟨e⟩ := diagonalMiddleDivisorBundle_iso_ajFamily f p hp
  exact ⟨(Iso.refl L ⊗ᵢ ((Scheme.Modules.pullback (pullback.snd f f)).mapIso eDual ≪≫ eB)) ≪≫
    e.symm⟩

/-- The original relative diagonal twist, used by actual Picard
representability, is the very same signed divisor bundle. -/
theorem diagonalTwistModule_iso_middleDivisorBundle :
    Nonempty
      ((RelPicard.diagDiv (a := f)).twistModule f ⟨p, hp⟩ ≅
        (graphEffectiveCartierDivisor f f (𝟙 X) (Category.id_comp f)).1.invModule ⊗
          (diagonalEdgeEffectiveCartierDivisor f p hp).1.module) := by
  let eL : (RelPicard.diagDiv (a := f)).lineBundle ⊗
      ((RelPicard.sectionIdeal f ⟨p, hp⟩ f) ^ 1).module ≅
        RelPicard.ajFamily (a := f) ⟨p, hp⟩ :=
    Iso.refl _ ⊗ᵢ eqToIso (congrArg Scheme.IdealSheafData.module (pow_one _))
  obtain ⟨e⟩ := rigidify_ajFamily_iso_middleDivisorBundle f p hp
  exact ⟨Scheme.Modules.rigidifyMapIso (RelPicard.rigSection f f ⟨p, hp⟩)
    (pullback.snd f f) eL ≪≫ e⟩

end EtaleCohomology
