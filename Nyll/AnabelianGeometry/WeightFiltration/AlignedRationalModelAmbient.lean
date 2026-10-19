/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.AnabelianGeometry.WeightFiltration.AlignedConstantGenericAmbient
import Nyll.AnabelianGeometry.WeightFiltration.NamedSquareLiteralBaseTransport
import Nyll.AnabelianGeometry.WeightFiltration.BareRationalConfigurationCuspRecognition
import Nyll.SchemeTheory.ProjectiveSpace.PuncturedProjectiveLineGeometry

/-! # A rational model retaining the original aligned generic point

An actual rational model of a finite constant cover is extended to the fixed
coefficient closure. Its actual function-field map then transports the same
ambient field. The canonical arithmetic point of the rational configuration
is exactly the image of the native finite-cover point, not merely an unrelated
point connected by an unspecified path.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open AlgebraicGeometry.FiniteEtale AlgebraicGeometry.ProjSpace

namespace AnabelianGeometry.WeightFiltration

/-- Base change of the supplied rational model, with no change of constants. -/
def rationalModelGeometricIso
    (k E κ : Type) [Field k] [Field E] [Field κ]
    [Algebra k E] [Algebra E κ]
    {X : Scheme} (f : X ⟶ Spec (.of k))
    (s : Finset (Projectivization E (E × E)))
    (J : pullback (Spec.map (CommRingCat.ofHom (algebraMap k E))) f ≅
      (rationalConfigurationOpen s : Scheme))
    (hJ : J.hom ≫ ((rationalConfigurationOpen s).ι ≫ π E 1) =
      pullback.fst (Spec.map (CommRingCat.ofHom (algebraMap k E))) f) :
    pullback (Spec.map (CommRingCat.ofHom (algebraMap E κ)))
        (pullback.fst (Spec.map (CommRingCat.ofHom (algebraMap k E))) f) ≅
      rationalConfigurationGeometricScheme E κ s :=
  asIso (pullback.map (Spec.map (CommRingCat.ofHom (algebraMap E κ)))
    (pullback.fst (Spec.map (CommRingCat.ofHom (algebraMap k E))) f)
    (Spec.map (CommRingCat.ofHom (algebraMap E κ)))
    ((rationalConfigurationOpen s).ι ≫ π E 1) (𝟙 _) J.hom (𝟙 _)
    ((Category.comp_id _).trans (Category.id_comp _).symm)
    ((Category.comp_id _).trans hJ.symm))

/-- The fixed aligned coefficient embedding survives both the finite constant
cover and its actual rational model. In particular the arithmetic point
needed by the split reconstruction theorem is constructed at the original Ω. -/
theorem exists_alignedRationalModel_genericAmbient
    (k E κ Ω : Type) [Field k] [Field E] [Infinite E] [Field κ] [Field Ω]
    [Algebra k E] [Algebra E κ] [Algebra k κ] [IsScalarTower k E κ]
    [IsSepClosure k κ] [IsSepClosed κ] [Algebra.IsAlgebraic E κ]
    [IsAlgClosed Ω] [IsSepClosed Ω]
    [Algebra κ Ω] [Algebra k Ω] [IsScalarTower k κ Ω]
    [IsFiniteEtale (Spec.map (CommRingCat.ofHom (algebraMap k E)))]
    {X : Scheme} [IsIntegral X] (f : X ⟶ Spec (.of k))
    [Algebra X.functionField Ω] [IsAlgClosure X.functionField Ω]
    [IsIntegral (pullback (Spec.map (CommRingCat.ofHom (algebraMap k E))) f)]
    [IsIntegral (pullback (Spec.map (CommRingCat.ofHom (algebraMap E κ)))
      (pullback.fst (Spec.map (CommRingCat.ofHom (algebraMap k E))) f))]
    (hbase : X.genericExtensionMorphism Ω ≫ f = ξ k Ω)
    (halign : fieldFiberExtensionIso k κ Ω ≪≫
      (eqToIso (congrArg fiber hbase)).symm =
        ((nonempty_fiber_iso (X.genericExtensionMorphism Ω ≫ f) (ξ k κ)).some).symm)
    (s : Finset (Projectivization E (E × E)))
    (J : pullback (Spec.map (CommRingCat.ofHom (algebraMap k E))) f ≅
      (rationalConfigurationOpen s : Scheme))
    (hJ : J.hom ≫ ((rationalConfigurationOpen s).ι ≫ π E 1) =
      pullback.fst (Spec.map (CommRingCat.ofHom (algebraMap k E))) f) :
    let c := pullback.fst (Spec.map (CommRingCat.ofHom (algebraMap k E))) f
    let Y := pullback (Spec.map (CommRingCat.ofHom (algebraMap E κ))) c
    let Z := rationalConfigurationGeometricScheme E κ s
    let Jκ := rationalModelGeometricIso k E κ f s J hJ
    ∃ a : Y.functionField →+* Ω,
      let _AY : Algebra Y.functionField Ω := a.toAlgebra
      IsAlgClosure Y.functionField Ω ∧
      let _AZ : Algebra Z.functionField Ω := namedBaseTransportAmbientAlgebra Jκ Ω
      IsAlgClosure Z.functionField Ω ∧
      Y.genericExtensionMorphism Ω ≫ Jκ.hom = Z.genericExtensionMorphism Ω ∧
      Z.genericExtensionMorphism Ω ≫
          pullback.fst (Spec.map (CommRingCat.ofHom (algebraMap E κ)))
            ((rationalConfigurationOpen s).ι ≫ π E 1) = ξ κ Ω ∧
      rationalConfigurationArithmeticBasePoint E κ s Ω =
        arithmeticConstantFieldLift k E κ f (X.genericExtensionMorphism Ω) ≫ J.hom := by
  intro c Y Z Jκ
  obtain ⟨a, ha⟩ := exists_alignedConstant_genericAmbient k E κ Ω f hbase halign
  refine ⟨a, ?_⟩
  intro AY
  obtain ⟨hclosure, hcoef, hlift, _horiginal⟩ := ha
  have : IsAlgClosure Y.functionField Ω := hclosure
  refine ⟨hclosure, ?_⟩
  intro AZ
  have hpoint : Y.genericExtensionMorphism Ω ≫ Jκ.hom = Z.genericExtensionMorphism Ω :=
    namedBaseTransport_genericPoint Jκ Ω
  refine ⟨namedBaseTransport_isAlgClosure Jκ Ω, hpoint, ?_, ?_⟩
  · rw [← hpoint, Category.assoc]
    simpa only [Jκ, rationalModelGeometricIso, asIso_hom,
      pullback.lift_fst, Category.comp_id] using hcoef
  · change Z.genericExtensionMorphism Ω ≫ _ = _
    rw [← hpoint, Category.assoc]
    have hcomp : Y.genericExtensionMorphism Ω ≫
        pullback.snd (Spec.map (CommRingCat.ofHom (algebraMap E κ))) c ≫ J.hom =
        arithmeticConstantFieldLift k E κ f (X.genericExtensionMorphism Ω) ≫ J.hom :=
      (Category.assoc (Y.genericExtensionMorphism Ω)
        (pullback.snd (Spec.map (CommRingCat.ofHom (algebraMap E κ))) c) J.hom).symm.trans
          (congrArg (fun z : Spec (.of Ω) ⟶
            ((FiniteEtale.pullback f).obj (originalConstantFieldCover k E)).left =>
              z ≫ J.hom) hlift)
    simpa only [Jκ, rationalModelGeometricIso, asIso_hom,
      pullback.lift_snd, Category.assoc, Y, c] using hcomp

end AnabelianGeometry.WeightFiltration
