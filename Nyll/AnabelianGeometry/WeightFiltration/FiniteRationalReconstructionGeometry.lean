/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.AnabelianGeometry.ArithmeticIsomorphisms.GeometricGaloisDescent
import Nyll.AnabelianGeometry.WeightFiltration.AlignedRationalModelAmbient
import Nyll.AnabelianGeometry.ProjectiveLine.LinearSchemeScalarExtension

/-! # The same reconstructed finite isomorphism in its geometric charts

The isomorphism returned by split reconstruction is transported through the
given finite models. Its scalar extension is compared with the literal
pullback of that same isomorphism, retaining the actual model square.
-/

noncomputable section
open AlgebraicGeometry.SmoothProperCurve

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicCurve
open AlgebraicGeometry.ProjSpace
open AnabelianGeometry.ArithmeticIsomorphisms
open AnabelianGeometry.GeometricFundamentalGroup AnabelianGeometry.ProjectiveLine

namespace AnabelianGeometry.WeightFiltration

variable (k E κ : Type) [Field k] [Field E] [Field κ]
  [Algebra k E] [Algebra E κ] [Algebra k κ] [IsScalarTower k E κ]

/-- Scalar extension of a specified isomorphism over the intermediate field. -/
def finiteModelOpenScalarExtensionIso
    {S T : Scheme} (gS : S ⟶ Spec (.of E)) (gT : T ⟶ Spec (.of E))
    (I : S ≅ T) (hI : I.hom ≫ gT = gS) :
    pullback (specMap E κ) gS ≅ pullback (specMap E κ) gT :=
  asIso (pullback.map (specMap E κ) gS (specMap E κ) gT
    (𝟙 _) I.hom (𝟙 _)
    ((Category.comp_id _).trans (Category.id_comp _).symm)
    ((Category.comp_id _).trans hI.symm))

/-- The finite reconstructed isomorphism is transported through the actual
source and target models, with no new choice of geometric isomorphism. -/
def finiteRationalModelReconstructionIso
    {X Y S T : Scheme} (f : X ⟶ Spec (.of k)) (g : Y ⟶ Spec (.of k))
    (Js : pullback (specMap k E) f ≅ S)
    (Jt : pullback (specMap k E) g ≅ T) (I : S ≅ T) :
    pullback (specMap k E) f ≅ pullback (specMap k E) g :=
  (Js ≪≫ I) ≪≫ Jt.symm

/-- The reconstructed finite isomorphism has its actual map to E. -/
theorem finiteRationalModelReconstructionIso_hom_base
    {X Y S T : Scheme} (f : X ⟶ Spec (.of k)) (g : Y ⟶ Spec (.of k))
    (gS : S ⟶ Spec (.of E)) (gT : T ⟶ Spec (.of E))
    (Js : pullback (specMap k E) f ≅ S)
    (Jt : pullback (specMap k E) g ≅ T)
    (hJs : Js.hom ≫ gS = pullback.fst (specMap k E) f)
    (hJt : Jt.hom ≫ gT = pullback.fst (specMap k E) g)
    (I : S ≅ T) (hI : I.hom ≫ gT = gS) :
    (finiteRationalModelReconstructionIso k E f g Js Jt I).hom ≫
        pullback.fst (specMap k E) g = pullback.fst (specMap k E) f := by
  change ((Js.hom ≫ I.hom) ≫ Jt.inv) ≫ _ = _
  rw [Category.assoc, ← hJt, Jt.inv_hom_id_assoc, Category.assoc, hI, hJs]

/-- The geometric isomorphism used for descent is literally the scalar
extension of the reconstructed finite map in the original chosen charts. -/
theorem finiteRationalModelReconstructionIso_geometric_square
    {X Y S T : Scheme} (f : X ⟶ Spec (.of k)) (g : Y ⟶ Spec (.of k))
    (gS : S ⟶ Spec (.of E)) (gT : T ⟶ Spec (.of E))
    (Js : pullback (specMap k E) f ≅ S)
    (Jt : pullback (specMap k E) g ≅ T)
    (hJs : Js.hom ≫ gS = pullback.fst (specMap k E) f)
    (hJt : Jt.hom ≫ gT = pullback.fst (specMap k E) g)
    (I : S ≅ T) (hI : I.hom ≫ gT = gS) :
    let i := finiteRationalModelReconstructionIso k E f g Js Jt I
    let hi := finiteRationalModelReconstructionIso_hom_base
      k E f g gS gT Js Jt hJs hJt I hI
    (constantCoverIsoScalarExtension k E κ f g i hi).hom ≫
        (scalarExtensionModelIso k E κ g gT Jt hJt).hom =
      (scalarExtensionModelIso k E κ f gS Js hJs).hom ≫
        (finiteModelOpenScalarExtensionIso E κ gS gT I hI).hom := by
  intro i hi
  let B := constantCoverIsoScalarExtension k E κ f g i hi
  let BS := scalarExtensionModelIso k E κ f gS Js hJs
  let BT := scalarExtensionModelIso k E κ g gT Jt hJt
  let J := finiteModelOpenScalarExtensionIso E κ gS gT I hI
  apply pullback.hom_ext
  · change (B.hom ≫ BT.hom) ≫ pullback.fst (specMap E κ) gT =
      (BS.hom ≫ J.hom) ≫ pullback.fst (specMap E κ) gT
    simp only [B, BS, BT, J, Category.assoc, scalarExtensionModelIso_hom_comp_base,
      constantCoverIsoScalarExtension_hom_base, finiteModelOpenScalarExtensionIso,
      asIso_hom, pullback.lift_fst, Category.comp_id]
  · change (B.hom ≫ BT.hom) ≫ pullback.snd (specMap E κ) gT =
      (BS.hom ≫ J.hom) ≫ pullback.snd (specMap E κ) gT
    have hmodel : i.hom ≫ Jt.hom = Js.hom ≫ I.hom := by
      change ((Js.hom ≫ I.hom) ≫ Jt.inv) ≫ Jt.hom = _
      rw [Category.assoc, Jt.inv_hom_id, Category.comp_id]
    calc
      (B.hom ≫ BT.hom) ≫ pullback.snd (specMap E κ) gT =
          B.hom ≫ constantCoverRestriction k E κ g ≫ Jt.hom := by
        rw [Category.assoc, scalarExtensionModelIso_hom_comp_model]
      _ = constantCoverRestriction k E κ f ≫ Js.hom ≫ I.hom := by
        rw [← Category.assoc, constantCoverIsoScalarExtension_hom_restriction,
          Category.assoc, hmodel]
      _ = (BS.hom ≫ pullback.snd (specMap E κ) gS) ≫ I.hom := by
        rw [scalarExtensionModelIso_hom_comp_model, Category.assoc]
      _ = (BS.hom ≫ J.hom) ≫ pullback.snd (specMap E κ) gT := by
        simp only [J, finiteModelOpenScalarExtensionIso, asIso_hom, Category.assoc,
          pullback.lift_snd]

/-- The scalar extension of the split reconstruction has the scalar-extended
linear transformation as its actual ambient map. -/
theorem finiteModelOpenScalarExtensionIso_projective_chart
    [Infinite E] [Infinite κ]
    (s t : Finset (Projectivization E (E × E)))
    (I : (rationalConfigurationOpen s : Scheme) ≅ (rationalConfigurationOpen t : Scheme))
    (hI : I.hom ≫ ((rationalConfigurationOpen t).ι ≫ π E 1) =
      (rationalConfigurationOpen s).ι ≫ π E 1)
    (F : (E × E) ≃ₗ[E] (E × E))
    (hF : I.hom ≫ (rationalConfigurationOpen t).ι =
      (rationalConfigurationOpen s).ι ≫ (pairLinearCoordinateIso F).hom) :
    (finiteModelOpenScalarExtensionIso E κ
        ((rationalConfigurationOpen s).ι ≫ π E 1)
        ((rationalConfigurationOpen t).ι ≫ π E 1) I hI).hom ≫
        rationalConfigurationBaseChangeChart E κ t =
      rationalConfigurationBaseChangeChart E κ s ≫
        (pairLinearCoordinateIso (linearEquivFieldMap (algebraMap E κ) F)).hom := by
  let J := finiteModelOpenScalarExtensionIso E κ
    ((rationalConfigurationOpen s).ι ≫ π E 1)
    ((rationalConfigurationOpen t).ι ≫ π E 1) I hI
  let Fκ := pairLinearCoordinateIso (linearEquivFieldMap (algebraMap E κ) F)
  apply (isPullback_map E κ 1).hom_ext
  · calc
      (J.hom ≫ rationalConfigurationBaseChangeChart E κ t) ≫ map E κ 1 =
          J.hom ≫ pullback.snd (specMap E κ)
            ((rationalConfigurationOpen t).ι ≫ π E 1) ≫
              (rationalConfigurationOpen t).ι := by
        rw [Category.assoc, rationalConfigurationBaseChangeChart_comp_map]
      _ = pullback.snd (specMap E κ) ((rationalConfigurationOpen s).ι ≫ π E 1) ≫
          I.hom ≫ (rationalConfigurationOpen t).ι := by
        simp only [J, finiteModelOpenScalarExtensionIso, asIso_hom, Category.assoc,
          pullback.lift_snd_assoc]
      _ = pullback.snd (specMap E κ) ((rationalConfigurationOpen s).ι ≫ π E 1) ≫
          (rationalConfigurationOpen s).ι ≫ (pairLinearCoordinateIso F).hom := by rw [hF]
      _ = rationalConfigurationBaseChangeChart E κ s ≫
          map E κ 1 ≫ (pairLinearCoordinateIso F).hom := by
        exact (Category.assoc _ _ _).symm.trans
          ((congrArg (fun z => z ≫ (pairLinearCoordinateIso F).hom)
            (rationalConfigurationBaseChangeChart_comp_map E κ s).symm).trans
              (Category.assoc _ _ _))
      _ = (rationalConfigurationBaseChangeChart E κ s ≫ Fκ.hom) ≫ map E κ 1 := by
        rw [Category.assoc, pairLinearCoordinateIso_fieldMap]
  · calc
      (J.hom ≫ rationalConfigurationBaseChangeChart E κ t) ≫ π κ 1 =
          pullback.fst (specMap E κ) ((rationalConfigurationOpen s).ι ≫ π E 1) := by
        rw [Category.assoc, rationalConfigurationBaseChangeChart_comp_π]
        dsimp only [J, finiteModelOpenScalarExtensionIso, asIso_hom]
        simp only [pullback.lift_fst, Category.comp_id]
      _ = (rationalConfigurationBaseChangeChart E κ s ≫ Fκ.hom) ≫ π κ 1 := by
        dsimp only [Fκ, pairLinearCoordinateIso]
        rw [Category.assoc, linearCoordinateIso_hom_comp_π,
          rationalConfigurationBaseChangeChart_comp_π]

/-- The actual geometric map used by descent is the same map whose projective
transformation is recovered by the finite split theorem. -/
theorem finiteRationalModelReconstructionIso_geometric_chart
    [Infinite E] [Infinite κ]
    {X Y : Scheme} (f : X ⟶ Spec (.of k)) (g : Y ⟶ Spec (.of k))
    (s t : Finset (Projectivization E (E × E)))
    (Js : pullback (specMap k E) f ≅ (rationalConfigurationOpen s : Scheme))
    (Jt : pullback (specMap k E) g ≅ (rationalConfigurationOpen t : Scheme))
    (hJs : Js.hom ≫ ((rationalConfigurationOpen s).ι ≫ π E 1) =
      pullback.fst (specMap k E) f)
    (hJt : Jt.hom ≫ ((rationalConfigurationOpen t).ι ≫ π E 1) =
      pullback.fst (specMap k E) g)
    (I : (rationalConfigurationOpen s : Scheme) ≅ (rationalConfigurationOpen t : Scheme))
    (hI : I.hom ≫ ((rationalConfigurationOpen t).ι ≫ π E 1) =
      (rationalConfigurationOpen s).ι ≫ π E 1)
    (F : (E × E) ≃ₗ[E] (E × E))
    (hF : I.hom ≫ (rationalConfigurationOpen t).ι =
      (rationalConfigurationOpen s).ι ≫ (pairLinearCoordinateIso F).hom) :
    let i := finiteRationalModelReconstructionIso k E f g Js Jt I
    let hi := finiteRationalModelReconstructionIso_hom_base k E f g
      ((rationalConfigurationOpen s).ι ≫ π E 1)
      ((rationalConfigurationOpen t).ι ≫ π E 1) Js Jt hJs hJt I hI
    (constantCoverIsoScalarExtension k E κ f g i hi).hom ≫
        (scalarExtensionModelIso k E κ g
          ((rationalConfigurationOpen t).ι ≫ π E 1) Jt hJt).hom ≫
        rationalConfigurationBaseChangeChart E κ t =
      (scalarExtensionModelIso k E κ f
          ((rationalConfigurationOpen s).ι ≫ π E 1) Js hJs).hom ≫
        rationalConfigurationBaseChangeChart E κ s ≫
        (pairLinearCoordinateIso (linearEquivFieldMap (algebraMap E κ) F)).hom := by
  intro i hi
  rw [← Category.assoc, finiteRationalModelReconstructionIso_geometric_square
    k E κ f g ((rationalConfigurationOpen s).ι ≫ π E 1)
      ((rationalConfigurationOpen t).ι ≫ π E 1) Js Jt hJs hJt I hI,
    Category.assoc, finiteModelOpenScalarExtensionIso_projective_chart E κ s t I hI F hF]

end AnabelianGeometry.WeightFiltration
