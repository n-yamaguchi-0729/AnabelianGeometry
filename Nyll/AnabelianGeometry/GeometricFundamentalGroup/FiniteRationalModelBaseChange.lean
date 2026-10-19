/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.AnabelianGeometry.GeometricFundamentalGroup.FiniteGenusZeroOpenModel
import Nyll.AnabelianGeometry.ArithmeticIsomorphisms.OpenBaseChange
import Nyll.AnabelianGeometry.ProjectiveLine.ConfigurationScalarExtension
import Nyll.AlgebraicCurves.Models.Rational.RationalConfigurationIteratedBaseChange
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback

/-! # Finite rational models in the native constant-cover convention

The geometric inverse-image open is compared with the native constant cover.
A model over an intermediate field can subsequently be extended to a larger
constant field, with the coefficient projection retained exactly.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicCurve
open AlgebraicGeometry.ProjSpace AnabelianGeometry.ArithmeticIsomorphisms
open AnabelianGeometry.ProjectiveLine
open AlgebraicGeometry.SmoothProperCurve

namespace AnabelianGeometry.GeometricFundamentalGroup

/-- Extend an actual model of a constant cover through a coefficient tower.
The two scalar extensions are compared by their actual pullback squares. -/
def scalarExtensionModelIso
    (k E L : Type) [Field k] [Field E] [Field L]
    [Algebra k E] [Algebra E L] [Algebra k L] [IsScalarTower k E L]
    {X Y : Scheme} (f : X ⟶ Spec (.of k)) (g : Y ⟶ Spec (.of E))
    (J : pullback (specMap k E) f ≅ Y)
    (hJ : J.hom ≫ g = pullback.fst (specMap k E) f) :
    pullback (specMap k L) f ≅ pullback (specMap E L) g :=
  (coefficientTowerPullbackIso (specMap k E) (specMap E L) (specMap k L)
    (configurationCoefficientTower_comp k E L) f
    (pullback.fst (specMap k E) f) rfl).symm ≪≫
      asIso (pullback.map (specMap E L) (pullback.fst (specMap k E) f)
        (specMap E L) g (𝟙 _) J.hom (𝟙 _)
        ((Category.comp_id _).trans (Category.id_comp _).symm)
        ((Category.comp_id _).trans hJ.symm))

/-- The larger coefficient field is preserved by the extended model. -/
theorem scalarExtensionModelIso_hom_comp_base
    (k E L : Type) [Field k] [Field E] [Field L]
    [Algebra k E] [Algebra E L] [Algebra k L] [IsScalarTower k E L]
    {X Y : Scheme} (f : X ⟶ Spec (.of k)) (g : Y ⟶ Spec (.of E))
    (J : pullback (specMap k E) f ≅ Y)
    (hJ : J.hom ≫ g = pullback.fst (specMap k E) f) :
    (scalarExtensionModelIso k E L f g J hJ).hom ≫ pullback.fst (specMap E L) g =
      pullback.fst (specMap k L) f := by
  let T := coefficientTowerPullbackIso (specMap k E) (specMap E L) (specMap k L)
    (configurationCoefficientTower_comp k E L) f
    (pullback.fst (specMap k E) f) rfl
  change (T.inv ≫ _) ≫ pullback.fst (specMap E L) g = _
  simp only [Category.assoc, asIso_hom, pullback.map, pullback.lift_fst, Category.comp_id]
  rw [← coefficientTowerPullbackIso_hom_fst (specMap k E) (specMap E L)
    (specMap k L) (configurationCoefficientTower_comp k E L) f
    (pullback.fst (specMap k E) f) rfl]
  exact T.inv_hom_id_assoc _

/-- The actual restriction map between two constant covers in a tower. -/
def constantCoverRestriction
    (k E L : Type) [Field k] [Field E] [Field L]
    [Algebra k E] [Algebra E L] [Algebra k L] [IsScalarTower k E L]
    {X : Scheme} (f : X ⟶ Spec (.of k)) :
    pullback (specMap k L) f ⟶ pullback (specMap k E) f :=
  pullback.lift (pullback.fst (specMap k L) f ≫ specMap E L)
    (pullback.snd (specMap k L) f) (by
      rw [Category.assoc, configurationCoefficientTower_comp, pullback.condition])

/-- The extended model retains its map to the original finite model. -/
theorem scalarExtensionModelIso_hom_comp_model
    (k E L : Type) [Field k] [Field E] [Field L]
    [Algebra k E] [Algebra E L] [Algebra k L] [IsScalarTower k E L]
    {X Y : Scheme} (f : X ⟶ Spec (.of k)) (g : Y ⟶ Spec (.of E))
    (J : pullback (specMap k E) f ≅ Y)
    (hJ : J.hom ≫ g = pullback.fst (specMap k E) f) :
    (scalarExtensionModelIso k E L f g J hJ).hom ≫ pullback.snd (specMap E L) g =
      constantCoverRestriction k E L f ≫ J.hom := by
  simp only [scalarExtensionModelIso, Iso.trans_hom, Iso.symm_hom, asIso_hom,
    coefficientTowerPullbackIso, pullback.map, Category.assoc, pullback.lift_snd,
    pullback.lift_snd_assoc, constantCoverRestriction]

/-- The native pullback open maps to the native pullback compactification. -/
def nativeOpenCompactification
    (k E : Type) [Field k] [Field E] [Algebra k E]
    {C : Scheme} (c : C ⟶ Spec (.of k)) (U : C.Opens) :
    pullback (specMap k E) (U.ι ≫ c) ⟶ pullback (specMap k E) c :=
  pullback.lift (pullback.fst (specMap k E) (U.ι ≫ c))
    (pullback.snd (specMap k E) (U.ι ≫ c) ≫ U.ι) (by
      rw [Category.assoc]
      exact pullback.condition)

/-- This is the same inclusion as the inverse-image open comparison. -/
theorem nativeOpenCompactification_eq
    (k E : Type) [Field k] [Field E] [Algebra k E]
    {C : Scheme} (c : C ⟶ Spec (.of k)) (U : C.Opens) :
    nativeOpenCompactification k E c U =
      (openBaseChangeIso c (specMap k E) U).hom ≫
        (pullback.fst c (specMap k E) ⁻¹ᵁ U).ι ≫
          (pullbackSymmetry c (specMap k E)).hom := by
  apply pullback.hom_ext
  · simp only [nativeOpenCompactification, pullback.lift_fst, Category.assoc,
      pullbackSymmetry_hom_comp_fst]
    exact (openBaseChangeIso_hom_comp_base c (specMap k E) U).symm
  · simp only [nativeOpenCompactification, pullback.lift_snd, Category.assoc,
      pullbackSymmetry_hom_comp_snd]
    exact (openBaseChangeIso_hom_comp_ambient c (specMap k E) U).symm

/-- Restriction of constants respects the actual open inclusion. -/
theorem constantCoverRestriction_open
    (k E L : Type) [Field k] [Field E] [Field L]
    [Algebra k E] [Algebra E L] [Algebra k L] [IsScalarTower k E L]
    {C : Scheme} (c : C ⟶ Spec (.of k)) (U : C.Opens) :
    nativeOpenCompactification k L c U ≫ constantCoverRestriction k E L c =
      constantCoverRestriction k E L (U.ι ≫ c) ≫ nativeOpenCompactification k E c U := by
  apply pullback.hom_ext
  · simp only [constantCoverRestriction, nativeOpenCompactification, Category.assoc,
      pullback.lift_fst, pullback.lift_fst_assoc]
  · simp only [constantCoverRestriction, nativeOpenCompactification, Category.assoc,
      pullback.lift_snd, pullback.lift_snd_assoc]

/-- An actual rational model remains a rational model after enlarging its
constant field; the punctures are the injective extensions of its coordinates. -/
def rationalModelScalarExtensionIso
    (k E L : Type) [Field k] [Field E] [Field L]
    [Algebra k E] [Algebra E L] [Algebra k L] [IsScalarTower k E L]
    {X : Scheme} (f : X ⟶ Spec (.of k))
    (s : Finset (Projectivization E (E × E)))
    (J : pullback (specMap k E) f ≅ (rationalConfigurationOpen s : Scheme))
    (hJ : J.hom ≫ ((rationalConfigurationOpen s).ι ≫ π E 1) =
      pullback.fst (specMap k E) f) :
    pullback (specMap k L) f ≅
      (rationalConfigurationOpen (configurationScalarExtension E L s) : Scheme) :=
  scalarExtensionModelIso k E L f ((rationalConfigurationOpen s).ι ≫ π E 1) J hJ ≪≫
    rationalConfigurationScalarExtensionIso E L s

theorem rationalModelScalarExtensionIso_hom_comp_base
    (k E L : Type) [Field k] [Field E] [Field L]
    [Algebra k E] [Algebra E L] [Algebra k L] [IsScalarTower k E L]
    {X : Scheme} (f : X ⟶ Spec (.of k))
    (s : Finset (Projectivization E (E × E)))
    (J : pullback (specMap k E) f ≅ (rationalConfigurationOpen s : Scheme))
    (hJ : J.hom ≫ ((rationalConfigurationOpen s).ι ≫ π E 1) =
      pullback.fst (specMap k E) f) :
    (rationalModelScalarExtensionIso k E L f s J hJ).hom ≫
        ((rationalConfigurationOpen (configurationScalarExtension E L s)).ι ≫ π L 1) =
      pullback.fst (specMap k L) f := by
  change (_ ≫ (rationalConfigurationScalarExtensionIso E L s).hom) ≫ _ = _
  rw [Category.assoc, rationalConfigurationScalarExtensionIso_hom_base]
  exact scalarExtensionModelIso_hom_comp_base k E L f
    ((rationalConfigurationOpen s).ι ≫ π E 1) J hJ

/-- Enlarge the constant field of the same proper model and open model.
The ambient equation is preserved for the actual base changes of both maps. -/
theorem exists_rationalModelScalarExtension_with_ambient
    (k E L : Type) [Field k] [Field E] [Field L]
    [Algebra k E] [Algebra E L] [Algebra k L] [IsScalarTower k E L]
    {C : Scheme} (c : C ⟶ Spec (.of k)) (U : C.Opens)
    (I : pullback c (specMap k E) ≅ (projectiveLineRatFuncModel E).C)
    (hI : I.hom ≫ (projectiveLineRatFuncModel E).toBase =
      pullback.snd c (specMap k E))
    (s : Finset (Projectivization E (E × E)))
    (J : ((pullback.fst c (specMap k E) ⁻¹ᵁ U) : Scheme) ≅
      (rationalConfigurationOpen s : Scheme))
    (hJ : J.hom ≫ (rationalConfigurationOpen s).ι =
      (pullback.fst c (specMap k E) ⁻¹ᵁ U).ι ≫ I.hom) :
    ∃ IL : pullback c (specMap k L) ≅ (projectiveLineRatFuncModel L).C,
      IL.hom ≫ (projectiveLineRatFuncModel L).toBase =
        pullback.snd c (specMap k L) ∧
      ∃ JL : pullback (specMap k L) (U.ι ≫ c) ≅
          (rationalConfigurationOpen (configurationScalarExtension E L s) : Scheme),
        JL.hom ≫ ((rationalConfigurationOpen (configurationScalarExtension E L s)).ι ≫ π L 1) =
          pullback.fst (specMap k L) (U.ι ≫ c) ∧
        JL.hom ≫ (rationalConfigurationOpen (configurationScalarExtension E L s)).ι =
          (openBaseChangeIso c (specMap k L) U).hom ≫
            (pullback.fst c (specMap k L) ⁻¹ᵁ U).ι ≫ IL.hom ∧
        JL = rationalModelScalarExtensionIso k E L (U.ι ≫ c) s
          (openBaseChangeIso c (specMap k E) U ≪≫ J) (by
            let Ihom : pullback c (specMap k E) ⟶ projectiveLineScheme E := I.hom
            have hIbase : Ihom ≫ π E 1 = pullback.snd c (specMap k E) := hI
            have hJambient : J.hom ≫ (rationalConfigurationOpen s).ι =
                (pullback.fst c (specMap k E) ⁻¹ᵁ U).ι ≫ Ihom := hJ
            change (_ ≫ J.hom) ≫ _ = _
            rw [Category.assoc, ← Category.assoc J.hom, hJambient, Category.assoc, hIbase]
            exact openBaseChangeIso_hom_comp_base c (specMap k E) U) := by
  let Ihom : pullback c (specMap k E) ⟶ projectiveLineScheme E := I.hom
  have hIbase : Ihom ≫ π E 1 = pullback.snd c (specMap k E) := hI
  have hJambient : J.hom ≫ (rationalConfigurationOpen s).ι =
      (pullback.fst c (specMap k E) ⁻¹ᵁ U).ι ≫ Ihom := hJ
  let B := openBaseChangeIso c (specMap k E) U
  let JN := B ≪≫ J
  have hJN : JN.hom ≫ ((rationalConfigurationOpen s).ι ≫ π E 1) =
      pullback.fst (specMap k E) (U.ι ≫ c) := by
    change (B.hom ≫ J.hom) ≫ _ = _
    rw [Category.assoc, ← Category.assoc J.hom, hJambient, Category.assoc, hIbase]
    exact openBaseChangeIso_hom_comp_base c (specMap k E) U
  let IN : pullback (specMap k E) c ≅ projectiveLineScheme E :=
    (pullbackSymmetry c (specMap k E)).symm ≪≫
      (show pullback c (specMap k E) ≅ projectiveLineScheme E from I)
  have hIN : IN.hom ≫ π E 1 = pullback.fst (specMap k E) c := by
    change ((pullbackSymmetry c (specMap k E)).inv ≫ Ihom) ≫ π E 1 = _
    rw [Category.assoc, hIbase, pullbackSymmetry_inv_comp_snd]
  let K := scalarExtensionModelIso k E L c (π E 1) IN hIN
  have hKbase : K.hom ≫ pullback.fst (specMap E L) (π E 1) =
      pullback.fst (specMap k L) c :=
    scalarExtensionModelIso_hom_comp_base k E L c (π E 1) IN hIN
  have hKmodel : K.hom ≫ pullback.snd (specMap E L) (π E 1) =
      constantCoverRestriction k E L c ≫ IN.hom :=
    scalarExtensionModelIso_hom_comp_model k E L c (π E 1) IN hIN
  let P := projectiveLineBaseChangeIso E L
  let N := (pullbackSymmetry (specMap E L) (π E 1)) ≪≫ P.symm
  have hNbase : N.hom ≫ π L 1 = pullback.fst (specMap E L) (π E 1) := by
    change (_ ≫ P.inv) ≫ _ = _
    rw [Category.assoc, ← projectiveLineBaseChangeIso_hom_snd E L,
      P.inv_hom_id_assoc, pullbackSymmetry_hom_comp_snd]
  have hNmap : N.hom ≫ map E L 1 = pullback.snd (specMap E L) (π E 1) := by
    have hPmap : P.hom ≫ pullback.fst (π E 1) (specMap E L) = map E L 1 :=
      (isPullback_map E L 1).isoPullback_hom_fst
    change (_ ≫ P.inv) ≫ _ = _
    rw [Category.assoc, ← hPmap, P.inv_hom_id_assoc, pullbackSymmetry_hom_comp_fst]
  let IL := ((pullbackSymmetry c (specMap k L)) ≪≫ K) ≪≫ N
  have hIL : IL.hom ≫ π L 1 = pullback.snd c (specMap k L) := by
    change ((_ ≫ K.hom) ≫ N.hom) ≫ _ = _
    rw [Category.assoc, hNbase, Category.assoc,
      hKbase, pullbackSymmetry_hom_comp_fst]
  let JL := rationalModelScalarExtensionIso k E L (U.ι ≫ c) s JN hJN
  have hJL : JL.hom ≫
      ((rationalConfigurationOpen (configurationScalarExtension E L s)).ι ≫ π L 1) =
      pullback.fst (specMap k L) (U.ι ≫ c) :=
    rationalModelScalarExtensionIso_hom_comp_base k E L (U.ι ≫ c) s JN hJN
  have hNJI : JN.hom ≫ (rationalConfigurationOpen s).ι =
      nativeOpenCompactification k E c U ≫ IN.hom := by
    rw [nativeOpenCompactification_eq]
    change (B.hom ≫ J.hom) ≫ _ =
      (B.hom ≫ _ ≫ (pullbackSymmetry c (specMap k E)).hom) ≫
        ((pullbackSymmetry c (specMap k E)).inv ≫ Ihom)
    simp only [Category.assoc, hJambient, Iso.hom_inv_id_assoc]
  let OL := nativeOpenCompactification k L c U
  have hleft : (JL.hom ≫
      (rationalConfigurationOpen (configurationScalarExtension E L s)).ι) ≫ map E L 1 =
      constantCoverRestriction k E L (U.ι ≫ c) ≫ JN.hom ≫
        (rationalConfigurationOpen s).ι := by
    let S := scalarExtensionModelIso k E L (U.ι ≫ c)
      ((rationalConfigurationOpen s).ι ≫ π E 1) JN hJN
    let Q := rationalConfigurationScalarExtensionIso E L s
    change ((S.hom ≫ Q.hom) ≫ _) ≫ _ = _
    calc
      ((S.hom ≫ Q.hom) ≫ _) ≫ _ =
          S.hom ≫ (Q.hom ≫ (rationalConfigurationOpen (configurationScalarExtension E L s)).ι) ≫
            map E L 1 := by simp only [Category.assoc]
      _ = S.hom ≫ rationalConfigurationBaseChangeChart E L s ≫ map E L 1 := by
        rw [rationalConfigurationScalarExtensionIso_hom_chart]
      _ = (S.hom ≫ pullback.snd (specMap E L)
          ((rationalConfigurationOpen s).ι ≫ π E 1)) ≫ (rationalConfigurationOpen s).ι := by
        rw [rationalConfigurationBaseChangeChart_comp_map, Category.assoc]
      _ = _ := by rw [scalarExtensionModelIso_hom_comp_model, Category.assoc]
  have hambient : JL.hom ≫ (rationalConfigurationOpen (configurationScalarExtension E L s)).ι =
      OL ≫ K.hom ≫ N.hom := by
    apply (isPullback_map E L 1).hom_ext
    · calc
        (JL.hom ≫ _) ≫ map E L 1 =
            constantCoverRestriction k E L (U.ι ≫ c) ≫ JN.hom ≫
              (rationalConfigurationOpen s).ι := hleft
        _ = constantCoverRestriction k E L (U.ι ≫ c) ≫
            nativeOpenCompactification k E c U ≫ IN.hom := by rw [hNJI]
        _ = OL ≫ constantCoverRestriction k E L c ≫ IN.hom := by
          simpa only [OL, Category.assoc] using congrArg (fun t => t ≫ IN.hom)
            (constantCoverRestriction_open k E L c U).symm
        _ = OL ≫ K.hom ≫ pullback.snd (specMap E L) (π E 1) := by
          rw [hKmodel]
        _ = (OL ≫ K.hom ≫ N.hom) ≫ map E L 1 := by
          rw [Category.assoc, Category.assoc, hNmap]
    · calc
        (JL.hom ≫ _) ≫ π L 1 = pullback.fst (specMap k L) (U.ι ≫ c) := by
          rw [Category.assoc, hJL]
        _ = OL ≫ pullback.fst (specMap k L) c := (pullback.lift_fst _ _ _).symm
        _ = OL ≫ K.hom ≫ pullback.fst (specMap E L) (π E 1) := by
          rw [hKbase]
        _ = (OL ≫ K.hom ≫ N.hom) ≫ π L 1 := by
          rw [Category.assoc, Category.assoc, hNbase]
  have hfinal : OL ≫ K.hom ≫ N.hom =
      (openBaseChangeIso c (specMap k L) U).hom ≫
        (pullback.fst c (specMap k L) ⁻¹ᵁ U).ι ≫
          (((pullbackSymmetry c (specMap k L)).hom ≫ K.hom) ≫ N.hom) := by
    dsimp only [OL]
    rw [nativeOpenCompactification_eq]
    simp only [Category.assoc]
  exact ⟨IL, hIL, JL, hJL, hambient.trans hfinal, rfl⟩

/-- Finite genus-zero splitting in the literal native constant-cover model.
The ambient projective-line model and the open comparison are both retained. -/
theorem exists_native_finiteGalois_rationalConfiguration_model_above
    {k Ω F : Type} [Field k] [Field Ω] [Algebra k Ω] [IsGalois k Ω]
    [IsAlgClosed Ω] [Field F] [Algebra Ω F] [Algebra k F] [IsScalarTower k Ω F]
    [IsCurveOver Ω F] [Algebra.EssFiniteType Ω F]
    (M : CurveModel Ω F) {C : Scheme} [IsIntegral C]
    (c : C ⟶ Spec (.of k)) [IsProper c] [SmoothOfRelativeDimension 1 c]
    [GeometricallyIntegral c]
    (e : M.C ≅ pullback c (specMap k Ω))
    (he : e.hom ≫ pullback.snd c (specMap k Ω) = M.toBase)
    (hg : genusFF Ω F = 0) (U : C.Opens) (hU : (U : Set C).Nonempty)
    (D : FiniteGaloisIntermediateField k Ω) :
    ∃ E : FiniteGaloisIntermediateField k Ω, D ≤ E ∧
      ∃ I : pullback c (specMap k E) ≅ (projectiveLineRatFuncModel E).C,
        I.hom ≫ (projectiveLineRatFuncModel E).toBase =
          pullback.snd c (specMap k E) ∧
        ∃ s : Finset (Projectivization E (E × E)),
          (∀ a, a ∈ s ↔ projectiveRationalPoint a ∉
            Set.range ((pullback.fst c (specMap k E) ⁻¹ᵁ U).ι ≫ I.hom)) ∧
          ∃ J : pullback (specMap k E) (U.ι ≫ c) ≅
              (rationalConfigurationOpen s : Scheme),
            J.hom ≫ (rationalConfigurationOpen s).ι =
              (openBaseChangeIso c (specMap k E) U).hom ≫
                (pullback.fst c (specMap k E) ⁻¹ᵁ U).ι ≫ I.hom ∧
            J.hom ≫ ((rationalConfigurationOpen s).ι ≫ π E 1) =
              pullback.fst (specMap k E) (U.ι ≫ c) := by
  obtain ⟨E, hDE, I, hI, s, hs, J, hJ, hJbase⟩ :=
    exists_finiteGalois_rationalConfiguration_model_above M c e he hg U hU D
  let B := openBaseChangeIso c (specMap k E) U
  refine ⟨E, hDE, I, hI, s, hs, B ≪≫ J, ?_, ?_⟩
  · exact (Category.assoc B.hom J.hom (rationalConfigurationOpen s).ι).trans
      (congrArg (fun t => B.hom ≫ t) hJ)
  · change (B.hom ≫ J.hom) ≫ _ = _
    rw [Category.assoc, hJbase]
    exact openBaseChangeIso_hom_comp_base c (specMap k E) U

end AnabelianGeometry.GeometricFundamentalGroup
