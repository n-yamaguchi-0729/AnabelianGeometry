/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.AnabelianGeometry.GeometricFundamentalGroup.BoundaryModelTransport
import Nyll.AnabelianGeometry.ArithmeticIsomorphisms.OpenBaseChange
import Nyll.AnabelianGeometry.ProjectiveLine.SchemeOpenRestriction
import Nyll.AlgebraicCurves.Models.ConstantExtension.SemilinearTower
import Nyll.SchemeTheory.ProjectiveSpace.PuncturedProjectiveLineBaseChange
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback

/-! # Geometric boundary cardinality of an actual finite rational model

The finite model is extended by its actual pullback square. Both the proper
model and the open model are transported, so the resulting boundary bijection
counts the punctures of the original geometric curve.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicCurve
open AlgebraicGeometry.ProjSpace AlgebraicGeometry.SmoothProperCurve
open AnabelianGeometry.ArithmeticIsomorphisms AnabelianGeometry.ProjectiveLine
open AnabelianGeometry.GeometricFundamentalGroup

attribute [local instance] MvPolynomial.gradedAlgebra

namespace AnabelianGeometry.WeightFiltration

/-- An actual rational model of an open curve supplies the commuting geometric
model isomorphisms after extension of constants. -/
theorem exists_geometric_rationalModel_comparison
    (E κ : Type) [Field E] [Field κ] [Algebra E κ]
    {F : Type} [Field F] [Algebra κ F]
    (M : CurveModel κ F) {C : Scheme} (c : C ⟶ Spec (.of E))
    (e : M.C ≅ pullback c (specMap E κ))
    (he : e.hom ≫ pullback.snd c (specMap E κ) = M.toBase)
    (U : C.Opens) (I : C ≅ (Proj (MvPolynomial.homogeneousSubmodule (Fin 2) E)))
    (hI : I.hom ≫ (π E 1) = c)
    (s : Finset (Projectivization E (E × E)))
    (J : (U : Scheme) ≅ (rationalConfigurationOpen s : Scheme))
    (hJ : J.hom ≫ (rationalConfigurationOpen s).ι = U.ι ≫ I.hom) :
    let V := (e.hom ≫ pullback.fst c (specMap E κ)) ⁻¹ᵁ U
    ∃ Iκ : M.C ≅ (projectiveLineRatFuncModel κ).C,
      Iκ.hom ≫ (projectiveLineRatFuncModel κ).toBase = M.toBase ∧
      ∃ Jκ : (V : Scheme) ≅ pullback (specMap E κ)
          ((rationalConfigurationOpen s).ι ≫ π E 1),
        Jκ.hom ≫ rationalConfigurationBaseChangeChart E κ s = V.ι ≫ Iκ.hom := by
  intro V
  have hJbase : J.hom ≫ ((rationalConfigurationOpen s).ι ≫ π E 1) = U.ι ≫ c := by
    rw [← Category.assoc, hJ, Category.assoc, hI]
  let T : pullback c (specMap E κ) ≅ pullback (π E 1) (specMap E κ) :=
    asIso (pullback.map c (specMap E κ) (π E 1) (specMap E κ)
      I.hom (𝟙 _) (𝟙 _) ((Category.comp_id c).trans hI.symm)
      ((Category.comp_id _).trans (Category.id_comp _).symm))
  have hTfst : T.hom ≫ pullback.fst (π E 1) (specMap E κ) =
      pullback.fst c (specMap E κ) ≫ I.hom :=
    pullback.lift_fst _ _ _
  have hTsnd : T.hom ≫ pullback.snd (π E 1) (specMap E κ) =
      pullback.snd c (specMap E κ) := by
    change pullback.lift _ _ _ ≫ _ = _
    rw [pullback.lift_snd, Category.comp_id]
  let P := projectiveLineBaseChangeIso E κ
  let R : pullback (specMap E κ) (U.ι ≫ c) ≅
      pullback (specMap E κ) ((rationalConfigurationOpen s).ι ≫ π E 1) :=
    asIso (pullback.map (specMap E κ) (U.ι ≫ c)
      (specMap E κ) ((rationalConfigurationOpen s).ι ≫ π E 1)
      (𝟙 _) J.hom (𝟙 _)
      ((Category.comp_id _).trans (Category.id_comp _).symm)
      ((Category.comp_id _).trans hJbase.symm))
  have hRfst : R.hom ≫ pullback.fst (specMap E κ)
      ((rationalConfigurationOpen s).ι ≫ π E 1) =
      pullback.fst (specMap E κ) (U.ι ≫ c) := by
    change pullback.lift _ _ _ ≫ _ = _
    rw [pullback.lift_fst, Category.comp_id]
  have hRsnd : R.hom ≫ pullback.snd (specMap E κ)
      ((rationalConfigurationOpen s).ι ≫ π E 1) =
      pullback.snd (specMap E κ) (U.ι ≫ c) ≫ J.hom :=
    pullback.lift_snd _ _ _
  let W := pullback.fst c (specMap E κ) ⁻¹ᵁ U
  let B := openBaseChangeIso c (specMap E κ) U
  have hBfst : B.hom ≫ W.ι ≫ pullback.fst c (specMap E κ) =
      pullback.snd (specMap E κ) (U.ι ≫ c) ≫ U.ι :=
    openBaseChangeIso_hom_comp_ambient c (specMap E κ) U
  have hBsnd : B.hom ≫ W.ι ≫ pullback.snd c (specMap E κ) =
      pullback.fst (specMap E κ) (U.ι ≫ c) :=
    openBaseChangeIso_hom_comp_base c (specMap E κ) U
  have hPfst : P.hom ≫ pullback.fst (π E 1) (specMap E κ) = map E κ 1 :=
    (isPullback_map E κ 1).isoPullback_hom_fst
  have hPsnd : P.hom ≫ pullback.snd (π E 1) (specMap E κ) = π κ 1 :=
    projectiveLineBaseChangeIso_hom_snd E κ
  have hchart : (R.hom ≫ rationalConfigurationBaseChangeChart E κ s) ≫ P.hom =
      (B.hom ≫ W.ι) ≫ T.hom := by
    apply pullback.hom_ext
    · calc
        ((R.hom ≫ rationalConfigurationBaseChangeChart E κ s) ≫ P.hom) ≫
            pullback.fst (π E 1) (specMap E κ) =
            R.hom ≫ (pullback.snd (specMap E κ)
              ((rationalConfigurationOpen s).ι ≫ π E 1) ≫
                (rationalConfigurationOpen s).ι) := by
          simp only [Category.assoc, hPfst,
            rationalConfigurationBaseChangeChart_comp_map]
        _ = pullback.snd (specMap E κ) (U.ι ≫ c) ≫ (U.ι ≫ I.hom) := by
          simpa only [Category.assoc, hJ] using
            congrArg (fun a => a ≫ (rationalConfigurationOpen s).ι) hRsnd
        _ = ((B.hom ≫ W.ι) ≫ T.hom) ≫
            pullback.fst (π E 1) (specMap E κ) := by
          simpa only [Category.assoc, hTfst] using
            (congrArg (fun a => a ≫ I.hom) hBfst).symm
    · calc
        ((R.hom ≫ rationalConfigurationBaseChangeChart E κ s) ≫ P.hom) ≫
            pullback.snd (π E 1) (specMap E κ) =
            pullback.fst (specMap E κ) (U.ι ≫ c) := by
          simp only [Category.assoc, hPsnd,
            rationalConfigurationBaseChangeChart_comp_π, hRfst]
        _ = ((B.hom ≫ W.ι) ≫ T.hom) ≫
            pullback.snd (π E 1) (specMap E κ) := by
          simpa only [Category.assoc, hTsnd] using hBsnd.symm
  have hV : e.hom ⁻¹ᵁ W = V :=
    (Scheme.Hom.comp_preimage e.hom (pullback.fst c (specMap E κ)) U).symm
  let A := restrictSchemeIso e V W hV
  have hA : A.hom ≫ W.ι = V.ι ≫ e.hom :=
    restrictSchemeIso_hom_ι e V W hV
  let Iκ := (e ≪≫ T) ≪≫ P.symm
  let Jκ := (A ≪≫ B.symm) ≪≫ R
  refine ⟨Iκ, ?_, Jκ, ?_⟩
  · change ((e.hom ≫ T.hom) ≫ P.inv) ≫ π κ 1 = M.toBase
    rw [Category.assoc, ← hPsnd, ← Category.assoc P.inv P.hom,
      P.inv_hom_id, Category.id_comp, Category.assoc, hTsnd]
    exact he
  · change ((A.hom ≫ B.inv) ≫ R.hom) ≫
      rationalConfigurationBaseChangeChart E κ s =
        V.ι ≫ ((e.hom ≫ T.hom) ≫ P.inv)
    apply (cancel_mono P.hom).mp
    calc
      (((A.hom ≫ B.inv) ≫ R.hom) ≫
          rationalConfigurationBaseChangeChart E κ s) ≫ P.hom =
          A.hom ≫ (B.inv ≫ ((B.hom ≫ W.ι) ≫ T.hom)) := by
        simpa only [Category.assoc] using
          congrArg (fun a => (A.hom ≫ B.inv) ≫ a) hchart
      _ = (V.ι ≫ e.hom) ≫ T.hom := by
        simpa only [Category.assoc, B.inv_hom_id_assoc] using
          congrArg (fun a => a ≫ T.hom) hA
      _ = (V.ι ≫ ((e.hom ≫ T.hom) ≫ P.inv)) ≫ P.hom := by
        simp only [Category.assoc, P.inv_hom_id, Category.comp_id]

/-- An actual rational model has the same number of punctures as the geometric
boundary of the original model, with no rationality assumption on that boundary
over the original field. -/
theorem rationalModel_card_eq_geometric_boundary_card
    (E κ : Type) [Field E] [Field κ] [Algebra E κ]
    {F : Type} [Field F] [Algebra κ F]
    (M : CurveModel κ F) {C : Scheme} (c : C ⟶ Spec (.of E))
    (e : M.C ≅ pullback c (specMap E κ))
    (he : e.hom ≫ pullback.snd c (specMap E κ) = M.toBase)
    (U : C.Opens) (I : C ≅ (Proj (MvPolynomial.homogeneousSubmodule (Fin 2) E)))
    (hI : I.hom ≫ (π E 1) = c)
    (s : Finset (Projectivization E (E × E)))
    (J : (U : Scheme) ≅ (rationalConfigurationOpen s : Scheme))
    (hJ : J.hom ≫ (rationalConfigurationOpen s).ι = U.ι ≫ I.hom) :
    s.card = Nat.card (M.openBoundaryPlaces
      (((e.hom ≫ pullback.fst c (specMap E κ)) ⁻¹ᵁ U).ι)) := by
  obtain ⟨Iκ, _hIκ, Jκ, hJκ⟩ :=
    exists_geometric_rationalModel_comparison E κ M c e he U I hI s J hJ
  exact rationalConfiguration_card_eq_boundary_card M _ s Iκ Jκ hJκ

/-- Apply the geometric comparison to a finite model inside a constant tower.
Its puncture cardinality is the boundary cardinality of the original curve,
not merely the cardinality of the intermediate finite model. -/
theorem finiteRationalModel_card_eq_original_boundary_card
    (k E κ : Type) [Field k] [Field E] [Field κ]
    [Algebra k E] [Algebra E κ] [Algebra k κ] [IsScalarTower k E κ]
    {F : Type} [Field F] [Algebra κ F]
    (M : CurveModel κ F) {C : Scheme} (c : C ⟶ Spec (.of k))
    (e : M.C ≅ pullback c (specMap k κ))
    (he : e.hom ≫ pullback.snd c (specMap k κ) = M.toBase)
    (U : C.Opens)
    (I : pullback c (specMap k E) ≅ (Proj (MvPolynomial.homogeneousSubmodule (Fin 2) E)))
    (hI : I.hom ≫ (π E 1) =
      pullback.snd c (specMap k E))
    (s : Finset (Projectivization E (E × E)))
    (J : ((pullback.fst c (specMap k E) ⁻¹ᵁ U) : Scheme) ≅
      (rationalConfigurationOpen s : Scheme))
    (hJ : J.hom ≫ (rationalConfigurationOpen s).ι =
      (pullback.fst c (specMap k E) ⁻¹ᵁ U).ι ≫ I.hom) :
    s.card = Nat.card (M.openBoundaryPlaces
      (((e.hom ≫ pullback.fst c (specMap k κ)) ⁻¹ᵁ U).ι)) := by
  let cE := pullback.snd c (specMap k E)
  let eE := M.constantTowerModelIso k E κ c e
  have heE := M.constantTowerModelIso_base k E κ c e he
  have hprojection :
      (eE.hom ≫ pullback.fst cE (specMap E κ)) ≫ pullback.fst c (specMap k E) =
        e.hom ≫ pullback.fst c (specMap k κ) := by
    change ((e.hom ≫ (Scheme.constantBaseChangeTowerIso k E κ c).inv) ≫
      pullback.fst cE (specMap E κ)) ≫ pullback.fst c (specMap k E) = _
    rw [Category.assoc, Category.assoc, ← Scheme.constantBaseChangeTowerIso_fst,
      (Scheme.constantBaseChangeTowerIso k E κ c).inv_hom_id_assoc]
  have hopen : (eE.hom ≫ pullback.fst cE (specMap E κ)) ⁻¹ᵁ
      (pullback.fst c (specMap k E) ⁻¹ᵁ U) =
        (e.hom ≫ pullback.fst c (specMap k κ)) ⁻¹ᵁ U := by
    rw [← Scheme.Hom.comp_preimage, hprojection]
  have hcard := rationalModel_card_eq_geometric_boundary_card E κ M cE eE heE
    (pullback.fst c (specMap k E) ⁻¹ᵁ U) I hI s J hJ
  rw [hopen] at hcard
  exact hcard

end AnabelianGeometry.WeightFiltration
