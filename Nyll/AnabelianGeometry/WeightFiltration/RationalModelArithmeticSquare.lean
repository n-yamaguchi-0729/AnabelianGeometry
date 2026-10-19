/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.AnabelianGeometry.GeometricFundamentalGroup.FiniteRationalModelBaseChange
import Nyll.AnabelianGeometry.WeightFiltration.NamedModelCoverGroupSquare
import Nyll.EtaleFundamentalGroups.GeometricFiber.ArithmeticConstantFieldCoverGroupTransport
import Nyll.EtaleFundamentalGroups.GeometricFiber.ArithmeticGeometricEquivUniqueness

/-! # The original arithmetic square of the actual rational models

The scalar-extended model and the original finite-cover point determine a
commuting square of pointed morphisms. Thus removing the correction in the
split model gives the original arithmetic square without a further path or
conjugator choice.
-/

noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicCurve
open AlgebraicGeometry.FiniteEtale AlgebraicGeometry.SmoothProperCurve
open AnabelianGeometry.GeometricFundamentalGroup

namespace AnabelianGeometry.WeightFiltration

private theorem pointed_map_congr
    {X Y : Scheme} {Ω : Type} [Field Ω]
    (f g : X ⟶ Y) (h : f = g)
    (x : Spec (.of Ω) ⟶ X) (y : Spec (.of Ω) ⟶ Y)
    (hf : x ≫ f = y) (hg : x ≫ g = y) :
    pointedFundamentalGroupHom f x y hf = pointedFundamentalGroupHom g x y hg := by
  subst g
  rfl

variable (k E κ : Type) [Field k] [Field E] [Field κ]
  [Algebra k E] [Algebra E κ] [Algebra k κ] [IsScalarTower k E κ]
  [IsSepClosure k κ] [IsSepClosed κ]
  [IsFiniteEtale (specMap k E)]

omit [IsSepClosure k κ] in
/-- The pointed model square determines the original geometric-to-arithmetic
map through the actual finite-cover inclusion. -/
theorem scalarExtensionModel_pointed_original_inclusion
    {X S : Scheme} [ConnectedSpace X]
    (f : X ⟶ Spec (.of k)) (gS : S ⟶ Spec (.of E))
    (J : pullback (specMap k E) f ≅ S)
    [ConnectedSpace (pullback (specMap k E) f : Scheme)]
    [ConnectedSpace (pullback (specMap k κ) f : Scheme)]
    {Ω : Type} [Field Ω] [IsSepClosed Ω]
    (x : Spec (.of Ω) ⟶ X)
    (z : Spec (.of Ω) ⟶ pullback (specMap E κ) gS)
    (hfinite : arithmeticConstantFieldLift k E κ f x ≫ J.hom =
      z ≫ pullback.snd (specMap E κ) gS)
    (hJ : J.hom ≫ gS = pullback.fst (specMap k E) f)
    (xκ : Spec (.of Ω) ⟶ pullback (specMap k κ) f)
    (hmodel : xκ ≫ (scalarExtensionModelIso k E κ f gS J hJ).hom = z)
    (hx : xκ ≫ pullback.snd (specMap k κ) f = x) :
    let xE : Spec (.of Ω) ⟶ pullback (specMap k E) f :=
      arithmeticConstantFieldLift k E κ f x
    let eJ := namedModelPointedGroupEquiv J xE
      (z ≫ pullback.snd (specMap E κ) gS) hfinite
    let B := scalarExtensionModelIso k E κ f gS J hJ
    let eB := namedModelPointedGroupEquiv B xκ z hmodel
    ∀ v : π₁ᵉᵗ(xκ),
      pointedFundamentalGroupHom (pullback.snd (specMap k κ) f) xκ x hx v =
        pointedFundamentalGroupHom (pullback.snd (specMap k E) f) xE x
          (arithmeticConstantFieldLift_comp k E κ f x)
          (eJ.symm (fundamentalGroupHom (pullback.snd (specMap E κ) gS) z (eB v))) := by
  intro xE eJ B eB v
  let R := constantCoverRestriction k E κ f
  have hR : xκ ≫ R = xE := by
    apply (cancel_mono J.hom).1
    rw [Category.assoc, ← scalarExtensionModelIso_hom_comp_model k E κ f gS J hJ,
      ← Category.assoc, hmodel]
    exact hfinite.symm
  let r := pointedFundamentalGroupHom R xκ xE hR
  have hsquare : eJ (r v) =
      fundamentalGroupHom (pullback.snd (specMap E κ) gS) z (eB v) := by
    have hright := pointedFundamentalGroupHom_comp R J.hom xκ xE
      (z ≫ pullback.snd (specMap E κ) gS) hR hfinite
    have hleft := pointedFundamentalGroupHom_comp B.hom
      (pullback.snd (specMap E κ) gS) xκ z
      (z ≫ pullback.snd (specMap E κ) gS) hmodel rfl
    have hrv := DFunLike.congr_fun hright v
    have hlv := DFunLike.congr_fun hleft v
    change pointedFundamentalGroupHom J.hom xE _ hfinite (r v) =
      pointedFundamentalGroupHom (R ≫ J.hom) xκ _ _ v at hrv
    change fundamentalGroupHom (pullback.snd (specMap E κ) gS) z
        (pointedFundamentalGroupHom B.hom xκ z hmodel v) =
      pointedFundamentalGroupHom (B.hom ≫ pullback.snd (specMap E κ) gS) xκ _ _ v at hlv
    have hmaps := pointed_map_congr
      (B.hom ≫ pullback.snd (specMap E κ) gS) (R ≫ J.hom)
      (scalarExtensionModelIso_hom_comp_model k E κ f gS J hJ)
      xκ (z ≫ pullback.snd (specMap E κ) gS)
      ((Category.assoc _ _ _).symm.trans (congrArg (· ≫ _) hmodel))
      ((Category.assoc _ _ _).symm.trans ((congrArg (· ≫ _) hR).trans hfinite))
    exact (namedModelPointedGroupEquiv_apply J xE _ hfinite (r v)).trans
      (hrv.trans ((hlv.trans (DFunLike.congr_fun hmaps v)).symm.trans
        (congrArg (fundamentalGroupHom (pullback.snd (specMap E κ) gS) z)
          (namedModelPointedGroupEquiv_apply B xκ z hmodel v).symm)))
  have hcomp := pointedFundamentalGroupHom_comp R
    (pullback.snd (specMap k E) f) xκ xE x hR
    (arithmeticConstantFieldLift_comp k E κ f x)
  have hr := DFunLike.congr_fun hcomp v
  have hprojection : R ≫ pullback.snd (specMap k E) f = pullback.snd (specMap k κ) f :=
    pullback.lift_snd _ _ _
  have hmaps := pointed_map_congr (R ≫ pullback.snd (specMap k E) f)
    (pullback.snd (specMap k κ) f) hprojection xκ x
    ((Category.assoc _ _ _).symm.trans ((congrArg (· ≫ _) hR).trans
      (arithmeticConstantFieldLift_comp k E κ f x))) hx
  have hremove : r v = eJ.symm
      (fundamentalGroupHom (pullback.snd (specMap E κ) gS) z (eB v)) :=
    (eJ.symm_apply_apply (r v)).symm.trans (congrArg eJ.symm hsquare)
  exact (hr.trans (DFunLike.congr_fun hmaps v)).symm.trans
    (congrArg (pointedFundamentalGroupHom (pullback.snd (specMap k E) f)
      xE x (arithmeticConstantFieldLift_comp k E κ f x)) hremove)

/-- A geometric equivalence above the uncorrected finite-model map gives an
equivalence above the original arithmetic map. The two model comparisons are
the actual pointed scalar extensions, so no new comparison is chosen. -/
theorem scalarExtensionModels_original_arithmetic_square
    {Xs Xt Ss St : Scheme} [ConnectedSpace Xs] [ConnectedSpace Xt]
    (fs : Xs ⟶ Spec (.of k)) (ft : Xt ⟶ Spec (.of k))
    (gs : Ss ⟶ Spec (.of E)) (gt : St ⟶ Spec (.of E))
    (Js : pullback (specMap k E) fs ≅ Ss)
    (Jt : pullback (specMap k E) ft ≅ St)
    [ConnectedSpace (pullback (specMap k E) fs : Scheme)]
    [ConnectedSpace (pullback (specMap k E) ft : Scheme)]
    [ConnectedSpace (pullback (specMap k κ) fs : Scheme)]
    [ConnectedSpace (pullback (specMap k κ) ft : Scheme)]
    {Ωs Ωt : Type} [Field Ωs] [Field Ωt] [IsSepClosed Ωs] [IsSepClosed Ωt]
    (xs : Spec (.of Ωs) ⟶ Xs) (xt : Spec (.of Ωt) ⟶ Xt)
    (zs : Spec (.of Ωs) ⟶ pullback (specMap E κ) gs)
    (zt : Spec (.of Ωt) ⟶ pullback (specMap E κ) gt)
    (hfiniteS : arithmeticConstantFieldLift k E κ fs xs ≫ Js.hom =
      zs ≫ pullback.snd (specMap E κ) gs)
    (hfiniteT : arithmeticConstantFieldLift k E κ ft xt ≫ Jt.hom =
      zt ≫ pullback.snd (specMap E κ) gt)
    (hJs : Js.hom ≫ gs = pullback.fst (specMap k E) fs)
    (hJt : Jt.hom ≫ gt = pullback.fst (specMap k E) ft)
    (xsκ : Spec (.of Ωs) ⟶ pullback (specMap k κ) fs)
    (xtκ : Spec (.of Ωt) ⟶ pullback (specMap k κ) ft)
    (hmodelS : xsκ ≫ (scalarExtensionModelIso k E κ fs gs Js hJs).hom = zs)
    (hmodelT : xtκ ≫ (scalarExtensionModelIso k E κ ft gt Jt hJt).hom = zt)
    (hxs : xsκ ≫ pullback.snd (specMap k κ) fs = xs)
    (hxt : xtκ ≫ pullback.snd (specMap k κ) ft = xt)
    (α : π₁ᵉᵗ(xs) ≃ₜ* π₁ᵉᵗ(xt))
    (hα : ∀ v, arithmeticFundamentalGroupHom k κ ft xt (α v) =
      arithmeticFundamentalGroupHom k κ fs xs v) :
    let xsE : Spec (.of Ωs) ⟶ pullback (specMap k E) fs :=
      arithmeticConstantFieldLift k E κ fs xs
    let xtE : Spec (.of Ωt) ⟶ pullback (specMap k E) ft :=
      arithmeticConstantFieldLift k E κ ft xt
    let es := namedModelPointedGroupEquiv Js xsE (zs ≫ pullback.snd (specMap E κ) gs) hfiniteS
    let et := namedModelPointedGroupEquiv Jt xtE (zt ≫ pullback.snd (specMap E κ) gt) hfiniteT
    let Bs := scalarExtensionModelIso k E κ fs gs Js hJs
    let Bt := scalarExtensionModelIso k E κ ft gt Jt hJt
    let bs := namedModelPointedGroupEquiv Bs xsκ zs hmodelS
    let bt := namedModelPointedGroupEquiv Bt xtκ zt hmodelT
    let αE := arithmeticConstantFieldCoverGroupTransport k E κ fs ft xs xt α hα
    let β := es.symm.trans (αE.trans et)
    ∀ (e : π₁ᵉᵗ(zs) ≃ₜ* π₁ᵉᵗ(zt))
      (_he : ∀ v, fundamentalGroupHom (pullback.snd (specMap E κ) gt) zt (e v) =
        β (fundamentalGroupHom (pullback.snd (specMap E κ) gs) zs v)),
      let e₀ := bs.trans (e.trans bt.symm)
      ∀ v, pointedFundamentalGroupHom (pullback.snd (specMap k κ) ft) xtκ xt hxt (e₀ v) =
        α (pointedFundamentalGroupHom (pullback.snd (specMap k κ) fs) xsκ xs hxs v) := by
  intro xsE xtE es et Bs Bt bs bt αE β e he e₀ v
  have hS := scalarExtensionModel_pointed_original_inclusion k E κ fs gs Js
    xs zs hfiniteS hJs xsκ hmodelS hxs v
  have hT := scalarExtensionModel_pointed_original_inclusion k E κ ft gt Jt
    xt zt hfiniteT hJt xtκ hmodelT hxt (e₀ v)
  change _ = pointedFundamentalGroupHom (pullback.snd (specMap k E) ft) xtE xt _
    (et.symm (fundamentalGroupHom (pullback.snd (specMap E κ) gt) zt
      (bt (bt.symm (e (bs v)))))) at hT
  rw [bt.apply_symm_apply, he] at hT
  change _ = pointedFundamentalGroupHom (pullback.snd (specMap k E) ft) xtE xt _
    (et.symm (et (αE (es.symm
      (fundamentalGroupHom (pullback.snd (specMap E κ) gs) zs (bs v)))))) at hT
  have hcancel := congrArg
    (pointedFundamentalGroupHom (pullback.snd (specMap k E) ft) xtE xt
      (arithmeticConstantFieldLift_comp k E κ ft xt))
    (et.symm_apply_apply (αE (es.symm
      (fundamentalGroupHom (pullback.snd (specMap E κ) gs) zs (bs v)))))
  exact (hT.trans hcancel).trans ((arithmeticConstantFieldCoverGroupTransport_inclusion
    k E κ fs ft xs xt α hα
    (es.symm (fundamentalGroupHom (pullback.snd (specMap E κ) gs) zs (bs v)))).trans
      (congrArg α hS.symm))

end AnabelianGeometry.WeightFiltration
