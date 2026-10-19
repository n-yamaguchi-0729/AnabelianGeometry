/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.AnabelianGeometry.WeightFiltration.RecoveredCandidateCyclotomicKernel
import Nyll.SchemeTheory.Pi1.FiniteEtale.Geometry
import Mathlib.RingTheory.Etale.Field

/-! # Candidate kernels after actual finite coefficient refinement -/

noncomputable section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.FiniteEtale
open CategoryTheory.PreGaloisCategory EtaleFundamentalGroups
open EtaleFundamentalGroups.Inertia ProCGroups.Abelian
open AlgebraicGeometry.SmoothProperCurve NeronModelInfra SchemeTheory

namespace AnabelianGeometry.WeightFiltration

private theorem candidateRefinement_congrHom_hom_snd
    {A B D : Scheme} {f₁ f₂ : A ⟶ D} {g₁ g₂ : B ⟶ D}
    (hf : f₁ = f₂) (hg : g₁ = g₂) :
    (Limits.pullback.congrHom hf hg).hom ≫ Limits.pullback.snd f₂ g₂ =
      Limits.pullback.snd f₁ g₁ := by
  simp only [Limits.pullback.congrHom_hom, Limits.pullback.lift_snd,
    Category.comp_id]

/-- A finite coefficient refinement supplies the actual compactification kernel
condition for the same recovered geometric cover and the original roots map.
The section, Picard representation, and weight equality are constructed by
the existing geometric weight owner; none is a comparison hypothesis. -/
theorem exists_finiteIntermediateField_recoveredCandidate_compactificationKernel
    (k E κ : Type) [Field k] [Field E] [NumberField E]
    [Field κ] [CharZero κ] [IsAlgClosed κ]
    [Algebra k E] [Algebra E κ] [Algebra k κ] [IsScalarTower k E κ]
    [IsSepClosure k κ] [IsSepClosure E κ]
    (X : Scheme) [CompactSpace X] [QuasiSeparatedSpace X]
    (f : X ⟶ Spec (.of k))
    [ConnectedSpace (show Scheme from Limits.pullback (specMap k κ) f)]
    {C N : Scheme} [CompactSpace N] [QuasiSeparatedSpace N]
    (c : C ⟶ Spec (.of E)) (j : N ⟶ C) [IsOpenImmersion j]
    [IsProper c] [SmoothOfRelativeDimension 1 c] [GeometricallyIntegral c]
    (a : N ⟶ X) [IsFiniteEtale a]
    (ha : a ≫ f = (j ≫ c) ≫ specMap k E)
    {Ω : Type} [Field Ω] [IsSepClosed Ω]
    (xi : Spec (.of Ω) ⟶ Limits.pullback (specMap k κ) f)
    (W : FiniteEtale (Limits.pullback (specMap k κ) f)) [IsConnected W]
    [IsIntegral W.left] [Algebra W.left.functionField Ω]
    [IsSepClosure W.left.functionField Ω]
    (w : (fiber xi).obj W)
    (hw : W.left.genericExtensionMorphism Ω = (fiberObjEquivHom xi W w).left)
    (R : Limits.pullback (specMap E κ) (j ≫ c) ≅ W.left)
    (hscheme : (R.hom ≫ W.hom) ≫ Limits.pullback.snd (specMap k κ) f =
      Limits.pullback.snd (specMap E κ) (j ≫ c) ≫ a)
    (J : ClosedSubgroup π₁ᵉᵗ(xi ≫ Limits.pullback.snd (specMap k κ) f))
    (hN : IsOpen (((Subgroup.normalizer (J : Set _)).map
      (arithmeticFundamentalGroupHom k κ f
        (xi ≫ Limits.pullback.snd (specMap k κ) f)).toMonoidHom :
          Subgroup Gal(κ/k)) : Set Gal(κ/k)))
    (psiV : (primeToRootsSystem κ κ).inverseLimit →*
      MulAction.stabilizer π₁ᵉᵗ(xi) w)
    (hcycl : ∀ γ ∈ Subgroup.normalizer (J : Set _), ∀ t,
      fundamentalGroupHom (Limits.pullback.snd (specMap k κ) f) xi
        (psiV (primeToRootsCoefficientMap κ κ
          (arithmeticFundamentalGroupHom k κ f
            (xi ≫ Limits.pullback.snd (specMap k κ) f) γ).toRingHom t) : π₁ᵉᵗ(xi)) =
        γ * fundamentalGroupHom (Limits.pullback.snd (specMap k κ) f) xi
          (psiV t : π₁ᵉᵗ(xi)) * γ⁻¹) :
    ∃ (F : IntermediateField E κ) (hF : FiniteDimensional E F),
      letI : FiniteDimensional E F := hF
      let phiF := specMap E F
      let NF : Scheme := Limits.pullback phiF (j ≫ c)
      let CF : Scheme := Limits.pullback c phiF
      let cF : CF ⟶ Spec (.of F) := Limits.pullback.snd c phiF
      let jF : NF ⟶ CF :=
        coefficientModelMap phiF c j ≫ (Limits.pullbackSymmetry phiF c).hom
      ∃ hjF : jF ≫ cF = Limits.pullback.fst phiF (j ≫ c),
        let RF : Limits.pullback (specMap F κ) (jF ≫ cF) ≅ W.left :=
          Limits.pullback.congrHom rfl hjF ≪≫
            constantFieldTowerIso E κ F N (j ≫ c) ≪≫ R
        letI : IsIntegral (show Scheme from
            Limits.pullback (specMap F κ) (jF ≫ cF)) :=
          IsIntegral.of_isIso RF.inv
        let x := W.left.genericExtensionMorphism Ω ≫ RF.inv
        ∃ (hgeo : x ≫ (RF.hom ≫ W.hom) = xi)
          (e : π₁ᵉᵗ(x) ≃ₜ* MulAction.stabilizer π₁ᵉᵗ(xi) w),
          (∀ v, (e v : π₁ᵉᵗ(xi)) =
            pointedFundamentalGroupHom (RF.hom ≫ W.hom) x xi hgeo v) ∧
          ∀ t, TopologicalAbelianization.mk _ (e.symm (psiV t)) ∈
            (compactificationAbelianizationMap
              (coefficientModelMap (specMap F κ) cF jF) x).toMonoidHom.ker := by
  classical
  obtain ⟨F, hF, hjF, _hxF, hweight⟩ :=
    exists_finiteIntermediateField_recovered_compactification_weight
      E κ c j R (Omega := Ω)
  let : FiniteDimensional E F := hF
  let : IsSepClosure F κ :=
    ⟨IsSepClosure.sep_closed E,
      Algebra.isSeparable_tower_top_of_isSeparable E F κ⟩
  let : Algebra k F := ((algebraMap E F).comp (algebraMap k E)).toAlgebra
  let : IsScalarTower k E F := IsScalarTower.of_algebraMap_eq' rfl
  let : IsScalarTower k F κ := by
    apply IsScalarTower.of_algebraMap_eq'
    ext b
    exact IsScalarTower.algebraMap_apply k E κ b
  let phiF := specMap E F
  let NF : Scheme := Limits.pullback phiF (j ≫ c)
  let CF : Scheme := Limits.pullback c phiF
  let cF : CF ⟶ Spec (.of F) := Limits.pullback.snd c phiF
  let jF : NF ⟶ CF :=
    coefficientModelMap phiF c j ≫ (Limits.pullbackSymmetry phiF c).hom
  let RF : Limits.pullback (specMap F κ) (jF ≫ cF) ≅ W.left :=
    Limits.pullback.congrHom rfl hjF ≪≫
      constantFieldTowerIso E κ F N (j ≫ c) ≪≫ R
  let : IsIntegral (show Scheme from Limits.pullback (specMap F κ) (jF ≫ cF)) :=
    IsIntegral.of_isIso RF.inv
  let : CompactSpace NF := inferInstance
  let : QuasiSeparatedSpace NF :=
    quasiSeparatedSpace_of_quasiSeparated (Limits.pullback.snd phiF (j ≫ c))
  let aF : NF ⟶ X := Limits.pullback.snd phiF (j ≫ c) ≫ a
  let : Algebra.Etale E F :=
    ⟨Algebra.FormallyEtale.of_isSeparable E F,
      Algebra.FinitePresentation.of_finiteType.mp inferInstance⟩
  let : IsFiniteEtale phiF := by
    change IsFiniteEtale (Spec.map (CommRingCat.ofHom (algebraMap E F)))
    rw [IsFiniteEtale.SpecMap_iff, CommRingCat.hom_ofHom,
      RingHom.finiteEtale_algebraMap_iff]
    exact ⟨⟩
  let : IsFiniteEtale aF := by
    dsimp only [aF]
    infer_instance
  let pY := Limits.pullback.snd (specMap E κ) (j ≫ c)
  let piN := Limits.pullback.snd phiF (j ≫ c)
  let pYF := Limits.pullback.snd (specMap F κ) (jF ≫ cF)
  let T : Limits.pullback (specMap F κ) (jF ≫ cF) ≅
      Limits.pullback (specMap E κ) (j ≫ c) :=
    Limits.pullback.congrHom rfl hjF ≪≫
      constantFieldTowerIso E κ F N (j ≫ c)
  have hT : T.hom ≫ pY = pYF ≫ piN := by
    let eF : Limits.pullback (specMap F κ) (jF ≫ cF) ≅
        Limits.pullback (specMap F κ) (Limits.pullback.fst phiF (j ≫ c)) :=
      Limits.pullback.congrHom rfl hjF
    have heF : eF.hom ≫
        Limits.pullback.snd (specMap F κ) (Limits.pullback.fst phiF (j ≫ c)) =
          pYF :=
      candidateRefinement_congrHom_hom_snd rfl hjF
    calc
      T.hom ≫ pY = eF.hom ≫
          ((constantFieldTowerIso E κ F N (j ≫ c)).hom ≫ pY) :=
        Category.assoc eF.hom (constantFieldTowerIso E κ F N (j ≫ c)).hom pY
      _ = eF.hom ≫
          (Limits.pullback.snd (specMap F κ)
            (Limits.pullback.fst phiF (j ≫ c)) ≫ piN) :=
        congrArg (fun m => eF.hom ≫ m)
          (constantFieldTowerIso_hom_snd E κ F N (j ≫ c))
      _ = (eF.hom ≫ Limits.pullback.snd (specMap F κ)
          (Limits.pullback.fst phiF (j ≫ c))) ≫ piN :=
        (Category.assoc _ _ _).symm
      _ = pYF ≫ piN := congrArg (fun m => m ≫ piN) heF
  have hschemeF : (RF.hom ≫ W.hom) ≫ Limits.pullback.snd (specMap k κ) f =
      pYF ≫ aF := by
    calc
      (RF.hom ≫ W.hom) ≫ Limits.pullback.snd (specMap k κ) f =
          T.hom ≫ ((R.hom ≫ W.hom) ≫ Limits.pullback.snd (specMap k κ) f) := by
        change (((Limits.pullback.congrHom rfl hjF).hom ≫
          ((constantFieldTowerIso E κ F N (j ≫ c)).hom ≫ R.hom)) ≫ W.hom) ≫
            Limits.pullback.snd (specMap k κ) f =
          ((Limits.pullback.congrHom rfl hjF).hom ≫
            (constantFieldTowerIso E κ F N (j ≫ c)).hom) ≫
              ((R.hom ≫ W.hom) ≫ Limits.pullback.snd (specMap k κ) f)
        simp only [Category.assoc]
      _ = T.hom ≫ (pY ≫ a) := congrArg (fun m => T.hom ≫ m) hscheme
      _ = (T.hom ≫ pY) ≫ a := (Category.assoc _ _ _).symm
      _ = (pYF ≫ piN) ≫ a := congrArg (fun m => m ≫ a) hT
      _ = pYF ≫ aF := Category.assoc _ _ _
  have hphi : phiF ≫ specMap k E = specMap k F := by
    dsimp only [phiF, specMap]
    rw [← Spec.map_comp]
    rfl
  have haF : aF ≫ f = (jF ≫ cF) ≫ specMap k F := by
    calc
      aF ≫ f = piN ≫ (a ≫ f) := Category.assoc _ _ _
      _ = piN ≫ ((j ≫ c) ≫ specMap k E) := congrArg (fun m => piN ≫ m) ha
      _ = (piN ≫ (j ≫ c)) ≫ specMap k E := (Category.assoc _ _ _).symm
      _ = (Limits.pullback.fst phiF (j ≫ c) ≫ phiF) ≫ specMap k E := by
        rw [Limits.pullback.condition]
      _ = Limits.pullback.fst phiF (j ≫ c) ≫ (phiF ≫ specMap k E) :=
        Category.assoc _ _ _
      _ = (jF ≫ cF) ≫ specMap k F := by rw [hphi, hjF]
  let x := W.left.genericExtensionMorphism Ω ≫ RF.inv
  have hxR : x ≫ RF.hom = (fiberObjEquivHom xi W w).left := by
    simpa only [x, Category.assoc, Iso.inv_hom_id, Category.comp_id] using hw
  obtain ⟨hgeo, e, he, hspan⟩ := recoveredCandidate_image_mem_openCyclotomicSpan
    k F κ X f NF (jF ≫ cF) aF haF xi W w (RF.hom ≫ W.hom) hschemeF
      RF rfl x hxR J hN psiV hcycl
  refine ⟨F, hF, hjF, hgeo, e, he, ?_⟩
  intro t
  rw [hweight]
  exact hspan t

end AnabelianGeometry.WeightFiltration
