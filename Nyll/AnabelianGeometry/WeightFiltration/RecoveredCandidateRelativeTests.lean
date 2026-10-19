/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.AnabelianGeometry.WeightFiltration.RecoveredCandidateFiniteRefinement
import Nyll.AnabelianGeometry.WeightFiltration.RecoveredCoverRelativeKernel
import Nyll.EtaleFundamentalGroups.GeometricFiber.RecoveredCoverConstantSquare

/-! # Relative inertia tests in the actual recovered cover -/

noncomputable section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.FiniteEtale AlgebraicCurve
open CategoryTheory.PreGaloisCategory EtaleFundamentalGroups TopologicalSpace
open EtaleFundamentalGroups.Inertia ProCGroups.Abelian
open AnabelianGeometry.CuspidalInertia
open AlgebraicGeometry.SmoothProperCurve NeronModelInfra SchemeTheory

namespace AnabelianGeometry.WeightFiltration

private theorem candidate_map_mem_relativeRelation
    {G H : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [Group H] [TopologicalSpace H] [IsTopologicalGroup H]
    (f : G →ₜ* H) (hf : Function.Surjective f)
    (S : Set G) (T : Set H) (hST : ∀ g ∈ S, f g ∈ T)
    {g : G} (hg : g ∈ (Subgroup.closure S ⊔ commutator G).topologicalClosure) :
    f g ∈ (Subgroup.closure T ⊔ commutator H).topologicalClosure := by
  let B := (Subgroup.closure T ⊔ commutator H).topologicalClosure
  have hclosed : IsClosed (B.comap f.toMonoidHom : Set G) :=
    (Subgroup.closure T ⊔ commutator H).isClosed_topologicalClosure.preimage
      f.continuous_toFun
  have hle : Subgroup.closure S ⊔ commutator G ≤ B.comap f.toMonoidHom := by
    apply sup_le
    · apply (Subgroup.closure_le (B.comap f.toMonoidHom)).mpr
      intro a ha
      exact (Subgroup.closure T ⊔ commutator H).le_topologicalClosure
        ((show Subgroup.closure T ≤ Subgroup.closure T ⊔ commutator H from
          le_sup_left) (Subgroup.subset_closure (hST a ha)))
    · intro a ha
      have hfa : f a ∈ (commutator G).map f.toMonoidHom := ⟨a, ha, rfl⟩
      rw [map_commutator_eq, MonoidHom.range_eq_top.mpr hf] at hfa
      exact (Subgroup.closure T ⊔ commutator H).le_topologicalClosure
        ((show commutator H ≤ Subgroup.closure T ⊔ commutator H from
          le_sup_right) hfa)
  exact (Subgroup.closure S ⊔ commutator G).topologicalClosure_minimal hle hclosed hg

attribute [local instance]
  placeBaseAmbientAlgebra placeBaseAmbientTower
  extendingPlaceAmbientAlgebra extendingPlaceAmbientTower
  connectedCoverPlaceConstantAmbientTower

variable
    (k E κ : Type) [Field k] [Field E] [NumberField E]
    [Field κ] [CharZero κ] [IsAlgClosed κ]
    [Algebra k E] [Algebra E κ] [Algebra k κ] [IsScalarTower k E κ]
    [IsSepClosure k κ] [IsSepClosure E κ]
    (X : Scheme) [CompactSpace X] [QuasiSeparatedSpace X]
    (f : X ⟶ Spec (.of k))

/-- Every value of the original roots map passes the actual relative test in
this prescribed connected cover. Finite coefficient refinement, the proper
kernel, and the relative-kernel equality are constructed in the proof. -/
theorem recoveredCandidate_mem_relativeRelation
    [IsIntegral (Limits.pullback (specMap k κ) f : Scheme)] [IsNormalIntegral (Limits.pullback
      (specMap k κ) f : Scheme)] [IsLocallyNoetherian (Limits.pullback (specMap k κ) f : Scheme)]
    [ConnectedSpace (Limits.pullback (specMap k κ) f : Scheme)] [CompactSpace (Limits.pullback
      (specMap k κ) f : Scheme)]
    [Algebra κ ((Limits.pullback (specMap k κ) f : Scheme)).functionField] [IsCurveOver κ
      ((Limits.pullback (specMap k κ) f : Scheme)).functionField]
    {Ω : Type} [Field Ω] [IsSepClosed Ω]
    [Algebra ((Limits.pullback (specMap k κ) f : Scheme)).functionField Ω] [IsSepClosure
      ((Limits.pullback (specMap k κ) f : Scheme)).functionField Ω]
    [Algebra κ Ω] [IsScalarTower κ ((Limits.pullback (specMap k κ) f : Scheme)).functionField Ω]
    (M : CurveModel κ ((Limits.pullback (specMap k κ) f : Scheme)).functionField)
    (jU : (Limits.pullback (specMap k κ) f : Scheme) ⟶ M.C) [IsOpenImmersion jU]
    [QuasiCompact jU] [QuasiSeparated jU]
    (hjU : DenseRange jU)
    (hfield : algebraMap ((Limits.pullback (specMap k κ) f : Scheme)).functionField
      ((Limits.pullback (specMap k κ) f : Scheme)).functionField =
      (jU.functionFieldMap hjU).comp M.ffEquiv.toRingHom)
    (hUbase : jU ≫ M.toBase = Limits.pullback.fst (specMap k κ) f)
    (Qfamily : ∀ p : M.openBoundaryPlaces jU,
      Ideal (normalizationCommAlgCat p.val.toValuationSubring Ω))
    [hQfamily : ∀ p, (Qfamily p).IsMaximal]
    {C N : Scheme} [CompactSpace N] [QuasiSeparatedSpace N]
    (c : C ⟶ Spec (.of E)) (j : N ⟶ C) [IsOpenImmersion j]
    [IsProper c] [SmoothOfRelativeDimension 1 c] [GeometricallyIntegral c]
    (a : N ⟶ X) [IsFiniteEtale a]
    (ha : a ≫ f = (j ≫ c) ≫ specMap k E)
    (W : FiniteEtale (Limits.pullback (specMap k κ) f : Scheme)) [IsConnected W]
    [IsIntegral W.left] [Algebra W.left.functionField Ω]
    [IsSepClosure W.left.functionField Ω]
    (w : (fiber (((Limits.pullback (specMap k κ) f : Scheme)).genericExtensionMorphism Ω)).obj W)
    (hw : W.left.genericExtensionMorphism Ω =
      (fiberObjEquivHom (((Limits.pullback (specMap k κ) f : Scheme)).genericExtensionMorphism Ω)
        W w).left)
    (R : Limits.pullback (specMap E κ) (j ≫ c) ≅ W.left)
    (hscheme : (R.hom ≫ W.hom) ≫ Limits.pullback.snd (specMap k κ) f =
      Limits.pullback.snd (specMap E κ) (j ≫ c) ≫ a)
    (hRbase : (R.hom ≫ W.hom) ≫ Limits.pullback.fst (specMap k κ) f =
      Limits.pullback.fst (specMap E κ) (j ≫ c))
    (J : ClosedSubgroup π₁ᵉᵗ(((Limits.pullback (specMap k κ) f : Scheme)).genericExtensionMorphism
      Ω ≫
      Limits.pullback.snd (specMap k κ) f))
    (hN : IsOpen (((Subgroup.normalizer (J : Set _)).map
      (arithmeticFundamentalGroupHom k κ f
        (((Limits.pullback (specMap k κ) f : Scheme)).genericExtensionMorphism Ω ≫
          Limits.pullback.snd (specMap k κ) f)).toMonoidHom :
          Subgroup Gal(κ/k)) : Set Gal(κ/k)))
    (psiV : (primeToRootsSystem κ κ).inverseLimit →*
      MulAction.stabilizer π₁ᵉᵗ(((Limits.pullback (specMap k κ) f :
        Scheme)).genericExtensionMorphism Ω) w)
    (hcycl : ∀ γ ∈ Subgroup.normalizer (J : Set _), ∀ t,
      fundamentalGroupHom (Limits.pullback.snd (specMap k κ) f)
        (((Limits.pullback (specMap k κ) f : Scheme)).genericExtensionMorphism Ω)
        (psiV (primeToRootsCoefficientMap κ κ
          (arithmeticFundamentalGroupHom k κ f
            (((Limits.pullback (specMap k κ) f : Scheme)).genericExtensionMorphism Ω ≫
              Limits.pullback.snd (specMap k κ) f)
              γ).toRingHom t) : π₁ᵉᵗ(((Limits.pullback (specMap k κ) f :
                Scheme)).genericExtensionMorphism Ω)) =
        γ * fundamentalGroupHom (Limits.pullback.snd (specMap k κ) f)
          (((Limits.pullback (specMap k κ) f : Scheme)).genericExtensionMorphism Ω) (psiV t :
            π₁ᵉᵗ(((Limits.pullback (specMap k κ) f : Scheme)).genericExtensionMorphism Ω)) * γ⁻¹)
            :
    ∀ t, psiV t ∈
      (Subgroup.closure
        {v : MulAction.stabilizer π₁ᵉᵗ(((Limits.pullback (specMap k κ) f :
          Scheme)).genericExtensionMorphism Ω) w |
          (v : π₁ᵉᵗ(((Limits.pullback (specMap k κ) f : Scheme)).genericExtensionMorphism Ω)) ∈
            conjugacySaturation (⋃ p : M.openBoundaryPlaces jU,
              (show Subgroup π₁ᵉᵗ(((Limits.pullback (specMap k κ) f :
                Scheme)).genericExtensionMorphism Ω) from
                genericPlaceInertia (Limits.pullback (specMap k κ) f : Scheme) p.val (Qfamily
                  p)).carrier)} ⊔
        commutator (MulAction.stabilizer π₁ᵉᵗ(((Limits.pullback (specMap k κ) f :
          Scheme)).genericExtensionMorphism Ω) w)).topologicalClosure := by
  classical
  let xi := ((Limits.pullback (specMap k κ) f : Scheme)).genericExtensionMorphism Ω
  obtain ⟨F, hF, hjF, hgeo, e, he, hkernel⟩ :=
    exists_finiteIntermediateField_recoveredCandidate_compactificationKernel
      k E κ X f c j a ha xi W w hw R hscheme J hN psiV hcycl
  let : FiniteDimensional E F := hF
  let phiF := specMap E F
  let NF : Scheme := Limits.pullback phiF (j ≫ c)
  let CF : Scheme := Limits.pullback c phiF
  let cF : CF ⟶ Spec (.of F) := Limits.pullback.snd c phiF
  let jF : NF ⟶ CF :=
    coefficientModelMap phiF c j ≫ (Limits.pullbackSymmetry phiF c).hom
  let RF : Limits.pullback (specMap F κ) (jF ≫ cF) ≅ W.left :=
    Limits.pullback.congrHom rfl hjF ≪≫
      constantFieldTowerIso E κ F N (j ≫ c) ≪≫ R
  let Y : Scheme := Limits.pullback (specMap F κ) (jF ≫ cF)
  let : IsIntegral Y := IsIntegral.of_isIso RF.inv
  let x : Spec (.of Ω) ⟶ Y := W.left.genericExtensionMorphism Ω ≫ RF.inv
  let Cbar : Scheme := Limits.pullback (specMap F κ) cF
  let cbar : Cbar ⟶ Spec (.of κ) := Limits.pullback.fst (specMap F κ) cF
  let jbar : Y ⟶ Cbar := coefficientModelMap (specMap F κ) cF jF
  let aGeo : Y ⟶ (Limits.pullback (specMap k κ) f : Scheme) := RF.hom ≫ W.hom
  let : IsFiniteEtale (show W.left ⟶ (Limits.pullback (specMap k κ) f : Scheme) from W.hom) :=
    W.prop
  let : IsIso (show Y ⟶ W.left from RF.hom) := RF.isIso_hom
  let hRFet : IsFiniteEtale (show Y ⟶ W.left from RF.hom) :=
    @IsFiniteEtale.mk _ _ _ inferInstance inferInstance
  let : IsFiniteEtale aGeo :=
    MorphismProperty.comp_mem (show MorphismProperty Scheme from @IsFiniteEtale)
      (show Y ⟶ W.left from RF.hom)
      (show W.left ⟶ (Limits.pullback (specMap k κ) f : Scheme) from W.hom)
      hRFet W.prop
  let : IsIntegral (Limits.pullback cF (specMap F κ)) :=
    isIntegral_pullback_Spec_field F cF (specMap F κ)
  let : IsIntegral Cbar :=
    IsIntegral.of_isIso (Limits.pullbackSymmetry cF (specMap F κ)).hom
  let : IsOpenImmersion jF := by
    dsimp only [jF]
    let : IsOpenImmersion (coefficientModelMap phiF c j) :=
      MorphismProperty.IsStableUnderBaseChange.of_isPullback
        (P := (show MorphismProperty Scheme from @IsOpenImmersion))
        (coefficientBaseChange_isPullback phiF c j).flip inferInstance
    infer_instance
  let : IsOpenImmersion jbar :=
    MorphismProperty.IsStableUnderBaseChange.of_isPullback
      (P := (show MorphismProperty Scheme from @IsOpenImmersion))
      (coefficientBaseChange_isPullback (specMap F κ) cF jF).flip inferInstance
  have hRFbase : aGeo ≫ Limits.pullback.fst (specMap k κ) f =
      Limits.pullback.fst (specMap F κ) (jF ≫ cF) := by
    exact refinedRecovery_constantSquare E κ F (j ≫ c) R
      W.hom (Limits.pullback.fst (specMap k κ) f) hRbase jF cF hjF
  have hjbar : jbar ≫ cbar = aGeo ≫ jU ≫ M.toBase := by
    calc
      jbar ≫ cbar = Limits.pullback.fst (specMap F κ) (jF ≫ cF) :=
        Limits.pullback.lift_fst _ _ _
      _ = aGeo ≫ Limits.pullback.fst (specMap k κ) f := hRFbase.symm
      _ = aGeo ≫ (jU ≫ M.toBase) := congrArg (fun q => aGeo ≫ q) hUbase.symm
  have hrelative := finiteEtale_relativeRelation_eq_compactificationKernel_at_point
    M jU hjU hfield Qfamily aGeo cbar jbar hjbar x hgeo
  let S : Set π₁ᵉᵗ(xi) := conjugacySaturation
    (⋃ p : M.openBoundaryPlaces jU, (show Subgroup π₁ᵉᵗ(xi) from
        genericPlaceInertia (Limits.pullback (specMap k κ) f : Scheme) p.val (Qfamily p)).carrier)
  let V : Subgroup π₁ᵉᵗ(xi) := MulAction.stabilizer π₁ᵉᵗ(xi) w
  let i : π₁ᵉᵗ(x) →* π₁ᵉᵗ(xi) :=
    (pointedFundamentalGroupHom aGeo x xi hgeo).toMonoidHom
  have hrelative' :
      (Subgroup.closure {v : π₁ᵉᵗ(x) | i v ∈ S} ⊔
        commutator π₁ᵉᵗ(x)).topologicalClosure =
      ((compactificationAbelianizationMap jbar x).toMonoidHom.ker).comap
        (TopologicalAbelianization.mk π₁ᵉᵗ(x)) := hrelative
  let econt : π₁ᵉᵗ(x) →ₜ* V :=
    { toMonoidHom := e.toMonoidHom, continuous_toFun := e.continuous_toFun }
  intro t
  have ht : e.symm (psiV t) ∈
      (Subgroup.closure {v : π₁ᵉᵗ(x) | i v ∈ S} ⊔ commutator π₁ᵉᵗ(x)).topologicalClosure := by
    exact hrelative'.ge (hkernel t)
  have hmap : ∀ v ∈ {v : π₁ᵉᵗ(x) | i v ∈ S},
      econt v ∈ {v : V | (v : π₁ᵉᵗ(xi)) ∈ S} := by
    intro v hv
    change (e v : π₁ᵉᵗ(xi)) ∈ S
    rw [he]
    exact hv
  have htV := candidate_map_mem_relativeRelation econt e.surjective
    {v : π₁ᵉᵗ(x) | i v ∈ S} {v : V | (v : π₁ᵉᵗ(xi)) ∈ S} hmap ht
  have hround : econt (e.symm (psiV t)) = psiV t := by
    change e (e.symm (psiV t)) = psiV t
    exact e.apply_symm_apply (psiV t)
  have htV' : psiV t ∈
      (Subgroup.closure {v : V | (v : π₁ᵉᵗ(xi)) ∈ S} ⊔
        commutator V).topologicalClosure := hround ▸ htV
  exact htV'

end AnabelianGeometry.WeightFiltration
