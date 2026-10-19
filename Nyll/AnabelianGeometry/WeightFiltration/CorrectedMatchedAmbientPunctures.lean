/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/
import Nyll.AnabelianGeometry.WeightFiltration.NamedSquareCorrectedGeometricComparison
import Nyll.AnabelianGeometry.WeightFiltration.CorrectedRationalCuspCorrespondence
import Nyll.AnabelianGeometry.WeightFiltration.MatchedAmbientPunctureCorrespondence
import Nyll.AlgebraicCurves.Models.Rational.PuncturedProjectiveLineAmbientFields
import Nyll.AlgebraicCurves.Models.Rational.PuncturedProjectiveLineGenericPoints

/-!
# Punctures of corrected maps at matched ambient points
-/

noncomputable section
open CategoryTheory AlgebraicGeometry AlgebraicCurve
open AlgebraicGeometry.FiniteEtale AlgebraicGeometry.ProjSpace
open scoped RatFunc
namespace AnabelianGeometry.WeightFiltration
attribute [local instance] MvPolynomial.gradedAlgebra Polynomial.algebra
  rationalConfigurationGeometricFieldAlgebra rationalConfigurationGeometricConstantAlgebra
  rationalConfigurationGeometricField_scalarTower

private theorem originalAmbient_arithmeticPoint
    (k κ : Type) [Field k] [Field κ] [Algebra k κ] [Infinite k]
    (s : Finset (Projectivization k (k × k))) (Ω : Type) [Field Ω]
    [Algebra (rationalConfigurationGeometricScheme k κ s).functionField Ω] :
    let _A : Algebra (RatFunc k) Ω := rationalConfigurationArithmeticAmbientAlgebra k κ s Ω
    rationalConfigurationArithmeticBasePoint k κ s Ω =
      Spec.map (CommRingCat.ofHom (algebraMap (RatFunc k) Ω)) ≫
        rationalConfigurationArithmeticGenericPoint k s := by
  intro A
  let : Algebra (RatFunc κ) Ω := rationalConfigurationGeometricAmbientAlgebra k κ s Ω
  let _ : SMul (RatFunc k) (RatFunc κ) :=
    (inferInstance : Algebra (RatFunc k) (RatFunc κ)).toSMul
  have : IsScalarTower (RatFunc k) (RatFunc κ) Ω :=
    (rationalConfigurationAmbient_scalarTowers k κ s Ω).2.2.2.1
  have hchart : (rationalConfigurationGeometricScheme k κ s).genericExtensionMorphism Ω ≫
      𝟙 (rationalConfigurationGeometricScheme k κ s) =
      Spec.map (CommRingCat.ofHom (algebraMap (RatFunc κ) Ω)) ≫
        rationalConfigurationGeometricGenericPoint k κ s :=
    rationalConfigurationGenericPoint_hchartpoint k κ s (Ω := Ω)
  exact (congrArg (· ≫ Limits.pullback.snd
    (Spec.map (CommRingCat.ofHom (algebraMap k κ)))
    ((rationalConfigurationOpen s).ι ≫ π k 1))
      ((Category.comp_id _).symm.trans hchart)).trans
        (rationalConfigurationGenericPoint_hpoint k κ s)

private theorem originalAmbient_equiv_target
    (k κ : Type) [Field k] [Field κ] [Algebra k κ] [IsSepClosure k κ]
    (X : Scheme) [CompactSpace X] [QuasiSeparatedSpace X]
    (f : X ⟶ Spec (.of k))
    [ConnectedSpace (Limits.pullback
      (Spec.map (CommRingCat.ofHom (algebraMap k κ))) f : Scheme)]
    {Ω : Type} [Field Ω] [IsSepClosed Ω]
    (x₀ x₁ : Spec (.of Ω) ⟶ Limits.pullback
      (Spec.map (CommRingCat.ofHom (algebraMap k κ))) f)
    (z z' : Spec (.of Ω) ⟶ X)
    (h₀ : x₀ ≫ Limits.pullback.snd _ f = z)
    (h₁ : x₁ ≫ Limits.pullback.snd _ f = z) (hz : z = z') :
    commonArithmeticPointGeometricEquiv k κ X f x₀ x₁ z' (h₀.trans hz) (h₁.trans hz) =
      commonArithmeticPointGeometricEquiv k κ X f x₀ x₁ z h₀ h₁ := by
  subst z'
  rfl

private theorem originalAmbient_corrected_geometricMap
    (k κ : Type) [Field k] [Field κ] [Algebra k κ] [IsSepClosure k κ]
    (XS XT : Scheme) [CompactSpace XS] [QuasiSeparatedSpace XS]
    [CompactSpace XT] [QuasiSeparatedSpace XT]
    (fs : XS ⟶ Spec (.of k)) (ft : XT ⟶ Spec (.of k))
    [ConnectedSpace (Limits.pullback
      (Spec.map (CommRingCat.ofHom (algebraMap k κ))) fs : Scheme)]
    [ConnectedSpace (Limits.pullback
      (Spec.map (CommRingCat.ofHom (algebraMap k κ))) ft : Scheme)]
    {Ωs Ωt : Type} [Field Ωs] [Field Ωt] [IsSepClosed Ωs] [IsSepClosed Ωt]
    (xs₀ xs₁ : Spec (.of Ωs) ⟶ Limits.pullback
      (Spec.map (CommRingCat.ofHom (algebraMap k κ))) fs)
    (xt₀ xt₁ : Spec (.of Ωt) ⟶ Limits.pullback
      (Spec.map (CommRingCat.ofHom (algebraMap k κ))) ft)
    (zs : Spec (.of Ωs) ⟶ XS) (zt : Spec (.of Ωt) ⟶ XT)
    (hs₀ : xs₀ ≫ Limits.pullback.snd _ fs = zs)
    (hs₁ : xs₁ ≫ Limits.pullback.snd _ fs = zs)
    (ht₀ : xt₀ ≫ Limits.pullback.snd _ ft = zt)
    (ht₁ : xt₁ ≫ Limits.pullback.snd _ ft = zt)
    (αP : π₁ᵉᵗ(zs) ≃ₜ* π₁ᵉᵗ(zt))
    (β : π₁ᵉᵗ(xs₁) ≃ₜ* π₁ᵉᵗ(xt₁)) (c : π₁ᵉᵗ(zt))
    (hβ : originalAmbientCorrectedComparison (Limits.pullback.snd _ fs)
      (Limits.pullback.snd _ ft) xs₁ xt₁ zs zt hs₁ ht₁ αP β c) :
    let eS := commonArithmeticPointGeometricEquiv k κ XS fs xs₀ xs₁ zs hs₀ hs₁
    let eT := commonArithmeticPointGeometricEquiv k κ XT ft xt₀ xt₁ zt ht₀ ht₁
    let α : π₁ᵉᵗ(xs₀) ≃ₜ* π₁ᵉᵗ(xt₀) := eS.trans (β.trans eT.symm)
    (∀ g, pointedFundamentalGroupHom (Limits.pullback.snd _ ft) xt₀ zt ht₀ (α g) =
      c * αP (pointedFundamentalGroupHom (Limits.pullback.snd _ fs) xs₀ zs hs₀ g) * c⁻¹) ∧
    β = eS.symm.trans (α.trans eT) := by
  intro eS eT α
  change ∀ g, pointedFundamentalGroupHom (Limits.pullback.snd _ ft) xt₁ zt ht₁ (β g) =
    c * αP (pointedFundamentalGroupHom (Limits.pullback.snd _ fs) xs₁ zs hs₁ g) * c⁻¹ at hβ
  constructor
  · intro g
    have hT := commonArithmeticPointGeometricEquiv_projection
      k κ XT ft xt₀ xt₁ zt ht₀ ht₁ (α g)
    change pointedFundamentalGroupHom (Limits.pullback.snd _ ft) xt₁ zt ht₁
      (eT (eT.symm (β (eS g)))) = _ at hT
    rw [eT.apply_symm_apply] at hT
    calc
      pointedFundamentalGroupHom (Limits.pullback.snd _ ft) xt₀ zt ht₀ (α g) =
          pointedFundamentalGroupHom (Limits.pullback.snd _ ft) xt₁ zt ht₁ (β (eS g)) :=
        hT.symm
      _ = c * αP (pointedFundamentalGroupHom
          (Limits.pullback.snd _ fs) xs₁ zs hs₁ (eS g)) * c⁻¹ := hβ (eS g)
      _ = c * αP (pointedFundamentalGroupHom
          (Limits.pullback.snd _ fs) xs₀ zs hs₀ g) * c⁻¹ :=
        congrArg (fun v => c * αP v * c⁻¹)
          (commonArithmeticPointGeometricEquiv_projection k κ XS fs xs₀ xs₁ zs hs₀ hs₁ g)
  · apply ContinuousMulEquiv.ext
    intro g
    change β g = eT (eT.symm (β (eS (eS.symm g))))
    rw [eS.apply_symm_apply, eT.apply_symm_apply]

theorem rationalConfiguration_correctedMatchedMap_same_punctures
    (k κ : Type) [Field k] [NumberField k]
    [Field κ] [CharZero κ] [IsAlgClosed κ] [Algebra k κ] [IsAlgClosure k κ]
    (s t : Finset (Projectivization k (k × k))) (htcard : 3 ≤ t.card)
    (Ωs Ωt : Type) [Field Ωs] [Field Ωt] [IsAlgClosed Ωs] [IsAlgClosed Ωt]
    [AS₀ : Algebra (rationalConfigurationGeometricScheme k κ s).functionField Ωs]
    [AT₀ : Algebra (rationalConfigurationGeometricScheme k κ t).functionField Ωt]
    [HS₀ : IsAlgClosure (rationalConfigurationGeometricScheme k κ s).functionField Ωs]
    [HT₀ : IsAlgClosure (rationalConfigurationGeometricScheme k κ t).functionField Ωt]
    (αP : rationalConfigurationArithmeticGroup k κ s Ωs ≃ₜ*
      rationalConfigurationArithmeticGroup k κ t Ωt)
    (α : rationalConfigurationGeometricGroup k κ s Ωs ≃ₜ*
      rationalConfigurationGeometricGroup k κ t Ωt)
    (hα : ∀ g, rationalConfigurationGeometricInclusion k κ t Ωt (α g) =
      αP (rationalConfigurationGeometricInclusion k κ s Ωs g))
    (σ : s ≃ t)
    (hI : ∀ p : s, ∃ a : rationalConfigurationGeometricGroup k κ t Ωt,
      (rationalConfigurationChosenInertia k κ s Ωs
        (rationalConfigurationBoundaryPlace k κ s p)).map α.toMonoidHom =
      (rationalConfigurationChosenInertia k κ t Ωt
        (rationalConfigurationBoundaryPlace k κ t (σ p))).map
          (MulAut.conj a).toMonoidHom)
    (AS₁ : Algebra (rationalConfigurationGeometricScheme k κ s).functionField Ωs)
    (AT₁ : Algebra (rationalConfigurationGeometricScheme k κ t).functionField Ωt)
    (HS₁ : let : Algebra (rationalConfigurationGeometricScheme k κ s).functionField Ωs := AS₁
      IsAlgClosure (rationalConfigurationGeometricScheme k κ s).functionField Ωs)
    (HT₁ : let : Algebra (rationalConfigurationGeometricScheme k κ t).functionField Ωt := AT₁
      IsAlgClosure (rationalConfigurationGeometricScheme k κ t).functionField Ωt) :
    let _originalSource : Algebra (rationalConfigurationGeometricScheme k κ s).functionField Ωs :=
      AS₀
    let _originalTarget : Algebra (rationalConfigurationGeometricScheme k κ t).functionField Ωt :=
      AT₀
    let zs : Spec (.of Ωs) ⟶ (rationalConfigurationOpen s : Scheme) :=
      @rationalConfigurationArithmeticBasePoint k κ _ _ _ _ s Ωs _ AS₀
    let zt : Spec (.of Ωt) ⟶ (rationalConfigurationOpen t : Scheme) :=
      @rationalConfigurationArithmeticBasePoint k κ _ _ _ _ t Ωt _ AT₀
    let fs : (rationalConfigurationOpen s : Scheme) ⟶ Spec (.of k) :=
      (rationalConfigurationOpen s).ι ≫ π k 1
    let ft : (rationalConfigurationOpen t : Scheme) ⟶ Spec (.of k) :=
      (rationalConfigurationOpen t).ι ≫ π k 1
    let us : Limits.pullback (Spec.map (CommRingCat.ofHom (algebraMap k κ))) fs ⟶
        (rationalConfigurationOpen s : Scheme) :=
      Limits.pullback.snd (Spec.map (CommRingCat.ofHom (algebraMap k κ))) fs
    let ut : Limits.pullback (Spec.map (CommRingCat.ofHom (algebraMap k κ))) ft ⟶
        (rationalConfigurationOpen t : Scheme) :=
      Limits.pullback.snd (Spec.map (CommRingCat.ofHom (algebraMap k κ))) ft
    let xs₁ : Spec (.of Ωs) ⟶ Limits.pullback
        (Spec.map (CommRingCat.ofHom (algebraMap k κ))) fs := by
      let : Algebra (rationalConfigurationGeometricScheme k κ s).functionField Ωs := AS₁
      exact (rationalConfigurationGeometricScheme k κ s).genericExtensionMorphism Ωs
    let xt₁ : Spec (.of Ωt) ⟶ Limits.pullback
        (Spec.map (CommRingCat.ofHom (algebraMap k κ))) ft := by
      let : Algebra (rationalConfigurationGeometricScheme k κ t).functionField Ωt := AT₁
      exact (rationalConfigurationGeometricScheme k κ t).genericExtensionMorphism Ωt
    ∀ (hs : xs₁ ≫ us = zs) (ht : xt₁ ≫ ut = zt)
      (β : π₁ᵉᵗ(xs₁) ≃ₜ* π₁ᵉᵗ(xt₁)) (c : π₁ᵉᵗ(zt)),
      originalAmbientCorrectedComparison us ut xs₁ xt₁ zs zt hs ht αP β c →
    let IS₁ : s → Subgroup (π₁ᵉᵗ(xs₁)) := by
      let : Algebra (rationalConfigurationGeometricScheme k κ s).functionField Ωs := AS₁
      let : IsAlgClosure (rationalConfigurationGeometricScheme k κ s).functionField Ωs := HS₁
      exact fun p => rationalConfigurationChosenInertia k κ s Ωs
        (rationalConfigurationBoundaryPlace k κ s p)
    let IT₁ : t → Subgroup (π₁ᵉᵗ(xt₁)) := by
      let : Algebra (rationalConfigurationGeometricScheme k κ t).functionField Ωt := AT₁
      let : IsAlgClosure (rationalConfigurationGeometricScheme k κ t).functionField Ωt := HT₁
      exact fun p => rationalConfigurationChosenInertia k κ t Ωt
        (rationalConfigurationBoundaryPlace k κ t p)
    ∀ p : s, ∃ a : π₁ᵉᵗ(xt₁), (IS₁ p).map β.toMonoidHom =
      (IT₁ (σ p)).map (MulAut.conj a).toMonoidHom := by
  intro originalSource originalTarget zs zt fs ft us ut xs₁ xt₁ hs ht β c hβ IS₁ IT₁
  let xs₀ : Spec (.of Ωs) ⟶ Limits.pullback
      (Spec.map (CommRingCat.ofHom (algebraMap k κ)))
      ((rationalConfigurationOpen s).ι ≫ π k 1) :=
    (rationalConfigurationGeometricScheme k κ s).genericExtensionMorphism Ωs
  let xt₀ : Spec (.of Ωt) ⟶ Limits.pullback
      (Spec.map (CommRingCat.ofHom (algebraMap k κ)))
      ((rationalConfigurationOpen t).ι ≫ π k 1) :=
    (rationalConfigurationGeometricScheme k κ t).genericExtensionMorphism Ωt
  let eS := commonArithmeticPointGeometricEquiv k κ
    (rationalConfigurationOpen s : Scheme) fs xs₀ xs₁ zs rfl hs
  let eT := commonArithmeticPointGeometricEquiv k κ
    (rationalConfigurationOpen t : Scheme) ft xt₀ xt₁ zt rfl ht
  let α' : π₁ᵉᵗ(xs₀) ≃ₜ* π₁ᵉᵗ(xt₀) := eS.trans (β.trans eT.symm)
  have hcommon := originalAmbient_corrected_geometricMap k κ
    (rationalConfigurationOpen s : Scheme) (rationalConfigurationOpen t : Scheme)
    fs ft xs₀ xs₁ xt₀ xt₁ zs zt rfl hs rfl ht
    αP β c hβ
  have hα' := hcommon.1
  have heq := hcommon.2
  have hc : ∀ g, rationalConfigurationGeometricInclusion k κ t Ωt (α' g) =
      c * rationalConfigurationGeometricInclusion k κ t Ωt (α g) * c⁻¹ := by
    intro g
    have hh := hα' g
    change rationalConfigurationGeometricInclusion k κ t Ωt (α' g) =
      c * αP (rationalConfigurationGeometricInclusion k κ s Ωs g) * c⁻¹ at hh
    exact hh.trans (congrArg (fun v => c * v * c⁻¹) (hα g).symm)
  have hI' := rationalConfiguration_corrected_geometricMap_same_punctures
    k κ s t htcard Ωs Ωt α α' σ hI c hc
  let : Algebra (RatFunc κ) Ωs := rationalConfigurationGeometricAmbientAlgebra k κ s Ωs
  let : Algebra κ Ωs := rationalConfigurationConstantAmbientAlgebra k κ s Ωs
  let : Algebra (RatFunc k) Ωs := rationalConfigurationArithmeticAmbientAlgebra k κ s Ωs
  let : Algebra k Ωs := rationalConfigurationBaseAmbientAlgebra k κ s Ωs
  let : Algebra (RatFunc κ) Ωt := rationalConfigurationGeometricAmbientAlgebra k κ t Ωt
  let : Algebra κ Ωt := rationalConfigurationConstantAmbientAlgebra k κ t Ωt
  let : Algebra (RatFunc k) Ωt := rationalConfigurationArithmeticAmbientAlgebra k κ t Ωt
  let : Algebra k Ωt := rationalConfigurationBaseAmbientAlgebra k κ t Ωt
  have : IsScalarTower k (RatFunc k) Ωs :=
    (rationalConfigurationAmbient_scalarTowers k κ s Ωs).2.2.2.2.2
  have : IsScalarTower k (RatFunc k) Ωt :=
    (rationalConfigurationAmbient_scalarTowers k κ t Ωt).2.2.2.2.2
  have : IsAlgClosure (RatFunc k) Ωs :=
    rationalConfigurationAmbient_isAlgClosure_arithmetic k κ s Ωs
  have : IsAlgClosure (RatFunc k) Ωt :=
    rationalConfigurationAmbient_isAlgClosure_arithmetic k κ t Ωt
  have hrawS := originalAmbient_arithmeticPoint k κ s Ωs
  have hrawT := originalAmbient_arithmeticPoint k κ t Ωt
  have htransport := rationalConfiguration_matchedAmbient_same_puncture_equiv
    k κ s t Ωs Ωt AS₀ AS₁ AT₀ AT₁ HS₀ HS₁ HT₀ HT₁
    hrawS (hs.trans hrawS) hrawT (ht.trans hrawT) α' σ hI'
  have heS := originalAmbient_equiv_target k κ (rationalConfigurationOpen s : Scheme)
    fs xs₀ xs₁ zs _ rfl hs hrawS
  have heT := originalAmbient_equiv_target k κ (rationalConfigurationOpen t : Scheme)
    ft xt₀ xt₁ zt _ rfl ht hrawT
  rw [heS, heT] at htransport
  rw [heq]
  exact htransport

end AnabelianGeometry.WeightFiltration
