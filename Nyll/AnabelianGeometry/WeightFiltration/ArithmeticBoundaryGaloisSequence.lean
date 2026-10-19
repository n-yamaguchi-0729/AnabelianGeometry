/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.AnabelianGeometry.WeightFiltration.ArithmeticBoundaryTateSequence
import Nyll.AnabelianGeometry.WeightFiltration.BoundaryCoefficientEquivariance
import Nyll.ProCGroups.Topologies.ContinuousMulEquiv

/-!
# The boundary exact sequence as continuous arithmetic Galois groups

Transport the original action on the compactification kernel through the
existing boundary quotient isomorphism. A single source correction yields
the actual place and root formulas, without imposing a multiplication law
on independently chosen semilinear lifts.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits AlgebraicCurve
open AlgebraicGeometry.FiniteEtale AlgebraicGeometry.SmoothProperCurve
open AlgebraicGeometry.RelPicard NeronModelInfra GoodReductionJacobian
open SchemeTheory EtaleFundamentalGroups.Inertia
open ProCGroups.Abelian

namespace AnabelianGeometry.WeightFiltration

variable
    (k K : Type) [Field k] [Field K] [CharZero K] [IsAlgClosed K]
    [Algebra k K] [IsSepClosure k K]
    {C U : Scheme} [CompactSpace U] [QuasiSeparatedSpace U]
    (c : C ⟶ Spec (.of k)) (i : U ⟶ C)


variable
    [IsIntegral (Limits.pullback (specMap k K) (i ≫ c))] [CompactSpace ↑(Limits.pullback (specMap
      k K) (i ≫ c))]
    {F : Type} [Field F] [Algebra K F]
    (M : CurveModel K F)
    (eC : M.C ≅ pullback c (specMap k K))
    (heC : eC.hom ≫ pullback.snd c (specMap k K) = M.toBase)
    (j : (Limits.pullback (specMap k K) (i ≫ c)) ⟶ M.C) [IsOpenImmersion j] (hj : DenseRange j)
    (hproj : j ≫ eC.hom ≫ pullback.fst c (specMap k K) = pullback.snd (specMap k K) (i ≫ c) ≫ i)
    (hbase : j ≫ M.toBase = pullback.fst (specMap k K) (i ≫ c))
    [Algebra F (Limits.pullback (specMap k K) (i ≫ c)).functionField]
    (hfield : algebraMap F (Limits.pullback (specMap k K) (i ≫ c)).functionField =
      (j.functionFieldMap hj).comp M.ffEquiv.toRingHom)
    {Ω : Type} [Field Ω] [Algebra (Limits.pullback (specMap k K) (i ≫ c)).functionField Ω]
      [Algebra F Ω]
    [IsScalarTower F (Limits.pullback (specMap k K) (i ≫ c)).functionField Ω]
    [IsSepClosed Ω] [IsSepClosure (Limits.pullback (specMap k K) (i ≫ c)).functionField Ω]
      [IsSepClosure F Ω]
    [∀ p : M.openBoundaryPlaces j, Algebra p.val.toValuationSubring Ω]
    [∀ p : M.openBoundaryPlaces j, IsScalarTower p.val.toValuationSubring F Ω]
    [Algebra K Ω]
    [∀ p : M.openBoundaryPlaces j, IsScalarTower K p.val.toValuationSubring Ω]
    (Q : ∀ p : M.openBoundaryPlaces j,
      Ideal (normalizationCommAlgCat p.val.toValuationSubring Ω))
    [∀ p, (Q p).IsMaximal]

variable
    [CompactSpace C] [QuasiSeparatedSpace C]
    [IsProper c] [SmoothOfRelativeDimension 1 c] [GeometricallyIntegral c]
    [Algebra.EssFiniteType K F] [IsCurveOver K F] [IsAlgClosed Ω]
    [Fintype (M.openBoundaryPlaces j)]

include eC heC hproj hbase in
/-- The original boundary quotient, geometric abelianization, and Jacobian
Tate module form an exact sequence of continuous Galois groups. -/
theorem exists_arithmetic_boundary_Galois_sequence
    (ε : SchemeHomOver (𝟙 (Spec (.of k))) c)
    (D : RelativePic0Designation k c)
    (hD : RepresentsRelSubPic c ε (algEquivZeroCut c ε) D)
    [Smooth D.toBase] [IsProper D.toBase] [GeometricallyConnected D.toBase] :
    let : IsIntegral (pullback c (specMap k K)) :=
      isIntegral_pullback_Spec_field k c (specMap k K)
    let : IsIntegral (pullback (specMap k K) c) :=
      IsIntegral.of_isIso (pullbackSymmetry c (specMap k K)).hom
    let J := EtaleFundamentalGroups.coefficientModelMap (specMap k K) c i
    let G := RepresentsRelSubPic.relativeGroupLaw (P := algEquivZeroGroupCut c ε) hD
    let hc : G.IsCommutative :=
      RepresentsRelSubPic.relativeGroupLaw_isCommutative (P := algEquivZeroGroupCut c ε) hD
    let η := Spec.map (CommRingCat.ofHom
      (algebraMap (pullback (specMap k K) (i ≫ c)).functionField Ω))
    let xi := η ≫ (pullback (specMap k K) (i ≫ c)).fromSpecStalk
      (genericPoint (↑(pullback (specMap k K) (i ≫ c)) : Type))
    let b := boundaryInertiaMap M j hj hfield Q
    let B := (M.openBoundaryPlaces j → (primeToRootsSystem K K).inverseLimit) ⧸
      b.toMonoidHom.ker
    ∃ E : TopologicalAbelianization (Aut (fiber (xi ≫ J))) ≃ₜ*
        Multiplicative (ProCGroups.FullTateModule (G.AlgPoints hc K)),
      ∃ (α : K ≃ₐ[k] K) (ρ : (K ≃ₐ[k] K) →* MulAut B)
        (ι : B →ₜ* TopologicalAbelianization (Aut (fiber xi))),
      let τ := (ContinuousMonoidHom.toContinuousMonoidHom E).comp
        (compactificationAbelianizationMap J xi)
      Function.Injective ι ∧ Function.Surjective τ ∧
        ι.toMonoidHom.range = τ.toMonoidHom.ker ∧
        b.toMonoidHom.ker = (Pi.constMonoidHom (M.openBoundaryPlaces j)
          (primeToRootsSystem K K).inverseLimit).range ∧
        Continuous (fun z : (K ≃ₐ[k] K) ×
            Multiplicative (ProCGroups.FullTateModule (G.AlgPoints hc K)) =>
          ProCGroups.FullTateModule.mapHom
            (RelativeGroupLaw.AlgPoints.map (L := G) (hc := hc) z.1.toAlgHom) z.2) ∧
        Continuous (fun z : (K ≃ₐ[k] K) × B => ρ z.1 z.2) ∧
        (∀ (σ : K ≃ₐ[k] K) (x : TopologicalAbelianization (Aut (fiber xi))),
          τ (geometricAbelianGaloisAction k K U (i ≫ c) xi σ x) =
            ProCGroups.FullTateModule.mapHom
              (RelativeGroupLaw.AlgPoints.map (L := G) (hc := hc) σ.toAlgHom) (τ x)) ∧
        (∀ (σ : K ≃ₐ[k] K) (z : B),
          ι (ρ σ z) = geometricAbelianGaloisAction k K U (i ≫ c) xi σ (ι z)) ∧
        (∀ t, ι (QuotientGroup.mk t) =
          geometricAbelianGaloisAction k K U (i ≫ c) xi α⁻¹ (b t)) ∧
        ∀ σ : K ≃ₐ[k] K,
          ∃ (g : SemilinearAut K F), SemilinearAut.baseAut g = σ.toRingEquiv ∧
            ∃ hS : ∀ p : Place K F,
              p ∈ M.openBoundaryPlaces j ↔ g • p ∈ M.openBoundaryPlaces j,
            ∀ (p : M.openBoundaryPlaces j) (t : (primeToRootsSystem K K).inverseLimit),
              geometricAbelianGaloisAction k K U (i ≫ c) xi σ
                  (geometricAbelianGaloisAction k K U (i ≫ c) xi α⁻¹
                    (boundaryPlaceInertiaHom M j hj hfield Q p t)) =
                geometricAbelianGaloisAction k K U (i ≫ c) xi α⁻¹
                  (boundaryPlaceInertiaHom M j hj hfield Q
                    ⟨g • p.val, (hS p.val).mp p.property⟩
                    (primeToRootsCoefficientMap K K σ.toRingHom t)) := by
  intro hY hYL J G hc η xi b B
  classical
  obtain ⟨E, hsurj, hbrange, hbker, hTc, hT⟩ := exists_arithmetic_boundary_Tate_map
    k K c i M eC heC j hj hproj hbase hfield Q ε D hD
  have hbcoeff := exists_boundary_coefficient_equivariance
    k K c i M eC heC j hj hproj hbase hfield Q
  dsimp only at hbcoeff
  obtain ⟨α, hα⟩ := hbcoeff
  let q := compactificationAbelianizationMap J xi
  let τ := (ContinuousMonoidHom.toContinuousMonoidHom E).comp q
  let P := TopologicalAbelianization (Aut (fiber xi))
  let H := q.toMonoidHom.ker
  have hτker : τ.toMonoidHom.ker = H :=
    MonoidHom.ker_comp_of_injective q.toMonoidHom E.toMonoidHom E.injective
  have hr : b.toMonoidHom.range = H := hbrange.trans hτker
  let eB₀ : B ≃ₜ* H := hr ▸
    ProCGroups.ContinuousMonoidHom.quotientKerContinuousMulEquivRange b
  have heB₀ (t : M.openBoundaryPlaces j → (primeToRootsSystem K K).inverseLimit) :
      (eB₀ (QuotientGroup.mk t) : P) = b t := by
    have transport (H' : Subgroup P) (h : b.toMonoidHom.range = H') :
        ((h ▸ ProCGroups.ContinuousMonoidHom.quotientKerContinuousMulEquivRange b)
          (QuotientGroup.mk t) : P) = b t := by
      subst H'
      exact ProCGroups.ContinuousMonoidHom.coe_quotientKerContinuousMulEquivRange_mk b t
    exact transport H hr
  let R := geometricBaseChangeKernelGaloisAction k K i c xi
  have hRjoint := continuous_geometricBaseChangeKernelGaloisAction_joint k K i c xi
  dsimp only at hRjoint
  have htransport := ProCGroups.ContinuousMulEquiv.exists_conjugated_action
    eB₀ R hRjoint α
  obtain ⟨eB, ρ, hρcont, hequiv, hecorr⟩ := htransport
  let ι : B →ₜ* P := (ProCGroups.ContinuousMonoidHom.subtype H).comp
    (ContinuousMonoidHom.toContinuousMonoidHom eB)
  have hιrange : ι.toMonoidHom.range = H := by
    change (H.subtype.comp eB.toMonoidHom).range = H
    rw [MonoidHom.range_comp, MonoidHom.range_eq_top.mpr eB.surjective,
      Subgroup.map_top, Subgroup.range_subtype]
  have hi := Subtype.val_injective.comp eB.injective
  have hir := hιrange.trans hτker.symm
  refine ⟨E, α, ρ, ι, ?_⟩
  dsimp only
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact hi
  · exact hsurj
  · exact hir
  · exact hbker
  · exact hTc
  · exact hρcont
  · exact hT
  · intro σ z
    change (eB (ρ σ z) : P) =
      geometricAbelianGaloisAction k K U (i ≫ c) xi σ (eB z).val
    rw [hequiv]
    exact geometricBaseChangeKernelGaloisAction_coe k K i c xi σ (eB z)
  · intro t
    change (eB (QuotientGroup.mk t) : P) = _
    rw [hecorr]
    exact (geometricBaseChangeKernelGaloisAction_coe k K i c xi α⁻¹
      (eB₀ (QuotientGroup.mk t))).trans (congrArg
        (geometricAbelianGaloisAction k K U (i ≫ c) xi α⁻¹) (heB₀ t))
  · exact hα

end AnabelianGeometry.WeightFiltration
