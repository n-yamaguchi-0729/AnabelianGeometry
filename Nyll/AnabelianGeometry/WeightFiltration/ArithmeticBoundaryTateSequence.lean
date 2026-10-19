/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.AnabelianGeometry.WeightFiltration.BoundaryInertiaRelations
import Nyll.AnabelianGeometry.WeightFiltration.ArithmeticOpenTateComparison
import Nyll.EtaleFundamentalGroups.GeometricFiber.GeometricKernelNaturality

/-!
# The original arithmetic compactification map with full Tate endpoint

The existing equivariant Tate comparison is applied at the actual image
of the open generic point. The original boundary kernel and diagonal
relation are preserved by the actual compactification isomorphism.
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
/-- The actual Tate-valued compactification map is Galois equivariant, and
its kernel and boundary relations are the previously computed ones. -/
theorem exists_arithmetic_boundary_Tate_map
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
    ∃ E : TopologicalAbelianization (Aut (fiber (xi ≫ J))) ≃ₜ*
        Multiplicative (ProCGroups.FullTateModule (G.AlgPoints hc K)),
      let τ := (ContinuousMonoidHom.toContinuousMonoidHom E).comp
        (compactificationAbelianizationMap J xi)
      Function.Surjective τ ∧
        (boundaryInertiaMap M j hj hfield Q).toMonoidHom.range = τ.toMonoidHom.ker ∧
        (boundaryInertiaMap M j hj hfield Q).toMonoidHom.ker =
          (Pi.constMonoidHom (M.openBoundaryPlaces j)
            (primeToRootsSystem K K).inverseLimit).range ∧
        Continuous (fun z : (K ≃ₐ[k] K) ×
            Multiplicative (ProCGroups.FullTateModule (G.AlgPoints hc K)) =>
          ProCGroups.FullTateModule.mapHom
            (RelativeGroupLaw.AlgPoints.map (L := G) (hc := hc) z.1.toAlgHom) z.2) ∧
        ∀ (σ : K ≃ₐ[k] K) (x : TopologicalAbelianization (Aut (fiber xi))),
          τ (geometricAbelianGaloisAction k K U (i ≫ c) xi σ x) =
            ProCGroups.FullTateModule.mapHom
              (RelativeGroupLaw.AlgPoints.map (L := G) (hc := hc) σ.toAlgHom) (τ x) := by
  intro hY hYL J G hc η xi
  let e := eC ≪≫ pullbackSymmetry c (specMap k K)
  have hJ : J = j ≫ e.hom := by
    apply pullback.hom_ext
    · simp [J, e, EtaleFundamentalGroups.coefficientModelMap, Category.assoc, heC, hbase]
    · simp [J, e, EtaleFundamentalGroups.coefficientModelMap, Category.assoc, hproj]
  have : IsOpenImmersion J := by rw [hJ]; infer_instance
  obtain ⟨E, hE⟩ := exists_arithmetic_fullTate_equiv_at_open_generic
    (k := k) (K := K) c ε D hD (pullback (specMap k K) (i ≫ c)) J Ω
  have hTc : Continuous (fun z : (K ≃ₐ[k] K) ×
      Multiplicative (ProCGroups.FullTateModule (G.AlgPoints hc K)) =>
      ProCGroups.FullTateModule.mapHom
        (RelativeGroupLaw.AlgPoints.map (L := G) (hc := hc) z.1.toAlgHom) z.2) := by
    have hp : Continuous (fun z : (K ≃ₐ[k] K) ×
        Multiplicative (ProCGroups.FullTateModule (G.AlgPoints hc K)) =>
        (z.1, E.symm z.2)) :=
      continuous_fst.prodMk (E.symm.continuous_toFun.comp continuous_snd)
    have ha := continuous_geometricAbelianGaloisAction_joint k K C c (xi ≫ J)
    have hh := E.continuous_toFun.comp (ha.comp hp)
    have heval : (fun z : (K ≃ₐ[k] K) ×
        Multiplicative (ProCGroups.FullTateModule (G.AlgPoints hc K)) =>
        ProCGroups.FullTateModule.mapHom
          (RelativeGroupLaw.AlgPoints.map (L := G) (hc := hc) z.1.toAlgHom) z.2) =
        (fun z => E (geometricAbelianGaloisAction k K C c (xi ≫ J)
          z.1 (E.symm z.2))) := by
      funext z
      rw [hE, E.apply_symm_apply]
    rw [heval]
    exact hh
  refine ⟨E, ?_⟩
  dsimp only
  have : Smooth c := SmoothOfRelativeDimension.smooth 1 c
  have : Smooth (pullback.fst (specMap k K) c) := inferInstance
  have : IsIntegrallyClosed Γ(Spec (.of K), ⊤) := IsIntegrallyClosed.of_equiv
    (Scheme.ΓSpecIso (.of K)).symm.commRingCatIsoToRingEquiv
  have : IsNormalIntegral (pullback (specMap k K) c) :=
    IsNormalIntegral.of_stalks (pullback (specMap k K) c)
      (fun z => (Smooth.isDomain_and_isIntegrallyClosed_stalk
        (pullback.fst (specMap k K) c) z).2)
  have : IsLocallyNoetherian (pullback (specMap k K) c) := inferInstance
  have hker : (compactificationAbelianizationMap J xi).toMonoidHom.ker =
      (compactificationAbelianizationMap j xi).toMonoidHom.ker := by
    rw [hJ]
    exact compactificationAbelianizationMap_ker_postcomp_iso j xi e
  refine ⟨E.surjective.comp (compactificationAbelianizationMap_surjective J xi), ?_,
    boundaryInertiaMap_ker M j hj hfield Q, hTc, ?_⟩
  · change (boundaryInertiaMap M j hj hfield Q).toMonoidHom.range =
      (E.toMonoidHom.comp (compactificationAbelianizationMap J xi).toMonoidHom).ker
    rw [MonoidHom.ker_comp_of_injective _ _ E.injective, hker]
    exact boundaryInertiaMap_range M j hj hfield Q
  · intro σ x
    change E (TopologicalAbelianization.map (fundamentalGroupHom J xi)
      (geometricAbelianGaloisAction k K U (i ≫ c) xi σ x)) = _
    rw [geometricAbelianGaloisAction_baseChange_map]
    exact hE σ (compactificationAbelianizationMap J xi x)

end AnabelianGeometry.WeightFiltration
