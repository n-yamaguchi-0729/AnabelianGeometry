/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.AnabelianGeometry.WeightFiltration.IntrinsicBoundaryWeight
import Nyll.AnabelianGeometry.WeightFiltration.BoundaryInertiaGeneration
import Nyll.AnabelianGeometry.CuspidalInertia.RelativeAbelianizationRelations

/-!
# The actual arithmetic boundary relation is the intrinsic cyclotomic relation

This is a direct application of the existing geometric compactification-kernel
calculation and the existing number-field weight theorem. For a recovered
cover, k is its finite coefficient field E and the point below is identified
with the recovered point using the original recovery isomorphism.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits AlgebraicCurve
open AlgebraicGeometry.FiniteEtale AlgebraicGeometry.SmoothProperCurve
open AlgebraicGeometry.RelPicard NeronModelInfra GoodReductionJacobian
open SchemeTheory EtaleFundamentalGroups.Inertia ProCGroups.Abelian
open AnabelianGeometry.CuspidalInertia

namespace AnabelianGeometry.WeightFiltration

variable
    (k K : Type) [Field k] [NumberField k] [Field K] [CharZero K] [IsAlgClosed K]
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
    [hfin : Finite (M.openBoundaryPlaces j)]


include eC heC hj hproj hbase hfield Q hfin in
/-- Actual boundary inertia, with commutators and topological closure, is the
preimage of the intrinsic cyclotomic span under the original abelianization. -/
theorem arithmetic_boundaryRelation_eq_openCyclotomicSpan
    (ε : SchemeHomOver (𝟙 (Spec (.of k))) c)
    (D : RelativePic0Designation k c)
    (hD : RepresentsRelSubPic c ε (algEquivZeroCut c ε) D)
    [Smooth D.toBase] [IsProper D.toBase] [GeometricallyConnected D.toBase] :
    let η := Spec.map (CommRingCat.ofHom
      (algebraMap (pullback (specMap k K) (i ≫ c)).functionField Ω))
    let xi := η ≫ (pullback (specMap k K) (i ≫ c)).fromSpecStalk
      (genericPoint (↑(pullback (specMap k K) (i ≫ c)) : Type))
    let G := Aut (fiber xi)
    (Subgroup.closure
      (⋃ p : M.openBoundaryPlaces j,
        (genericPlaceInertia (pullback (specMap k K) (i ≫ c))
          p.val (Q p) : Set G)) ⊔ commutator G).topologicalClosure =
      (openCyclotomicSpan
        (fun σ : K ≃ₐ[k] K => primeToRootsCoefficientMap K K σ.toRingHom)
        (fun σ => geometricAbelianGaloisAction k K U (i ≫ c) xi σ)).comap
          (TopologicalAbelianization.mk G) := by
  intro η xi G
  have hboundary := compactificationAbelianization_ker_eq_boundaryInertia_closure
    M j hj hfield Q
  have hweight := curveModel_kernel_eq_openCyclotomicSpan
    k K c i M eC heC j hj hproj hbase hfield Q ε D hD
  rw [relativeRelation_eq_abelianization_comap, Subgroup.closure_iUnion]
  simp only [Subgroup.closure_eq, Subgroup.map_iSup]
  exact congrArg
    (fun B : Subgroup (TopologicalAbelianization G) =>
      B.comap (TopologicalAbelianization.mk G))
    (hboundary.symm.trans hweight)

end AnabelianGeometry.WeightFiltration
