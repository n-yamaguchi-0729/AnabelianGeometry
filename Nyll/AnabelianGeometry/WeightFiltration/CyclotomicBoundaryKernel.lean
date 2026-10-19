/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.AnabelianGeometry.WeightFiltration.ArithmeticBoundaryGaloisSequence
import Nyll.AnabelianGeometry.WeightFiltration.OpenCyclotomicHomVanishing

/-!
# Cyclotomic images lie in the actual boundary kernel

Compose an actual equivariant roots homomorphism with the actual
compactification Tate map. Number-field Hom vanishing annihilates this
composite. This is the containment direction of intrinsic weight recognition;
no rationality or pointwise fixedness of the boundary is assumed here.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits AlgebraicCurve
open AlgebraicGeometry.FiniteEtale AlgebraicGeometry.SmoothProperCurve
open AlgebraicGeometry.RelPicard NeronModelInfra GoodReductionJacobian
open SchemeTheory EtaleFundamentalGroups.Inertia
open ProCGroups.Abelian

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
/-- Every actual arithmetic-equivariant cyclotomic image lies in the
compactification kernel, without rationalizing the boundary. -/
theorem cyclotomicHom_range_le_compactification_kernel_of_open_subgroup
    (ε : SchemeHomOver (𝟙 (Spec (.of k))) c)
    (D : RelativePic0Designation k c)
    (hD : RepresentsRelSubPic c ε (algEquivZeroCut c ε) D)
    [Smooth D.toBase] [IsProper D.toBase] [GeometricallyConnected D.toBase]
    (H : OpenSubgroup (K ≃ₐ[k] K)) :
    let : IsIntegral (pullback c (specMap k K)) :=
      isIntegral_pullback_Spec_field k c (specMap k K)
    let : IsIntegral (pullback (specMap k K) c) :=
      IsIntegral.of_isIso (pullbackSymmetry c (specMap k K)).hom
    let J := EtaleFundamentalGroups.coefficientModelMap (specMap k K) c i
    let η := Spec.map (CommRingCat.ofHom
      (algebraMap (pullback (specMap k K) (i ≫ c)).functionField Ω))
    let xi := η ≫ (pullback (specMap k K) (i ≫ c)).fromSpecStalk
      (genericPoint (↑(pullback (specMap k K) (i ≫ c)) : Type))
    ∀ φ : (primeToRootsSystem K K).inverseLimit →*
        TopologicalAbelianization (Aut (fiber xi)),
      (∀ (σ : K ≃ₐ[k] K), σ ∈ H → ∀ t,
        φ (primeToRootsCoefficientMap K K σ.toRingHom t) =
          geometricAbelianGaloisAction k K U (i ≫ c) xi σ (φ t)) →
      φ.range ≤ (compactificationAbelianizationMap J xi).toMonoidHom.ker := by
  intro hY hYL J η xi φ hφ
  let := Fintype.ofFinite (M.openBoundaryPlaces j)
  have : IsAlgClosure k K := ⟨inferInstance, inferInstance⟩
  obtain ⟨E, α, ρ, ι, _, _, _, _, _, _, hτ, _, _, _⟩ :=
    exists_arithmetic_boundary_Galois_sequence
      k K c i M eC heC j hj hproj hbase hfield Q ε D hD
  let q := compactificationAbelianizationMap J xi
  let χ := E.toMonoidHom.comp (q.toMonoidHom.comp φ)
  have hχ := numberField_cyclotomicHom_eq_one_of_open_subgroup k K c ε D hD H χ (by
    intro σ hσ t
    change E (q (φ (primeToRootsCoefficientMap K K σ.toRingHom t))) = _
    rw [hφ σ hσ]
    exact hτ σ (φ t))
  rintro z ⟨t, rfl⟩
  change q (φ t) = 1
  apply E.injective
  exact (DFunLike.congr_fun hχ t).trans E.map_one.symm

end AnabelianGeometry.WeightFiltration
