/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.AnabelianGeometry.WeightFiltration.RationalBoundaryArithmeticEquivariance
import Nyll.AnabelianGeometry.WeightFiltration.BoundaryInertiaCyclotomicUpgrade
import Nyll.AlgebraicCurves.FunctionFields.Rational.InstIsCurveOverRatFunc

/-! # Original nonabelian rational boundary conjugation

-/

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits AlgebraicCurve
open AlgebraicGeometry.FiniteEtale AlgebraicGeometry.SmoothProperCurve
open SchemeTheory EtaleFundamentalGroups.Inertia
open ProCGroups.Abelian

open scoped RatFunc
attribute [local instance] Polynomial.algebra

namespace AnabelianGeometry.WeightFiltration

variable
    (k K : Type) [Field k] [Field K] [CharZero K] [IsAlgClosed K]
    [Algebra k K] [IsSepClosure k K]
    {C U : Scheme} [CompactSpace U] [QuasiSeparatedSpace U]
    (c : C ⟶ Spec (.of k)) (i : U ⟶ C)

variable
    [IsIntegral (Limits.pullback (specMap k K) (i ≫ c))] [CompactSpace ↑(Limits.pullback (specMap
      k K) (i ≫ c))]
    (M : CurveModel K (RatFunc K))
    (eC : M.C ≅ pullback c (specMap k K))
    (heC : eC.hom ≫ pullback.snd c (specMap k K) = M.toBase)
    (j : (Limits.pullback (specMap k K) (i ≫ c)) ⟶ M.C) [IsOpenImmersion j] (hj : DenseRange j)
    (hproj : j ≫ eC.hom ≫ pullback.fst c (specMap k K) = pullback.snd (specMap k K) (i ≫ c) ≫ i)
    (hbase : j ≫ M.toBase = pullback.fst (specMap k K) (i ≫ c))
    [Algebra (RatFunc K) (Limits.pullback (specMap k K) (i ≫ c)).functionField]
    (hfield : algebraMap (RatFunc K) (Limits.pullback (specMap k K) (i ≫ c)).functionField =
      (j.functionFieldMap hj).comp M.ffEquiv.toRingHom)
    {Ω : Type} [Field Ω] [Algebra (Limits.pullback (specMap k K) (i ≫ c)).functionField Ω]
      [Algebra (RatFunc K) Ω]
    [IsScalarTower (RatFunc K) (Limits.pullback (specMap k K) (i ≫ c)).functionField Ω]
    [IsSepClosed Ω] [IsSepClosure (Limits.pullback (specMap k K) (i ≫ c)).functionField Ω]
      [IsSepClosure (RatFunc K) Ω]
    [∀ p : M.openBoundaryPlaces j, Algebra p.val.toValuationSubring Ω]
    [∀ p : M.openBoundaryPlaces j, @IsScalarTower p.val.toValuationSubring (RatFunc K) Ω
      (inferInstance : Algebra p.val.toValuationSubring (RatFunc K)).toSMul
      inferInstance inferInstance]
    [Algebra K Ω]
    [∀ p : M.openBoundaryPlaces j, IsScalarTower K p.val.toValuationSubring Ω]
    (Q : ∀ p : M.openBoundaryPlaces j,
      Ideal (normalizationCommAlgCat p.val.toValuationSubring Ω))
    [∀ p, (Q p).IsMaximal]

variable [IsIntegral C]

variable [Finite (M.openBoundaryPlaces j)] [Nontrivial (M.openBoundaryPlaces j)]

local instance rationalBoundaryInertiaConjugationCurve :
    IsCurveOver K (RatFunc K) := AlgebraicCurve.instIsCurveOverRatFunc K

include eC heC hproj hbase in
/-- Every actual arithmetic normalizer element acts cyclotomically on the
original nonabelian boundary lift, with the same roots parameter. -/
theorem rational_boundaryPlaceInertiaLift_conjugate
    (hπ : DenseRange (eC.hom ≫ pullback.fst c (specMap k K)))
    (e0 : RatFunc k ≃+* C.functionField)
    (hchart : ∀ x : RatFunc k,
      (eC.hom ≫ pullback.fst c (specMap k K)).functionFieldMap hπ (e0 x) =
        M.ffEquiv (algebraMap (RatFunc k) (RatFunc K) x))
    (V : Place k (RatFunc k)) (hV : V.IsRational)
    (p : M.openBoundaryPlaces j)
    (hord : ∀ x : RatFunc k,
      p.val.ord (algebraMap (RatFunc k) (RatFunc K) x) = V.ord x) :
    let η := Spec.map (CommRingCat.ofHom
      (algebraMap (pullback (specMap k K) (i ≫ c)).functionField Ω))
    let xi := η ≫ (pullback (specMap k K) (i ≫ c)).fromSpecStalk
      (genericPoint (↑(pullback (specMap k K) (i ≫ c)) : Type))
    let ι := (fundamentalGroupHom (pullback.snd (specMap k K) (i ≫ c)) xi).toMonoidHom
    let q := arithmeticFundamentalGroupHom k K (i ≫ c)
      (xi ≫ pullback.snd (specMap k K) (i ≫ c))
    ∀ γ : Aut (fiber (xi ≫ pullback.snd (specMap k K) (i ≫ c))),
      γ ∈ Subgroup.normalizer
        ((genericPlaceInertia (pullback (specMap k K) (i ≫ c)) p.val (Q p)).map ι : Set _) →
      ∀ t : (primeToRootsSystem K K).inverseLimit,
        ι (boundaryPlaceInertiaLift M j hj hfield Q p
          (primeToRootsCoefficientMap K K (q γ).toRingHom t)) =
        γ * ι (boundaryPlaceInertiaLift M j hj hfield Q p t) * γ⁻¹ := by
  intro η xi ι q γ hγ t
  let E := geometricFundamentalGroupKernelEquiv k K U (i ≫ c) xi
  let v := E.symm (MulAut.conjNormal γ
    (E (boundaryPlaceInertiaLift M j hj hfield Q p t)))
  have hv : ι v = γ * ι (boundaryPlaceInertiaLift M j hj hfield Q p t) * γ⁻¹ := by
    change (E v).val = _
    rw [E.apply_symm_apply]
    rfl
  have hι : Function.Injective ι := by
    intro a b hab
    apply E.injective
    exact Subtype.ext hab
  have hact := geometricAbelianGaloisAction_mk_of_conjugate k K U (i ≫ c) xi
    γ (boundaryPlaceInertiaLift M j hj hfield Q p t) v hv
  have hb := rational_boundaryPlaceInertiaHom_arithmetic_equivariance
    k K c i M eC heC j hj hproj hbase hfield Q hπ e0 hchart V hV p hord (q γ) t
  have hab : TopologicalAbelianization.mk _ v =
      boundaryPlaceInertiaHom M j hj hfield Q p
        (primeToRootsCoefficientMap K K (q γ).toRingHom t) :=
    hact.symm.trans hb
  exact boundaryPlaceInertiaLift_conjugate_of_abelian_eq
    M j hj hfield Q p ι hι γ hγ t
      (primeToRootsCoefficientMap K K (q γ).toRingHom t) v hv hab

end AnabelianGeometry.WeightFiltration
