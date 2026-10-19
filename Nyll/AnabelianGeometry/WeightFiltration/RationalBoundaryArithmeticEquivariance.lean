/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.AnabelianGeometry.WeightFiltration.CoefficientProjectionFunctionFieldFixed
import Nyll.AnabelianGeometry.WeightFiltration.RationalBoundaryCyclotomicFixedPlace
import Nyll.AnabelianGeometry.WeightFiltration.BoundaryInertiaSemilinear
import Nyll.AnabelianGeometry.WeightFiltration.OpenBoundarySemilinear
import Nyll.AnabelianGeometry.WeightFiltration.GenericCoefficientDuality
import Nyll.AlgebraicCurves.Models.ConstantExtension.BaseChangeSemilinearAction

/-! # Original rational boundary inertia and arithmetic cyclotomic action
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

include eC heC hproj hbase in
/-- At an actual rational arithmetic place, the original geometric boundary
homomorphism is cyclotomic for the actual Galois action. The chart square
identifies the prescribed arithmetic function-field embedding; it is not a
hypothesis on inertia or Galois preservation. -/
theorem rational_boundaryPlaceInertiaHom_arithmetic_equivariance
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
    ∀ (σ : K ≃ₐ[k] K) (t : (primeToRootsSystem K K).inverseLimit),
      geometricAbelianGaloisAction k K U (i ≫ c) xi σ
        (boundaryPlaceInertiaHom M j hj hfield Q p t) =
      boundaryPlaceInertiaHom M j hj hfield Q p
        (primeToRootsCoefficientMap K K σ.toRingHom t) := by
  intro η xi
  classical
  obtain ⟨α, hα⟩ := exists_genericCoefficient_sourceAction k K U (i ≫ c) Ω xi rfl
  have hraw : ∀ (σ : K ≃ₐ[k] K) (t : (primeToRootsSystem K K).inverseLimit),
      geometricAbelianGaloisAction k K U (i ≫ c) xi (α * σ * α⁻¹)
        (boundaryPlaceInertiaHom M j hj hfield Q p t) =
      boundaryPlaceInertiaHom M j hj hfield Q p
        (primeToRootsCoefficientMap K K σ.toRingHom t) := by
    intro σ t
    let θX := coefficientBaseChangeIso k K (i ≫ c) σ
    obtain ⟨θ, g, hθproj, hθbase, hgbase, hgfun, hgpoint⟩ :=
      M.exists_baseChange_semilinear_action c eC heC σ
    have hsquare : θX.hom ≫ j = j ≫ θ.hom := by
      apply (cancel_mono eC.hom).1
      apply pullback.hom_ext
      · simp only [Category.assoc]
        rw [hproj, ← Category.assoc θX.hom (pullback.snd (specMap k K) (i ≫ c)) i,
          coefficientBaseChangeIso_hom_snd, hθproj, hproj]
      · simp only [Category.assoc, heC]
        rw [hbase, coefficientBaseChangeIso_hom_fst,
          hθbase, ← Category.assoc j M.toBase (Spec.map (CommRingCat.ofHom σ.toRingHom)), hbase]
    have hφM := M.functionFieldRingEquiv_semilinear θ g hgfun
    obtain ⟨hS, hφ⟩ := M.openBoundary_semilinear_compatibility j hj θX θ
      σ.toRingEquiv g hθbase hsquare hgpoint hφM
    obtain ⟨a, ha, hpoint, hlabel⟩ := hα σ
    let e := Scheme.Spec.mapIso a.toCommRingCatIso.op
    let p₀ := pullback.snd (specMap k K) (i ≫ c)
    have hp : e.hom ≫ xi = xi ≫ θX.hom := hpoint
    have hsource : e.hom ≫ (xi ≫ p₀) = xi ≫ p₀ := by
      rw [← Category.assoc, hp, Category.assoc, coefficientBaseChangeIso_hom_snd]
    let gA : Aut (fiber (xi ≫ p₀)) :=
      fiberSourceIso (xi ≫ p₀) e ≪≫ eqToIso (congrArg fiber hsource)
    change arithmeticFundamentalGroupHom k K (i ≫ c) (xi ≫ p₀) gA = α * σ * α⁻¹ at hlabel
    have hfixed (x : RatFunc k) :
        SemilinearAut.toRingAut g (algebraMap (RatFunc k) (RatFunc K) x) =
          algebraMap (RatFunc k) (RatFunc K) x := by
      have hx := semilinear_fixed_arithmeticFunctionField M
        (eC.hom ≫ pullback.fst c (specMap k K)) hπ θ g
        hθproj hφM (e0 x)
      simpa only [hchart, M.ffEquiv.symm_apply_apply] using hx
    have hpfix : g • p.val = p.val :=
      AnabelianGeometry.KummerTheory.ratFunc_rationalPlace_semilinear_fixed
        V hV p.val hord g hfixed
    have hpfix' : (⟨g • p.val, (hS p.val).mp p.property⟩ :
        M.openBoundaryPlaces j) = p := Subtype.ext hpfix
    have hb := boundaryPlaceInertiaHom_source_semilinear k K U (i ≫ c)
      M j hj hfield Q g hS θX.hom.functionFieldRingEquivOfIsOpenImmersion
      hφ a ha hsource p t
    change geometricAbelianGaloisAction k K U (i ≫ c) xi
      (arithmeticFundamentalGroupHom k K (i ≫ c) (xi ≫ p₀) gA)
      (boundaryPlaceInertiaHom M j hj hfield Q p t) = _ at hb
    rw [hlabel, hgbase, hpfix'] at hb
    exact hb
  intro σ t
  have hb := hraw (α⁻¹ * σ * α) t
  have hcancel : α * (α⁻¹ * σ * α) * α⁻¹ = σ := by
    simp [mul_assoc]
  rw [hcancel] at hb
  have hroot :
      primeToRootsCoefficientMap K K (α⁻¹ * σ * α).toRingHom t =
        primeToRootsCoefficientMap K K σ.toRingHom t := by
    exact primeToRootsCoefficientMap_conjugate K K α.toRingEquiv.symm
      σ.toRingEquiv t
  rw [hroot] at hb
  exact hb

end AnabelianGeometry.WeightFiltration

