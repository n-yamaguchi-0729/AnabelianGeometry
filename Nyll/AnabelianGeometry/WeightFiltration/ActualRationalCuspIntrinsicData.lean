/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/
import Nyll.AnabelianGeometry.WeightFiltration.TransportedCuspArithmeticData
import Nyll.AnabelianGeometry.WeightFiltration.BoundaryInertiaSelfNormalizer

/-! # Intrinsic Nakamura conditions of an actual rational cusp

The original geometric subgroup is self-normalizing and its actual arithmetic
image has full Galois normalizer image with cyclotomic conjugation.
The explicit rational-chart and rational-place hypotheses are retained.
-/

noncomputable section
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.FiniteEtale AlgebraicCurve
open CategoryTheory.PreGaloisCategory SchemeTheory EtaleFundamentalGroups.Inertia
open EtaleFundamentalGroups AlgebraicGeometry.SmoothProperCurve

namespace AnabelianGeometry.WeightFiltration
attribute [local instance] placeBaseAmbientAlgebra placeBaseAmbientTower
  placeConstantAmbientTower

private theorem rationalIntrinsic_normalizer_full_image_at_canonical_point
    (k κ : Type) [Field k] [Field κ] [Algebra k κ] [IsSepClosure k κ]
    {X Y : Scheme} (f : X ⟶ Spec (.of k)) (u : Y ⟶ X)
    {Ω : Type} [Field Ω] [IsSepClosed Ω]
    (xi : Spec (.of Ω) ⟶ Y) (z : Spec (.of Ω) ⟶ X) (hz : xi ≫ u = z)
    (I : Subgroup (Aut (fiber xi)))
    (hfull : ∀ τ : Gal(κ/k), ∃ γ : Aut (fiber z),
      γ ∈ Subgroup.normalizer
        (I.map (pointedFundamentalGroupHom u xi z hz).toMonoidHom : Set _) ∧
      arithmeticFundamentalGroupHom k κ f z γ = τ) :
    ∀ τ : Gal(κ/k), ∃ γ : Aut (fiber (xi ≫ u)),
      γ ∈ Subgroup.normalizer
        (I.map (fundamentalGroupHom u xi).toMonoidHom : Set _) ∧
      arithmeticFundamentalGroupHom k κ f (xi ≫ u) γ = τ := by
  subst z
  exact hfull

section SourceChart

open scoped RatFunc
attribute [local instance] Polynomial.algebra

local instance (priority := 2000) actualRationalCuspIntrinsicSMulRatFunc
    {A E : Type*} [CommSemiring A] [Field E]
    [Algebra A (RatFunc E)] : SMul A (RatFunc E) :=
  (inferInstance : Algebra A (RatFunc E)).toSMul

variable
    (k κ : Type) [Field k] [NumberField k] [Field κ] [CharZero κ] [IsAlgClosed κ]
    [Algebra k κ] [IsSepClosure k κ] [IsAlgClosure k κ]
    {C X₁ : Scheme} [IsIntegral C] [IsIntegral X₁]
    [CompactSpace X₁] [QuasiSeparatedSpace X₁]
    (c : C ⟶ Spec (.of k)) (i : X₁ ⟶ C)

variable
    [IsIntegral (Limits.pullback (specMap k κ) (i ≫ c))]
    [CompactSpace ↥(Limits.pullback (specMap k κ) (i ≫ c) : Scheme)]
    [ConnectedSpace ↥(Limits.pullback (specMap k κ) (i ≫ c) : Scheme)]
    (M : CurveModel κ (RatFunc κ))
    (eC : M.C ≅ Limits.pullback c (specMap k κ))
    (heC : eC.hom ≫ Limits.pullback.snd c (specMap k κ) = M.toBase)
    (j : (Limits.pullback (specMap k κ) (i ≫ c)) ⟶ M.C) [IsOpenImmersion j] (hj : DenseRange j)
    (hproj : j ≫ eC.hom ≫ Limits.pullback.fst c (specMap k κ) = (Limits.pullback.snd (specMap k κ)
      (i ≫ c)) ≫ i)
    (hbase : j ≫ M.toBase = Limits.pullback.fst (specMap k κ) (i ≫ c))
    [Algebra (RatFunc κ) (Limits.pullback (specMap k κ) (i ≫ c)).functionField]
    (hfield : algebraMap (RatFunc κ) (Limits.pullback (specMap k κ) (i ≫ c)).functionField =
      (j.functionFieldMap hj).comp M.ffEquiv.toRingHom)
    {Ω : Type} [Field Ω] [IsSepClosed Ω]
    [Algebra (Limits.pullback (specMap k κ) (i ≫ c)).functionField Ω] [Algebra (RatFunc κ) Ω]
    [IsScalarTower (RatFunc κ) (Limits.pullback (specMap k κ) (i ≫ c)).functionField Ω]
    [IsSepClosure (Limits.pullback (specMap k κ) (i ≫ c)).functionField Ω]
    [IsSepClosure (RatFunc κ) Ω]
    [∀ p : M.openBoundaryPlaces j, Algebra p.val.toValuationSubring Ω]
    [∀ p : M.openBoundaryPlaces j, IsScalarTower p.val.toValuationSubring (RatFunc κ) Ω]
    [Algebra κ Ω]
    [∀ p : M.openBoundaryPlaces j, IsScalarTower κ p.val.toValuationSubring Ω]
    (Q : ∀ p : M.openBoundaryPlaces j,
      Ideal (normalizationCommAlgCat p.val.toValuationSubring Ω))
    [∀ p, (Q p).IsMaximal]
    [Finite (M.openBoundaryPlaces j)] [Nontrivial (M.openBoundaryPlaces j)]

local instance actualRationalCuspIntrinsicCurve : IsCurveOver κ (RatFunc κ) :=
  AlgebraicCurve.instIsCurveOverRatFunc κ

variable
    [Algebra (RatFunc k) Ω] [IsScalarTower (RatFunc k) (RatFunc κ) Ω]
    [Algebra k Ω] [IsScalarTower k κ Ω] [IsScalarTower k (RatFunc k) Ω]
    [IsScalarTower κ (RatFunc κ) Ω]
    [IsGalois (RatFunc k) Ω] [Algebra.IsAlgebraic (RatFunc κ) Ω]
    [IsSepClosure (RatFunc k) Ω]
    (V : Place k (RatFunc k)) (hV : V.IsRational)
    [Algebra V.toValuationSubring Ω]
    [IsScalarTower V.toValuationSubring (RatFunc k) Ω]

variable
    [IsNormalIntegral (Limits.pullback (specMap k κ) (i ≫ c) : Scheme)]
    [IsLocallyNoetherian (Limits.pullback (specMap k κ) (i ≫ c) : Scheme)]
    [QuasiCompact j] [QuasiSeparated j]
    [Algebra κ (Limits.pullback (specMap k κ) (i ≫ c)).functionField]
    [IsScalarTower κ (RatFunc κ) (Limits.pullback (specMap k κ) (i ≫ c)).functionField]
    [IsScalarTower κ (Limits.pullback (specMap k κ) (i ≫ c)).functionField Ω]

omit [NumberField k] in
include eC heC hproj hbase hV in
/-- The actual roots map at a specified rational cusp satisfies all intrinsic
Nakamura conditions, without an arithmetic equivalence or another curve. -/
theorem actual_rationalCusp_intrinsic_cyclotomic_data
    (hπ : DenseRange (eC.hom ≫ Limits.pullback.fst c (specMap k κ)))
    (e0 : RatFunc k ≃+* C.functionField)
    (hchart : ∀ x : RatFunc k,
      (eC.hom ≫ Limits.pullback.fst c (specMap k κ)).functionFieldMap hπ (e0 x) =
        M.ffEquiv (algebraMap (RatFunc k) (RatFunc κ) x))
    (p : M.openBoundaryPlaces j)
    (hord : ∀ x : RatFunc k,
      p.val.ord (algebraMap (RatFunc k) (RatFunc κ) x) = V.ord x)
    (jgeom : Spec (.of (RatFunc κ)) ⟶ (Limits.pullback (specMap k κ) (i ≫ c)))
    (jarith : Spec (.of (RatFunc k)) ⟶ X₁)
    (hchartpoint : ((Limits.pullback (specMap k κ) (i ≫ c)).genericExtensionMorphism Ω) ≫ 𝟙
      (Limits.pullback (specMap k κ) (i ≫ c)) =
      Spec.map (CommRingCat.ofHom (algebraMap (RatFunc κ) Ω)) ≫ jgeom)
    (hpoint : (Spec.map (CommRingCat.ofHom (algebraMap (RatFunc κ) Ω)) ≫ jgeom) ≫
      (Limits.pullback.snd (specMap k κ) (i ≫ c)) =
      Spec.map (CommRingCat.ofHom (algebraMap (RatFunc k) Ω)) ≫ jarith)
    (hbasearith : (Spec.map (CommRingCat.ofHom (algebraMap (RatFunc k) Ω)) ≫ jarith) ≫
      (i ≫ c) = Spec.map (CommRingCat.ofHom (algebraMap k Ω)))
    (hthree₁ : 3 ≤ Nat.card (M.openBoundaryPlaces j)) :
    let xi := ((Limits.pullback (specMap k κ) (i ≫ c) : Scheme)).genericExtensionMorphism Ω
    let ι := fundamentalGroupHom (Limits.pullback.snd (specMap k κ) (i ≫ c)) xi
    let q := arithmeticFundamentalGroupHom k κ (i ≫ c)
      (xi ≫ Limits.pullback.snd (specMap k κ) (i ≫ c))
    let psi := boundaryPlaceInertiaLift M j hj hfield Q p
    Function.Injective psi ∧
      Subgroup.normalizer (psi.toMonoidHom.range : Set _) = psi.toMonoidHom.range ∧
      ∃ J : ClosedSubgroup (Aut (fiber (xi ≫ Limits.pullback.snd (specMap k κ) (i ≫ c)))),
        (J : Subgroup _) = psi.toMonoidHom.range.map ι.toMonoidHom ∧
        (Subgroup.normalizer (J : Set _)).map q.toMonoidHom = ⊤ ∧
        IsOpen (((Subgroup.normalizer (J : Set _)).map q.toMonoidHom :
          Subgroup Gal(κ/k)) : Set Gal(κ/k)) ∧
        ∀ γ ∈ Subgroup.normalizer (J : Set _), ∀ t,
          ι (psi (primeToRootsCoefficientMap κ κ (q γ).toRingHom t)) =
            γ * ι (psi t) * γ⁻¹ := by
  intro xi ι q psi
  refine ⟨boundaryPlaceInertiaLift_injective M j hj hfield Q p, ?_, ?_⟩
  · rw [boundaryPlaceInertiaLift_range]
    exact fieldChart_boundaryInertia_self_normalizing M j hj hfield hthree₁ Q p
  · let a := ι.comp psi
    let J : ClosedSubgroup (Aut (fiber (xi ≫ Limits.pullback.snd (specMap k κ) (i ≫ c)))) :=
      ⟨a.toMonoidHom.range, a.continuous_toFun.isClosedMap.isClosed_range⟩
    have hJrange : (J : Subgroup _) = psi.toMonoidHom.range.map ι.toMonoidHom := by
      ext y
      constructor
      · rintro ⟨t, rfl⟩
        exact ⟨psi t, ⟨t, rfl⟩, rfl⟩
      · rintro ⟨v, ⟨t, rfl⟩, rfl⟩
        exact ⟨t, rfl⟩
    have hJI : (J : Subgroup _) =
        (genericPlaceInertia (Limits.pullback (specMap k κ) (i ≫ c)) p.val (Q p)).map
          ι.toMonoidHom := by
      rw [hJrange, boundaryPlaceInertiaLift_range]
    have hJIset :
        (J : Set (Aut (fiber (xi ≫ Limits.pullback.snd (specMap k κ) (i ≫ c))))) =
          ((genericPlaceInertia (Limits.pullback (specMap k κ) (i ≫ c)) p.val (Q p)).map
            ι.toMonoidHom).carrier := by
      exact congrArg
        (fun H : Subgroup (Aut (fiber (xi ≫
          Limits.pullback.snd (specMap k κ) (i ≫ c)))) => H.carrier) hJI
    have hsurj : Function.Surjective (algebraMap (RatFunc κ)
        (Limits.pullback (specMap k κ) (i ≫ c)).functionField) := by
      rw [hfield]
      exact (j.functionFieldRingEquivOfIsOpenImmersion).surjective.comp M.ffEquiv.surjective
    let xarith := Spec.map (CommRingCat.ofHom (algebraMap (RatFunc k) Ω)) ≫ jarith
    have hgeneric : xi ≫ Limits.pullback.snd (specMap k κ) (i ≫ c) = xarith := by
      dsimp only [xi, xarith]
      rw [← hpoint, ← hchartpoint, Category.comp_id]
    have hfull_chart := original_ratFuncPlace_normalizer_full_image
      V hV p.val hord (Q p) hsurj (i ≫ c)
      (Limits.pullback.snd (specMap k κ) (i ≫ c)) jgeom jarith
      hchartpoint hpoint hbasearith
    have hfull : ∀ τ : Gal(κ/k), ∃ γ : Aut (fiber (xi ≫
        Limits.pullback.snd (specMap k κ) (i ≫ c))),
        γ ∈ Subgroup.normalizer (J : Set _) ∧ q γ = τ := by
      have hcanonical := rationalIntrinsic_normalizer_full_image_at_canonical_point
        k κ (i ≫ c) (Limits.pullback.snd (specMap k κ) (i ≫ c))
        xi xarith hgeneric
        (genericPlaceInertia (Limits.pullback (specMap k κ) (i ≫ c)) p.val (Q p)) hfull_chart
      rw [hJIset]
      exact hcanonical
    have htop : (Subgroup.normalizer (J : Set _)).map q.toMonoidHom = ⊤ := by
      apply top_unique
      intro τ _
      obtain ⟨γ, hγ, hτ⟩ := hfull τ
      exact ⟨γ, hγ, hτ⟩
    refine ⟨J, hJrange, htop, ?_, ?_⟩
    · rw [htop]
      exact isOpen_univ
    · intro γ hγ t
      have hcycl := rational_boundaryPlaceInertiaLift_conjugate
        k κ c i M eC heC j hj hproj hbase hfield Q hπ e0 hchart V hV p hord
      exact hcycl γ (by
        rw [hJIset] at hγ
        exact hγ) t

end SourceChart
end AnabelianGeometry.WeightFiltration
