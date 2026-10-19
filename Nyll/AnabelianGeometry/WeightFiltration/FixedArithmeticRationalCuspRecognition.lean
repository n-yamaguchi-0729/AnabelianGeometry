/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/
import Nyll.AnabelianGeometry.WeightFiltration.ActualRationalCuspRecognition
import Nyll.EtaleFundamentalGroups.GeometricFiber.ArithmeticGeometricEquivUniqueness

/-! # Recognition at the same fixed geometric equivalence for every source cusp

This forwards the single-cusp construction to any geometric equivalence
already fixed above the arithmetic map. Uniqueness follows from the actual
arithmetic exact sequence, not from a preservation assumption.
-/

noncomputable section
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.FiniteEtale AlgebraicCurve
open CategoryTheory.PreGaloisCategory SchemeTheory EtaleFundamentalGroups.Inertia
open EtaleFundamentalGroups AlgebraicGeometry.SmoothProperCurve

namespace AnabelianGeometry.WeightFiltration
attribute [local instance] placeBaseAmbientAlgebra placeBaseAmbientTower
  placeConstantAmbientTower

section SourceChart

open scoped RatFunc
attribute [local instance] Polynomial.algebra

local instance (priority := 2000) fixedRationalCuspRecognitionSMulRatFunc
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

local instance fixedRationalCuspRecognitionCurve : IsCurveOver κ (RatFunc κ) :=
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

include eC heC hproj hbase hV in
/-- For a specified rational source cusp, an arithmetic equivalence over G_k
carries its original inertia onto an actual target boundary inertia conjugate.
The geometric equivalence in the conclusion is the one constructed over eP. -/
theorem actual_rationalCusp_image_eq_boundary_conjugate_of_fixed_geometricEquiv
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
    (hthree₁ : 3 ≤ Nat.card (M.openBoundaryPlaces j))
    {C₂ X₂ : Scheme} [CompactSpace X₂] [QuasiSeparatedSpace X₂]
    (c₂ : C₂ ⟶ Spec (.of k))
    [IsProper c₂] [SmoothOfRelativeDimension 1 c₂] [GeometricallyIntegral c₂]
    (i₂ : X₂ ⟶ C₂) [IsOpenImmersion i₂]
    [IsIntegral (Limits.pullback (specMap k κ) (i₂ ≫ c₂) : Scheme)] [IsNormalIntegral
      (Limits.pullback (specMap k κ) (i₂ ≫ c₂) : Scheme)] [IsLocallyNoetherian (Limits.pullback
      (specMap k κ) (i₂ ≫ c₂) : Scheme)]
    [ConnectedSpace ↥(Limits.pullback (specMap k κ) (i₂ ≫ c₂) : Scheme)] [CompactSpace
      ↥(Limits.pullback (specMap k κ) (i₂ ≫ c₂) : Scheme)]
    [Algebra κ (Limits.pullback (specMap k κ) (i₂ ≫ c₂) : Scheme).functionField] [IsCurveOver κ
      (Limits.pullback (specMap k κ) (i₂ ≫ c₂) : Scheme).functionField]
    {Ω₂ : Type} [Field Ω₂] [IsSepClosed Ω₂]
    [Algebra (Limits.pullback (specMap k κ) (i₂ ≫ c₂) : Scheme).functionField Ω₂] [IsSepClosure
      (Limits.pullback (specMap k κ) (i₂ ≫ c₂) : Scheme).functionField Ω₂]
    [Algebra κ Ω₂] [IsScalarTower κ (Limits.pullback (specMap k κ) (i₂ ≫ c₂) :
      Scheme).functionField Ω₂]
    (M₂ : CurveModel κ (Limits.pullback (specMap k κ) (i₂ ≫ c₂) : Scheme).functionField)
    (j₂ : (Limits.pullback (specMap k κ) (i₂ ≫ c₂) : Scheme) ⟶ M₂.C) [IsOpenImmersion j₂]
      [QuasiCompact j₂] [QuasiSeparated j₂]
    (hj₂ : DenseRange j₂)
    (hfield₂ : algebraMap (Limits.pullback (specMap k κ) (i₂ ≫ c₂) : Scheme).functionField
      (Limits.pullback (specMap k κ) (i₂ ≫ c₂) : Scheme).functionField =
      (j₂.functionFieldMap hj₂).comp M₂.ffEquiv.toRingHom)
    (hbase₂ : j₂ ≫ M₂.toBase = Limits.pullback.fst (specMap k κ) (i₂ ≫ c₂))
    (Q₂ : ∀ q : M₂.openBoundaryPlaces j₂,
      Ideal (normalizationCommAlgCat q.val.toValuationSubring Ω₂))
    [∀ q, (Q₂ q).IsMaximal]
    (hthree₂ : 3 ≤ Nat.card (M₂.openBoundaryPlaces j₂))
    (eP : Aut (fiber (((Limits.pullback (specMap k κ) (i ≫ c) : Scheme).genericExtensionMorphism
      Ω) ≫ (Limits.pullback.snd (specMap k κ) (i ≫ c)))) ≃ₜ* Aut (fiber (((Limits.pullback
      (specMap k κ) (i₂ ≫ c₂) : Scheme).genericExtensionMorphism Ω₂) ≫ (Limits.pullback.snd
      (specMap k κ) (i₂ ≫ c₂)))))
    (hP : ∀ γ, arithmeticFundamentalGroupHom k κ (i₂ ≫ c₂) (((Limits.pullback (specMap k κ) (i₂ ≫
      c₂) : Scheme).genericExtensionMorphism Ω₂) ≫ (Limits.pullback.snd (specMap k κ) (i₂ ≫ c₂)))
      (eP γ) =
      arithmeticFundamentalGroupHom k κ (i ≫ c) (((Limits.pullback (specMap k κ) (i ≫ c) :
        Scheme).genericExtensionMorphism Ω) ≫ (Limits.pullback.snd (specMap k κ) (i ≫ c))) γ) :
    ∀ eΔ : Aut (fiber ((Limits.pullback (specMap k κ) (i ≫ c) : Scheme).genericExtensionMorphism
      Ω)) ≃ₜ* Aut (fiber ((Limits.pullback (specMap k κ) (i₂ ≫ c₂) :
      Scheme).genericExtensionMorphism Ω₂)),
      (∀ v, fundamentalGroupHom (Limits.pullback.snd (specMap k κ) (i₂ ≫ c₂)) ((Limits.pullback
        (specMap k κ) (i₂ ≫ c₂) : Scheme).genericExtensionMorphism Ω₂) (eΔ v) =
        eP (fundamentalGroupHom (Limits.pullback.snd (specMap k κ) (i ≫ c)) ((Limits.pullback
          (specMap k κ) (i ≫ c) : Scheme).genericExtensionMorphism Ω) v)) →
      ∃ (q : M₂.openBoundaryPlaces j₂) (a : Aut (fiber ((Limits.pullback (specMap k κ) (i₂ ≫ c₂) :
        Scheme).genericExtensionMorphism Ω₂))),
        (boundaryPlaceInertiaLift M j hj hfield Q p).toMonoidHom.range.map
            eΔ.toMonoidHom =
          (genericPlaceInertia (Limits.pullback (specMap k κ) (i₂ ≫ c₂) : Scheme) q.val (Q₂
            q)).map (MulAut.conj a).toMonoidHom := by
  intro eΔ heΔ
  obtain ⟨eΔ', heΔ', q, a, hq⟩ :=
    actual_rationalCusp_image_eq_boundary_conjugate
      (k := k) (κ := κ) (c := c) (i := i) (M := M) (eC := eC) (heC := heC)
      (j := j) (hj := hj) (hproj := hproj) (hbase := hbase) (hfield := hfield)
      (Q := Q) (V := V) (hV := hV)
      hπ e0 hchart p hord jgeom jarith hchartpoint hpoint hbasearith hthree₁
      c₂ i₂ M₂ j₂ hj₂ hfield₂ hbase₂ Q₂ hthree₂ eP hP
  have heq : eΔ' = eΔ := geometricEquiv_eq_of_same_arithmeticEquiv
    k κ X₁ X₂ (i ≫ c) (i₂ ≫ c₂)
    ((Limits.pullback (specMap k κ) (i ≫ c) : Scheme).genericExtensionMorphism Ω)
    ((Limits.pullback (specMap k κ) (i₂ ≫ c₂) : Scheme).genericExtensionMorphism Ω₂)
    eP eΔ' eΔ heΔ' heΔ
  exact ⟨q, a, heq ▸ hq⟩

end SourceChart
end AnabelianGeometry.WeightFiltration
