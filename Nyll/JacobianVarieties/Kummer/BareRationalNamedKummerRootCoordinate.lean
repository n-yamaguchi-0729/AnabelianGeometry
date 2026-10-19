/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.AlgebraicCurves.Models.Rational.PuncturedProjectiveLineOriginalFields
import Nyll.JacobianVarieties.Kummer.NamedKummerCoefficientRootCoordinate
import Nyll.AnabelianGeometry.WeightFiltration.BareRationalConfigurationCuspRecognition

/-! # Retaining the same root coordinate at the original bare point

The canonical generic root coordinate and the original bare-point coordinate
are related by literal equality transport of the actual fiber. The same
chosen torsor, geometric comparison and original generic action are retained.
-/

noncomputable section
open AlgebraicGeometry AlgebraicGeometry.FiniteEtale AlgebraicCurve
open AlgebraicCurve.CurveModel.OpenKummer
open CategoryTheory CategoryTheory.PreGaloisCategory
open JacobianVarieties.Kummer
open scoped RatFunc FintypeCatDiscrete

namespace AlgebraicGeometry.ProjSpace

attribute [local instance] MvPolynomial.gradedAlgebra Polynomial.algebra
  rationalConfigurationGeometricFieldAlgebra rationalConfigurationGeometricConstantAlgebra
  rationalConfigurationOriginalFieldAlgebra rationalConfigurationOriginalConstantAlgebra
  rationalConfigurationOriginalFieldExtensionAlgebra

local instance (priority := 2000) bareRootedRestrictionSMulRatFunc
    {A E : Type*} [CommSemiring A] [Field E] [Algebra A (RatFunc E)] :
    SMul A (RatFunc E) := (inferInstance : Algebra A (RatFunc E)).toSMul

local instance bareRootedRestrictionArithmeticChart_isOpenImmersion
    (k : Type) [Field k] (s : Finset (Projectivization k (k × k))) :
    IsOpenImmersion (show (rationalConfigurationOpen s : Scheme) ⟶
      (projectiveLineRatFuncModel k).C from (rationalConfigurationOpen s).ι) :=
  inferInstanceAs (IsOpenImmersion (rationalConfigurationOpen s).ι)

local instance bareRootedRestrictionGeometricChart_isOpenImmersion
    (k κ : Type) [Field k] [Field κ] [Algebra k κ] [IsAlgClosed κ]
    (s : Finset (Projectivization k (k × k))) :
    IsOpenImmersion (show rationalConfigurationGeometricScheme k κ s ⟶
      (projectiveLineRatFuncModel κ).C from rationalConfigurationBaseChangeChart k κ s) :=
  rationalConfigurationBaseChangeChart_isOpenImmersion k κ s

/-- Equality transport retains the coordinate on the same chosen torsor. -/
private theorem restriction_at_composite_point_rooted
    (k κ : Type) [Field k] [Field κ] [Algebra k κ] [IsSepClosure k κ]
    {Ω : Type} [Field Ω] [IsSepClosed Ω]
    {X Y : Scheme} (a : Y ⟶ X) (x : Spec (.of Ω) ⟶ Y)
    (y : Spec (.of Ω) ⟶ X) (h : x ≫ a = y)
    (c : X ⟶ Spec (.of k)) (n : ℕ) (WA : FiniteEtale X) (WG : FiniteEtale Y)
    [MulAction (rootsOfUnity n κ) ((fiber x).obj WG)]
    (b : Ω) (ρ : κ →+* Ω)
    (e : (fiber y).obj WA ≃ {z : Ω // z ^ n = b})
    (H : ∃ t : Torsor (rootsOfUnity n κ) ((fiber y).obj WA),
      ∃ E : (fiber x).obj WG ≃ (fiber y).obj WA,
        (∀ (ζ : rootsOfUnity n κ) z,
          (e (t.toMulAction.toSMul.smul ζ z)).val = ρ (ζ.val : κ) * (e z).val) ∧
        (∀ (ζ : rootsOfUnity n κ) z, E (ζ • z) = t.toMulAction.toSMul.smul ζ (E z)) ∧
        (∀ (g : π₁ᵉᵗ(x)) z,
          E (g • z) = pointedFundamentalGroupHom a x y h g • E z) ∧
        ∀ (p : π₁ᵉᵗ(y)) (ζ : rootsOfUnity n κ) z,
          p • (t.toMulAction.toSMul.smul ζ z) = t.toMulAction.toSMul.smul
            (restrictRootsOfUnity (arithmeticFundamentalGroupHom k κ c y p).toRingHom n ζ)
            (p • z)) :
    ∃ t : Torsor (rootsOfUnity n κ) ((fiber (x ≫ a)).obj WA),
      ∃ E : (fiber x).obj WG ≃ (fiber (x ≫ a)).obj WA,
      ∃ e' : (fiber (x ≫ a)).obj WA ≃ {z : Ω // z ^ n = b},
        (∀ (ζ : rootsOfUnity n κ) z,
          (e' (t.toMulAction.toSMul.smul ζ z)).val = ρ (ζ.val : κ) * (e' z).val) ∧
        (∀ (ζ : rootsOfUnity n κ) z, E (ζ • z) = t.toMulAction.toSMul.smul ζ (E z)) ∧
        (∀ (g : π₁ᵉᵗ(x)) z, E (g • z) = fundamentalGroupHom a x g • E z) ∧
        (∀ (p : π₁ᵉᵗ(x ≫ a)) (ζ : rootsOfUnity n κ) z,
          p • (t.toMulAction.toSMul.smul ζ z) = t.toMulAction.toSMul.smul
            (restrictRootsOfUnity
              (arithmeticFundamentalGroupHom k κ c (x ≫ a) p).toRingHom n ζ) (p • z)) ∧
        ∀ z, e' z = e (((eqToIso (congrArg fiber h)).hom.app WA) z) := by
  subst y
  obtain ⟨t, E, ht, hμ, hI, hsemi⟩ := H
  exact ⟨t, E, e, ht, hμ, hI, hsemi, fun _ => rfl⟩

/-- Retain the same arithmetic root coordinate at the original bare point,
with its literal equality transport and its original generic Galois formula. -/
theorem rationalConfiguration_namedKummer_geometricRestriction_with_rootCoordinate
    (k κ : Type) [Field k] [CharZero k] [Field κ] [IsAlgClosed κ]
    [Algebra k κ] [IsAlgClosure k κ]
    (s : Finset (Projectivization k (k × k)))
    (Ω : Type) [Field Ω] [IsAlgClosed Ω]
    [Algebra (rationalConfigurationGeometricScheme k κ s).functionField Ω]
    [IsAlgClosure (rationalConfigurationGeometricScheme k κ s).functionField Ω]
    (n : ℕ+)
    (u : Pic0.openKummerUnits k (RatFunc k)
      ((projectiveLineRatFuncModel k).openBoundaryPlaces (rationalConfigurationOpen s).ι) n)
    (w : Pic0.openKummerUnits κ (RatFunc κ)
      ((projectiveLineRatFuncModel κ).openBoundaryPlaces
        (rationalConfigurationBaseChangeChart k κ s)) n)
    (hunit : (w.val : RatFunc κ) = algebraMap (RatFunc k) (RatFunc κ) (u.val : RatFunc k)) :
    letI : Algebra (rationalConfigurationOpen s : Scheme).functionField Ω :=
      rationalConfigurationOriginalAmbientAlgebra k κ s Ω
    letI : Algebra (RatFunc k) Ω := rationalConfigurationArithmeticAmbientAlgebra k κ s Ω
    letI : Algebra κ Ω := rationalConfigurationConstantAmbientAlgebra k κ s Ω
    letI : IsSepClosure (rationalConfigurationOpen s : Scheme).functionField Ω :=
      (rationalConfigurationOriginalField_suppliers k κ s Ω).2.2.2.2.1
    let hn : IsUnit ((n : ℕ) : k) :=
      isUnit_iff_ne_zero.mpr (Nat.cast_ne_zero.mpr n.ne_zero)
    let hnκ : IsUnit ((n : ℕ) : κ) := by
      simpa only [map_natCast] using hn.map (algebraMap k κ)
    let ξG := (rationalConfigurationGeometricScheme k κ s).genericExtensionMorphism Ω
    let ξA := rationalConfigurationArithmeticBasePoint k κ s Ω
    let jA := (rationalConfigurationOpen s).ι
    let jG := rationalConfigurationBaseChangeChart k κ s
    let MA := projectiveLineRatFuncModel k
    let MG := projectiveLineRatFuncModel κ
    let hjA := rationalConfigurationOpen_denseRange k s
    let hjG := rationalConfigurationBaseChangeChart_denseRange k κ s
    let WA := MA.openKummerCover (MA.openBoundaryPlaces jA) n hn u jA hjA
      (MA.place_not_mem_openBoundaryPlaces jA)
    let WG := MG.openKummerCover (MG.openBoundaryPlaces jG) n hnκ w jG hjG
      (MG.place_not_mem_openBoundaryPlaces jG)
    let q := arithmeticFundamentalGroupHom k κ (jA ≫ MA.toBase) ξA
    let inc := rationalConfigurationGeometricInclusion k κ s Ω
    letI := CurveModel.OpenKummer.kummerGeometricRootAction MG (MG.openBoundaryPlaces jG)
      n w jG hjG (MG.place_not_mem_openBoundaryPlaces jG) hnκ ξG
    let ξCan := (rationalConfigurationOpen s : Scheme).genericExtensionMorphism Ω
    let b := algebraMap (RatFunc k) Ω (u.val : RatFunc k)
    ∃ hp : ξA = ξCan,
      ∃ eCan : (fiber ξCan).obj WA ≃ {z : Ω // z ^ (n : ℕ) = b},
        (∀ (σ : Gal(Ω/(rationalConfigurationOpen s : Scheme).functionField))
            (x : (fiber ξCan).obj WA),
          (eCan ((show π₁ᵉᵗ(ξCan) from
            fundamentalGroupHom ((rationalConfigurationOpen s : Scheme).fromSpecStalk
              (genericPoint (rationalConfigurationOpen s : Scheme)))
              (Spec.map (CommRingCat.ofHom
                (algebraMap (rationalConfigurationOpen s : Scheme).functionField Ω)))
              (toAut (fib (rationalConfigurationOpen s : Scheme).functionField Ω)
                Gal(Ω/(rationalConfigurationOpen s : Scheme).functionField) σ)) • x)).val =
                  σ (eCan x).val) ∧
        ∃ tA : Torsor (rootsOfUnity (n : ℕ) κ) ((fiber ξA).obj WA),
        ∃ E : (fiber ξG).obj WG ≃ (fiber ξA).obj WA,
        ∃ eBare : (fiber ξA).obj WA ≃ {z : Ω // z ^ (n : ℕ) = b},
          (∀ (ζ : rootsOfUnity (n : ℕ) κ) x,
            (eBare (tA.toMulAction.toSMul.smul ζ x)).val =
              algebraMap κ Ω (ζ.val : κ) * (eBare x).val) ∧
          (∀ (ζ : rootsOfUnity (n : ℕ) κ) x,
            E (ζ • x) = tA.toMulAction.toSMul.smul ζ (E x)) ∧
          (∀ (g : π₁ᵉᵗ(ξG)) x, E (g • x) = inc g • E x) ∧
          (∀ (p : π₁ᵉᵗ(ξA)) (ζ : rootsOfUnity (n : ℕ) κ) x,
            p • (tA.toMulAction.toSMul.smul ζ x) =
              tA.toMulAction.toSMul.smul
                (restrictRootsOfUnity (q p).toRingHom (n : ℕ) ζ) (p • x)) ∧
          ∀ x, eBare x = eCan (((eqToIso (congrArg fiber hp)).hom.app WA) x) := by
  let : Algebra (rationalConfigurationOpen s : Scheme).functionField Ω :=
    rationalConfigurationOriginalAmbientAlgebra k κ s Ω
  let : Algebra (RatFunc k) Ω := rationalConfigurationArithmeticAmbientAlgebra k κ s Ω
  let : Algebra κ Ω := rationalConfigurationConstantAmbientAlgebra k κ s Ω
  let : IsSepClosure (rationalConfigurationOpen s : Scheme).functionField Ω :=
    (rationalConfigurationOriginalField_suppliers k κ s Ω).2.2.2.2.1
  intro hn hnκ ξG ξA jA jG MA MG hjA hjG WA WG q inc ξCan b
  let := CurveModel.OpenKummer.kummerGeometricRootAction MG (MG.openBoundaryPlaces jG)
    n w jG hjG (MG.place_not_mem_openBoundaryPlaces jG) hnκ ξG
  let X := (rationalConfigurationOpen s : Scheme)
  let Y := rationalConfigurationGeometricScheme k κ s
  let a : Y ⟶ X := Limits.pullback.snd
    (Spec.map (CommRingCat.ofHom (algebraMap k κ))) (jA ≫ MA.toBase)
  let : Algebra (RatFunc κ) Ω := rationalConfigurationGeometricAmbientAlgebra k κ s Ω
  let : Algebra k Ω := rationalConfigurationBaseAmbientAlgebra k κ s Ω
  have ht := rationalConfigurationAmbient_scalarTowers k κ s Ω
  let : IsScalarTower (RatFunc κ) Y.functionField Ω := ht.1
  let : IsScalarTower (RatFunc k) (RatFunc κ) Ω := ht.2.2.2.1
  let : IsScalarTower k κ Ω := ht.2.2.2.2.1
  obtain ⟨hFA, hAG, hkA, _hAlgA, _hSepA, hpoint, hbaseA, hbaseG⟩ :=
    rationalConfigurationOriginalField_suppliers k κ s Ω
  let : IsScalarTower (RatFunc k) X.functionField Ω := hFA
  let : IsScalarTower X.functionField Y.functionField Ω := hAG
  let : IsScalarTower k X.functionField Ω := hkA
  let : CharZero κ := Algebra.charZero_of_charZero (R := k) (A := κ)
  let : CharZero Y.functionField :=
    Algebra.charZero_of_charZero (R := κ) (A := Y.functionField)
  let : IsSepClosure Y.functionField Ω := inferInstance
  let : IsIntegral (projectiveLineScheme k) := projectiveSpace_isIntegral k 1
  let : IsIntegral (projectiveLineScheme κ) := projectiveSpace_isIntegral κ 1
  have hfieldA : algebraMap (RatFunc k) X.functionField =
      (jA.functionFieldMap hjA).comp MA.ffEquiv.toRingHom := rfl
  have hfieldG : algebraMap (RatFunc κ) Y.functionField =
      (jG.functionFieldMap hjG).comp MG.ffEquiv.toRingHom := rfl
  obtain ⟨tCan, ECan, eA, htA, hgA, hμ, hI, hsemi⟩ :=
    exists_namedKummer_geometricRestriction_equiv_with_coefficientRootCoordinate
      MA MG (MA.openBoundaryPlaces jA) (MG.openBoundaryPlaces jG) n u w hunit
      jA hjA jG hjG (MA.place_not_mem_openBoundaryPlaces jA)
      (MG.place_not_mem_openBoundaryPlaces jG) hn hnκ hfieldA hfieldG a hpoint hbaseA hbaseG
  refine ⟨hpoint, eA, ?_, ?_⟩
  · intro σ x
    exact hgA σ x
  · exact restriction_at_composite_point_rooted k κ a ξG ξCan hpoint
      (jA ≫ MA.toBase) (n : ℕ) WA WG b (algebraMap κ Ω) eA
      ⟨tCan, ECan, htA, hμ, hI, hsemi⟩

end AlgebraicGeometry.ProjSpace
