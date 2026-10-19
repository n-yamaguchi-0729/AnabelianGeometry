/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/
import Nyll.AlgebraicCurves.Models.Rational.PuncturedProjectiveLineAmbientFields
import Nyll.AlgebraicCurves.Models.Rational.RationalConfigurationBoundaryPlaceOrders
import Nyll.AlgebraicCurves.Models.Ramification.BoundaryNormalizationPrimes
import Nyll.AnabelianGeometry.WeightFiltration.FieldChartBoundaryPrimeFamily
import Nyll.AnabelianGeometry.WeightFiltration.FixedArithmeticRationalCuspRecognition

/-! # All original cusps of bare finite rational configurations

Only the finite configurations, their cardinalities, and the arithmetic
isomorphism over the original number field are supplied as geometric input.
The actual charts, places, orders, function-field coordinates and point equations
are constructed by the imported owners. Both ambient fields and both original
normalization-prime families remain fixed. One geometric equivalence is chosen
before quantification over all source cusps.

This is an inertia-recognition statement, not yet projective reconstruction.
-/

noncomputable section
open CategoryTheory AlgebraicGeometry AlgebraicCurve AlgebraicGeometry.FiniteEtale
open SchemeTheory EtaleFundamentalGroups.Inertia
open scoped RatFunc

namespace AlgebraicGeometry.ProjSpace

attribute [local instance] MvPolynomial.gradedAlgebra Polynomial.algebra
  rationalConfigurationGeometricFieldAlgebra rationalConfigurationGeometricConstantAlgebra
  rationalConfigurationGeometricField_scalarTower
  placeBaseAmbientAlgebra placeBaseAmbientTower placeConstantAmbientTower

local instance (priority := 2000) bareConfigurationSMulRatFunc
    {A E : Type*} [CommSemiring A] [Field E] [Algebra A (RatFunc E)] :
    SMul A (RatFunc E) := (inferInstance : Algebra A (RatFunc E)).toSMul

/-- The literal geometric pullback, with all original configuration parameters. -/
abbrev rationalConfigurationGeometricScheme
    (k κ : Type) [Field k] [Field κ] [Algebra k κ]
    (s : Finset (Projectivization k (k × k))) : Scheme :=
  Limits.pullback (Spec.map (CommRingCat.ofHom (algebraMap k κ)))
    ((rationalConfigurationOpen s).ι ≫ π k 1)

/-- The generic point of the original arithmetic open, induced from the same Ω. -/
def rationalConfigurationArithmeticBasePoint
    (k κ : Type) [Field k] [Field κ] [Algebra k κ] [Infinite k]
    (s : Finset (Projectivization k (k × k)))
    (Ω : Type) [Field Ω]
    [Algebra (rationalConfigurationGeometricScheme k κ s).functionField Ω] :
    Spec (.of Ω) ⟶ (rationalConfigurationOpen s : Scheme) :=
  (rationalConfigurationGeometricScheme k κ s).genericExtensionMorphism Ω ≫
    Limits.pullback.snd (Spec.map (CommRingCat.ofHom (algebraMap k κ)))
      ((rationalConfigurationOpen s).ι ≫ π k 1)

/-- The actual geometric fundamental group at that fixed ambient-field point. -/
abbrev rationalConfigurationGeometricGroup
    (k κ : Type) [Field k] [Field κ] [Algebra k κ] [Infinite k]
    (s : Finset (Projectivization k (k × k)))
    (Ω : Type) [Field Ω]
    [Algebra (rationalConfigurationGeometricScheme k κ s).functionField Ω] :=
  Aut (fiber ((rationalConfigurationGeometricScheme k κ s).genericExtensionMorphism Ω))

/-- The actual arithmetic fundamental group at the corresponding arithmetic point. -/
abbrev rationalConfigurationArithmeticGroup
    (k κ : Type) [Field k] [Field κ] [Algebra k κ] [Infinite k]
    (s : Finset (Projectivization k (k × k)))
    (Ω : Type) [Field Ω]
    [Algebra (rationalConfigurationGeometricScheme k κ s).functionField Ω] :=
  Aut (fiber (rationalConfigurationArithmeticBasePoint k κ s Ω))

/-- The original geometric-to-arithmetic map, with no choice of a lift. -/
def rationalConfigurationGeometricInclusion
    (k κ : Type) [Field k] [Field κ] [Algebra k κ] [Infinite k]
    (s : Finset (Projectivization k (k × k)))
    (Ω : Type) [Field Ω]
    [Algebra (rationalConfigurationGeometricScheme k κ s).functionField Ω] :
    rationalConfigurationGeometricGroup k κ s Ω →ₜ*
      rationalConfigurationArithmeticGroup k κ s Ω :=
  fundamentalGroupHom
    (Limits.pullback.snd (Spec.map (CommRingCat.ofHom (algebraMap k κ)))
      ((rationalConfigurationOpen s).ι ≫ π k 1))
    ((rationalConfigurationGeometricScheme k κ s).genericExtensionMorphism Ω)

/-- Original place inertia, using a fixed prime family in the original RatFunc chart. -/
def rationalConfigurationChosenInertia
    (k κ : Type) [Field k] [Field κ] [CharZero κ] [Algebra k κ] [Infinite k]
    (s : Finset (Projectivization k (k × k)))
    (Ω : Type) [Field Ω] [IsAlgClosed Ω]
    [Algebra (rationalConfigurationGeometricScheme k κ s).functionField Ω]
    [IsAlgClosure (rationalConfigurationGeometricScheme k κ s).functionField Ω]
    (p : (projectiveLineRatFuncModel κ).openBoundaryPlaces
      (rationalConfigurationBaseChangeChart k κ s)) :
    Subgroup (rationalConfigurationGeometricGroup k κ s Ω) := by
  let U := rationalConfigurationGeometricScheme k κ s
  let : CharZero U.functionField := Algebra.charZero_of_charZero (R := κ) (A := U.functionField)
  let : IsSepClosure U.functionField Ω := inferInstance
  let : Algebra (RatFunc κ) Ω := rationalConfigurationGeometricAmbientAlgebra k κ s Ω
  let : IsScalarTower (RatFunc κ) U.functionField Ω :=
    IsScalarTower.of_algebraMap_eq' rfl
  let : IsAlgClosure (RatFunc κ) Ω :=
    rationalConfigurationAmbient_isAlgClosure_geometric k κ s Ω
  let : IsSepClosure (RatFunc κ) Ω := inferInstance
  exact AnabelianGeometry.WeightFiltration.genericPlaceInertia U p.val
    ((projectiveLineRatFuncModel κ).boundaryNormalizationPrimes
      (Ω := Ω) (rationalConfigurationBaseChangeChart k κ s) p)

/-- A canonical ambient algebraic closure for the actual geometric open. -/
abbrev rationalConfigurationCanonicalAmbient
    (k : Type) [Field k] [NumberField k]
    (s : Finset (Projectivization k (k × k))) :=
  AlgebraicClosure
    (rationalConfigurationGeometricScheme k (AlgebraicClosure k) s).functionField

end AlgebraicGeometry.ProjSpace

namespace AnabelianGeometry.WeightFiltration

open AlgebraicGeometry.ProjSpace

attribute [local instance] MvPolynomial.gradedAlgebra Polynomial.algebra
  rationalConfigurationGeometricFieldAlgebra rationalConfigurationGeometricConstantAlgebra
  rationalConfigurationGeometricField_scalarTower
  placeBaseAmbientAlgebra placeBaseAmbientTower placeConstantAmbientTower

local instance (priority := 2000) bareRecognitionSMulRatFunc
    {A E : Type*} [CommSemiring A] [Field E] [Algebra A (RatFunc E)] :
    SMul A (RatFunc E) := (inferInstance : Algebra A (RatFunc E)).toSMul

/-- Every actual source cusp is recognized using one fixed geometric equivalence
above the given arithmetic isomorphism. All finite cardinalities at least three
are retained; the target is displayed in its original RatFunc chart and original Q. -/
theorem bare_rationalConfiguration_allCusps_recognition
    (k κ : Type) [Field k] [NumberField k]
    [Field κ] [CharZero κ] [IsAlgClosed κ] [Algebra k κ] [IsAlgClosure k κ]
    (s t : Finset (Projectivization k (k × k))) (hs : 3 ≤ s.card) (ht : 3 ≤ t.card)
    (Ω₁ Ω₂ : Type) [Field Ω₁] [Field Ω₂] [IsAlgClosed Ω₁] [IsAlgClosed Ω₂]
    [Algebra (rationalConfigurationGeometricScheme k κ s).functionField Ω₁]
    [Algebra (rationalConfigurationGeometricScheme k κ t).functionField Ω₂]
    [IsAlgClosure (rationalConfigurationGeometricScheme k κ s).functionField Ω₁]
    [IsAlgClosure (rationalConfigurationGeometricScheme k κ t).functionField Ω₂]
    (eP : rationalConfigurationArithmeticGroup k κ s Ω₁ ≃ₜ*
      rationalConfigurationArithmeticGroup k κ t Ω₂)
    (hP : ∀ γ,
      arithmeticFundamentalGroupHom k κ ((rationalConfigurationOpen t).ι ≫ π k 1)
        (rationalConfigurationArithmeticBasePoint k κ t Ω₂) (eP γ) =
      arithmeticFundamentalGroupHom k κ ((rationalConfigurationOpen s).ι ≫ π k 1)
        (rationalConfigurationArithmeticBasePoint k κ s Ω₁) γ) :
    ∃ eΔ : rationalConfigurationGeometricGroup k κ s Ω₁ ≃ₜ*
        rationalConfigurationGeometricGroup k κ t Ω₂,
      (∀ v, rationalConfigurationGeometricInclusion k κ t Ω₂ (eΔ v) =
        eP (rationalConfigurationGeometricInclusion k κ s Ω₁ v)) ∧
      ∀ p : (projectiveLineRatFuncModel κ).openBoundaryPlaces
          (rationalConfigurationBaseChangeChart k κ s),
        ∃ (q : (projectiveLineRatFuncModel κ).openBoundaryPlaces
            (rationalConfigurationBaseChangeChart k κ t))
          (a : rationalConfigurationGeometricGroup k κ t Ω₂),
          (rationalConfigurationChosenInertia k κ s Ω₁ p).map eΔ.toMonoidHom =
            (rationalConfigurationChosenInertia k κ t Ω₂ q).map
              (MulAut.conj a).toMonoidHom := by
  classical
  let U₁ := rationalConfigurationGeometricScheme k κ s
  let U₂ := rationalConfigurationGeometricScheme k κ t
  let M := projectiveLineRatFuncModel κ
  let j₁ : U₁ ⟶ M.C := rationalConfigurationBaseChangeChart k κ s
  let jt : U₂ ⟶ M.C := rationalConfigurationBaseChangeChart k κ t
  let : IsIntegral (projectiveLineScheme k) := projectiveSpace_isIntegral k 1
  let : SmoothOfRelativeDimension 1 (π k 1) := projectiveLine_smoothOfRelativeDimension k
  let : GeometricallyIntegral (π k 1) := projectiveSpace_geometricallyIntegral k 1
  let : IsSepClosure k κ := inferInstance
  let : IsOpenImmersion j₁ := inferInstanceAs
    (IsOpenImmersion (rationalConfigurationBaseChangeChart k κ s))
  let : QuasiCompact j₁ := inferInstanceAs
    (QuasiCompact (rationalConfigurationBaseChangeChart k κ s))
  let : QuasiSeparated j₁ := inferInstanceAs
    (QuasiSeparated (rationalConfigurationBaseChangeChart k κ s))
  let : IsOpenImmersion jt := inferInstanceAs
    (IsOpenImmersion (rationalConfigurationBaseChangeChart k κ t))
  let : CharZero U₁.functionField :=
    Algebra.charZero_of_charZero (R := κ) (A := U₁.functionField)
  let : CharZero U₂.functionField :=
    Algebra.charZero_of_charZero (R := κ) (A := U₂.functionField)
  let : IsSepClosure U₁.functionField Ω₁ := inferInstance
  let : IsSepClosure U₂.functionField Ω₂ := inferInstance
  let : Algebra (RatFunc κ) Ω₁ := rationalConfigurationGeometricAmbientAlgebra k κ s Ω₁
  let : Algebra κ Ω₁ := rationalConfigurationConstantAmbientAlgebra k κ s Ω₁
  let : Algebra (RatFunc k) Ω₁ := rationalConfigurationArithmeticAmbientAlgebra k κ s Ω₁
  let : Algebra k Ω₁ := rationalConfigurationBaseAmbientAlgebra k κ s Ω₁
  let : Algebra (RatFunc κ) Ω₂ := rationalConfigurationGeometricAmbientAlgebra k κ t Ω₂
  let : Algebra κ Ω₂ := rationalConfigurationConstantAmbientAlgebra k κ t Ω₂
  obtain ⟨hF₁, hκF₁, hκU₁, hkF₁, hkκ₁, hkkF₁⟩ :=
    rationalConfigurationAmbient_scalarTowers k κ s Ω₁
  let : IsScalarTower (RatFunc κ) U₁.functionField Ω₁ := hF₁
  let : IsScalarTower κ (RatFunc κ) Ω₁ := hκF₁
  let : IsScalarTower κ U₁.functionField Ω₁ := hκU₁
  let : IsScalarTower (RatFunc k) (RatFunc κ) Ω₁ := hkF₁
  let : IsScalarTower k κ Ω₁ := hkκ₁
  let : IsScalarTower k (RatFunc k) Ω₁ := hkkF₁
  have htowers₂ := rationalConfigurationAmbient_scalarTowers k κ t Ω₂
  let : IsScalarTower (RatFunc κ) U₂.functionField Ω₂ := htowers₂.1
  let : IsScalarTower κ (RatFunc κ) Ω₂ := htowers₂.2.1
  let : IsScalarTower κ U₂.functionField Ω₂ := htowers₂.2.2.1
  let : IsAlgClosure (RatFunc κ) Ω₁ :=
    rationalConfigurationAmbient_isAlgClosure_geometric k κ s Ω₁
  let : IsAlgClosure (RatFunc κ) Ω₂ :=
    rationalConfigurationAmbient_isAlgClosure_geometric k κ t Ω₂
  let : IsAlgClosure (RatFunc k) Ω₁ :=
    rationalConfigurationAmbient_isAlgClosure_arithmetic k κ s Ω₁
  let : IsSepClosure (RatFunc κ) Ω₁ := inferInstance
  let : IsSepClosure (RatFunc κ) Ω₂ := inferInstance
  let : IsSepClosure (RatFunc k) Ω₁ := inferInstance
  let : IsGalois (RatFunc k) Ω₁ := inferInstance
  let : IsCurveOver κ (RatFunc κ) := AlgebraicCurve.instIsCurveOverRatFunc κ
  let : Finite (M.openBoundaryPlaces j₁) := rationalConfigurationBoundaryPlaces_finite k κ s
  let : Nontrivial (M.openBoundaryPlaces j₁) :=
    rationalConfigurationBoundaryPlaces_nontrivial k κ s hs
  let Q₁ := M.boundaryNormalizationPrimes (Ω := Ω₁) j₁
  let Qt := M.boundaryNormalizationPrimes (Ω := Ω₂) jt
  let : ∀ p, (Q₁ p).IsMaximal := fun p => inferInstance
  let : ∀ q, (Qt q).IsMaximal := fun q => inferInstance
  let et := rationalConfigurationGeometricFieldAlgEquiv k κ t
  let N := rationalConfigurationFunctionFieldModel k κ t
  let j₂ : U₂ ⟶ N.C := rationalConfigurationBaseChangeChart k κ t
  let : IsOpenImmersion j₂ := inferInstanceAs
    (IsOpenImmersion (rationalConfigurationBaseChangeChart k κ t))
  let : QuasiCompact j₂ := inferInstanceAs
    (QuasiCompact (rationalConfigurationBaseChangeChart k κ t))
  let : QuasiSeparated j₂ := inferInstanceAs
    (QuasiSeparated (rationalConfigurationBaseChangeChart k κ t))
  let : IsCurveOver κ U₂.functionField := rationalConfigurationFunctionField_isCurveOver k κ t
  let E := M.reparametrizeFieldBoundaryEquiv et jt
  obtain ⟨Q₂, hQ₂, hsame⟩ :=
    exists_fieldChart_boundaryNormalizationPrimeFamily_same_inertia
      U₂ et (fun _ => rfl) M jt Qt
  let : ∀ q : N.openBoundaryPlaces j₂, (Q₂ q).IsMaximal := fun q => hQ₂ q
  obtain ⟨eΔ, heΔ, _⟩ := exists_geometricEquiv_equivariant_of_arithmeticEquiv
    k κ (rationalConfigurationOpen s : Scheme) (rationalConfigurationOpen t : Scheme)
    ((rationalConfigurationOpen s).ι ≫ π k 1) ((rationalConfigurationOpen t).ι ≫ π k 1)
    (U₁.genericExtensionMorphism Ω₁) (U₂.genericExtensionMorphism Ω₂) eP hP
  refine ⟨eΔ, heΔ, ?_⟩
  intro p
  obtain ⟨V, hV, hord⟩ :=
    rationalConfiguration_every_boundaryPlace_exists_rationalPlace k κ s p
  have hj₁ : DenseRange j₁ := rationalConfigurationBaseChangeChart_denseRange k κ s
  have hj₂ : DenseRange j₂ := rationalConfigurationBaseChangeChart_denseRange k κ t
  have hfield₁ : algebraMap (RatFunc κ) U₁.functionField =
      (j₁.functionFieldMap hj₁).comp M.ffEquiv.toRingHom :=
    rationalConfigurationGeometricFunctionFieldEquiv_hfield k κ s
  have hfield₂ : algebraMap U₂.functionField U₂.functionField =
      (j₂.functionFieldMap hj₂).comp N.ffEquiv.toRingHom :=
    rationalConfigurationFunctionFieldModel_hfield k κ t
  have hthree₂ : 3 ≤ Nat.card (N.openBoundaryPlaces j₂) := by
    rw [rationalConfigurationFunctionFieldModel_boundary_card]
    exact ht
  obtain ⟨q₂, a, hrec⟩ :=
    actual_rationalCusp_image_eq_boundary_conjugate_of_fixed_geometricEquiv
      (k := k) (κ := κ) (c := π k 1) (i := (rationalConfigurationOpen s).ι)
      (M := M) (eC := projectiveLineBaseChangeIso k κ)
      (heC := projectiveLineBaseChangeIso_hom_snd k κ)
      (j := j₁) (hj := hj₁)
      (hproj := rationalConfigurationBaseChangeChart_comp_comparison_fst k κ s)
      (hbase := rationalConfigurationBaseChangeChart_comp_π k κ s)
      (hfield := hfield₁) (Q := Q₁) (V := V) (hV := hV)
      (projectiveLineBaseChangeProjection_denseRange k κ)
      (projectiveLineRatFuncEquiv k) (projectiveLineRatFuncModel_baseChange_hchart k κ)
      p hord (rationalConfigurationGeometricGenericPoint k κ s)
      (rationalConfigurationArithmeticGenericPoint k s)
      (rationalConfigurationGenericPoint_hchartpoint_of_hfield k κ s hfield₁)
      (rationalConfigurationGenericPoint_hpoint k κ s)
      (rationalConfigurationGenericPoint_hbasearith k s)
      (rationalConfigurationBoundaryPlaces_card_ge_three k κ s hs)
      (π k 1) (rationalConfigurationOpen t).ι N j₂ hj₂ hfield₂
      (rationalConfigurationBaseChangeChart_comp_π k κ t) Q₂ hthree₂ eP hP eΔ heΔ
  let q := E.symm q₂
  have htarget : rationalConfigurationChosenInertia k κ t Ω₂ q =
      genericPlaceInertia U₂ q₂.val (Q₂ q₂) := by
    change genericPlaceInertia U₂ q.val (Qt q) = _
    have htargetValue := congrArg
      (fun r : N.openBoundaryPlaces j₂ => genericPlaceInertia U₂ r.val (Q₂ r))
      (E.apply_symm_apply q₂)
    exact (hsame (E.symm q₂)).trans htargetValue
  have hsource : (boundaryPlaceInertiaLift M j₁ hj₁ hfield₁ Q₁ p).toMonoidHom.range =
      rationalConfigurationChosenInertia k κ s Ω₁ p := by
    exact boundaryPlaceInertiaLift_range M j₁ hj₁ hfield₁ Q₁ p
  refine ⟨q, a, ?_⟩
  exact (congrArg (fun H => H.map eΔ.toMonoidHom) hsource.symm).trans
    (hrec.trans (congrArg (fun H => H.map (MulAut.conj a).toMonoidHom) htarget.symm))

/-- Canonical closure/basepoint specialization: the inputs are exactly the
number field, the two finite rational configurations, cardinality bounds and
the arithmetic isomorphism over G_k. -/
theorem bare_rationalConfiguration_allCusps_recognition_canonical
    (k : Type) [Field k] [NumberField k]
    (s t : Finset (Projectivization k (k × k))) (hs : 3 ≤ s.card) (ht : 3 ≤ t.card)
    (eP : rationalConfigurationArithmeticGroup k (AlgebraicClosure k) s
        (rationalConfigurationCanonicalAmbient k s) ≃ₜ*
      rationalConfigurationArithmeticGroup k (AlgebraicClosure k) t
        (rationalConfigurationCanonicalAmbient k t))
    (hP : ∀ γ,
      arithmeticFundamentalGroupHom k (AlgebraicClosure k)
        ((rationalConfigurationOpen t).ι ≫ π k 1)
        (rationalConfigurationArithmeticBasePoint k (AlgebraicClosure k) t
          (rationalConfigurationCanonicalAmbient k t)) (eP γ) =
      arithmeticFundamentalGroupHom k (AlgebraicClosure k)
        ((rationalConfigurationOpen s).ι ≫ π k 1)
        (rationalConfigurationArithmeticBasePoint k (AlgebraicClosure k) s
          (rationalConfigurationCanonicalAmbient k s)) γ) :
    ∃ eΔ : rationalConfigurationGeometricGroup k (AlgebraicClosure k) s
          (rationalConfigurationCanonicalAmbient k s) ≃ₜ*
        rationalConfigurationGeometricGroup k (AlgebraicClosure k) t
          (rationalConfigurationCanonicalAmbient k t),
      (∀ v, rationalConfigurationGeometricInclusion k (AlgebraicClosure k) t
          (rationalConfigurationCanonicalAmbient k t) (eΔ v) =
        eP (rationalConfigurationGeometricInclusion k (AlgebraicClosure k) s
          (rationalConfigurationCanonicalAmbient k s) v)) ∧
      ∀ p : (projectiveLineRatFuncModel (AlgebraicClosure k)).openBoundaryPlaces
          (rationalConfigurationBaseChangeChart k (AlgebraicClosure k) s),
        ∃ (q : (projectiveLineRatFuncModel (AlgebraicClosure k)).openBoundaryPlaces
            (rationalConfigurationBaseChangeChart k (AlgebraicClosure k) t))
          (a : rationalConfigurationGeometricGroup k (AlgebraicClosure k) t
            (rationalConfigurationCanonicalAmbient k t)),
          (rationalConfigurationChosenInertia k (AlgebraicClosure k) s
            (rationalConfigurationCanonicalAmbient k s) p).map eΔ.toMonoidHom =
          (rationalConfigurationChosenInertia k (AlgebraicClosure k) t
            (rationalConfigurationCanonicalAmbient k t) q).map (MulAut.conj a).toMonoidHom :=
  bare_rationalConfiguration_allCusps_recognition k (AlgebraicClosure k) s t hs ht
    (rationalConfigurationCanonicalAmbient k s) (rationalConfigurationCanonicalAmbient k t)
    eP hP

end AnabelianGeometry.WeightFiltration
