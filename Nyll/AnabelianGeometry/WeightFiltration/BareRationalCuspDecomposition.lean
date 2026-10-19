/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/
import Nyll.AnabelianGeometry.WeightFiltration.BareRationalConfigurationPunctureEquiv
import Nyll.AnabelianGeometry.WeightFiltration.BoundaryInertiaSelfNormalizer
import Nyll.AnabelianGeometry.WeightFiltration.OriginalRationalCuspDecompositionImage
import Nyll.AnabelianGeometry.WeightFiltration.ArithmeticInertiaNormalizerGroupBridge

/-! # Actual arithmetic decomposition images at the recovered rational cusps

Each arithmetic prime is constructed from the original chosen geometric prime
inside the same ambient field. Its decomposition image is transported only by
the proved equality of the original field-source point and the canonical
arithmetic point. The arithmetic exact sequence and geometric self-normalizer
identify this image with the arithmetic inertia normalizer. The already proved
inertia conjugacy then transports this actual image with the same conjugator.
-/

noncomputable section
open CategoryTheory AlgebraicGeometry AlgebraicCurve AlgebraicGeometry.FiniteEtale
open AlgebraicGeometry.ProjSpace SchemeTheory EtaleFundamentalGroups.Inertia
open AnabelianGeometry.KummerTheory
open scoped RatFunc

namespace AnabelianGeometry.WeightFiltration

attribute [local instance] MvPolynomial.gradedAlgebra Polynomial.algebra
  rationalConfigurationGeometricFieldAlgebra rationalConfigurationGeometricConstantAlgebra
  rationalConfigurationGeometricField_scalarTower
  placeBaseAmbientAlgebra placeBaseAmbientTower placeConstantAmbientTower
  normalizationCommAlgGaloisAction

local instance (priority := 2000) bareDecompositionSMulRatFunc
    {A E : Type*} [CommSemiring A] [Field E] [Algebra A (RatFunc E)] :
    SMul A (RatFunc E) := (inferInstance : Algebra A (RatFunc E)).toSMul

private def decompositionSubgroupAtEqualPoint
    {X : Scheme} {Ω : Type} [Field Ω]
    {x y : Spec (.of Ω) ⟶ X} (h : x = y) (D : Subgroup (Aut (fiber x))) :
    Subgroup (Aut (fiber y)) :=
  Eq.ndrec (motive := fun z : Spec (.of Ω) ⟶ X => Subgroup (Aut (fiber z))) D h

private theorem decomposition_data_at_canonical_point
    (k κ : Type) [Field k] [Field κ] [Algebra k κ] [IsSepClosure k κ]
    {X Y : Scheme} (f : X ⟶ Spec (.of k)) (u : Y ⟶ X)
    {Ω : Type} [Field Ω] [IsSepClosed Ω]
    (xi : Spec (.of Ω) ⟶ Y) (z : Spec (.of Ω) ⟶ X) (hz : xi ≫ u = z)
    (I : Subgroup (Aut (fiber xi))) (D : Subgroup (Aut (fiber z)))
    (hdata : I.map (pointedFundamentalGroupHom u xi z hz).toMonoidHom ≤ D ∧
      D ≤ Subgroup.normalizer
        (I.map (pointedFundamentalGroupHom u xi z hz).toMonoidHom).carrier ∧
      ∀ τ : Gal(κ/k), ∃ γ : Aut (fiber z),
        γ ∈ D ∧ arithmeticFundamentalGroupHom k κ f z γ = τ) :
    let D' : Subgroup (Aut (fiber (xi ≫ u))) := decompositionSubgroupAtEqualPoint hz.symm D
    I.map (fundamentalGroupHom u xi).toMonoidHom ≤ D' ∧
      D' ≤ Subgroup.normalizer (I.map (fundamentalGroupHom u xi).toMonoidHom).carrier ∧
      ∀ τ : Gal(κ/k), ∃ γ : Aut (fiber (xi ≫ u)),
        γ ∈ D' ∧ arithmeticFundamentalGroupHom k κ f (xi ≫ u) γ = τ := by
  subst z
  exact hdata

/-- The image of the SAME normalization-prime decomposition group at the actual point. -/
def rationalConfigurationChosenDecomposition
    (k κ : Type) [Field k] [NumberField k]
    [Field κ] [CharZero κ] [IsAlgClosed κ] [Algebra k κ] [IsAlgClosure k κ]
    (s : Finset (Projectivization k (k × k)))
    (Ω : Type) [Field Ω] [IsAlgClosed Ω]
    [Algebra (rationalConfigurationGeometricScheme k κ s).functionField Ω]
    [IsAlgClosure (rationalConfigurationGeometricScheme k κ s).functionField Ω]
    (p : (projectiveLineRatFuncModel κ).openBoundaryPlaces
      (rationalConfigurationBaseChangeChart k κ s)) :
    Subgroup (rationalConfigurationArithmeticGroup k κ s Ω) := by
  let U := rationalConfigurationGeometricScheme k κ s
  let M := projectiveLineRatFuncModel κ
  let j : U ⟶ M.C := rationalConfigurationBaseChangeChart k κ s
  let u : U ⟶ (rationalConfigurationOpen s : Scheme) :=
    Limits.pullback.snd (Spec.map (CommRingCat.ofHom (algebraMap k κ)))
      ((rationalConfigurationOpen s).ι ≫ π k 1)
  let : IsOpenImmersion j := inferInstanceAs
    (IsOpenImmersion (rationalConfigurationBaseChangeChart k κ s))
  let : CharZero U.functionField := Algebra.charZero_of_charZero (R := κ) (A := U.functionField)
  let : IsSepClosure k κ := inferInstance
  let : IsSepClosure U.functionField Ω := inferInstance
  let : Algebra (RatFunc κ) Ω := rationalConfigurationGeometricAmbientAlgebra k κ s Ω
  let : Algebra κ Ω := rationalConfigurationConstantAmbientAlgebra k κ s Ω
  let : Algebra (RatFunc k) Ω := rationalConfigurationArithmeticAmbientAlgebra k κ s Ω
  let : Algebra k Ω := rationalConfigurationBaseAmbientAlgebra k κ s Ω
  obtain ⟨hF, hκF, hκU, hkF, hkκ, hkkF⟩ :=
    rationalConfigurationAmbient_scalarTowers k κ s Ω
  let : IsScalarTower (RatFunc κ) U.functionField Ω := hF
  let : IsScalarTower κ (RatFunc κ) Ω := hκF
  let : IsScalarTower κ U.functionField Ω := hκU
  let : IsScalarTower (RatFunc k) (RatFunc κ) Ω := hkF
  let : IsScalarTower k κ Ω := hkκ
  let : IsScalarTower k (RatFunc k) Ω := hkkF
  let : IsAlgClosure (RatFunc κ) Ω :=
    rationalConfigurationAmbient_isAlgClosure_geometric k κ s Ω
  let : IsAlgClosure (RatFunc k) Ω :=
    rationalConfigurationAmbient_isAlgClosure_arithmetic k κ s Ω
  let : IsSepClosure (RatFunc κ) Ω := inferInstance
  let : IsSepClosure (RatFunc k) Ω := inferInstance
  let : IsGalois (RatFunc k) Ω := inferInstance
  let V := (rationalConfiguration_every_boundaryPlace_exists_rationalPlace k κ s p).choose
  have hV : V.IsRational :=
    (rationalConfiguration_every_boundaryPlace_exists_rationalPlace k κ s p).choose_spec.1
  have hord : ∀ x : RatFunc k,
      p.val.ord (algebraMap (RatFunc k) (RatFunc κ) x) = V.ord x :=
    (rationalConfiguration_every_boundaryPlace_exists_rationalPlace k κ s p).choose_spec.2
  let Q := M.boundaryNormalizationPrimes (Ω := Ω) j
  let e := ratFuncRationalPlaceNormalizationEquiv V hV p.val hord (Ω := Ω)
  let Qa : Ideal (normalizationCommAlgCat V.toValuationSubring Ω) :=
    (Q p).comap e.symm.toRingHom
  let jarith := rationalConfigurationArithmeticGenericPoint k s
  let jgeom := rationalConfigurationGeometricGenericPoint k κ s
  let z := Spec.map (CommRingCat.ofHom (algebraMap (RatFunc k) Ω)) ≫ jarith
  let d := (fieldSourceAbsoluteGaloisHom (RatFunc k) Ω jarith).toMonoidHom.comp
    (normalizationDecompositionInclusion V.toValuationSubring (RatFunc k) Ω Qa)
  have hj : DenseRange j := rationalConfigurationBaseChangeChart_denseRange k κ s
  have hfield : algebraMap (RatFunc κ) U.functionField =
      (j.functionFieldMap hj).comp M.ffEquiv.toRingHom :=
    rationalConfigurationGeometricFunctionFieldEquiv_hfield k κ s
  have hchartpoint : U.genericExtensionMorphism Ω ≫ 𝟙 U =
      Spec.map (CommRingCat.ofHom (algebraMap (RatFunc κ) Ω)) ≫ jgeom :=
    rationalConfigurationGenericPoint_hchartpoint_of_hfield k κ s (Ω := Ω) hfield
  have hpoint :
      (Spec.map (CommRingCat.ofHom (algebraMap (RatFunc κ) Ω)) ≫ jgeom) ≫ u = z :=
    rationalConfigurationGenericPoint_hpoint k κ s (Ω := Ω)
  have hgeneric : U.genericExtensionMorphism Ω ≫ u = z := by
    rw [← hpoint, ← hchartpoint, Category.comp_id]
  exact decompositionSubgroupAtEqualPoint hgeneric.symm d.range

/-- The actual decomposition image equals the normalizer of the original inertia image. -/
theorem rationalConfigurationChosenDecomposition_eq_normalizer
    (k κ : Type) [Field k] [NumberField k]
    [Field κ] [CharZero κ] [IsAlgClosed κ] [Algebra k κ] [IsAlgClosure k κ]
    (s : Finset (Projectivization k (k × k)))
    (Ω : Type) [Field Ω] [IsAlgClosed Ω]
    [Algebra (rationalConfigurationGeometricScheme k κ s).functionField Ω]
    [IsAlgClosure (rationalConfigurationGeometricScheme k κ s).functionField Ω]
    (p : (projectiveLineRatFuncModel κ).openBoundaryPlaces
      (rationalConfigurationBaseChangeChart k κ s))
    (hs : 3 ≤ s.card) :
    rationalConfigurationChosenDecomposition k κ s Ω p =
      Subgroup.normalizer ((rationalConfigurationChosenInertia k κ s Ω p).map
        (rationalConfigurationGeometricInclusion k κ s Ω).toMonoidHom).carrier := by
  let U := rationalConfigurationGeometricScheme k κ s
  let M := projectiveLineRatFuncModel κ
  let j : U ⟶ M.C := rationalConfigurationBaseChangeChart k κ s
  let u : U ⟶ (rationalConfigurationOpen s : Scheme) :=
    Limits.pullback.snd (Spec.map (CommRingCat.ofHom (algebraMap k κ)))
      ((rationalConfigurationOpen s).ι ≫ π k 1)
  let : IsOpenImmersion j := inferInstanceAs
    (IsOpenImmersion (rationalConfigurationBaseChangeChart k κ s))
  let : CharZero U.functionField := Algebra.charZero_of_charZero (R := κ) (A := U.functionField)
  let : IsSepClosure k κ := inferInstance
  let : IsSepClosure U.functionField Ω := inferInstance
  let : Algebra (RatFunc κ) Ω := rationalConfigurationGeometricAmbientAlgebra k κ s Ω
  let : Algebra κ Ω := rationalConfigurationConstantAmbientAlgebra k κ s Ω
  let : Algebra (RatFunc k) Ω := rationalConfigurationArithmeticAmbientAlgebra k κ s Ω
  let : Algebra k Ω := rationalConfigurationBaseAmbientAlgebra k κ s Ω
  obtain ⟨hF, hκF, hκU, hkF, hkκ, hkkF⟩ :=
    rationalConfigurationAmbient_scalarTowers k κ s Ω
  let : IsScalarTower (RatFunc κ) U.functionField Ω := hF
  let : IsScalarTower κ (RatFunc κ) Ω := hκF
  let : IsScalarTower κ U.functionField Ω := hκU
  let : IsScalarTower (RatFunc k) (RatFunc κ) Ω := hkF
  let : IsScalarTower k κ Ω := hkκ
  let : IsScalarTower k (RatFunc k) Ω := hkkF
  let : IsAlgClosure (RatFunc κ) Ω :=
    rationalConfigurationAmbient_isAlgClosure_geometric k κ s Ω
  let : IsAlgClosure (RatFunc k) Ω :=
    rationalConfigurationAmbient_isAlgClosure_arithmetic k κ s Ω
  let : IsSepClosure (RatFunc κ) Ω := inferInstance
  let : IsSepClosure (RatFunc k) Ω := inferInstance
  let : IsGalois (RatFunc k) Ω := inferInstance
  let V := (rationalConfiguration_every_boundaryPlace_exists_rationalPlace k κ s p).choose
  have hV : V.IsRational :=
    (rationalConfiguration_every_boundaryPlace_exists_rationalPlace k κ s p).choose_spec.1
  have hord : ∀ x : RatFunc k,
      p.val.ord (algebraMap (RatFunc k) (RatFunc κ) x) = V.ord x :=
    (rationalConfiguration_every_boundaryPlace_exists_rationalPlace k κ s p).choose_spec.2
  let Q := M.boundaryNormalizationPrimes (Ω := Ω) j
  let e := ratFuncRationalPlaceNormalizationEquiv V hV p.val hord (Ω := Ω)
  let Qa : Ideal (normalizationCommAlgCat V.toValuationSubring Ω) :=
    (Q p).comap e.symm.toRingHom
  let jarith := rationalConfigurationArithmeticGenericPoint k s
  let jgeom := rationalConfigurationGeometricGenericPoint k κ s
  let z := Spec.map (CommRingCat.ofHom (algebraMap (RatFunc k) Ω)) ≫ jarith
  let d := (fieldSourceAbsoluteGaloisHom (RatFunc k) Ω jarith).toMonoidHom.comp
    (normalizationDecompositionInclusion V.toValuationSubring (RatFunc k) Ω Qa)
  have hj : DenseRange j := rationalConfigurationBaseChangeChart_denseRange k κ s
  have hfield : algebraMap (RatFunc κ) U.functionField =
      (j.functionFieldMap hj).comp M.ffEquiv.toRingHom :=
    rationalConfigurationGeometricFunctionFieldEquiv_hfield k κ s
  have hchartpoint : U.genericExtensionMorphism Ω ≫ 𝟙 U =
      Spec.map (CommRingCat.ofHom (algebraMap (RatFunc κ) Ω)) ≫ jgeom :=
    rationalConfigurationGenericPoint_hchartpoint_of_hfield k κ s (Ω := Ω) hfield
  have hpoint :
      (Spec.map (CommRingCat.ofHom (algebraMap (RatFunc κ) Ω)) ≫ jgeom) ≫ u = z :=
    rationalConfigurationGenericPoint_hpoint k κ s (Ω := Ω)
  have hgeneric : U.genericExtensionMorphism Ω ≫ u = z := by
    rw [← hpoint, ← hchartpoint, Category.comp_id]
  let : QuasiCompact j := inferInstanceAs
    (QuasiCompact (rationalConfigurationBaseChangeChart k κ s))
  let : QuasiSeparated j := inferInstanceAs
    (QuasiSeparated (rationalConfigurationBaseChangeChart k κ s))
  let : IsCurveOver κ (RatFunc κ) := AlgebraicCurve.instIsCurveOverRatFunc κ
  let : Finite (M.openBoundaryPlaces j) := rationalConfigurationBoundaryPlaces_finite k κ s
  let : Nontrivial (M.openBoundaryPlaces j) :=
    rationalConfigurationBoundaryPlaces_nontrivial k κ s hs
  let : ∀ q : M.openBoundaryPlaces j, (Q q).IsMaximal := fun q => inferInstance
  have hsurj : Function.Surjective (algebraMap (RatFunc κ) U.functionField) := by
    rw [hfield]
    exact j.functionFieldRingEquivOfIsOpenImmersion.surjective.comp M.ffEquiv.surjective
  have hdata := original_ratFuncPlace_decomposition_image_data V hV p.val hord
    (Q p) hsurj ((rationalConfigurationOpen s).ι ≫ π k 1) u jgeom jarith
    hchartpoint hpoint (rationalConfigurationGenericPoint_hbasearith k s)
  have hcanonical := decomposition_data_at_canonical_point k κ
    ((rationalConfigurationOpen s).ι ≫ π k 1) u (U.genericExtensionMorphism Ω) z hgeneric
    (genericPlaceInertia U p.val (Q p)) d.range hdata
  have hself := fieldChart_boundaryInertia_self_normalizing M j hj hfield
    (rationalConfigurationBoundaryPlaces_card_ge_three k κ s hs) Q p
  have hexact := arithmetic_exactSequence_of_isSepClosure k κ
    (rationalConfigurationOpen s : Scheme) ((rationalConfigurationOpen s).ι ≫ π k 1)
    (U.genericExtensionMorphism Ω)
  change (decompositionSubgroupAtEqualPoint hgeneric.symm d.range) = Subgroup.normalizer
    ((genericPlaceInertia U p.val (Q p)).map
      (fundamentalGroupHom u (U.genericExtensionMorphism Ω)).toMonoidHom).carrier
  exact arithmeticImage_normalizer_eq_of_full_image
    (fundamentalGroupHom u (U.genericExtensionMorphism Ω)).toMonoidHom
    (arithmeticFundamentalGroupHom k κ ((rationalConfigurationOpen s).ι ≫ π k 1)
      (U.genericExtensionMorphism Ω ≫ u)).toMonoidHom
    hexact.1 hexact.2.2.symm (genericPlaceInertia U p.val (Q p)) hself
    (decompositionSubgroupAtEqualPoint hgeneric.symm d.range)
    hcanonical.1 hcanonical.2.1 hcanonical.2.2

/-- The same geometric inertia conjugator transports the actual decomposition images. -/
theorem rationalConfigurationChosenDecomposition_map_of_inertia
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
    (eΔ : rationalConfigurationGeometricGroup k κ s Ω₁ ≃ₜ*
      rationalConfigurationGeometricGroup k κ t Ω₂)
    (heΔ : ∀ v, rationalConfigurationGeometricInclusion k κ t Ω₂ (eΔ v) =
      eP (rationalConfigurationGeometricInclusion k κ s Ω₁ v))
    (p : (projectiveLineRatFuncModel κ).openBoundaryPlaces
      (rationalConfigurationBaseChangeChart k κ s))
    (q : (projectiveLineRatFuncModel κ).openBoundaryPlaces
      (rationalConfigurationBaseChangeChart k κ t))
    (a : rationalConfigurationGeometricGroup k κ t Ω₂)
    (hI : (rationalConfigurationChosenInertia k κ s Ω₁ p).map eΔ.toMonoidHom =
      (rationalConfigurationChosenInertia k κ t Ω₂ q).map (MulAut.conj a).toMonoidHom) :
    (rationalConfigurationChosenDecomposition k κ s Ω₁ p).map eP.toMonoidHom =
      (rationalConfigurationChosenDecomposition k κ t Ω₂ q).map
        (MulAut.conj (rationalConfigurationGeometricInclusion k κ t Ω₂ a)).toMonoidHom := by
  rw [rationalConfigurationChosenDecomposition_eq_normalizer k κ s Ω₁ p hs,
    rationalConfigurationChosenDecomposition_eq_normalizer k κ t Ω₂ q ht]
  exact arithmeticImage_normalizer_map_eq_conjugate eP.toMulEquiv eΔ.toMulEquiv
    (rationalConfigurationGeometricInclusion k κ s Ω₁).toMonoidHom
    (rationalConfigurationGeometricInclusion k κ t Ω₂).toMonoidHom heΔ
    (rationalConfigurationChosenInertia k κ s Ω₁ p)
    (rationalConfigurationChosenInertia k κ t Ω₂ q) a hI

/-- Bare arithmetic recognition also recovers the actual decomposition images. -/
theorem bare_rationalConfiguration_punctureEquiv_decomposition
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
      ∃ σ : s ≃ t, ∀ p : s,
        ∃ a : rationalConfigurationGeometricGroup k κ t Ω₂,
          (rationalConfigurationChosenInertia k κ s Ω₁
            (rationalConfigurationBoundaryPlace k κ s p)).map eΔ.toMonoidHom =
          (rationalConfigurationChosenInertia k κ t Ω₂
            (rationalConfigurationBoundaryPlace k κ t (σ p))).map
              (MulAut.conj a).toMonoidHom ∧
          (rationalConfigurationChosenDecomposition k κ s Ω₁
            (rationalConfigurationBoundaryPlace k κ s p)).map eP.toMonoidHom =
          (rationalConfigurationChosenDecomposition k κ t Ω₂
            (rationalConfigurationBoundaryPlace k κ t (σ p))).map
              (MulAut.conj
                (rationalConfigurationGeometricInclusion k κ t Ω₂ a)).toMonoidHom := by
  obtain ⟨eΔ, heΔ, σ, hσ⟩ :=
    bare_rationalConfiguration_punctureEquiv k κ s t hs ht Ω₁ Ω₂ eP hP
  refine ⟨eΔ, heΔ, σ, ?_⟩
  intro p
  obtain ⟨a, ha⟩ := hσ p
  exact ⟨a, ha, rationalConfigurationChosenDecomposition_map_of_inertia
    k κ s t hs ht Ω₁ Ω₂ eP eΔ heΔ
    (rationalConfigurationBoundaryPlace k κ s p)
    (rationalConfigurationBoundaryPlace k κ t (σ p)) a ha⟩

end AnabelianGeometry.WeightFiltration
