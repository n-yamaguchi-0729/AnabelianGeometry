/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/
import Nyll.AnabelianGeometry.WeightFiltration.BareRationalCuspDecomposition

/-! # Public projection and raw membership suppliers for the chosen decomposition image -/

noncomputable section
open CategoryTheory CategoryTheory.PreGaloisCategory AlgebraicGeometry AlgebraicCurve
open AlgebraicGeometry.FiniteEtale
open AlgebraicGeometry.ProjSpace SchemeTheory EtaleFundamentalGroups.Inertia
open AnabelianGeometry.KummerTheory
open scoped RatFunc

namespace AnabelianGeometry.WeightFiltration

attribute [local instance] MvPolynomial.gradedAlgebra Polynomial.algebra
  rationalConfigurationGeometricFieldAlgebra rationalConfigurationGeometricConstantAlgebra
  rationalConfigurationGeometricField_scalarTower
  placeBaseAmbientAlgebra placeBaseAmbientTower placeConstantAmbientTower
  normalizationCommAlgGaloisAction

local instance (priority := 2000) chosenProjectionSMulRatFunc
    {A E : Type*} [CommSemiring A] [Field E] [Algebra A (RatFunc E)] :
    SMul A (RatFunc E) := (inferInstance : Algebra A (RatFunc E)).toSMul

private def projectionDecompositionSubgroupAtEqualPoint
    {X : Scheme} {Ω : Type} [Field Ω]
    {x y : Spec (.of Ω) ⟶ X} (h : x = y) (D : Subgroup (Aut (fiber x))) :
    Subgroup (Aut (fiber y)) :=
  Eq.ndrec (motive := fun z : Spec (.of Ω) ⟶ X => Subgroup (Aut (fiber z))) D h

private theorem projection_decomposition_data_at_canonical_point
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
    let D' : Subgroup (Aut (fiber (xi ≫ u))) :=
      projectionDecompositionSubgroupAtEqualPoint hz.symm D
    I.map (fundamentalGroupHom u xi).toMonoidHom ≤ D' ∧
      D' ≤ Subgroup.normalizer (I.map (fundamentalGroupHom u xi).toMonoidHom).carrier ∧
      ∀ τ : Gal(κ/k), ∃ γ : Aut (fiber (xi ≫ u)),
        γ ∈ D' ∧ arithmeticFundamentalGroupHom k κ f (xi ≫ u) γ = τ := by
  subst z
  exact hdata

/-- The original arithmetic quotient is surjective on the SAME chosen
normalization-prime decomposition image. No preservation hypothesis is used. -/
theorem rationalConfigurationChosenDecomposition_arithmetic_surjective
    (k κ : Type) [Field k] [NumberField k]
    [Field κ] [CharZero κ] [IsAlgClosed κ] [Algebra k κ] [IsAlgClosure k κ]
    (s : Finset (Projectivization k (k × k)))
    (Ω : Type) [Field Ω] [IsAlgClosed Ω]
    [Algebra (rationalConfigurationGeometricScheme k κ s).functionField Ω]
    [IsAlgClosure (rationalConfigurationGeometricScheme k κ s).functionField Ω]
    (p : (projectiveLineRatFuncModel κ).openBoundaryPlaces
      (rationalConfigurationBaseChangeChart k κ s))
    : Function.Surjective (fun γ : rationalConfigurationChosenDecomposition k κ s Ω p =>
      arithmeticFundamentalGroupHom k κ ((rationalConfigurationOpen s).ι ≫ π k 1)
        (rationalConfigurationArithmeticBasePoint k κ s Ω) γ.val) := by
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
  let : ∀ q : M.openBoundaryPlaces j, (Q q).IsMaximal := fun q => inferInstance
  have hsurj : Function.Surjective (algebraMap (RatFunc κ) U.functionField) := by
    rw [hfield]
    exact j.functionFieldRingEquivOfIsOpenImmersion.surjective.comp M.ffEquiv.surjective
  have hdata := original_ratFuncPlace_decomposition_image_data V hV p.val hord
    (Q p) hsurj ((rationalConfigurationOpen s).ι ≫ π k 1) u jgeom jarith
    hchartpoint hpoint (rationalConfigurationGenericPoint_hbasearith k s)
  have hcanonical := projection_decomposition_data_at_canonical_point k κ
    ((rationalConfigurationOpen s).ι ≫ π k 1) u (U.genericExtensionMorphism Ω) z hgeneric
    (genericPlaceInertia U p.val (Q p)) d.range hdata
  intro τ
  obtain ⟨γ, hγ, hτ⟩ := hcanonical.2.2 τ
  refine ⟨⟨γ, ?_⟩, hτ⟩
  change γ ∈ projectionDecompositionSubgroupAtEqualPoint hgeneric.symm d.range
  exact hγ

private theorem projectionDecompositionSubgroupAtEqualPoint_mem_range
    {G : Type*} [Group G] {X : Scheme} {Ω : Type} [Field Ω]
    {x y : Spec (.of Ω) ⟶ X} (h : x = y)
    (d : G →* Aut (fiber x)) (γ : Aut (fiber y)) :
    γ ∈ projectionDecompositionSubgroupAtEqualPoint h d.range ↔
      ∃ δ : G, Eq.ndrec (motive := fun z : Spec (.of Ω) ⟶ X => Aut (fiber z))
        (d δ) h = γ := by
  subst y
  rfl

private theorem projectionAutAtEqualPoint_eq_continuousConjAut
    {X : Scheme} {Ω : Type} [Field Ω]
    {x y : Spec (.of Ω) ⟶ X} (h : x = y) (γ : Aut (fiber x)) :
    Eq.ndrec (motive := fun z : Spec (.of Ω) ⟶ X => Aut (fiber z)) γ h =
      continuousConjAut (eqToIso (congrArg fiber h)) γ := by
  subst y
  apply Aut.ext
  ext Z z
  rfl

private theorem projectionDecompositionSubgroupAtEqualPoint_mem_range_conj
    {G : Type*} [Group G] {X : Scheme} {Ω : Type} [Field Ω]
    {x y : Spec (.of Ω) ⟶ X} (h : x = y)
    (d : G →* Aut (fiber x)) (γ : Aut (fiber y)) :
    γ ∈ projectionDecompositionSubgroupAtEqualPoint h d.range ↔
      ∃ δ : G, continuousConjAut (eqToIso (congrArg fiber h)) (d δ) = γ := by
  rw [projectionDecompositionSubgroupAtEqualPoint_mem_range]
  simp only [projectionAutAtEqualPoint_eq_continuousConjAut]

/-- Membership in the actual chosen decomposition image is equivalent to a
lift in the SAME raw normalization-prime decomposition group. The original
field-source point equality is constructed internally, and its equality-induced
fiber conjugation is retained explicitly. -/
theorem rationalConfigurationChosenDecomposition_mem_iff_exists_raw
    (k κ : Type) [Field k] [NumberField k]
    [Field κ] [CharZero κ] [IsAlgClosed κ] [Algebra k κ] [IsAlgClosure k κ]
    (s : Finset (Projectivization k (k × k)))
    (Ω : Type) [Field Ω] [IsAlgClosed Ω]
    [Algebra (rationalConfigurationGeometricScheme k κ s).functionField Ω]
    [IsAlgClosure (rationalConfigurationGeometricScheme k κ s).functionField Ω]
    (p : (projectiveLineRatFuncModel κ).openBoundaryPlaces
      (rationalConfigurationBaseChangeChart k κ s)) :
    let U := rationalConfigurationGeometricScheme k κ s
    let M := projectiveLineRatFuncModel κ
    let j : U ⟶ M.C := rationalConfigurationBaseChangeChart k κ s
    letI : Algebra (RatFunc κ) Ω := rationalConfigurationGeometricAmbientAlgebra k κ s Ω
    letI : Algebra κ Ω := rationalConfigurationConstantAmbientAlgebra k κ s Ω
    letI : Algebra (RatFunc k) Ω := rationalConfigurationArithmeticAmbientAlgebra k κ s Ω
    letI : Algebra k Ω := rationalConfigurationBaseAmbientAlgebra k κ s Ω
    let ambient := rationalConfigurationAmbient_scalarTowers k κ s Ω
    letI : IsScalarTower (RatFunc κ) U.functionField Ω := ambient.1
    letI : IsScalarTower κ (RatFunc κ) Ω := ambient.2.1
    letI : IsScalarTower κ U.functionField Ω := ambient.2.2.1
    letI : IsScalarTower (RatFunc k) (RatFunc κ) Ω := ambient.2.2.2.1
    letI : IsScalarTower k κ Ω := ambient.2.2.2.2.1
    letI : IsScalarTower k (RatFunc k) Ω := ambient.2.2.2.2.2
    letI : IsAlgClosure (RatFunc k) Ω :=
      rationalConfigurationAmbient_isAlgClosure_arithmetic k κ s Ω
    letI : IsSepClosure (RatFunc k) Ω := inferInstance
    letI : IsGalois (RatFunc k) Ω := inferInstance
    let V := (rationalConfiguration_every_boundaryPlace_exists_rationalPlace k κ s p).choose
    let hV : V.IsRational :=
      (rationalConfiguration_every_boundaryPlace_exists_rationalPlace k κ s p).choose_spec.1
    let hord : ∀ x : RatFunc k,
        p.val.ord (algebraMap (RatFunc k) (RatFunc κ) x) = V.ord x :=
      (rationalConfiguration_every_boundaryPlace_exists_rationalPlace k κ s p).choose_spec.2
    let Q := M.boundaryNormalizationPrimes (Ω := Ω) j
    let e := ratFuncRationalPlaceNormalizationEquiv V hV p.val hord (Ω := Ω)
    let Qa : Ideal (normalizationCommAlgCat V.toValuationSubring Ω) :=
      (Q p).comap e.symm.toRingHom
    let jarith := rationalConfigurationArithmeticGenericPoint k s
    let z := Spec.map (CommRingCat.ofHom (algebraMap (RatFunc k) Ω)) ≫ jarith
    ∃ hpoint : rationalConfigurationArithmeticBasePoint k κ s Ω = z,
      ∀ γ : rationalConfigurationArithmeticGroup k κ s Ω,
        γ ∈ rationalConfigurationChosenDecomposition k κ s Ω p ↔
          ∃ δ : normalizationDecompositionGroup V.toValuationSubring (RatFunc k) Ω Qa,
            continuousConjAut (eqToIso (congrArg fiber hpoint.symm))
              (fieldSourceAbsoluteGaloisHom (RatFunc k) Ω jarith δ.val) = γ := by
  intro U M j
  let : Algebra (RatFunc κ) Ω := rationalConfigurationGeometricAmbientAlgebra k κ s Ω
  let : Algebra κ Ω := rationalConfigurationConstantAmbientAlgebra k κ s Ω
  let : Algebra (RatFunc k) Ω := rationalConfigurationArithmeticAmbientAlgebra k κ s Ω
  let : Algebra k Ω := rationalConfigurationBaseAmbientAlgebra k κ s Ω
  intro ambient
  let : IsScalarTower (RatFunc κ) U.functionField Ω := ambient.1
  let : IsScalarTower κ (RatFunc κ) Ω := ambient.2.1
  let : IsScalarTower κ U.functionField Ω := ambient.2.2.1
  let : IsScalarTower (RatFunc k) (RatFunc κ) Ω := ambient.2.2.2.1
  let : IsScalarTower k κ Ω := ambient.2.2.2.2.1
  let : IsScalarTower k (RatFunc k) Ω := ambient.2.2.2.2.2
  let : IsAlgClosure (RatFunc k) Ω :=
    rationalConfigurationAmbient_isAlgClosure_arithmetic k κ s Ω
  let : IsSepClosure (RatFunc k) Ω := inferInstance
  let : IsGalois (RatFunc k) Ω := inferInstance
  intro V hV hord Q e Qa jarith z
  let u : U ⟶ (rationalConfigurationOpen s : Scheme) :=
    Limits.pullback.snd (Spec.map (CommRingCat.ofHom (algebraMap k κ)))
      ((rationalConfigurationOpen s).ι ≫ π k 1)
  let jgeom := rationalConfigurationGeometricGenericPoint k κ s
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
  let d := (fieldSourceAbsoluteGaloisHom (RatFunc k) Ω jarith).toMonoidHom.comp
    (normalizationDecompositionInclusion V.toValuationSubring (RatFunc k) Ω Qa)
  refine ⟨hgeneric, ?_⟩
  intro γ
  change γ ∈ projectionDecompositionSubgroupAtEqualPoint hgeneric.symm d.range ↔ _
  exact projectionDecompositionSubgroupAtEqualPoint_mem_range_conj hgeneric.symm d γ

end AnabelianGeometry.WeightFiltration
