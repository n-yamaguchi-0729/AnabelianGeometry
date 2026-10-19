/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.EtaleFundamentalGroups.Inertia.ConnectedCoverActualInertia
import Nyll.EtaleFundamentalGroups.Inertia.AbsolutePrimeContractionOrbit
import Nyll.EtaleFundamentalGroups.Inertia.NormalizationPrimeHeightOne
import Nyll.EtaleFundamentalGroups.Inertia.AbsoluteGenericGaloisSurjectivity
import Nyll.EtaleFundamentalGroups.Inertia.InertiaConjugateImage
import Nyll.EtaleFundamentalGroups.GeometricFiber.PointedCoverInjectivity
import Nyll.EtaleFundamentalGroups.GaloisCovers.OpenCoverSquareBoundary
import Nyll.EtaleFundamentalGroups.GaloisCovers.OpenCoverConstantField
import Nyll.EtaleFundamentalGroups.GaloisCovers.OpenSquareFunctionField
import Nyll.AnabelianGeometry.WeightFiltration.BoundaryInertiaAnyPrime
import Nyll.AnabelianGeometry.CuspidalInertia.FiniteQuotientSeparation

/-! # Actual boundary ranges on every connected finite cover -/

noncomputable section

open AlgebraicGeometry CategoryTheory AlgebraicCurve IsDedekindDomain SchemeTheory
open AlgebraicGeometry.FiniteEtale CategoryTheory.PreGaloisCategory
open AnabelianGeometry.WeightFiltration AnabelianGeometry.CuspidalInertia
open ProCGroups.Abelian
open scoped Pointwise

namespace EtaleFundamentalGroups.Inertia

attribute [local instance]
  Place.instIsFractionRingIntegralClosureAt
  Place.instIsDedekindDomainIntegralClosureAt
  Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt
  Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt
  placeBaseAmbientAlgebra placeBaseAmbientTower
  extendingPlaceAmbientAlgebra extendingPlaceAmbientTower
  finiteNormalizationPlaceAlgebra finiteNormalizationPlaceTower
  finiteNormalizationPlaceLocalization finiteNormalizationPlaceAmbientTower
  originalPlaceNormalizationAction extendingPlaceNormalizationAction

attribute [local instance] CurveModel.isIntegral CurveModel.isProper CurveModel.smooth

local instance connectedCoverPlaceConstantAmbientTower
    {κ F Ω : Type} [Field κ] [Field F] [Field Ω]
    [Algebra κ F] [Algebra F Ω] [Algebra κ Ω]
    [IsScalarTower κ F Ω] (p : Place κ F) :
    IsScalarTower κ p.toValuationSubring Ω := by
  apply IsScalarTower.of_algebraMap_eq
  intro a
  change algebraMap κ Ω a = algebraMap F Ω (algebraMap κ F a)
  exact IsScalarTower.algebraMap_apply κ F Ω a

/-- The abelian images of all cuspidal elements lying in the prescribed
connected cover are exactly the boundary coordinate ranges of that cover.
The compactification and its field identification come from the original
cover, and the cover is not assumed Galois. -/
theorem connectedCover_abelianized_cuspSaturation_eq_boundaryRanges_with_base
    {κ : Type} [Field κ] [CharZero κ] [IsAlgClosed κ]
    {U : Scheme} [IsIntegral U] [IsNormalIntegral U]
    [IsLocallyNoetherian U] [ConnectedSpace U] [CompactSpace U]
    [Algebra κ U.functionField] [IsCurveOver κ U.functionField]
    {Ω : Type} [Field Ω] [Algebra U.functionField Ω]
    [IsSepClosure U.functionField Ω] [IsSepClosed Ω]
    [Algebra κ Ω] [IsScalarTower κ U.functionField Ω]
    (M : CurveModel κ U.functionField)
    (jU : U ⟶ M.C) [IsOpenImmersion jU]
    [QuasiCompact jU] [QuasiSeparated jU]
    (hjU : DenseRange jU)
    (hbase : algebraMap U.functionField U.functionField =
      (jU.functionFieldMap hjU).comp M.ffEquiv.toRingHom)
    (Qfamily : ∀ p : M.openBoundaryPlaces jU,
      Ideal (normalizationCommAlgCat p.val.toValuationSubring Ω))
    [hQfamily : ∀ p, (Qfamily p).IsMaximal]
    (W : FiniteEtale U) [IsConnected W]
    (w : (fiber (U.genericExtensionMorphism Ω)).obj W) :
    letI : IsIntegral W.left := isIntegral_left_of_isConnected_finiteEtale W
    let K := U.functionField
    let L := W.left.functionField
    letI : Algebra K L := finiteEtaleFunctionFieldAlgebra W
    letI : FiniteDimensional K L :=
      finiteDimensional_functionField_of_finiteEtale_isConnected W
    letI : Algebra.IsSeparable K L :=
      isSeparable_functionField_of_finiteEtale_isConnected W
    let g := fiberObjEquivHom (U.genericExtensionMorphism Ω) W w
    let j := finiteEtaleGenericHomFunctionFieldAlgHom W g
    letI : Algebra L Ω := j.toRingHom.toAlgebra
    letI : IsScalarTower K L Ω := by
      apply IsScalarTower.of_algebraMap_eq'
      ext a
      exact (j.commutes a).symm
    letI : IsSepClosure L Ω :=
      ⟨IsSepClosure.sep_closed K,
        Algebra.isSeparable_tower_top_of_isSeparable K L Ω⟩
    let jL := W.left.fromSpecStalk (genericPoint W.left)
    let hpoint : (ξ L Ω ≫ jL) ≫ W.hom = U.genericExtensionMorphism Ω :=
      finiteEtaleGenericHomFunctionFieldAlgHom_spec_comp W g
    let H := π₁ᵉᵗ(ξ L Ω ≫ jL)
    let i := (pointedFundamentalGroupHom W.hom (ξ L Ω ≫ jL)
      (U.genericExtensionMorphism Ω) hpoint).toMonoidHom
    letI : Algebra κ L := ((algebraMap K L).comp (algebraMap κ K)).toAlgebra
    letI : IsScalarTower κ K L := IsScalarTower.of_algebraMap_eq' rfl
    letI : IsScalarTower κ L Ω := by
      apply IsScalarTower.of_algebraMap_eq'
      ext a
      change algebraMap κ Ω a = j (algebraMap K L (algebraMap κ K a))
      exact (IsScalarTower.algebraMap_apply κ K Ω a).trans
        (j.commutes (algebraMap κ K a)).symm
    letI : IsFiniteEtale (show W.left ⟶ U from W.hom) := W.prop
    letI : CompactSpace W.left :=
      QuasiCompact.compactSpace_of_compactSpace (show W.left ⟶ U from W.hom)
    ∃ (Mc : CurveModel κ L) (jW : W.left ⟶ Mc.C) (hopen : IsOpenImmersion jW),
      letI : IsOpenImmersion jW := hopen
      ∃ (hjW : DenseRange jW)
        (hcover : algebraMap L L = (jW.functionFieldMap hjW).comp Mc.ffEquiv.toRingHom),
      (jW ≫ Mc.toBase = W.hom ≫ jU ≫ M.toBase) ∧
      ∀ (Qc : ∀ r : Mc.openBoundaryPlaces jW,
          Ideal (normalizationCommAlgCat r.val.toValuationSubring Ω))
        (hQc : ∀ r, (Qc r).IsMaximal),
        letI : ∀ r, (Qc r).IsMaximal := hQc
        (TopologicalAbelianization.mk H) ''
          {h : H | i h ∈ conjugacySaturation
            (⋃ p : M.openBoundaryPlaces jU,
              (genericPlaceInertia U p.val (Qfamily p) :
                Set (Aut (fiber (Spec.map (CommRingCat.ofHom (algebraMap U.functionField Ω)) ≫
                  U.fromSpecStalk (genericPoint U))))))} =
          ⋃ r : Mc.openBoundaryPlaces jW,
            ((boundaryPlaceInertiaHom Mc jW hjW hcover Qc r).toMonoidHom.range :
              Set (TopologicalAbelianization H)) := by
  classical
  let : IsIntegral W.left := isIntegral_left_of_isConnected_finiteEtale W
  let K := U.functionField
  let L := W.left.functionField
  let G := Aut (fiber (Spec.map (CommRingCat.ofHom (algebraMap U.functionField Ω)) ≫
                  U.fromSpecStalk (genericPoint U)))
  let : Algebra K L := finiteEtaleFunctionFieldAlgebra W
  let : FiniteDimensional K L :=
    finiteDimensional_functionField_of_finiteEtale_isConnected W
  let : Algebra.IsSeparable K L :=
    isSeparable_functionField_of_finiteEtale_isConnected W
  let g := fiberObjEquivHom (U.genericExtensionMorphism Ω) W w
  let j := finiteEtaleGenericHomFunctionFieldAlgHom W g
  let : Algebra L Ω := j.toRingHom.toAlgebra
  let : IsScalarTower K L Ω := by
    apply IsScalarTower.of_algebraMap_eq'
    ext a
    exact (j.commutes a).symm
  let : IsSepClosure L Ω :=
    ⟨IsSepClosure.sep_closed K,
      Algebra.isSeparable_tower_top_of_isSeparable K L Ω⟩
  let jL := W.left.fromSpecStalk (genericPoint W.left)
  let hpoint : (ξ L Ω ≫ jL) ≫ W.hom = U.genericExtensionMorphism Ω :=
    finiteEtaleGenericHomFunctionFieldAlgHom_spec_comp W g
  let H := π₁ᵉᵗ(ξ L Ω ≫ jL)
  let i : H →* G := (pointedFundamentalGroupHom W.hom (ξ L Ω ≫ jL)
    (U.genericExtensionMorphism Ω) hpoint).toMonoidHom
  let : Algebra κ L := ((algebraMap K L).comp (algebraMap κ K)).toAlgebra
  let : IsScalarTower κ K L := IsScalarTower.of_algebraMap_eq' rfl
  let : IsScalarTower κ L Ω := by
    apply IsScalarTower.of_algebraMap_eq'
    ext a
    change algebraMap κ Ω a = j (algebraMap K L (algebraMap κ K a))
    exact (IsScalarTower.algebraMap_apply κ K Ω a).trans
      (j.commutes (algebraMap κ K a)).symm
  let : IsFiniteEtale (show W.left ⟶ U from W.hom) := W.prop
  let : CompactSpace W.left :=
    QuasiCompact.compactSpace_of_compactSpace (show W.left ⟶ U from W.hom)
  have hcompact := exists_open_cover_curveModel_square_boundary_with_functionField M jU W
  have hcAlg := finiteEtaleFunctionField_constantAlgebra_eq M jU hjU hbase W
  dsimp only at hcompact hcAlg
  rw [← hcAlg] at hcompact
  obtain ⟨Mc, d, jW, hd, hfinite, hopen, hsquare, hboundary, hcover⟩ := hcompact
  let : IsFinite d := hfinite
  let : IsOpenImmersion jW := hopen
  have hjW : DenseRange jW :=
    jW.isOpenEmbedding.isOpenMap.denseRange_of_isPreirreducibleSpace jW
  have hcoverLiteral := hcover hjW
  have hWsurj : Function.Surjective W.hom := by
    intro x
    have hx := (finiteEtale_hom_denseRange_of_isConnected W) x
    rw [W.hom.isClosedMap.isClosed_range.closure_eq] at hx
    exact hx
  have hdsurj : Function.Surjective d :=
    surjective_finite_extension_of_open_square jU W.hom hWsurj jW d hsquare
  have hfield : (M.finiteCurveFieldMap Mc d hd hdsurj).toRingHom = algebraMap K L :=
    finiteCurveFieldMap_eq_of_literal_open_square M Mc d hd hdsurj
      jU jW W.hom hjU hjW (finiteEtale_hom_denseRange_of_isConnected W)
      hsquare hbase hcoverLiteral
  have hstruct : jW ≫ Mc.toBase = W.hom ≫ jU ≫ M.toBase := by
    calc
      jW ≫ Mc.toBase = jW ≫ (d ≫ M.toBase) :=
        congrArg (fun q => jW ≫ q) hd.symm
      _ = (jW ≫ d) ≫ M.toBase := (Category.assoc _ _ _).symm
      _ = (W.hom ≫ jU) ≫ M.toBase := congrArg (fun q => q ≫ M.toBase) hsquare
      _ = W.hom ≫ jU ≫ M.toBase := Category.assoc _ _ _
  refine ⟨Mc, jW, hopen, hjW, hcoverLiteral, hstruct, ?_⟩
  intro Qc hQc
  let (r : Mc.openBoundaryPlaces jW) : (Qc r).IsMaximal := hQc r
  let : ∀ p : M.openBoundaryPlaces jU,
      (show Ideal (integralClosure p.val.toValuationSubring Ω) from Qfamily p).IsMaximal :=
    hQfamily
  let qU : Gal(Ω/K) →* G := absoluteGenericGaloisToFundamentalGroup U Ω
  let I (p : M.openBoundaryPlaces jU) : Subgroup G :=
    genericPlaceInertia U p.val (Qfamily p)
  let S : Set G := conjugacySaturation (⋃ p : M.openBoundaryPlaces jU, (I p : Set G))
  let ab := TopologicalAbelianization.mk H
  let C (r : Mc.openBoundaryPlaces jW) : Subgroup (TopologicalAbelianization H) :=
    (boundaryPlaceInertiaHom Mc jW hjW hcoverLiteral Qc r).toMonoidHom.range
  change ab '' {h : H | i h ∈ S} =
    ⋃ r : Mc.openBoundaryPlaces jW, (C r : Set (TopologicalAbelianization H))
  have hi : Function.Injective i :=
    pointedFundamentalGroupHom_injective W (ξ L Ω ≫ jL)
      (U.genericExtensionMorphism Ω) hpoint
  let Q0 (p : M.openBoundaryPlaces jU) :
      Ideal (integralClosure p.val.toValuationSubring Ω) := Qfamily p
  let (p : M.openBoundaryPlaces jU) : (Q0 p).IsMaximal := hQfamily p
  let Qσ (p : M.openBoundaryPlaces jU) (σ : Gal(Ω/K)) :
      Ideal (integralClosure p.val.toValuationSubring Ω) :=
    σ • Q0 p
  let (p : M.openBoundaryPlaces jU) (σ : Gal(Ω/K)) : (Qσ p σ).IsMaximal := by
    change (σ • Q0 p).IsMaximal
    rw [Ideal.pointwise_smul_eq_comap]
    exact Ideal.comap_isMaximal_of_surjective _
      (MulSemiringAction.toRingAut Gal(Ω/K)
        (integralClosure p.val.toValuationSubring Ω) σ).symm.surjective
  choose P hP using fun (p : M.openBoundaryPlaces jU) (σ : Gal(Ω/K)) =>
    exists_heightOneSpectrum_absoluteNormalizationPrimeContraction
      (L := L) p.val (Qσ p σ)
  let φ := M.finiteCurveFieldMap Mc d hd hdsurj
  have hrestrict (r : Place κ L) :
      r.restrictAlong φ (M.finiteCurveFieldMap_integral Mc d hd hdsurj) =
        r.restrict K := by
    apply Place.ext
    ext a
    change φ.toRingHom a ∈ r.toValuationSubring ↔
      algebraMap K L a ∈ r.toValuationSubring
    rw [DFunLike.congr_fun hfield a]
  have hboundaryPlace (r : Place κ L) :
      r ∈ Mc.openBoundaryPlaces jW ↔
        r.restrict K ∈ M.openBoundaryPlaces jU := by
    rw [M.openBoundaryPlaces_eq_restrict_preimage Mc d hd hdsurj jU jW hboundary]
    change r.restrictAlong φ _ ∈ M.openBoundaryPlaces jU ↔ _
    rw [hrestrict r]
  let z (p : M.openBoundaryPlaces jU) (σ : Gal(Ω/K)) :
      Mc.openBoundaryPlaces jW :=
    ⟨Place.placeOfPrime (P p σ), (hboundaryPlace _).mpr (by
      rw [Place.restrict_placeOfPrime]
      exact p.property)⟩
  have hzsurj (r : Mc.openBoundaryPlaces jW) :
      ∃ (p : M.openBoundaryPlaces jU) (σ : Gal(Ω/K)), z p σ = r := by
    let p : M.openBoundaryPlaces jU :=
      ⟨r.val.restrict K, (hboundaryPlace r.val).mp r.property⟩
    let Pr := Place.fiberCenter L p.val (show r.val.restrict K = p.val from rfl)
    obtain ⟨σ, hσ⟩ :=
      exists_smul_absoluteNormalizationPrimeContraction_eq p.val Pr (Qfamily p)
    have hPr : P p σ = Pr := HeightOneSpectrum.ext ((hP p σ).trans hσ)
    refine ⟨p, σ, Subtype.ext ?_⟩
    change Place.placeOfPrime (P p σ) = r.val
    rw [hPr]
    exact Place.eq_of_fiberCenter_eq (Place.restrict_placeOfPrime Pr)
      (show r.val.restrict K = p.val from rfl) (Place.fiberCenter_placeOfPrime Pr)
  let R (p : M.openBoundaryPlaces jU) (σ : Gal(Ω/K)) :=
    (Place.placeOfPrime (P p σ)).toValuationSubring
  let QB (p : M.openBoundaryPlaces jU) (σ : Gal(Ω/K)) :=
    (Qσ p σ).comap (normalizationIntegralBaseRingEquiv
      p.val.toValuationSubring (Place.integralClosureAt L p.val) Ω).toRingHom
  let qloc (p : M.openBoundaryPlaces jU) (σ : Gal(Ω/K)) :=
    (QB p σ).map (normalizationBaseLocalizationRingMap
      (Place.integralClosureAt L p.val) (R p σ) Ω)
  let J (p : M.openBoundaryPlaces jU) (σ : Gal(Ω/K)) : Subgroup H :=
    genericPlaceInertia W.left (Place.placeOfPrime (P p σ)) (qloc p σ)
  have hactual (p : M.openBoundaryPlaces jU) (σ : Gal(Ω/K)) :
      (qloc p σ).IsMaximal ∧
        (J p σ).map i = genericPlaceInertia U p.val (Qσ p σ) ⊓ i.range :=
    connectedCover_actualPlaceInertia_image Ω p.val (Qσ p σ) W w
      (P p σ) (hP p σ)
  have hconj (p : M.openBoundaryPlaces jU) (σ : Gal(Ω/K)) :
      genericPlaceInertia U p.val (Qσ p σ) =
        (I p).map (MulAut.conj (qU σ)).toMonoidHom := by
    dsimp only [I]
    rw [genericPlaceInertia_eq_absoluteInertiaImage U p.val (Qσ p σ),
      genericPlaceInertia_eq_absoluteInertiaImage U p.val (Qfamily p)]
    exact inertia_smul_map (Q0 p) σ qU
  have hJ (p : M.openBoundaryPlaces jU) (σ : Gal(Ω/K)) :
      (J p σ).map i =
        (I p).map (MulAut.conj (qU σ)).toMonoidHom ⊓ i.range := by
    rw [← hconj p σ]
    exact (hactual p σ).2
  have hC (p : M.openBoundaryPlaces jU) (σ : Gal(Ω/K)) :
      (J p σ).map ab = C (z p σ) := by
    let : (show Ideal (normalizationCommAlgCat (z p σ).val.toValuationSubring Ω)
      from qloc p σ).IsMaximal := (hactual p σ).1
    exact boundaryInertia_abelianized_range_eq_coordinate_of_maximal
      Mc jW hjW hcoverLiteral Qc (z p σ) (qloc p σ)
  ext a
  constructor
  · rintro ⟨h, hh, rfl⟩
    obtain ⟨b, t, ht, hbt⟩ := hh
    obtain ⟨p, htp⟩ := Set.mem_iUnion.mp ht
    obtain ⟨σ, hσ⟩ := absoluteGenericGaloisToFundamentalGroup_surjective U Ω b
    have hσ' : qU σ = b := hσ
    have him : i h ∈ (J p σ).map i := by
      rw [hJ p σ]
      refine ⟨⟨t, htp, ?_⟩, ⟨h, rfl⟩⟩
      change qU σ * t * (qU σ)⁻¹ = i h
      rw [hσ']
      exact hbt
    obtain ⟨h', hh', heq⟩ := him
    have heq' : h' = h := hi heq
    rw [heq'] at hh'
    apply Set.mem_iUnion.mpr
    refine ⟨z p σ, ?_⟩
    change ab h ∈ C (z p σ)
    rw [← hC p σ]
    exact ⟨h, hh', rfl⟩
  · intro ha
    obtain ⟨r, har⟩ := Set.mem_iUnion.mp ha
    obtain ⟨p, σ, hz⟩ := hzsurj r
    rw [← hz, ← hC p σ] at har
    obtain ⟨h, hh, rfl⟩ := har
    refine ⟨h, ?_, rfl⟩
    have him : i h ∈
        (I p).map (MulAut.conj (qU σ)).toMonoidHom ⊓ i.range := by
      rw [← hJ p σ]
      exact ⟨h, hh, rfl⟩
    obtain ⟨t, ht, hti⟩ := him.1
    exact ⟨qU σ, t, Set.mem_iUnion.mpr ⟨p, ht⟩, hti⟩

/-- The original export, retaining its existing interface. -/
theorem connectedCover_abelianized_cuspSaturation_eq_boundaryRanges
    {κ : Type} [Field κ] [CharZero κ] [IsAlgClosed κ]
    {U : Scheme} [IsIntegral U] [IsNormalIntegral U]
    [IsLocallyNoetherian U] [ConnectedSpace U] [CompactSpace U]
    [Algebra κ U.functionField] [IsCurveOver κ U.functionField]
    {Ω : Type} [Field Ω] [Algebra U.functionField Ω]
    [IsSepClosure U.functionField Ω] [IsSepClosed Ω]
    [Algebra κ Ω] [IsScalarTower κ U.functionField Ω]
    (M : CurveModel κ U.functionField)
    (jU : U ⟶ M.C) [IsOpenImmersion jU]
    [QuasiCompact jU] [QuasiSeparated jU]
    (hjU : DenseRange jU)
    (hbase : algebraMap U.functionField U.functionField =
      (jU.functionFieldMap hjU).comp M.ffEquiv.toRingHom)
    (Qfamily : ∀ p : M.openBoundaryPlaces jU,
      Ideal (normalizationCommAlgCat p.val.toValuationSubring Ω))
    [hQfamily : ∀ p, (Qfamily p).IsMaximal]
    (W : FiniteEtale U) [IsConnected W]
    (w : (fiber (U.genericExtensionMorphism Ω)).obj W) :
    letI : IsIntegral W.left := isIntegral_left_of_isConnected_finiteEtale W
    let K := U.functionField
    let L := W.left.functionField
    letI : Algebra K L := finiteEtaleFunctionFieldAlgebra W
    letI : FiniteDimensional K L :=
      finiteDimensional_functionField_of_finiteEtale_isConnected W
    letI : Algebra.IsSeparable K L :=
      isSeparable_functionField_of_finiteEtale_isConnected W
    let g := fiberObjEquivHom (U.genericExtensionMorphism Ω) W w
    let j := finiteEtaleGenericHomFunctionFieldAlgHom W g
    letI : Algebra L Ω := j.toRingHom.toAlgebra
    letI : IsScalarTower K L Ω := by
      apply IsScalarTower.of_algebraMap_eq'
      ext a
      exact (j.commutes a).symm
    letI : IsSepClosure L Ω :=
      ⟨IsSepClosure.sep_closed K,
        Algebra.isSeparable_tower_top_of_isSeparable K L Ω⟩
    let jL := W.left.fromSpecStalk (genericPoint W.left)
    let hpoint : (ξ L Ω ≫ jL) ≫ W.hom = U.genericExtensionMorphism Ω :=
      finiteEtaleGenericHomFunctionFieldAlgHom_spec_comp W g
    let H := π₁ᵉᵗ(ξ L Ω ≫ jL)
    let i := (pointedFundamentalGroupHom W.hom (ξ L Ω ≫ jL)
      (U.genericExtensionMorphism Ω) hpoint).toMonoidHom
    letI : Algebra κ L := ((algebraMap K L).comp (algebraMap κ K)).toAlgebra
    letI : IsScalarTower κ K L := IsScalarTower.of_algebraMap_eq' rfl
    letI : IsScalarTower κ L Ω := by
      apply IsScalarTower.of_algebraMap_eq'
      ext a
      change algebraMap κ Ω a = j (algebraMap K L (algebraMap κ K a))
      exact (IsScalarTower.algebraMap_apply κ K Ω a).trans
        (j.commutes (algebraMap κ K a)).symm
    letI : IsFiniteEtale (show W.left ⟶ U from W.hom) := W.prop
    letI : CompactSpace W.left :=
      QuasiCompact.compactSpace_of_compactSpace (show W.left ⟶ U from W.hom)
    ∃ (Mc : CurveModel κ L) (jW : W.left ⟶ Mc.C) (hopen : IsOpenImmersion jW),
      letI : IsOpenImmersion jW := hopen
      ∃ (hjW : DenseRange jW)
        (hcover : algebraMap L L = (jW.functionFieldMap hjW).comp Mc.ffEquiv.toRingHom),
      ∀ (Qc : ∀ r : Mc.openBoundaryPlaces jW,
          Ideal (normalizationCommAlgCat r.val.toValuationSubring Ω))
        (hQc : ∀ r, (Qc r).IsMaximal),
        letI : ∀ r, (Qc r).IsMaximal := hQc
        (TopologicalAbelianization.mk H) ''
          {h : H | i h ∈ conjugacySaturation
            (⋃ p : M.openBoundaryPlaces jU,
              (genericPlaceInertia U p.val (Qfamily p) :
                Set (Aut (fiber (Spec.map (CommRingCat.ofHom (algebraMap U.functionField Ω)) ≫
                  U.fromSpecStalk (genericPoint U))))))} =
          ⋃ r : Mc.openBoundaryPlaces jW,
            ((boundaryPlaceInertiaHom Mc jW hjW hcover Qc r).toMonoidHom.range :
              Set (TopologicalAbelianization H)) := by
  classical
  let : IsIntegral W.left := isIntegral_left_of_isConnected_finiteEtale W
  let K := U.functionField
  let L := W.left.functionField
  let G := Aut (fiber (Spec.map (CommRingCat.ofHom (algebraMap U.functionField Ω)) ≫
                  U.fromSpecStalk (genericPoint U)))
  let : Algebra K L := finiteEtaleFunctionFieldAlgebra W
  let : FiniteDimensional K L :=
    finiteDimensional_functionField_of_finiteEtale_isConnected W
  let : Algebra.IsSeparable K L :=
    isSeparable_functionField_of_finiteEtale_isConnected W
  let g := fiberObjEquivHom (U.genericExtensionMorphism Ω) W w
  let j := finiteEtaleGenericHomFunctionFieldAlgHom W g
  let : Algebra L Ω := j.toRingHom.toAlgebra
  let : IsScalarTower K L Ω := by
    apply IsScalarTower.of_algebraMap_eq'
    ext a
    exact (j.commutes a).symm
  let : IsSepClosure L Ω :=
    ⟨IsSepClosure.sep_closed K,
      Algebra.isSeparable_tower_top_of_isSeparable K L Ω⟩
  let jL := W.left.fromSpecStalk (genericPoint W.left)
  let hpoint : (ξ L Ω ≫ jL) ≫ W.hom = U.genericExtensionMorphism Ω :=
    finiteEtaleGenericHomFunctionFieldAlgHom_spec_comp W g
  let H := π₁ᵉᵗ(ξ L Ω ≫ jL)
  let i : H →* G := (pointedFundamentalGroupHom W.hom (ξ L Ω ≫ jL)
    (U.genericExtensionMorphism Ω) hpoint).toMonoidHom
  let : Algebra κ L := ((algebraMap K L).comp (algebraMap κ K)).toAlgebra
  let : IsScalarTower κ K L := IsScalarTower.of_algebraMap_eq' rfl
  let : IsScalarTower κ L Ω := by
    apply IsScalarTower.of_algebraMap_eq'
    ext a
    change algebraMap κ Ω a = j (algebraMap K L (algebraMap κ K a))
    exact (IsScalarTower.algebraMap_apply κ K Ω a).trans
      (j.commutes (algebraMap κ K a)).symm
  let : IsFiniteEtale (show W.left ⟶ U from W.hom) := W.prop
  let : CompactSpace W.left :=
    QuasiCompact.compactSpace_of_compactSpace (show W.left ⟶ U from W.hom)
  obtain ⟨Mc, jW, hopen, hjW, hcover, _hstruct, hRanges⟩ :=
    connectedCover_abelianized_cuspSaturation_eq_boundaryRanges_with_base
      M jU hjU hbase Qfamily W w
  exact ⟨Mc, jW, hopen, hjW, hcover, hRanges⟩

end EtaleFundamentalGroups.Inertia
