/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.EtaleFundamentalGroups.Inertia.PointedCoverInertiaIntersection
import Nyll.EtaleFundamentalGroups.Inertia.PlaceNormalizationInertiaRestriction
import Nyll.EtaleFundamentalGroups.Inertia.GenericPlaceInertiaImage

import Nyll.AnabelianGeometry.CuspidalInertia.InertiaCoordinateCentralizer
import Nyll.AnabelianGeometry.WeightFiltration.BoundaryInertiaAnyPrime
import Nyll.EtaleFundamentalGroups.Inertia.PointedCoverActualInertia
import Nyll.EtaleFundamentalGroups.Inertia.AbsoluteGenericGaloisSurjectivity
import Nyll.EtaleFundamentalGroups.Inertia.NormalizationPrimeHeightOne
import Nyll.EtaleFundamentalGroups.Inertia.NormalizationPlaceConjugatePrime
import Nyll.EtaleFundamentalGroups.Inertia.InertiaConjugateImage
import Nyll.EtaleFundamentalGroups.Inertia.BoundaryPlaceFiberEmbedding
import Nyll.EtaleFundamentalGroups.GeometricFiber.PointedCoverInjectivity
import Nyll.EtaleFundamentalGroups.GaloisCovers.OpenCoverSquareBoundary
import Nyll.EtaleFundamentalGroups.GaloisCovers.OpenCoverConstantField
import Nyll.EtaleFundamentalGroups.GaloisCovers.OpenSquareFunctionField
import Nyll.EtaleFundamentalGroups.GaloisCovers.OpenCoverBoundaryRestriction

/-!
# Images of restricted inertia in the actual pointed cover

The prescribed lift determines the cover map and field restriction. The
image of every restricted subgroup is its exact intersection with the
actual cover image.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory
open AlgebraicGeometry.FiniteEtale CategoryTheory.PreGaloisCategory

namespace EtaleFundamentalGroups.Inertia

universe u

private theorem genericExtension_point_comp
    (U : Scheme.{u}) [IsIntegral U]
    (Ω : Type u) [Field Ω] [Algebra U.functionField Ω] :
    ξ U.functionField Ω ≫ U.genericExtensionMorphism U.functionField =
      U.genericExtensionMorphism Ω := by
  simp only [Scheme.genericExtensionMorphism]
  rw [← Spec.map_comp_assoc]
  congr 1


open scoped Pointwise

open AlgebraicCurve IsDedekindDomain
open AnabelianGeometry.WeightFiltration ProCGroups.Abelian SchemeTheory

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

local instance placeConstantAmbientTower
    {κ F Ω : Type} [Field κ] [Field F] [Field Ω]
    [Algebra κ F] [Algebra F Ω] [Algebra κ Ω]
    [IsScalarTower κ F Ω] (p : Place κ F) :
    IsScalarTower κ p.toValuationSubring Ω := by
  apply IsScalarTower.of_algebraMap_eq
  intro a
  change algebraMap κ Ω a = algebraMap F Ω (algebraMap κ F a)
  exact IsScalarTower.algebraMap_apply κ F Ω a

/-- Every actual finite Galois cover detects the inertia double coset of
an element centralizing a nontrivial boundary inertia element. -/
theorem boundaryInertia_doubleCoset_eq_of_commute
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
    (hthree : 3 ≤ Nat.card (M.openBoundaryPlaces jU))
    (Qfamily : ∀ p : M.openBoundaryPlaces jU,
      Ideal (integralClosure p.val.toValuationSubring Ω))
    [hQfamily : ∀ p, (Qfamily p).IsMaximal]
    (v : M.openBoundaryPlaces jU)
    (W : FiniteEtale U) (hW : IsGalois W)
    (w : (fiber (U.genericExtensionMorphism Ω)).obj W)
    {x g : π₁ᵉᵗ(U.genericExtensionMorphism Ω)}
    (hx : x ∈ genericPlaceInertia U v.val (Qfamily v))
    (hx1 : x ≠ 1) (hcomm : Commute g x) :
    letI : IsGalois W := hW
    let I := genericPlaceInertia U v.val (Qfamily v)
    let N := (finiteEtaleGaloisCoverQuotientMonoidHom
      (U.genericExtensionMorphism Ω) W hW w).ker
    DoubleCoset.mk N I 1 = DoubleCoset.mk N I g := by
  classical
  let : Fintype (M.openBoundaryPlaces jU) := (M.openBoundaryPlaces_finite jU).fintype
  have hthreeBase : 3 ≤ Fintype.card (M.openBoundaryPlaces jU) := by
    simpa only [Nat.card_eq_fintype_card] using hthree
  let : Nontrivial (M.openBoundaryPlaces jU) :=
    Fintype.one_lt_card_iff_nontrivial.mp (by omega)
  let : ∀ p : M.openBoundaryPlaces jU,
      (show Ideal (normalizationCommAlgCat p.val.toValuationSubring Ω) from Qfamily p).IsMaximal :=
    hQfamily
  have hpow : ∀ n : ℕ, n ≠ 0 → x ^ n ≠ 1 := fun n hn =>
    boundaryInertia_pow_ne_one (Ω := Ω) M jU hjU hbase Qfamily v hx hx1 hn
  let : IsGalois W := hW
  let : IsIntegral W.left := isIntegral_left_of_isConnected_finiteEtale W
  let K := U.functionField
  let L := W.left.functionField
  let G := π₁ᵉᵗ(U.genericExtensionMorphism Ω)
  let : Algebra K L := finiteEtaleFunctionFieldAlgebra W
  let : FiniteDimensional K L :=
    finiteDimensional_functionField_of_finiteEtale_isConnected W
  let : _root_.IsGalois K L := isGalois_functionField_of_isGalois_finiteEtale W hW
  let h := genericExtension_point_comp U Ω
  let w' := (absoluteGenericFiberIso U Ω).inv.app W w
  let lift := genericPointLiftRebase h W
    (fiberObjEquivHom (ξ K Ω ≫ U.genericExtensionMorphism K) W w')
  let j := finiteEtaleGenericHomFunctionFieldAlgHom W lift
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
    finiteEtaleGenericHomFunctionFieldAlgHom_spec_comp W lift
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
  have hcompact :=
    exists_open_cover_curveModel_square_boundary_with_functionField M jU W
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
    intro z
    have hz := (finiteEtale_hom_denseRange_of_isConnected W) z
    rw [W.hom.isClosedMap.isClosed_range.closure_eq] at hz
    exact hz
  have hdsurj : Function.Surjective d :=
    surjective_finite_extension_of_open_square jU W.hom hWsurj jW d hsquare
  have hfield : (M.finiteCurveFieldMap Mc d hd hdsurj).toRingHom = algebraMap K L :=
    finiteCurveFieldMap_eq_of_literal_open_square M Mc d hd hdsurj
      jU jW W.hom hjU hjW (finiteEtale_hom_denseRange_of_isConnected W)
      hsquare hbase hcoverLiteral
  let : IsCurveOver κ L :=
    AlgebraicCurve.isCurveOver_of_isIntegral_of_smoothOfRelativeDimension_one
      Mc.toBase Mc.ffEquiv Mc.ffEquiv_algebraMap
  let : Fintype (Mc.openBoundaryPlaces jW) := (Mc.openBoundaryPlaces_finite jW).fintype
  have hthreeCover : 3 ≤ Fintype.card (Mc.openBoundaryPlaces jW) :=
    hthreeBase.trans (finiteSquareBoundary_card_le M Mc d hd hdsurj jU jW hboundary)
  let : Nontrivial (Mc.openBoundaryPlaces jW) :=
    Fintype.one_lt_card_iff_nontrivial.mp (by omega)
  choose Qc hQc using fun p : Mc.openBoundaryPlaces jW => by
    let : Nontrivial (normalizationCommAlgCat p.val.toValuationSubring Ω) :=
      (inferInstance : Nontrivial (integralClosure p.val.toValuationSubring Ω))
    exact Ideal.exists_maximal (normalizationCommAlgCat p.val.toValuationSubring Ω)
  let (p : Mc.openBoundaryPlaces jW) : (Qc p).IsMaximal := hQc p
  let Q := Qfamily v
  let qU := absoluteGenericGaloisToFundamentalGroup U Ω
  let I : Subgroup G := (Q.inertia Gal(Ω/K)).map qU
  have hIeq : genericPlaceInertia U v.val Q = I :=
    genericPlaceInertia_eq_absoluteInertiaImage U v.val Q
  let ρ := finiteEtaleGaloisCoverFunctionFieldQuotientMonoidHom
    (U.genericExtensionMorphism Ω) W hW w
  let N : Subgroup G := ρ.ker
  have hNdeck : N = (finiteEtaleGaloisCoverQuotientMonoidHom
      (U.genericExtensionMorphism Ω) W hW w).ker :=
    (finiteEtaleGaloisCoverFunctionFieldQuotientMonoidHom_ker
      (U.genericExtensionMorphism Ω) W hW w).trans
      (finiteEtaleGaloisCoverQuotientMonoidHom_ker
        (U.genericExtensionMorphism Ω) W hW w).symm
  have hi : Function.Injective i :=
    pointedFundamentalGroupHom_injective W (ξ L Ω ≫ jL)
      (U.genericExtensionMorphism Ω) hpoint
  have hrange : i.range = N :=
    (pointedCover_sameGenericLift_range Ω W hW w).trans hNdeck.symm
  have hN : N.index ≠ 0 := by
    change ρ.ker.index ≠ 0
    rw [Subgroup.index_ker]
    exact Nat.card_pos.ne'
  have hρ : Function.Surjective ρ :=
    finiteEtaleGaloisCoverFunctionFieldQuotientMonoidHom_surjective
      (U.genericExtensionMorphism Ω) W hW w
  have hcomp : ρ.comp qU = AlgEquiv.restrictNormalHom (F := K) (K₁ := Ω) L := by
    apply MonoidHom.ext
    intro τ
    exact (finiteEtaleGaloisCoverFunctionFieldQuotientMonoidHom_apply
      (U.genericExtensionMorphism Ω) W hW w (qU τ)).trans
      (restrictNormalHom_eq_finiteEtaleAutFunctionFieldAlgEquiv_absoluteGenericGalois_rebased
        Ω W hW w τ).symm
  obtain ⟨P, hP⟩ :=
    exists_heightOneSpectrum_absoluteNormalizationPrimeContraction (L := L) v.val Q
  let E : DoubleCoset.Quotient (N : Set G) (I : Set G) ≃
      Place.galoisPlaceFiber (L := L) v.val :=
    normalizationPlaceDoubleCosetEquiv v.val qU ρ hρ hcomp Q P hP
  let b0 := boundaryPlaceFiberEmbedding M Mc d hd hdsurj jU jW hboundary hfield v
  let b : DoubleCoset.Quotient (N : Set G) (I : Set G) ↪ Mc.openBoundaryPlaces jW :=
    ⟨fun t => b0 (E t), b0.injective.comp E.injective⟩
  choose σ hσ using (absoluteGenericGaloisToFundamentalGroup_surjective U Ω)
  have hσ' (a : G) : qU (σ a) = a := hσ a
  let Qσ (a : G) : Ideal (integralClosure v.val.toValuationSubring Ω) := σ a • Q
  let (a : G) : (Qσ a).IsPrime := by dsimp only [Qσ]; infer_instance
  let z (a : G) : Place.galoisPlaceFiber (L := L) v.val := E (DoubleCoset.mk N I a)
  let Pg (a : G) : HeightOneSpectrum (Place.integralClosureAt L v.val) :=
    Place.fiberCenter L v.val (z a).property
  have hPg (a : G) : (Pg a).asIdeal =
      absoluteNormalizationPrimeContraction
        (A := v.val.toValuationSubring) (L := L) (Omega := Ω) (Qσ a) := by
    have hτ := normalizationPlaceDoubleCosetEquiv_mk_fiberCenter
      v.val qU ρ hρ hcomp Q P hP (σ a)
    change (Place.fiberCenter L v.val
      (E (DoubleCoset.mk N I (qU (σ a)))).property).asIdeal =
        absoluteNormalizationPrimeContraction
          (A := v.val.toValuationSubring) (L := L) (Omega := Ω) (Qσ a) at hτ
    rw [hσ' a] at hτ
    exact hτ
  have hplace (a : G) : Place.placeOfPrime (Pg a) = (z a).val :=
    Place.eq_of_fiberCenter_eq (Place.restrict_placeOfPrime (Pg a))
      (z a).property (Place.fiberCenter_placeOfPrime (Pg a))
  let R (a : G) := (Place.placeOfPrime (Pg a)).toValuationSubring
  let QB (a : G) := (Qσ a).comap (normalizationIntegralBaseRingEquiv
    v.val.toValuationSubring (Place.integralClosureAt L v.val) Ω).toRingHom
  let qloc (a : G) := (QB a).map
    (normalizationBaseLocalizationRingMap (Place.integralClosureAt L v.val) (R a) Ω)
  let J (a : G) : Subgroup H :=
    genericPlaceInertia W.left (Place.placeOfPrime (Pg a)) (qloc a)
  have hactual (a : G) : (qloc a).IsMaximal ∧
      (J a).map i = genericPlaceInertia U v.val (Qσ a) ⊓ i.range :=
    pointedCover_actualPlaceInertia_image Ω v.val (Qσ a) W hW w (Pg a) (hPg a)
  have hconj (a : G) : genericPlaceInertia U v.val (Qσ a) =
      I.map (MulAut.conj a).toMonoidHom := by
    rw [genericPlaceInertia_eq_absoluteInertiaImage U v.val (Qσ a)]
    have hsmul := inertia_smul_map Q (σ a) qU
    rw [hσ' a] at hsmul
    exact hsmul
  have hJ (a : G) : (J a).map i = (I.map (MulAut.conj a).toMonoidHom) ⊓ N := by
    rw [← hconj a, ← hrange]
    exact (hactual a).2
  let pLoc (a : G) : Mc.openBoundaryPlaces jW :=
    ⟨Place.placeOfPrime (Pg a), by
      rw [hplace a]
      exact (b (DoubleCoset.mk N I a)).property⟩
  have hpLoc (a : G) : pLoc a = b (DoubleCoset.mk N I a) := Subtype.ext (hplace a)
  let ab := TopologicalAbelianization.mk H
  let C : DoubleCoset.Quotient (N : Set G) (I : Set G) →
      Subgroup (TopologicalAbelianization H) := fun t =>
    (boundaryPlaceInertiaHom Mc jW hjW hcoverLiteral Qc (b t)).toMonoidHom.range
  have hC (a : G) : (J a).map ab ≤ C (DoubleCoset.mk N I a) := by
    let : (show Ideal (normalizationCommAlgCat (pLoc a).val.toValuationSubring Ω)
      from qloc a).IsMaximal := (hactual a).1
    have hCab : (J a).map ab =
        (boundaryPlaceInertiaHom Mc jW hjW hcoverLiteral Qc (pLoc a)).toMonoidHom.range :=
      boundaryInertia_abelianized_range_eq_coordinate_of_maximal
        Mc jW hjW hcoverLiteral Qc (pLoc a) (qloc a)
    rw [hpLoc a] at hCab
    exact hCab.le
  have hdetect : Set.InjOn ab (J 1 : Set H) := by
    let : (show Ideal (normalizationCommAlgCat (pLoc 1).val.toValuationSubring Ω)
      from qloc 1).IsMaximal := (hactual 1).1
    exact boundaryInertia_abelianization_injOn_of_maximal
      Mc jW hjW hcoverLiteral Qc (pLoc 1) (qloc 1)
  have hsep (t u : DoubleCoset.Quotient (N : Set G) (I : Set G))
      (htu : t ≠ u) : C t ⊓ C u = ⊥ := by
    have hbu : b t ≠ b u := fun h => htu (b.injective h)
    have hlt : ({b t, b u} : Finset (Mc.openBoundaryPlaces jW)).card <
        (Finset.univ : Finset (Mc.openBoundaryPlaces jW)).card := by
      have hp := Finset.card_le_two (a := b t) (b := b u)
      simp only [Finset.card_univ]
      omega
    obtain ⟨r, _, hr⟩ := Finset.exists_mem_notMem_of_card_lt_card hlt
    have hrtu : r ≠ b t ∧ r ≠ b u := by
      simpa only [Finset.mem_insert, Finset.mem_singleton, not_or] using hr
    exact boundaryPlaceInertiaHom_range_inf_eq_bot Mc jW hjW hcoverLiteral Qc
      (b t) (b u) r hbu hrtu.1.symm hrtu.2.symm
  have hxI : x ∈ I := by rw [← hIeq]; exact hx
  have hDC := AnabelianGeometry.CuspidalInertia.doubleCoset_eq_of_commute_of_inertia_coordinates
    I N hN i hi J hJ ab C hC hsep hdetect x hxI hpow g hcomm
  change DoubleCoset.mk
      (finiteEtaleGaloisCoverQuotientMonoidHom
        (U.genericExtensionMorphism Ω) W hW w).ker
      (genericPlaceInertia U v.val (Qfamily v)) 1 = _
  rw [← hNdeck, hIeq]
  exact hDC

end EtaleFundamentalGroups.Inertia
