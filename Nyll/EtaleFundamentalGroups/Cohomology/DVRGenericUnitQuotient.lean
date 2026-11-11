/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.EtaleFundamentalGroups.Cohomology.GenericSectionsComparison
public import Nyll.EtaleFundamentalGroups.StrictHenselian.GeometricStalkDVR
public import Nyll.SchemeTheory.Divisors.DVRUnitQuotient
public import Nyll.SchemeTheory.Divisors.DedekindPrincipalDivisor
public import Nyll.EtaleFundamentalGroups.StrictHenselian.GeometricStalkFractionFieldMap
public import Mathlib.Algebra.Group.Units.Equiv
public import Mathlib.Algebra.Category.Grp.Zero
public import Mathlib.Algebra.Category.Grp.EpiMono
public import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor
public import Mathlib.RingTheory.DedekindDomain.Dvr
public import Nyll.EtaleCohomology.Classical.AbelianSheafFunctors
public import Nyll.EtaleCohomology.Classical.MultiplicativeGroup
public import Nyll.EtaleCohomology.Classical.MultiplicativeGroupPushforward
public import Nyll.SchemeTheory.Sheaves.UnitStalks

/-!
# The actual generic-unit quotient stalk over a DVR

The geometric stalk of the actual quotient of the direct image of the
generic multiplicative group by the local multiplicative group is infinite
cyclic. The comparison uses the actual ring-stalk map and its proved
compatibility with the fraction-field inclusion.
-/

@[expose] public section

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

namespace EtaleFundamentalGroups.StrictHenselian

universe u

section General

variable (R : Type u) [CommRing R] [IsDomain R] [IsIntegrallyClosed R]
  {Ω : Type u} [Field Ω] [IsSepClosed Ω] (φ : R →+* Ω)

/-- The actual generic-unit quotient stalk identifies with the actual
fraction-field unit cokernel of the geometric local ring. -/
def geometricGenericUnitQuotientStalkIso :
    ((Scheme.pointSmallEtale (Spec.map (CommRingCat.ofHom φ))).sheafFiber
        (A := AddCommGrpCat.{u})).obj
      (cokernel (EtaleCohomology.etaleMultiplicativeGroupToPushforward
        (Spec.map (CommRingCat.ofHom (algebraMap R (FractionRing R)))))) ≅
      cokernel (IsDiscreteValuationRing.fractionUnitInclusion
        (geometricStalk (Spec.map (CommRingCat.ofHom φ)))
        (FractionRing (geometricStalk (Spec.map (CommRingCat.ofHom φ))))) := by
  let s := Spec.map (CommRingCat.ofHom φ)
  let j := Spec.map (CommRingCat.ofHom (algebraMap R (FractionRing R)))
  let A := geometricStalk s
  let B := ((Scheme.pointSmallEtale s).presheafFiber (A := CommRingCat.{u})).obj
    (etaleBaseChangedSections j)
  let F := FractionRing A
  let p : AddCommGrpCat.of (Additive Aˣ) ⟶ AddCommGrpCat.of (Additive Bˣ) :=
    AddCommGrpCat.ofHom
      (Units.map
        (((Scheme.pointSmallEtale s).presheafFiber (A := CommRingCat.{u})).map
          (etaleSectionsToBaseChanged j)).hom.toMonoidHom).toAdditive
  let q := IsDiscreteValuationRing.fractionUnitInclusion A F
  let e₁ : AddCommGrpCat.of (Additive Aˣ) ≅ AddCommGrpCat.of (Additive Aˣ) :=
    Iso.refl _
  let e₂ : AddCommGrpCat.of (Additive Bˣ) ≅ AddCommGrpCat.of (Additive Fˣ) :=
    (Units.mapEquiv (geometricGenericSectionsStalkEquiv R φ).toMulEquiv).toAdditive.toAddCommGrpIso
  have h : p ≫ e₂.hom = e₁.hom ≫ q := by
    apply AddCommGrpCat.ext
    intro a
    let a₀ : Additive Aˣ := a
    apply Units.ext
    exact geometricGenericSectionsStalkEquiv_map R φ ((a₀.toMul : Aˣ) : A)
  exact geometricUnitQuotientStalkIso s j ≪≫
    cokernel.mapIso (f := p) q e₁ e₂ h

/-- The generic-unit quotient comparison retains the actual cokernel projection. -/
theorem geometricGenericUnitQuotientStalkIso_π :
    let s := Spec.map (CommRingCat.ofHom φ)
    let j := Spec.map (CommRingCat.ofHom (algebraMap R (FractionRing R)))
    let F := (Scheme.pointSmallEtale s).sheafFiber (A := AddCommGrpCat.{u})
    let g := EtaleCohomology.etaleMultiplicativeGroupToPushforward j
    let Q := etaleBaseChangedSections j
    let B := ((Scheme.pointEtaleNeighborhoods s).presheafFiber
      (A := CommRingCat.{u})).obj Q
    F.map (cokernel.π g) ≫ (geometricGenericUnitQuotientStalkIso R φ).hom =
      ((geometricMultiplicativeGroupPushforwardStalkEquiv s j).toAddCommGrpIso
        (X := F.obj ((EtaleCohomology.etaleAbelianPushforward j).obj
          (EtaleCohomology.etaleMultiplicativeGroupSheaf (Spec (CommRingCat.of (FractionRing R))))))
        (Y := AddCommGrpCat.of (Additive (Bˣ)))).hom ≫
        ((Units.mapEquiv
          (geometricGenericSectionsStalkEquiv R φ).toMulEquiv).toAdditive.toAddCommGrpIso
          (X := AddCommGrpCat.of (Additive (Bˣ)))
          (Y := AddCommGrpCat.of (Additive (FractionRing (geometricStalk s))ˣ))).hom ≫
          cokernel.π (IsDiscreteValuationRing.fractionUnitInclusion
            (geometricStalk s) (FractionRing (geometricStalk s))) := by
  intro s j F g
  let A := geometricStalk s
  let U := ((Scheme.pointEtaleNeighborhoods s).presheafFiber
    (A := CommRingCat.{u})).obj (etaleSections (Spec (CommRingCat.of R)))
  let B := ((Scheme.pointEtaleNeighborhoods s).presheafFiber
    (A := CommRingCat.{u})).obj (etaleBaseChangedSections j)
  let eUnits : F.obj (EtaleCohomology.etaleMultiplicativeGroupSheaf
      (Spec (CommRingCat.of R))) ≅ AddCommGrpCat.of (Additive Uˣ) :=
    (Scheme.pointEtaleNeighborhoods s).unitStalkEquiv
      (etaleSections (Spec (CommRingCat.of R))) |>.toAddCommGrpIso
  let p := AddCommGrpCat.ofHom (Units.map
      (((Scheme.pointEtaleNeighborhoods s).presheafFiber
        (A := CommRingCat.{u})).map (etaleSectionsToBaseChanged j)).hom.toMonoidHom).toAdditive
  let q := IsDiscreteValuationRing.fractionUnitInclusion A (FractionRing A)
  let e₁ : AddCommGrpCat.of (Additive Uˣ) ≅ AddCommGrpCat.of (Additive Aˣ) := Iso.refl _
  let e₂ : AddCommGrpCat.of (Additive Bˣ) ≅
      AddCommGrpCat.of (Additive (FractionRing A)ˣ) :=
    (Units.mapEquiv (geometricGenericSectionsStalkEquiv R φ).toMulEquiv).toAdditive.toAddCommGrpIso
  let ePush : F.obj ((EtaleCohomology.etaleAbelianPushforward j).obj
      (EtaleCohomology.etaleMultiplicativeGroupSheaf
        (Spec (CommRingCat.of (FractionRing R))))) ≅
      AddCommGrpCat.of (Additive Bˣ) :=
    (geometricMultiplicativeGroupPushforwardStalkEquiv s j).toAddCommGrpIso
  have hUnits : F.map g ≫ ePush.hom = eUnits.hom ≫ p := by
    apply AddCommGrpCat.ext
    intro a
    exact geometricMultiplicativeGroupPushforwardStalkEquiv_map s j a
  have hFirst : F.map (cokernel.π g) ≫
      (geometricUnitQuotientStalkIso s j).hom = ePush.hom ≫ cokernel.π p := by
    change F.map (cokernel.π g) ≫
      ((PreservesCokernel.iso F g) ≪≫
        cokernel.mapIso (f := F.map g) p eUnits ePush
          hUnits).hom = ePush.hom ≫ cokernel.π p
    rw [Iso.trans_hom, ← Category.assoc, PreservesCokernel.π_iso_hom]
    rw [cokernel.mapIso_hom, cokernel.map]
    exact cokernel.π_desc _ _ _
  have hCompare : p ≫ e₂.hom = e₁.hom ≫ q := by
    apply AddCommGrpCat.ext
    intro a
    let a₀ : Additive Aˣ := a
    apply Units.ext
    change geometricGenericSectionsStalkEquiv R φ
      (((Scheme.pointSmallEtale s).presheafFiber (A := CommRingCat.{u})).map
        (etaleSectionsToBaseChanged j) ((a₀.toMul : Aˣ) : A)) =
        algebraMap A (FractionRing A) ((a₀.toMul : Aˣ) : A)
    exact geometricGenericSectionsStalkEquiv_map R φ ((a₀.toMul : Aˣ) : A)
  calc
    F.map (cokernel.π g) ≫ (geometricGenericUnitQuotientStalkIso R φ).hom =
        F.map (cokernel.π g) ≫ (geometricUnitQuotientStalkIso s j).hom ≫
          (cokernel.mapIso (f := p) q e₁ e₂ hCompare).hom := by
      change F.map (cokernel.π g) ≫
        (geometricUnitQuotientStalkIso s j ≪≫ cokernel.mapIso (f := p) q e₁ e₂ hCompare).hom = _
      rw [Iso.trans_hom]
    _ = ePush.hom ≫ cokernel.π p ≫
        (cokernel.mapIso (f := p) q e₁ e₂ hCompare).hom := by
      simpa only [Category.assoc] using
        congrArg (fun k => k ≫ (cokernel.mapIso (f := p) q e₁ e₂ hCompare).hom) hFirst
    _ = ePush.hom ≫ e₂.hom ≫ cokernel.π q := by
      apply congrArg (fun k => ePush.hom ≫ k)
      rw [cokernel.mapIso_hom, cokernel.map]
      exact cokernel.π_desc _ _ _
    _ = _ := rfl

/-- At a geometric point over the generic point of a normal affine scheme,
the actual generic-unit quotient sheaf has zero stalk. -/
theorem geometricGenericUnitQuotientStalk_isZero_of_injective
    (hφ : Function.Injective φ) :
    IsZero (((Scheme.pointSmallEtale (Spec.map (CommRingCat.ofHom φ))).sheafFiber
        (A := AddCommGrpCat.{u})).obj
      (cokernel (EtaleCohomology.etaleMultiplicativeGroupToPushforward
        (Spec.map (CommRingCat.ofHom (algebraMap R (FractionRing R))))))) := by
  let A := geometricStalk (Spec.map (CommRingCat.ofHom φ))
  let F := FractionRing A
  have hA : IsField A := geometricStalk_isField_of_injective φ hφ
  have hb : Function.Bijective (algebraMap A F) :=
    ⟨IsFractionRing.injective A F, (IsFractionRing.surjective_iff_isField).mpr hA⟩
  let e : Aˣ ≃* Fˣ :=
    Units.mapEquiv (RingEquiv.ofBijective (algebraMap A F) hb).toMulEquiv
  let q := IsDiscreteValuationRing.fractionUnitInclusion A F
  have hq : Function.Surjective q := e.toAdditive.surjective
  have : Epi q := ConcreteCategory.epi_of_surjective q hq
  exact (isZero_cokernel_of_epi q).of_iso (geometricGenericUnitQuotientStalkIso R φ)

/-- If the actual geometric local ring is a DVR, its generic-unit quotient
stalk is infinite cyclic. The following corollaries supply this DVR structure
from the ordinary local ring, rather than assuming it for a curve. -/
def geometricGenericUnitQuotientStalkIntEquiv
    [IsDiscreteValuationRing (geometricStalk (Spec.map (CommRingCat.ofHom φ)))] :
    ((Scheme.pointSmallEtale (Spec.map (CommRingCat.ofHom φ))).sheafFiber
        (A := AddCommGrpCat.{u})).obj
      (cokernel (EtaleCohomology.etaleMultiplicativeGroupToPushforward
        (Spec.map (CommRingCat.ofHom (algebraMap R (FractionRing R)))))) ≃+ ℤ := by
  let A := geometricStalk (Spec.map (CommRingCat.ofHom φ))
  let F := FractionRing A
  let π : A := Classical.choose (IsDiscreteValuationRing.exists_irreducible A)
  have hπ : Irreducible π :=
    Classical.choose_spec (IsDiscreteValuationRing.exists_irreducible A)
  have hπF : algebraMap A F π ≠ 0 := by
    intro h
    apply hπ.ne_zero
    apply IsFractionRing.injective A F
    exact h.trans (map_zero (algebraMap A F)).symm
  let πF : Fˣ := Units.mk0 (algebraMap A F π) hπF
  exact (geometricGenericUnitQuotientStalkIso R φ).addCommGroupIsoToAddEquiv.trans
    (IsDiscreteValuationRing.fractionUnitCokernelEquiv A F hπ πF rfl).symm

end General

section LocalBase

variable (R : Type u) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  {Ω : Type u} [Field Ω] [IsSepClosed Ω] (φ : R →+* Ω) [IsLocalHom φ]

/-- Over a DVR base, the actual generic-unit quotient has integer geometric stalk. -/
def geometricDVRGenericUnitQuotientStalkIntEquiv :
    ((Scheme.pointSmallEtale (Spec.map (CommRingCat.ofHom φ))).sheafFiber
        (A := AddCommGrpCat.{u})).obj
      (cokernel (EtaleCohomology.etaleMultiplicativeGroupToPushforward
        (Spec.map (CommRingCat.ofHom (algebraMap R (FractionRing R)))))) ≃+ ℤ :=
  geometricGenericUnitQuotientStalkIntEquiv R φ

end LocalBase

section DedekindBase

variable (R : Type u) [CommRing R] [IsDedekindDomain R]
  {Ω : Type u} [Field Ω] [IsSepClosed Ω] (φ : R →+* Ω)

/-- At a non-generic geometric point of an affine Dedekind scheme, the
actual generic-unit quotient sheaf has stalk isomorphic to the integers. -/
def geometricDedekindGenericUnitQuotientStalkIntEquiv (hφ : RingHom.ker φ ≠ ⊥) :
    ((Scheme.pointSmallEtale (Spec.map (CommRingCat.ofHom φ))).sheafFiber
        (A := AddCommGrpCat.{u})).obj
      (cokernel (EtaleCohomology.etaleMultiplicativeGroupToPushforward
        (Spec.map (CommRingCat.ofHom (algebraMap R (FractionRing R)))))) ≃+ ℤ := by
  have hP : (geometricBasePrime φ).asIdeal ≠ ⊥ := hφ
  have : IsDiscreteValuationRing (Localization.AtPrime (geometricBasePrime φ).asIdeal) :=
    IsLocalization.AtPrime.isDiscreteValuationRing_of_dedekind_domain R hP _
  have : IsDiscreteValuationRing (geometricStalk (Spec.map (CommRingCat.ofHom φ))) :=
    geometricStalk_isDiscreteValuationRing_of_baseLocalization φ
  exact geometricGenericUnitQuotientStalkIntEquiv R φ

/-- Multiplication by a positive integer is injective on every actual
generic-unit quotient stalk of a Dedekind affine scheme. -/
theorem geometricDedekindGenericUnitQuotientStalk_nsmul_injective
    (n : ℕ) (hn : n ≠ 0) :
    Function.Injective (fun a =>
      n • a : ((Scheme.pointSmallEtale
        (Spec.map (CommRingCat.ofHom φ))).sheafFiber
          (A := AddCommGrpCat.{u})).obj
        (cokernel (EtaleCohomology.etaleMultiplicativeGroupToPushforward
          (Spec.map (CommRingCat.ofHom (algebraMap R (FractionRing R)))))) → _) := by
  by_cases hφ : RingHom.ker φ = ⊥
  · have hzero := geometricGenericUnitQuotientStalk_isZero_of_injective R φ
      ((RingHom.injective_iff_ker_eq_bot φ).mpr hφ)
    have := AddCommGrpCat.subsingleton_of_isZero hzero
    intro a b _
    exact Subsingleton.elim a b
  · let e := geometricDedekindGenericUnitQuotientStalkIntEquiv R φ hφ
    intro a b h
    apply e.injective
    have he := congrArg e h
    rw [map_nsmul, map_nsmul] at he
    change (n : ℤ) * e a = (n : ℤ) * e b at he
    exact mul_left_cancel₀ (Int.natCast_ne_zero.mpr hn) he

end DedekindBase

section GlobalDedekind

variable (R : Type u) [CommRing R] [IsDedekindDomain R]

/-- The actual quotient of generic units by local units on a Dedekind
affine scheme has no nonzero integer torsion, as a sheaf. -/
theorem genericUnitQuotient_nsmul_mono (n : ℕ) (hn : n ≠ 0) :
    Mono (n • 𝟙 (cokernel
      (EtaleCohomology.etaleMultiplicativeGroupToPushforward
        (Spec.map (CommRingCat.ofHom (algebraMap R (FractionRing R))))))) := by
  let Q := cokernel (EtaleCohomology.etaleMultiplicativeGroupToPushforward
    (Spec.map (CommRingCat.ofHom (algebraMap R (FractionRing R)))))
  have hgeo {Ω : Type u} [Field Ω] [IsSepClosed Ω]
      (s : Spec (CommRingCat.of Ω) ⟶ Spec (CommRingCat.of R)) :
      Mono (((Scheme.pointSmallEtale s).sheafFiber
        (A := AddCommGrpCat.{u})).map (n • 𝟙 Q)) := by
    obtain ⟨φ, rfl⟩ := Spec.map_surjective s
    rw [Functor.map_nsmul, CategoryTheory.Functor.map_id]
    apply ConcreteCategory.mono_of_injective
    exact geometricDedekindGenericUnitQuotientStalk_nsmul_injective R φ.hom n hn
  apply ((Scheme.isConservativeFamilyOfPoints_pointSmallEtale'
    (Spec (CommRingCat.of R))).jointlyReflectMonomorphisms AddCommGrpCat.{u}).mono_iff
      (n • 𝟙 Q) |>.mpr
  rintro ⟨_, ⟨x⟩⟩
  exact hgeo _

end GlobalDedekind

section PrincipalDivisorGerm

open IsDedekindDomain

variable (R : Type u) [CommRing R] [IsDedekindDomain R]
  {Ω : Type u} [Field Ω] (φ : R →+* Ω)
  (v : HeightOneSpectrum R) (hv : v.asIdeal = RingHom.ker φ)

/-- Identify the base localization with the valuation subring at the specified height-one point. -/
def geometricStalkValuationSubringEquiv :
    Localization.AtPrime (geometricBasePrime φ).asIdeal ≃ₐ[R]
      HeightOneSpectrum.valuationSubringAtPrime (FractionRing R) v := by
  have hM : v.asIdeal.primeCompl = (geometricBasePrime φ).asIdeal.primeCompl := by
    ext r
    change r ∉ v.asIdeal ↔ r ∉ RingHom.ker φ
    rw [hv]
  letI : IsLocalization ((geometricBasePrime φ).asIdeal.primeCompl)
      (HeightOneSpectrum.valuationSubringAtPrime (FractionRing R) v) := by
    exact hM ▸ (inferInstance : IsLocalization (v.asIdeal.primeCompl)
      (HeightOneSpectrum.valuationSubringAtPrime (FractionRing R) v))
  exact IsLocalization.algEquiv ((geometricBasePrime φ).asIdeal.primeCompl)
    (Localization.AtPrime (geometricBasePrime φ).asIdeal)
    (HeightOneSpectrum.valuationSubringAtPrime (FractionRing R) v)

/-- The actual geometric germ map extends to the valuation subring at its base point. -/
def geometricStalkValuationSubringMap :
    HeightOneSpectrum.valuationSubringAtPrime (FractionRing R) v →+*
      geometricStalk (Spec.map (CommRingCat.ofHom φ)) := by
  exact (geometricStalkBaseLocalizationMap φ).comp
    (geometricStalkValuationSubringEquiv (R := R) (φ := φ) (v := v) (hv := hv)).symm.toRingHom

/-- The actual map from the base valuation ring into the geometric stalk is local. -/
instance geometricStalkValuationSubringMap_isLocalHom :
    IsLocalHom (geometricStalkValuationSubringMap R φ v hv) := by
  let e := geometricStalkValuationSubringEquiv
    (R := R) (φ := φ) (v := v) (hv := hv)
  constructor
  intro a ha
  have hb : IsUnit (e.symm a) :=
    IsLocalHom.map_nonunit (f := geometricStalkBaseLocalizationMap φ) (e.symm a) ha
  have hc := hb.map e.toRingHom
  change IsUnit (e (e.symm a)) at hc
  rw [e.apply_symm_apply] at hc
  exact hc

/-- On base elements the localized map is the actual structure map. -/
theorem geometricStalkValuationSubringMap_apply (r : R) :
    geometricStalkValuationSubringMap (R := R) (φ := φ) (v := v) (hv := hv)
      (algebraMap R (HeightOneSpectrum.valuationSubringAtPrime (FractionRing R) v) r) =
        geometricStalkStructureMap φ r := by
  rw [geometricStalkValuationSubringMap, RingHom.comp_apply]
  rw [show (geometricStalkValuationSubringEquiv
      (R := R) (φ := φ) (v := v) (hv := hv)).symm.toRingEquiv.toRingHom
      (algebraMap R (HeightOneSpectrum.valuationSubringAtPrime (FractionRing R) v) r) =
      algebraMap R (Localization.AtPrime (geometricBasePrime φ).asIdeal) r from
        (geometricStalkValuationSubringEquiv (R := R) (φ := φ) (v := v) (hv := hv)).symm.commutes r,
    geometricStalkBaseLocalizationMap_apply]

/-- Compatibility with the actual map on fraction fields. -/
theorem geometricStalkValuationSubringMap_fraction :
    (algebraMap (geometricStalk (Spec.map (CommRingCat.ofHom φ)))
      (FractionRing (geometricStalk (Spec.map (CommRingCat.ofHom φ))))).comp
        (geometricStalkValuationSubringMap (R := R) (φ := φ) (v := v) (hv := hv)) =
      (geometricStalkFractionFieldMap φ).comp
        (algebraMap (HeightOneSpectrum.valuationSubringAtPrime (FractionRing R) v)
          (FractionRing R)) := by
  apply IsLocalization.ringHom_ext v.asIdeal.primeCompl
  ext r
  change algebraMap _ _ (geometricStalkValuationSubringMap
      (R := R) (φ := φ) (v := v) (hv := hv) (algebraMap R _ r)) =
    geometricStalkFractionFieldMap φ (algebraMap _ (FractionRing R) (algebraMap R _ r))
  rw [geometricStalkValuationSubringMap_apply]
  rw [← IsScalarTower.algebraMap_apply R
    (HeightOneSpectrum.valuationSubringAtPrime (FractionRing R) v) (FractionRing R) r]
  rw [geometricStalkFractionFieldMap_algebraMap]

include hv in
/-- A vanishing principal-divisor coefficient gives an actual unit in the geometric stalk
whose fraction-field image is the original rational function. -/
theorem exists_geometricUnit_of_principalDivisor_eq_zero
    (a : Additive (FractionRing R)ˣ)
    (ha : FractionalIdeal.principalDivisorAddHom R (FractionRing R) a v = 0) :
    ∃ u : (geometricStalk (Spec.map (CommRingCat.ofHom φ)))ˣ,
      Units.map (algebraMap _ (FractionRing (geometricStalk
        (Spec.map (CommRingCat.ofHom φ))))).toMonoidHom u =
      Units.map (geometricStalkFractionFieldMap φ).toMonoidHom a.toMul := by
  obtain ⟨u, hu⟩ :=
    FractionalIdeal.exists_localUnit_of_principalDivisor_apply_eq_zero
      R (FractionRing R) v a ha
  let f := geometricStalkValuationSubringMap
    (R := R) (φ := φ) (v := v) (hv := hv)
  refine ⟨Units.map f.toMonoidHom u, ?_⟩
  apply Units.ext
  change algebraMap _ _ (f (u : _)) =
    geometricStalkFractionFieldMap φ (a.toMul : FractionRing R)
  have hmap := congrArg (fun f => f (u : _))
    (geometricStalkValuationSubringMap_fraction
      (R := R) (φ := φ) (v := v) (hv := hv))
  rw [RingHom.comp_apply] at hmap
  rw [hmap]
  exact congrArg (geometricStalkFractionFieldMap φ) (congrArg Units.val hu)

include hv in
/-- A rational function which becomes an actual geometric local unit has zero
principal-divisor coefficient at the base point. -/
theorem principalDivisor_eq_zero_of_exists_geometricUnit
    (a : Additive (FractionRing R)ˣ)
    (h : ∃ u : (geometricStalk (Spec.map (CommRingCat.ofHom φ)))ˣ,
      Units.map (algebraMap _ (FractionRing (geometricStalk
        (Spec.map (CommRingCat.ofHom φ))))).toMonoidHom u =
      Units.map (geometricStalkFractionFieldMap φ).toMonoidHom a.toMul) :
    FractionalIdeal.principalDivisorAddHom R (FractionRing R) a v = 0 := by
  obtain ⟨u, hu⟩ := h
  apply (FractionalIdeal.principalDivisor_apply_eq_zero_iff_mem_localUnitGroup
    R (FractionRing R) v a).mpr
  apply ValuationSubring.mem_unitGroup_of_fraction_image_unit
    (HeightOneSpectrum.valuationSubringAtPrime (FractionRing R) v)
    (geometricStalkValuationSubringMap R φ v hv)
    (geometricStalkFractionFieldMap φ)
    (geometricStalkValuationSubringMap_fraction R φ v hv) a.toMul u
  exact (congrArg Units.val hu).symm

include hv in
/-- Vanishing of a base principal-divisor coefficient is equivalent to becoming
a unit in the actual geometric local ring. -/
theorem principalDivisor_eq_zero_iff_exists_geometricUnit
    (a : Additive (FractionRing R)ˣ) :
    FractionalIdeal.principalDivisorAddHom R (FractionRing R) a v = 0 ↔
      ∃ u : (geometricStalk (Spec.map (CommRingCat.ofHom φ)))ˣ,
        Units.map (algebraMap _ (FractionRing (geometricStalk
          (Spec.map (CommRingCat.ofHom φ))))).toMonoidHom u =
        Units.map (geometricStalkFractionFieldMap φ).toMonoidHom a.toMul :=
  ⟨exists_geometricUnit_of_principalDivisor_eq_zero R φ v hv a,
    principalDivisor_eq_zero_of_exists_geometricUnit R φ v hv a⟩

include hv in
/-- A rational function of order zero has zero class in the actual
fraction-unit cokernel of the geometric local ring. -/
theorem geometricFractionUnitCokernel_eq_zero_of_principalDivisor_eq_zero
    (a : Additive (FractionRing R)ˣ)
    (ha : FractionalIdeal.principalDivisorAddHom R (FractionRing R) a v = 0) :
    cokernel.π (IsDiscreteValuationRing.fractionUnitInclusion
      (geometricStalk (Spec.map (CommRingCat.ofHom φ)))
      (FractionRing (geometricStalk (Spec.map (CommRingCat.ofHom φ)))))
      (Additive.ofMul (Units.map (geometricStalkFractionFieldMap φ).toMonoidHom
        a.toMul)) = 0 := by
  obtain ⟨u, hu⟩ := exists_geometricUnit_of_principalDivisor_eq_zero
    (R := R) (φ := φ) (v := v) (hv := hv) a ha
  rw [← hu]
  exact ConcreteCategory.congr_hom (cokernel.condition
    (IsDiscreteValuationRing.fractionUnitInclusion
      (geometricStalk (Spec.map (CommRingCat.ofHom φ)))
      (FractionRing (geometricStalk (Spec.map (CommRingCat.ofHom φ))))))
    (Additive.ofMul u)

include hv in
/-- Zero in the actual geometric fraction-unit cokernel detects a zero
principal-divisor coefficient on the base. -/
theorem principalDivisor_eq_zero_of_geometricFractionUnitCokernel_eq_zero
    (a : Additive (FractionRing R)ˣ)
    (ha : cokernel.π (IsDiscreteValuationRing.fractionUnitInclusion
      (geometricStalk (Spec.map (CommRingCat.ofHom φ)))
      (FractionRing (geometricStalk (Spec.map (CommRingCat.ofHom φ)))))
      (Additive.ofMul (Units.map (geometricStalkFractionFieldMap φ).toMonoidHom
        a.toMul)) = 0) :
    FractionalIdeal.principalDivisorAddHom R (FractionRing R) a v = 0 := by
  let A := geometricStalk (Spec.map (CommRingCat.ofHom φ))
  let f := IsDiscreteValuationRing.fractionUnitInclusion A (FractionRing A)
  let T := ShortComplex.mk f (cokernel.π f) (cokernel.condition f)
  have hT : T.Exact := ShortComplex.exact_cokernel f
  obtain ⟨b, hb⟩ := (ShortComplex.ab_exact_iff T).mp hT
    (Additive.ofMul (Units.map (geometricStalkFractionFieldMap φ).toMonoidHom
      a.toMul)) ha
  apply principalDivisor_eq_zero_of_exists_geometricUnit
    (R := R) (φ := φ) (v := v) (hv := hv) a
  refine ⟨b.toMul, ?_⟩
  exact congrArg Additive.toMul hb

include hv in
/-- The actual geometric fraction-unit quotient detects exactly the
principal-divisor coefficient at the chosen base point. -/
theorem geometricFractionUnitCokernel_eq_zero_iff_principalDivisor_eq_zero
    (a : Additive (FractionRing R)ˣ) :
    cokernel.π (IsDiscreteValuationRing.fractionUnitInclusion
      (geometricStalk (Spec.map (CommRingCat.ofHom φ)))
      (FractionRing (geometricStalk (Spec.map (CommRingCat.ofHom φ)))))
      (Additive.ofMul (Units.map (geometricStalkFractionFieldMap φ).toMonoidHom
        a.toMul)) = 0 ↔
    FractionalIdeal.principalDivisorAddHom R (FractionRing R) a v = 0 :=
  ⟨principalDivisor_eq_zero_of_geometricFractionUnitCokernel_eq_zero
      (R := R) (φ := φ) (v := v) (hv := hv) a,
    geometricFractionUnitCokernel_eq_zero_of_principalDivisor_eq_zero
      (R := R) (φ := φ) (v := v) (hv := hv) a⟩

/-- Under the actual quotient-stalk comparison, a rational section maps to its
class in the actual geometric fraction-unit cokernel. -/
theorem geometricGenericUnitQuotient_rational_germ_image [IsSepClosed Ω]
    (W : (Spec (CommRingCat.of R)).Etale)
    (t : (Scheme.pointSmallEtale (Spec.map (CommRingCat.ofHom φ))).fiber.obj W)
    (a : Additive (FractionRing R)ˣ) :
    let s := Spec.map (CommRingCat.ofHom φ)
    let j := Spec.map (CommRingCat.ofHom (algebraMap R (FractionRing R)))
    let Φ := Scheme.pointSmallEtale s
    let P := etaleBaseChangedSections j
    let z :
        (CategoryTheory.GrothendieckTopology.Point.additiveUnitsPresheaf P).obj (Opposite.op W) :=
      Additive.ofMul (Units.map
        (((Scheme.ΓSpecIso (CommRingCat.of (FractionRing R))).inv ≫
          (pullback.snd W.hom j).appTop).hom.toMonoidHom) a.toMul)
    (geometricGenericUnitQuotientStalkIso R φ).hom
      ((Φ.sheafFiber (A := AddCommGrpCat.{u})).map
        (cokernel.π (EtaleCohomology.etaleMultiplicativeGroupToPushforward j))
        (Φ.toPresheafFiber W t
          (CategoryTheory.GrothendieckTopology.Point.additiveUnitsPresheaf P) z)) =
      cokernel.π (IsDiscreteValuationRing.fractionUnitInclusion
        (geometricStalk s) (FractionRing (geometricStalk s)))
        (Additive.ofMul (Units.map (geometricStalkFractionFieldMap φ).toMonoidHom
          a.toMul)) := by
  intro s j Φ P z
  let b := Φ.toPresheafFiber W t
    (CategoryTheory.GrothendieckTopology.Point.additiveUnitsPresheaf P) z
  change (Φ.sheafFiber (A := AddCommGrpCat.{u})).obj
    ((EtaleCohomology.etaleAbelianPushforward j).obj
      (EtaleCohomology.etaleMultiplicativeGroupSheaf
        (Spec (CommRingCat.of (FractionRing R))))) at b
  have hπ := ConcreteCategory.congr_hom
    (geometricGenericUnitQuotientStalkIso_π R φ) b
  change ConcreteCategory.hom
    ((Φ.sheafFiber (A := AddCommGrpCat.{u})).map
      (cokernel.π (EtaleCohomology.etaleMultiplicativeGroupToPushforward j)) ≫
        (geometricGenericUnitQuotientStalkIso R φ).hom) b = _
  rw [hπ]
  have hu := geometricGenericUnitStalk_scalar R φ W t a
  change cokernel.π (IsDiscreteValuationRing.fractionUnitInclusion
    (geometricStalk s) (FractionRing (geometricStalk s)))
    ((Units.map (geometricGenericSectionsStalkEquiv R φ).toMonoidHom).toAdditive
      (geometricMultiplicativeGroupPushforwardStalkEquiv s j b)) = _
  rw [hu]
  rfl

include hv in
/-- A rational unit with zero order at the base point has zero germ in
the actual quotient sheaf of generic units by regular units. -/
theorem geometricGenericUnitQuotient_rational_germ_eq_zero [IsSepClosed Ω]
    (W : (Spec (CommRingCat.of R)).Etale)
    (t : (Scheme.pointSmallEtale (Spec.map (CommRingCat.ofHom φ))).fiber.obj W)
    (a : Additive (FractionRing R)ˣ)
    (ha : FractionalIdeal.principalDivisorAddHom R (FractionRing R) a v = 0) :
    let s := Spec.map (CommRingCat.ofHom φ)
    let j := Spec.map (CommRingCat.ofHom (algebraMap R (FractionRing R)))
    let Φ := Scheme.pointSmallEtale s
    let P := etaleBaseChangedSections j
    let z :
        (CategoryTheory.GrothendieckTopology.Point.additiveUnitsPresheaf P).obj (Opposite.op W) :=
      Additive.ofMul (Units.map
        (((Scheme.ΓSpecIso (CommRingCat.of (FractionRing R))).inv ≫
          (pullback.snd W.hom j).appTop).hom.toMonoidHom) a.toMul)
    (Φ.sheafFiber (A := AddCommGrpCat.{u})).map
      (cokernel.π (EtaleCohomology.etaleMultiplicativeGroupToPushforward j))
      (Φ.toPresheafFiber W t
        (CategoryTheory.GrothendieckTopology.Point.additiveUnitsPresheaf P) z) = 0 := by
  intro s j Φ P z
  let e := (geometricGenericUnitQuotientStalkIso R φ).addCommGroupIsoToAddEquiv
  apply e.injective
  rw [map_zero]
  change (geometricGenericUnitQuotientStalkIso R φ).hom
    ((Φ.sheafFiber (A := AddCommGrpCat.{u})).map
      (cokernel.π (EtaleCohomology.etaleMultiplicativeGroupToPushforward j))
      (Φ.toPresheafFiber W t
        (CategoryTheory.GrothendieckTopology.Point.additiveUnitsPresheaf P) z)) = 0
  rw [geometricGenericUnitQuotient_rational_germ_image R φ W t a]
  exact geometricFractionUnitCokernel_eq_zero_of_principalDivisor_eq_zero
    (R := R) (φ := φ) (v := v) (hv := hv) a ha

include hv in
/-- A zero rational germ in the actual quotient sheaf has zero order on the base. -/
theorem principalDivisor_eq_zero_of_geometricGenericUnitQuotient_rational_germ_eq_zero
    [IsSepClosed Ω]
    (W : (Spec (CommRingCat.of R)).Etale)
    (t : (Scheme.pointSmallEtale (Spec.map (CommRingCat.ofHom φ))).fiber.obj W)
    (a : Additive (FractionRing R)ˣ)
    (ha :
      let s := Spec.map (CommRingCat.ofHom φ)
      let j := Spec.map (CommRingCat.ofHom (algebraMap R (FractionRing R)))
      let Φ := Scheme.pointSmallEtale s
      let P := etaleBaseChangedSections j
      let z :
          (CategoryTheory.GrothendieckTopology.Point.additiveUnitsPresheaf P).obj (Opposite.op W) :=
        Additive.ofMul (Units.map
          (((Scheme.ΓSpecIso (CommRingCat.of (FractionRing R))).inv ≫
            (pullback.snd W.hom j).appTop).hom.toMonoidHom) a.toMul)
      (Φ.sheafFiber (A := AddCommGrpCat.{u})).map
        (cokernel.π (EtaleCohomology.etaleMultiplicativeGroupToPushforward j))
        (Φ.toPresheafFiber W t
          (CategoryTheory.GrothendieckTopology.Point.additiveUnitsPresheaf P) z) = 0) :
    FractionalIdeal.principalDivisorAddHom R (FractionRing R) a v = 0 := by
  apply principalDivisor_eq_zero_of_geometricFractionUnitCokernel_eq_zero
    (R := R) (φ := φ) (v := v) (hv := hv) a
  rw [← geometricGenericUnitQuotient_rational_germ_image R φ W t a, ha, map_zero]

include hv in
/-- Every actual geometric fraction-unit class at a closed point is represented
by a rational function on the base. -/
theorem geometricFractionUnitCokernel_rational_surjective [IsSepClosed Ω] :
    Function.Surjective (fun a : Additive (FractionRing R)ˣ =>
      cokernel.π (IsDiscreteValuationRing.fractionUnitInclusion
        (geometricStalk (Spec.map (CommRingCat.ofHom φ)))
        (FractionRing (geometricStalk (Spec.map (CommRingCat.ofHom φ)))))
        (Additive.ofMul (Units.map (geometricStalkFractionFieldMap φ).toMonoidHom
          a.toMul))) := by
  let L := Localization.AtPrime (geometricBasePrime φ).asIdeal
  let A := HeightOneSpectrum.valuationSubringAtPrime (FractionRing R) v
  let B := geometricStalk (Spec.map (CommRingCat.ofHom φ))
  have hP : (geometricBasePrime φ).asIdeal ≠ ⊥ := by
    change RingHom.ker φ ≠ ⊥
    rw [← hv]
    exact v.ne_bot
  have : IsDiscreteValuationRing L :=
    IsLocalization.AtPrime.isDiscreteValuationRing_of_dedekind_domain R hP _
  have : IsDiscreteValuationRing B :=
    geometricStalk_isDiscreteValuationRing_of_baseLocalization φ
  let e : L ≃ₐ[R] A := geometricStalkValuationSubringEquiv
    (R := R) (φ := φ) (v := v) (hv := hv)
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible L
  let πB : B := geometricStalkBaseLocalizationMap φ π
  have hπB0 : πB ≠ 0 := by
    intro hz
    apply hπ.ne_zero
    apply geometricStalkBaseLocalizationMap_injective φ
    exact hz.trans (map_zero (geometricStalkBaseLocalizationMap φ)).symm
  have hπB : Irreducible πB :=
    IsDiscreteValuationRing.irreducible_of_span_eq_maximalIdeal _ hπB0
      (geometricStalk_maximalIdeal_eq_span_baseLocal_uniformizer φ π hπ)
  have hπK0 : ((e π : A) : FractionRing R) ≠ 0 := by
    intro hz
    apply hπ.ne_zero
    apply e.injective
    apply Subtype.ext
    simpa only [map_zero, ZeroMemClass.coe_zero] using hz
  let πK : (FractionRing R)ˣ := Units.mk0 ((e π : A) : FractionRing R) hπK0
  let πF : (FractionRing B)ˣ :=
    Units.map (geometricStalkFractionFieldMap φ).toMonoidHom πK
  have hπF : (πF : FractionRing B) = algebraMap B (FractionRing B) πB := by
    change geometricStalkFractionFieldMap φ ((e π : A) : FractionRing R) =
      algebraMap B (FractionRing B) (geometricStalkBaseLocalizationMap φ π)
    have hfrac := RingHom.congr_fun
      (geometricStalkValuationSubringMap_fraction R φ v hv) (e π)
    change algebraMap B (FractionRing B)
        (geometricStalkValuationSubringMap R φ v hv (e π)) =
      geometricStalkFractionFieldMap φ
        (algebraMap A (FractionRing R) (e π)) at hfrac
    have hmap : geometricStalkValuationSubringMap R φ v hv (e π) =
        geometricStalkBaseLocalizationMap φ π := by
      change geometricStalkBaseLocalizationMap φ (e.symm (e π)) = _
      rw [e.symm_apply_apply]
    rw [hmap] at hfrac
    change algebraMap B (FractionRing B) (geometricStalkBaseLocalizationMap φ π) =
      geometricStalkFractionFieldMap φ ((e π : A) : FractionRing R) at hfrac
    exact hfrac.symm
  let E := IsDiscreteValuationRing.fractionUnitCokernelEquiv B (FractionRing B)
    hπB πF hπF
  intro z
  refine ⟨E.symm z • Additive.ofMul πK, ?_⟩
  change (cokernel.π (IsDiscreteValuationRing.fractionUnitInclusion B (FractionRing B))).hom
    ((Units.map (geometricStalkFractionFieldMap φ).toMonoidHom).toAdditive
      (E.symm z • Additive.ofMul πK)) = z
  rw [map_zsmul, map_zsmul]
  change (E.symm z) •
    (cokernel.π (IsDiscreteValuationRing.fractionUnitInclusion B (FractionRing B))).hom
      (Additive.ofMul πF) = z
  exact E.apply_symm_apply z

end PrincipalDivisorGerm

end EtaleFundamentalGroups.StrictHenselian
