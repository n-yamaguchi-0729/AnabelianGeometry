/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.AlgebraicCurves.Places.Rational.RatFuncRationalPlaceIntegralBase
import Nyll.EtaleFundamentalGroups.Inertia.RationalCuspInertiaConstants
import Nyll.EtaleFundamentalGroups.Inertia.NormalRestrictionKernel
import Nyll.EtaleFundamentalGroups.Inertia.NormalizationIntegralBaseInertia
import Nyll.EtaleFundamentalGroups.GeometricFiber.FieldSourceGaloisNaturality
import Nyll.EtaleFundamentalGroups.GeometricFiber.CanonicalPointedMaps

/-!
# The same rational cusp under extension to algebraically closed constants

The geometric normalization prime is the literal contraction of the original
prime along the integral-base normalization equivalence. Its inertia maps ONTO
the original arithmetic inertia. The reverse inclusion follows from the actual
constant-restriction kernel, rather than a supplied image-comparison hypothesis.
-/

noncomputable section

open AlgebraicCurve AlgebraicGeometry CategoryTheory SchemeTheory
open AlgebraicGeometry.FiniteEtale CategoryTheory.PreGaloisCategory
open AnabelianGeometry.KummerTheory
open scoped RatFunc

attribute [local instance] Polynomial.algebra

namespace EtaleFundamentalGroups.Inertia

attribute [local instance] normalizationCommAlgGaloisAction

-- RatFunc also carries an independently constructed SMul via FractionRing.
-- Every tower below must use the SMul belonging to its selected Algebra,
-- matching the generic scalar-restriction and integral-closure owners.
local instance (priority := 2000) ratFuncAlgebraSMul
    {R K : Type*} [CommSemiring R] [Field K] [Algebra R (RatFunc K)] :
    SMul R (RatFunc K) :=
  (inferInstance : Algebra R (RatFunc K)).toSMul

universe u

private theorem pointedHom_equality_conjugation
    {X Y : Scheme.{u}} {Ω : Type u} [Field Ω]
    (f : Y ⟶ X) (y : Spec (.of Ω) ⟶ Y) (x : Spec (.of Ω) ⟶ X)
    (h : y ≫ f = x) (a : π₁ᵉᵗ(y)) :
    pointedFundamentalGroupHom f y x h a =
      continuousConjAut (eqToIso (congrArg fiber h)) (fundamentalGroupHom f y a) := by
  subst x
  rfl

section FieldKernel

variable {k κ Ω : Type u} [Field k] [Field κ] [Field Ω]
  [Algebra k κ] [Algebra k Ω] [Algebra κ Ω]
  [Algebra (RatFunc k) Ω] [Algebra (RatFunc κ) Ω]
  [IsScalarTower k κ Ω]
  [IsScalarTower k (RatFunc k) Ω]
  [IsScalarTower κ (RatFunc κ) Ω]
  [IsScalarTower (RatFunc k) (RatFunc κ) Ω]
  [IsAlgClosed κ] [IsAlgClosure k κ]

omit [IsAlgClosed κ] in
/-- Fixing the prescribed constants inside the arithmetic absolute group is
exactly the image of the geometric absolute group, with the same embeddings. -/
theorem ratFunc_constantsRestriction_ker_eq :
    ((AlgEquiv.restrictNormalHom (F := k) (K₁ := Ω) κ).comp
      (AlgEquiv.restrictScalarsHom k : Gal(Ω/RatFunc k) →* Gal(Ω/k))).ker =
    (AlgEquiv.restrictScalarsHom (RatFunc k) :
      Gal(Ω/RatFunc κ) →* Gal(Ω/RatFunc k)).range := by
  ext γ
  constructor
  · intro hγ
    have hc : γ.restrictScalars k ∈
        (AlgEquiv.restrictNormalHom (F := k) (K₁ := Ω) κ).ker := hγ
    rw [normalRestriction_ker_eq_restrictScalars_range] at hc
    obtain ⟨δ, hδ⟩ := hc
    have hconstants (c : κ) :
        γ (algebraMap κ Ω c) = algebraMap κ Ω c := by
      have he := congrArg (fun z : Gal(Ω/k) => z (algebraMap κ Ω c)) hδ
      exact he.symm.trans (δ.commutes c)
    let j : RatFunc κ →ₐ[RatFunc k] Ω :=
      IsScalarTower.toAlgHom (RatFunc k) (RatFunc κ) Ω
    have hj : γ.toAlgHom.comp j = j := by
      apply AlgHom.ext_of_adjoin_eq_top
        (ratFunc_constantExtension_adjoin_eq_top (k := k) (L := κ))
      rintro _ ⟨c, rfl⟩
      change γ (algebraMap (RatFunc κ) Ω (algebraMap κ (RatFunc κ) c)) =
        algebraMap (RatFunc κ) Ω (algebraMap κ (RatFunc κ) c)
      rw [← IsScalarTower.algebraMap_apply κ (RatFunc κ) Ω]
      exact hconstants c
    let γgeom : Gal(Ω/RatFunc κ) :=
      { γ with
        commutes' := fun z => DFunLike.congr_fun hj z }
    exact ⟨γgeom, AlgEquiv.ext (fun _ => rfl)⟩
  · rintro ⟨γ, rfl⟩
    apply MonoidHom.mem_ker.mpr
    apply AlgEquiv.ext
    intro c
    apply (algebraMap κ Ω).injective
    calc
      algebraMap κ Ω
          (((γ.restrictScalars (RatFunc k)).restrictScalars k).restrictNormal κ c) =
          γ (algebraMap κ Ω c) :=
        (((γ.restrictScalars (RatFunc k)).restrictScalars k).restrictNormal_commutes κ c)
      _ = γ (algebraMap (RatFunc κ) Ω (algebraMap κ (RatFunc κ) c)) :=
        congrArg γ (IsScalarTower.algebraMap_apply κ (RatFunc κ) Ω c)
      _ = algebraMap (RatFunc κ) Ω (algebraMap κ (RatFunc κ) c) := γ.commutes _
      _ = algebraMap κ Ω c :=
        (IsScalarTower.algebraMap_apply κ (RatFunc κ) Ω c).symm

end FieldKernel

private theorem subgroup_image_of_comap
    {G H : Type*} [Group G] [Group H]
    (r : H →* G) (I : Subgroup G) (J : Subgroup H)
    (hcomap : I.comap r = J) (hrange : I ≤ r.range) : J.map r = I := by
  rw [← hcomap]
  apply Subgroup.ext
  intro γ
  constructor
  · rintro ⟨δ, hδ, rfl⟩
    exact hδ
  · intro hγ
    obtain ⟨δ, hδ⟩ := hrange hγ
    refine ⟨δ, ?_, hδ⟩
    change r δ ∈ I
    rw [hδ]
    exact hγ

private theorem maximal_comap_ringEquiv
    {A B : Type*} [CommRing A] [CommRing B]
    (e : B ≃+* A) (Q : Ideal A) (hQ : Q.IsMaximal) :
    (Q.comap e.toRingHom).IsMaximal := by
  let : Q.IsMaximal := hQ
  exact Ideal.comap_isMaximal_of_surjective e.toRingHom e.surjective

/-- Keep the integral-base theorem on opaque ring and field parameters.
The equality input identifies the already constructed ring equivalence only. -/
private theorem integralBaseInertiaComap_viaEquiv
    {A B F L Ω : Type u} [CommRing A] [CommRing B]
    [Field F] [Field L] [Field Ω]
    [Algebra A B] [Algebra A Ω] [Algebra B Ω]
    [IsScalarTower A B Ω] [Algebra.IsIntegral A B]
    [Algebra A F] [IsFractionRing A F]
    [Algebra B L] [IsFractionRing B L]
    [Algebra F L] [Algebra F Ω] [Algebra L Ω]
    [IsScalarTower F L Ω] [IsScalarTower A F Ω] [IsScalarTower B L Ω]
    [Algebra.IsAlgebraic F Ω] [Algebra.IsAlgebraic L Ω]
    (e : integralClosure B Ω ≃+* integralClosure A Ω)
    (he : e = normalizationIntegralBaseRingEquiv A B Ω)
    (Q : Ideal (normalizationCommAlgCat A Ω)) :
    (Q.inertia Gal(Ω/F)).comap (AlgEquiv.restrictScalarsHom F) =
      (Q.comap e.toRingHom).inertia Gal(Ω/L) := by
  subst e
  let e := normalizationIntegralBaseRingEquiv A B Ω
  -- The ambient-subtype action and the fraction-field restriction action
  -- have the same coefficients, but are not definitionally the same action.
  have hsource (σ : Gal(Ω/L)) (b : integralClosure B Ω) :
      σ • b = galRestrict B L Ω (integralClosure B Ω) σ b := by
    apply Subtype.ext
    change σ (b : Ω) = algebraMap (integralClosure B Ω) Ω
      (galRestrict B L Ω (integralClosure B Ω) σ b)
    exact (algebraMap_galRestrict_apply B
      (K := L) (L := Ω) (B := integralClosure B Ω) σ b).symm
  have hsmul (σ : Gal(Ω/L)) (b : integralClosure B Ω) :
      e (σ • b) = galRestrict A F Ω (integralClosure A Ω)
        (σ.restrictScalars F) (e b) := by
    rw [hsource]
    exact normalizationIntegralBaseRingEquiv_smul
      (A := A) (B := B) (Ω := Ω) F L σ b
  apply Subgroup.ext
  intro σ
  constructor
  · intro h b
    change e (σ • b - b) ∈ Q
    rw [map_sub, hsmul]
    exact h (e b)
  · intro h a
    obtain ⟨b, rfl⟩ := e.surjective a
    have hb := h b
    change e (σ • b - b) ∈ Q at hb
    rw [map_sub, hsmul] at hb
    exact hb

section Normalization

variable {k κ Ω : Type u} [Field k] [Field κ] [Field Ω]
  [Algebra k κ] [Algebra (RatFunc k) Ω] [Algebra (RatFunc κ) Ω]
  [IsScalarTower (RatFunc k) (RatFunc κ) Ω]
  [IsAlgClosed κ] [IsAlgClosure k κ]
  (V : Place k (RatFunc k)) (hV : V.IsRational)
  (W : Place κ (RatFunc κ))
  (hord : ∀ x : RatFunc k,
    W.ord (algebraMap (RatFunc k) (RatFunc κ) x) = V.ord x)
  [Algebra V.toValuationSubring Ω] [Algebra W.toValuationSubring Ω]
  [IsScalarTower V.toValuationSubring (RatFunc k) Ω]
  [IsScalarTower W.toValuationSubring (RatFunc κ) Ω]

omit [IsAlgClosed κ] in
private theorem ratFuncPlace_extension_ambientTower :
    let : Algebra V.toValuationSubring W.toValuationSubring :=
      (ratFuncPlaceExtensionRingHom V W hord).toAlgebra
    IsScalarTower V.toValuationSubring W.toValuationSubring Ω := by
  intro algebraVW
  apply IsScalarTower.of_algebraMap_eq
    (R := V.toValuationSubring) (S := W.toValuationSubring) (A := Ω)
  intro a
  calc
    algebraMap V.toValuationSubring Ω a =
        algebraMap (RatFunc k) Ω (a : RatFunc k) :=
      IsScalarTower.algebraMap_apply V.toValuationSubring (RatFunc k) Ω a
    _ = algebraMap (RatFunc κ) Ω
        (algebraMap (RatFunc k) (RatFunc κ) (a : RatFunc k)) :=
      IsScalarTower.algebraMap_apply (RatFunc k) (RatFunc κ) Ω (a : RatFunc k)
    _ = algebraMap W.toValuationSubring Ω
        (ratFuncPlaceExtensionRingHom V W hord a) :=
      (IsScalarTower.algebraMap_apply W.toValuationSubring (RatFunc κ) Ω
        (ratFuncPlaceExtensionRingHom V W hord a)).symm

/-- The integral-base equivalence for the actual valuation-ring inclusion.
Neither ambient embedding is reselected. -/
def ratFuncRationalPlaceNormalizationEquiv :
    integralClosure W.toValuationSubring Ω ≃+*
      integralClosure V.toValuationSubring Ω := by
  let : Algebra V.toValuationSubring W.toValuationSubring :=
    (ratFuncPlaceExtensionRingHom V W hord).toAlgebra
  let : Algebra.IsIntegral V.toValuationSubring W.toValuationSubring :=
    ratFunc_rationalPlace_extension_isIntegral V hV W hord
  let : IsScalarTower V.toValuationSubring W.toValuationSubring Ω :=
    ratFuncPlace_extension_ambientTower V W hord
  exact normalizationIntegralBaseRingEquiv V.toValuationSubring W.toValuationSubring Ω

include hV in
private theorem rationalPlace_residueRetraction :
    ∃ r : V.toValuationSubring →ₐ[k] k,
      RingHom.ker r.toRingHom = IsLocalRing.maximalIdeal V.toValuationSubring := by
  let e : k ≃ₐ[k] V.ResidueField :=
    AlgEquiv.ofBijective (Algebra.ofId k V.ResidueField)
      ⟨V.algebraMap_residueField_injective, hV⟩
  let r : V.toValuationSubring →ₐ[k] k :=
    e.symm.toAlgHom.comp
      (IsScalarTower.toAlgHom k V.toValuationSubring V.ResidueField)
  refine ⟨r, ?_⟩
  ext a
  change e.symm (IsLocalRing.residue V.toValuationSubring a) = 0 ↔
    a ∈ IsLocalRing.maximalIdeal V.toValuationSubring
  rw [← IsLocalRing.residue_eq_zero_iff]
  constructor
  · intro h
    exact e.symm.injective (h.trans (map_zero e.symm).symm)
  · intro h
    rw [h, map_zero]

variable [Algebra k Ω] [Algebra κ Ω]
  [IsScalarTower k κ Ω] [IsScalarTower k (RatFunc k) Ω]
  [IsScalarTower κ (RatFunc κ) Ω]
  [IsGalois (RatFunc k) Ω] [Algebra.IsAlgebraic (RatFunc κ) Ω]

omit [IsGalois (RatFunc k) Ω] in
private theorem ratFuncPlace_baseConstantTower :
    IsScalarTower k V.toValuationSubring Ω := by
  apply IsScalarTower.of_algebraMap_eq
    (R := k) (S := V.toValuationSubring) (A := Ω)
  intro a
  calc
    algebraMap k Ω a =
        algebraMap (RatFunc k) Ω (algebraMap k (RatFunc k) a) :=
      IsScalarTower.algebraMap_apply k (RatFunc k) Ω a
    _ = algebraMap V.toValuationSubring Ω
        (algebraMap k V.toValuationSubring a) :=
      (IsScalarTower.algebraMap_apply V.toValuationSubring (RatFunc k) Ω
        (algebraMap k V.toValuationSubring a)).symm

omit [Algebra.IsAlgebraic (RatFunc κ) Ω] in
include hV in
private theorem rationalPlace_inertia_le_restrictionRange
    (Q : Ideal (normalizationCommAlgCat V.toValuationSubring Ω)) [Q.IsMaximal] :
    Q.inertia Gal(Ω/RatFunc k) ≤
      (AlgEquiv.restrictScalarsHom (RatFunc k) :
        Gal(Ω/RatFunc κ) →* Gal(Ω/RatFunc k)).range := by
  let : IsScalarTower k V.toValuationSubring Ω := ratFuncPlace_baseConstantTower V
  obtain ⟨r, hr⟩ := rationalPlace_residueRetraction V hV
  rw [← ratFunc_constantsRestriction_ker_eq (k := k) (κ := κ) (Ω := Ω)]
  intro γ hγ
  exact rationalCusp_inertia_restrict_constants_eq_one k V.toValuationSubring
    (RatFunc k) κ Ω Q r hr γ hγ

omit [Algebra k Ω] [Algebra κ Ω]
  [IsScalarTower k κ Ω] [IsScalarTower k (RatFunc k) Ω]
  [IsScalarTower κ (RatFunc κ) Ω] in
private theorem ratFuncRationalPlaceNormalizationEquiv_inertia_comap
    (Q : Ideal (normalizationCommAlgCat V.toValuationSubring Ω)) :
    (Q.inertia Gal(Ω/RatFunc k)).comap (AlgEquiv.restrictScalarsHom (RatFunc k)) =
      (Q.comap (ratFuncRationalPlaceNormalizationEquiv
        V hV W hord (Ω := Ω)).toRingHom).inertia Gal(Ω/RatFunc κ) := by
  let : Algebra V.toValuationSubring W.toValuationSubring :=
    (ratFuncPlaceExtensionRingHom V W hord).toAlgebra
  let : Algebra.IsIntegral V.toValuationSubring W.toValuationSubring :=
    ratFunc_rationalPlace_extension_isIntegral V hV W hord
  let : IsScalarTower V.toValuationSubring W.toValuationSubring Ω :=
    ratFuncPlace_extension_ambientTower V W hord
  let e : integralClosure W.toValuationSubring Ω ≃+*
      integralClosure V.toValuationSubring Ω :=
    ratFuncRationalPlaceNormalizationEquiv V hV W hord (Ω := Ω)
  have he : e = normalizationIntegralBaseRingEquiv
      V.toValuationSubring W.toValuationSubring Ω := by
    dsimp only [e, ratFuncRationalPlaceNormalizationEquiv]
  have h : (Q.inertia Gal(Ω/RatFunc k)).comap
      (AlgEquiv.restrictScalarsHom (RatFunc k)) =
      (Q.comap e.toRingHom).inertia Gal(Ω/RatFunc κ) :=
    integralBaseInertiaComap_viaEquiv
      (F := RatFunc k) (L := RatFunc κ) e he Q
  exact h

/-- The same contracted normalization prime is maximal and its geometric
inertia maps onto arithmetic inertia under the actual scalar restriction. -/
theorem ratFunc_rationalPlace_normalization_inertia_image
    (Q : Ideal (normalizationCommAlgCat V.toValuationSubring Ω)) [hQ : Q.IsMaximal] :
    let e := ratFuncRationalPlaceNormalizationEquiv V hV W hord (Ω := Ω)
    let Qgeom := Q.comap e.toRingHom
    Qgeom.IsMaximal ∧
      (Qgeom.inertia Gal(Ω/RatFunc κ)).map
        (AlgEquiv.restrictScalarsHom (RatFunc k)) =
      Q.inertia Gal(Ω/RatFunc k) := by
  intro e Qgeom
  have hmax : Qgeom.IsMaximal := maximal_comap_ringEquiv e
    (show Ideal (integralClosure V.toValuationSubring Ω) from Q) hQ
  refine ⟨hmax, ?_⟩
  exact subgroup_image_of_comap
    (AlgEquiv.restrictScalarsHom (RatFunc k))
    (Q.inertia Gal(Ω/RatFunc k)) (Qgeom.inertia Gal(Ω/RatFunc κ))
    (ratFuncRationalPlaceNormalizationEquiv_inertia_comap V hV W hord Q)
    (rationalPlace_inertia_le_restrictionRange V hV Q)

/-- Passing through the actual field-source maps and the specified scheme
point square preserves the same rational-cusp inertia image. -/
theorem ratFunc_rationalPlace_pointed_inertia_image
    [IsSepClosure (RatFunc k) Ω] [IsSepClosure (RatFunc κ) Ω] [IsSepClosed Ω]
    (Q : Ideal (normalizationCommAlgCat V.toValuationSubring Ω)) [Q.IsMaximal]
    {X Y : Scheme.{u}} [IsIntegral X] [IsIntegral Y]
    (f : Y ⟶ X)
    (jgeom : Spec (.of (RatFunc κ)) ⟶ Y)
    (jarith : Spec (.of (RatFunc k)) ⟶ X)
    (hpoint :
      (Spec.map (CommRingCat.ofHom (algebraMap (RatFunc κ) Ω)) ≫ jgeom) ≫ f =
        Spec.map (CommRingCat.ofHom (algebraMap (RatFunc k) Ω)) ≫ jarith) :
    let e := ratFuncRationalPlaceNormalizationEquiv V hV W hord (Ω := Ω)
    let Qgeom := Q.comap e.toRingHom
    let qgeom := fieldSourceAbsoluteGaloisHom (RatFunc κ) Ω jgeom
    let qarith := fieldSourceAbsoluteGaloisHom (RatFunc k) Ω jarith
    let i := (pointedFundamentalGroupHom f
      (Spec.map (CommRingCat.ofHom (algebraMap (RatFunc κ) Ω)) ≫ jgeom)
      (Spec.map (CommRingCat.ofHom (algebraMap (RatFunc k) Ω)) ≫ jarith)
      hpoint).toMonoidHom
    ((Qgeom.inertia Gal(Ω/RatFunc κ)).map qgeom.toMonoidHom).map i =
      (Q.inertia Gal(Ω/RatFunc k)).map qarith.toMonoidHom := by
  intro e Qgeom qgeom qarith i
  have hI : (Qgeom.inertia Gal(Ω/RatFunc κ)).map
      (AlgEquiv.restrictScalarsHom (RatFunc k)) = Q.inertia Gal(Ω/RatFunc k) :=
    (ratFunc_rationalPlace_normalization_inertia_image V hV W hord Q).2
  have hcomp : i.comp qgeom.toMonoidHom =
      qarith.toMonoidHom.comp (AlgEquiv.restrictScalarsHom (RatFunc k)) := by
    apply MonoidHom.ext
    intro σ
    change pointedFundamentalGroupHom f
        (Spec.map (CommRingCat.ofHom (algebraMap (RatFunc κ) Ω)) ≫ jgeom)
        (Spec.map (CommRingCat.ofHom (algebraMap (RatFunc k) Ω)) ≫ jarith) hpoint
        (fieldSourceAbsoluteGaloisHom (RatFunc κ) Ω jgeom σ) =
      fieldSourceAbsoluteGaloisHom (RatFunc k) Ω jarith (σ.restrictScalars (RatFunc k))
    rw [pointedHom_equality_conjugation]
    exact fieldSourceAbsoluteGaloisHom_naturality
      (RatFunc k) (RatFunc κ) Ω f jgeom jarith hpoint σ
  rw [Subgroup.map_map, hcomp, ← Subgroup.map_map, hI]

end Normalization

end EtaleFundamentalGroups.Inertia
