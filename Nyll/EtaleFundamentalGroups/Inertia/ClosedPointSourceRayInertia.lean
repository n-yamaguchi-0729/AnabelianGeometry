/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.EtaleFundamentalGroups.Inertia.ClosedPointRayInertia
public import Nyll.EtaleFundamentalGroups.Inertia.SuppliedSourceAbelianKernel
public import Nyll.EtaleFundamentalGroups.Inertia.NormalizationActionComparison
public import Nyll.SchemeTheory.FunctionFields.GenericFieldSourceStalk
public import Nyll.AlgebraicCurves.Places.Restriction.EquivComapEqOrdEqDegEq
public import Mathlib.RingTheory.Ideal.Maximal
public import Nyll.ClassFieldTheory.AlgebraicFunctionFieldTheory.RayClass.LocalRayInertia
public import Nyll.ClassFieldTheory.AlgebraicFunctionFieldTheory.RayClass.RayArtinRamification
public import Nyll.ProCGroups.Abelian.TopologicalAbelianization

/-!
# Closed-point inertia in the actual supplied generic field

The supplied generic-point morphism identifies its field with the original
function field. Its actual equality over the base proves compatibility
with constants. Transporting the already constructed places along this
specified field isomorphism gives their valuation rings as the images of
the original stalk maps into the supplied field.

Normalization prime contraction then identifies their original abelian
inertia images with the local Artin ordinary-unit images in that same
supplied field. This keeps the interior and boundary groups inside the
same original absolute Galois group when an open curve is compactified.
-/

@[expose] public section

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.FiniteEtale
open AlgebraicCurve SchemeTheory LocalClassFieldTheory

namespace EtaleFundamentalGroups.Inertia

attribute [local instance] normalizationCommAlgGaloisAction

variable {k F : Type u} [Field k] [Field F] [Algebra k F]
  {X : Scheme.{u}} [IsIntegral X]
  (c : X ⟶ Spec (.of k)) [SmoothOfRelativeDimension 1 c]
  (p : Spec (.of F) ⟶ X) [IsDominant p] [IsPreimmersion p]
  (hp : p ≫ c = Spec.map (CommRingCat.ofHom (algebraMap k F)))

include hp in
omit [SmoothOfRelativeDimension 1 c] in
/-- The original supplied generic-field isomorphism respects the actual
base coefficients because its original scheme morphism lies over the base. -/
theorem genericFieldSourceRingEquiv_baseToFunctionField (a : k) :
    genericFieldSourceRingEquiv p (baseToFunctionField c a) = algebraMap k F a := by
  have hcoeff :
      CommRingCat.ofHom ((genericFieldSourceRingEquiv p).toRingHom.comp
        (baseToFunctionField c)) = CommRingCat.ofHom (algebraMap k F) := by
    apply Spec.map_injective
    change Spec.map (CommRingCat.ofHom (baseToFunctionField c) ≫
      CommRingCat.ofHom (genericFieldSourceRingEquiv p).toRingHom) = _
    rw [Spec.map_comp, ← fromSpecStalk_genericPoint_comp_base c, ← Category.assoc]
    have hsource : Spec.map (CommRingCat.ofHom (genericFieldSourceRingEquiv p).toRingHom) ≫
        X.fromSpecStalk (genericPoint X) = p := genericFieldSourceIso_hom_fromSpecStalk p
    exact (congrArg (fun q : Spec (.of F) ⟶ X => q ≫ c) hsource).trans hp
  exact congrArg (fun f : CommRingCat.of k ⟶ CommRingCat.of F => f.hom a) hcoeff

/-- Places transported along the actual supplied generic-field
isomorphism, with the scalar compatibility proved from the original map. -/
def genericFieldSourcePlaceEquiv :
    let _ : Algebra k X.functionField := (baseToFunctionField c).toAlgebra
    Place k X.functionField ≃ Place k F := by
  intro sourceBaseAlgebra
  exact (Place.exists_equiv_comap_eq_and_ord_eq_and_deg_eq_of_ringEquiv
    (RingEquiv.refl k) (genericFieldSourceRingEquiv p)
      (genericFieldSourceRingEquiv_baseToFunctionField c p hp)).choose

omit [SmoothOfRelativeDimension 1 c] in
/-- The supplied place transport has the literal inverse-comap valuation ring. -/
theorem genericFieldSourcePlaceEquiv_toValuationSubring :
    let _ : Algebra k X.functionField := (baseToFunctionField c).toAlgebra
    ∀ v : Place k X.functionField,
    (genericFieldSourcePlaceEquiv c p hp v).toValuationSubring =
      v.toValuationSubring.comap (genericFieldSourceRingEquiv p).symm.toRingHom := by
  intro sourceBaseAlgebra v
  exact (Place.exists_equiv_comap_eq_and_ord_eq_and_deg_eq_of_ringEquiv
    (RingEquiv.refl k) (genericFieldSourceRingEquiv p)
      (genericFieldSourceRingEquiv_baseToFunctionField c p hp)).choose_spec.1 v

/-- The original closed point, regarded as a place of the supplied field. -/
def closedPointSourcePlace (x : closedPoints X) :
    let _ : Algebra k X.functionField := (baseToFunctionField c).toAlgebra
    Place k F := by
  intro sourceBaseAlgebra
  exact genericFieldSourcePlaceEquiv c p hp (closedPointPlace c x)

/-- The transported valuation ring is exactly the image of the original
stalk under its specified generic-source coefficient map. -/
theorem closedPointSourcePlace_range (x : closedPoints X) :
    let _ : Algebra k X.functionField := (baseToFunctionField c).toAlgebra
    let : Algebra (X.presheaf.stalk x.val) F := genericFieldSourceStalkAlgebra p x.val
    (algebraMap (X.presheaf.stalk x.val) F).range =
      (closedPointSourcePlace c p hp x).toValuationSubring.toSubring := by
  intro sourceBaseAlgebra instAF
  let e := genericFieldSourceRingEquiv p
  change (algebraMap (X.presheaf.stalk x.val) F).range =
    (genericFieldSourcePlaceEquiv c p hp (closedPointPlace c x)).toValuationSubring.toSubring
  rw [genericFieldSourcePlaceEquiv_toValuationSubring]
  apply Subring.ext
  intro z
  change (∃ a : X.presheaf.stalk x.val,
    e (algebraMap (X.presheaf.stalk x.val) X.functionField a) = z) ↔
      e.symm z ∈ (closedPointPlace c x).toValuationSubring.toSubring
  rw [← closedPointPlace_range c x]
  constructor
  · rintro ⟨a, ha⟩
    refine ⟨a, ?_⟩
    have h := congrArg e.symm ha
    rw [e.symm_apply_apply] at h
    exact h
  · rintro ⟨a, ha⟩
    refine ⟨a, ?_⟩
    have h := congrArg e ha
    rw [e.apply_symm_apply] at h
    exact h

/-- The actual supplied stalk inclusion is an isomorphism onto the
valuation ring just constructed. -/
def closedPointSourceStalkValuationEquiv (x : closedPoints X) :
    let _ : Algebra k X.functionField := (baseToFunctionField c).toAlgebra
    X.presheaf.stalk x.val ≃+* (closedPointSourcePlace c p hp x).toValuationSubring := by
  intro sourceBaseAlgebra
  let A := X.presheaf.stalk x.val
  let : Algebra A F := genericFieldSourceStalkAlgebra p x.val
  have : IsFractionRing A F := genericFieldSourceStalk_isFractionRing p x.val
  let R := (closedPointSourcePlace c p hp x).toValuationSubring
  let f : A →+* R := (algebraMap A F).codRestrict R.toSubring (fun a => by
    rw [← closedPointSourcePlace_range c p hp x]
    exact ⟨a, rfl⟩)
  refine RingEquiv.ofBijective f ⟨?_, ?_⟩
  · intro a b hab
    exact (IsFractionRing.injective A F) (congrArg Subtype.val hab)
  · intro b
    have hb : (b : F) ∈ (algebraMap A F).range := by
      rw [closedPointSourcePlace_range c p hp x]
      exact b.property
    obtain ⟨a, ha⟩ := hb
    exact ⟨a, Subtype.ext ha⟩

/-- The ring equivalence retains each original coefficient in the
supplied generic field. -/
theorem closedPointSourceStalkValuationEquiv_toField
    (x : closedPoints X) (a : X.presheaf.stalk x.val) :
    let _ : Algebra k X.functionField := (baseToFunctionField c).toAlgebra
    let : Algebra (X.presheaf.stalk x.val) F := genericFieldSourceStalkAlgebra p x.val
    algebraMap (closedPointSourcePlace c p hp x).toValuationSubring F
        (closedPointSourceStalkValuationEquiv c p hp x a) =
      algebraMap (X.presheaf.stalk x.val) F a := by
  intro sourceBaseAlgebra
  rfl

/-- The actual supplied-field place map is injective for a separated curve. -/
theorem closedPointSourcePlace_injective [IsSeparated c] :
    let _ : Algebra k X.functionField := (baseToFunctionField c).toAlgebra
    Function.Injective (closedPointSourcePlace c p hp) := by
  intro sourceBaseAlgebra
  exact (genericFieldSourcePlaceEquiv c p hp).injective.comp (closedPointPlace_injective c)

/-- On the actual proper curve every supplied-field place has its
unique original closed-point center. -/
def closedPointSourcePlaceEquiv [IsProper c] :
    let _ : Algebra k X.functionField := (baseToFunctionField c).toAlgebra
    closedPoints X ≃ Place k F := by
  intro sourceBaseAlgebra
  exact (closedPointPlaceEquiv c).trans (genericFieldSourcePlaceEquiv c p hp)

section AbelianInertia

variable [Finite k] [Algebra (RatFunc k) F] [IsScalarTower k (RatFunc k) F]
  [FunctionField k F] [HasPrincipalDivisors k F]

/-- The original inertia at each actual supplied-source normalization
prime has the ordinary-unit Artin image at the corresponding actual place. -/
theorem closedPointSourceNormalizationInertia_image (x : closedPoints X) :
    let _ : Algebra k X.functionField := (baseToFunctionField c).toAlgebra
    let A := X.presheaf.stalk x.val
    let Ω := SeparableClosure F
    let : Algebra A F := genericFieldSourceStalkAlgebra p x.val
    let : IsFractionRing A F := genericFieldSourceStalk_isFractionRing p x.val
    let : Algebra A Ω := ((algebraMap F Ω).comp (algebraMap A F)).toAlgebra
    let : IsScalarTower A F Ω := IsScalarTower.of_algebraMap_eq' rfl
    ∀ Q : MaximalSpectrum (normalizationCommAlgCat A Ω),
      (Q.asIdeal.inertia Gal(Ω/F)).map
        (ProCGroups.Abelian.TopologicalAbelianization.mk Gal(Ω/F)) =
      FunctionField.RayClass.placeArtinUnitImage (closedPointSourcePlace c p hp x) 0 := by
  intro sourceBaseAlgebra A Ω instAF instFrac instAΩ instAFΩ Q
  let v := closedPointSourcePlace c p hp x
  let R := v.toValuationSubring
  let e := closedPointSourceStalkValuationEquiv c p hp x
  let : Algebra A R := e.toRingHom.toAlgebra
  let : Algebra R Ω := Algebra.ofSubsemiring v.toValuationSubring
  have : IsScalarTower R F Ω := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  have : IsScalarTower A R Ω := by
    apply IsScalarTower.of_algebraMap_eq
    intro a
    change algebraMap F Ω (algebraMap A F a) =
      algebraMap F Ω (algebraMap R F (e a))
    exact congrArg (algebraMap F Ω)
      (closedPointSourceStalkValuationEquiv_toField c p hp x a).symm
  have : Algebra.IsIntegral A R := by
    constructor
    intro b
    obtain ⟨a, rfl⟩ := e.surjective b
    exact isIntegral_algebraMap
  let eN := normalizationIntegralBaseRingEquiv A R Ω
  let Qv : Ideal (normalizationCommAlgCat R Ω) := Q.asIdeal.comap eN.toRingHom
  have : Q.asIdeal.IsMaximal := Q.isMaximal
  have : Qv.IsMaximal :=
    Ideal.comap_isMaximal_of_surjective eN.toRingHom eN.surjective
      (K := Q.asIdeal) (H := Q.isMaximal)
  have : Algebra.IsIntegral R (normalizationCommAlgCat R Ω) :=
    inferInstanceAs (Algebra.IsIntegral R (integralClosure R Ω))
  have : Qv.LiesOver (IsLocalRing.maximalIdeal R) :=
    ⟨(IsLocalRing.eq_maximalIdeal (Ideal.IsMaximal.under R Qv)).symm⟩
  have hI : Q.asIdeal.inertia Gal(Ω/F) = Qv.inertia Gal(Ω/F) := by
    have hbase := normalizationCommAlg_integralBase_inertia_comap
      (A := A) (B := R) (F := F) (L := F) (Ω := Ω) Q.asIdeal
    apply Subgroup.ext
    intro σ
    have hσ : σ.restrictScalars F = σ := by
      apply AlgEquiv.ext
      intro z
      rfl
    have h := congrArg (fun H : Subgroup Gal(Ω/F) => σ ∈ H) hbase
    change (σ.restrictScalars F ∈ Q.asIdeal.inertia Gal(Ω/F)) =
      (σ ∈ Qv.inertia Gal(Ω/F)) at h
    rw [hσ] at h
    exact h.to_iff
  rw [hI]
  change FunctionField.placeAbsoluteInertia v Qv =
    FunctionField.RayClass.placeArtinUnitImage v 0
  have hprime : Qv.IsPrime := (inferInstance : Qv.IsMaximal).isPrime
  have hover : Qv.LiesOver (IsLocalRing.maximalIdeal v.toValuationSubring) := inferInstance
  exact @FunctionField.RayClass.placeAbsoluteInertia_eq_placeArtinUnitImage
    k F _ _ _ _ _ _ _ _ v Qv hprime hover

/-- The full supplied-source stalk inertia has exactly the original local
ordinary-unit Artin image. Every actual maximal normalization prime has
that image, and such a prime exists. -/
theorem sourceAbsoluteStalkInertiaImage_closedPoint (x : closedPoints X) :
    let _ : Algebra k X.functionField := (baseToFunctionField c).toAlgebra
    (sourceAbsoluteStalkInertiaImage p (SeparableClosure F) x.val).map
        (ProCGroups.Abelian.TopologicalAbelianization.mk Gal(SeparableClosure F/F)) =
      FunctionField.RayClass.placeArtinUnitImage (closedPointSourcePlace c p hp x) 0 := by
  intro sourceBaseAlgebra
  let A := X.presheaf.stalk x.val
  let Ω := SeparableClosure F
  let : Algebra A F := genericFieldSourceStalkAlgebra p x.val
  have : IsFractionRing A F := genericFieldSourceStalk_isFractionRing p x.val
  let : Algebra A Ω := ((algebraMap F Ω).comp (algebraMap A F)).toAlgebra
  have : IsScalarTower A F Ω := IsScalarTower.of_algebraMap_eq' rfl
  let : MulSemiringAction Gal(Ω/F) (integralClosure A Ω) :=
    IsIntegralClosure.MulSemiringAction A F Ω (integralClosure A Ω)
  let a := ProCGroups.Abelian.TopologicalAbelianization.mk Gal(Ω/F)
  let U := FunctionField.RayClass.placeArtinUnitImage (closedPointSourcePlace c p hp x) 0
  change (⨆ Q : MaximalSpectrum (integralClosure A Ω),
    Q.asIdeal.inertia Gal(Ω/F)).map a = U
  have hQ (Q : MaximalSpectrum (integralClosure A Ω)) :
      (Q.asIdeal.inertia Gal(Ω/F)).map a = U := by
    have h := closedPointSourceNormalizationInertia_image c p hp x
      (show MaximalSpectrum (normalizationCommAlgCat A Ω) from Q)
    rw [normalizationCommAlg_inertia_eq_fractionFieldInertia (F := F)] at h
    exact h
  apply le_antisymm
  · have hle : (⨆ Q : MaximalSpectrum (integralClosure A Ω),
        Q.asIdeal.inertia Gal(Ω/F)) ≤ U.comap a := by
      apply iSup_le
      intro Q σ hσ
      have hmem : a σ ∈ (Q.asIdeal.inertia Gal(Ω/F)).map a := ⟨σ, hσ, rfl⟩
      rw [hQ Q] at hmem
      exact hmem
    rintro σ ⟨τ, hτ, rfl⟩
    exact hle hτ
  · obtain ⟨Q, hmax⟩ := Ideal.exists_maximal (integralClosure A Ω)
    rw [← hQ ⟨Q, hmax⟩]
    rintro σ ⟨τ, hτ, rfl⟩
    refine ⟨τ, ?_, rfl⟩
    exact (le_iSup (fun P : MaximalSpectrum (integralClosure A Ω) =>
      P.asIdeal.inertia Gal(Ω/F)) ⟨Q, hmax⟩) hτ

variable [IsNormalIntegral X]

/-- The original generic-source Galois map has abelian kernel generated
by the actual ordinary-unit Artin images at the closed points of the
original smooth curve, inside the supplied function field itself. -/
theorem fieldSourceAbsoluteGaloisHom_ker_localUnits :
    let _ : Algebra k X.functionField := (baseToFunctionField c).toAlgebra
    ((fieldSourceAbsoluteGaloisHom F (SeparableClosure F) p).toMonoidHom.ker).map
        (ProCGroups.Abelian.TopologicalAbelianization.mk Gal(SeparableClosure F/F)) =
      (⨆ x : closedPoints X,
        FunctionField.RayClass.placeArtinUnitImage
          (closedPointSourcePlace c p hp x) 0).topologicalClosure := by
  intro sourceBaseAlgebra
  rw [fieldSourceAbsoluteGaloisHom_ker_closedPoint_image p (SeparableClosure F) c]
  congr 1
  apply iSup_congr
  intro x
  exact sourceAbsoluteStalkInertiaImage_closedPoint c p hp x

end AbelianInertia

end EtaleFundamentalGroups.Inertia
