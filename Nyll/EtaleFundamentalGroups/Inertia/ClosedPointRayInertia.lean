/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.ClassFieldTheory.AlgebraicFunctionFieldTheory.RayClass.LocalRayInertia
public import Nyll.EtaleFundamentalGroups.Inertia.GenericSourceAbelianKernel
public import Nyll.EtaleFundamentalGroups.Inertia.NormalizationActionComparison
public import Nyll.AlgebraicCurves.Models.LocalGeometry.EqRangeStalkEq
public import Nyll.AlgebraicCurves.Models.LocalGeometry.ClosedPointRangeStalkEq
public import Nyll.AlgebraicCurves.Places.ValuationRings.RangeStalkEq
public import Mathlib.RingTheory.Ideal.GoingUp
public import Mathlib.RingTheory.Ideal.Maps
public import Mathlib.RingTheory.LocalRing.MaximalIdeal.Basic
public import Nyll.ClassFieldTheory.AlgebraicFunctionFieldTheory.RayClass.RayArtinRamification
public import Nyll.ProCGroups.Abelian.TopologicalAbelianization

/-!
# The original closed-point inertia is the original local Artin unit image

The place of a closed point is constructed from the actual image of its
scheme stalk in the function field. The stalk and that valuation ring are
isomorphic through their original inclusions. Integral base change then
compares their actual normalization primes and their prescribed Galois
actions. The resulting abelian inertia image is the ordinary-unit image
of the original local Artin map.

Consequently the original generic fundamental-group kernel on a smooth
curve is generated, after abelianization, by precisely those local unit
images whose places have a center on that curve.
-/

@[expose] public section

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry AlgebraicCurve
open AlgebraicGeometry.FiniteEtale SchemeTheory LocalClassFieldTheory

namespace EtaleFundamentalGroups.Inertia

attribute [local instance] normalizationCommAlgGaloisAction

variable {k : Type u} [Field k] {X : Scheme.{u}} [IsIntegral X]
  (c : X ⟶ Spec (.of k)) [SmoothOfRelativeDimension 1 c]

/-- The actual place whose valuation ring is the image of the original
closed-point stalk in the original function field. -/
def closedPointPlace (x : closedPoints X) :
    let _ : Algebra k X.functionField := (baseToFunctionField c).toAlgebra
    Place k X.functionField := by
  intro baseAlgebra
  exact (exists_place_range_stalk_eq c x.val (mem_closedPoints_iff.mp x.property)).choose

/-- The defining range equality for the place constructed from the stalk. -/
theorem closedPointPlace_range (x : closedPoints X) :
    let _ : Algebra k X.functionField := (baseToFunctionField c).toAlgebra
    (algebraMap (X.presheaf.stalk x.val) X.functionField).range =
      (closedPointPlace c x).toValuationSubring.toSubring := by
  intro baseAlgebra
  exact (exists_place_range_stalk_eq c x.val (mem_closedPoints_iff.mp x.property)).choose_spec

/-- On a separated smooth curve the original valuation ring determines
its actual closed-point center uniquely. -/
theorem closedPointPlace_injective [IsSeparated c] :
    let _ : Algebra k X.functionField := (baseToFunctionField c).toAlgebra
    Function.Injective (closedPointPlace c) := by
  intro baseAlgebra x y hxy
  apply Subtype.ext
  apply eq_of_range_stalk_eq c x.val y.val
  rw [closedPointPlace_range c x, closedPointPlace_range c y, hxy]

/-- Properness supplies a center for every place of the original
function field, through the original valuative-criterion theorem. -/
theorem closedPointPlace_surjective [IsProper c] :
    let _ : Algebra k X.functionField := (baseToFunctionField c).toAlgebra
    Function.Surjective (closedPointPlace c) := by
  intro baseAlgebra v
  obtain ⟨x, hx, hrange⟩ := exists_closedPoint_range_stalk_eq c v
  refine ⟨⟨x, mem_closedPoints_iff.mpr hx⟩, ?_⟩
  apply Place.ext
  apply ValuationSubring.toSubring_injective
  exact (closedPointPlace_range c ⟨x, mem_closedPoints_iff.mpr hx⟩).symm.trans hrange

/-- The actual closed points of a smooth proper curve, identified with
the places of that same curve's original function field. -/
def closedPointPlaceEquiv [IsProper c] :
    let _ : Algebra k X.functionField := (baseToFunctionField c).toAlgebra
    closedPoints X ≃ Place k X.functionField := by
  intro baseAlgebra
  exact Equiv.ofBijective (closedPointPlace c)
    ⟨closedPointPlace_injective c, closedPointPlace_surjective c⟩

/-- The actual stalk inclusion, with codomain restricted to its place
valuation ring, is a ring isomorphism. -/
def closedPointStalkValuationEquiv (x : closedPoints X) :
    let _ : Algebra k X.functionField := (baseToFunctionField c).toAlgebra
    X.presheaf.stalk x.val ≃+* (closedPointPlace c x).toValuationSubring := by
  intro baseAlgebra
  let A := X.presheaf.stalk x.val
  let R := (closedPointPlace c x).toValuationSubring
  let f : A →+* R := (algebraMap A X.functionField).codRestrict R.toSubring
    (fun a => by
      rw [← closedPointPlace_range c x]
      exact ⟨a, rfl⟩)
  refine RingEquiv.ofBijective f ⟨?_, ?_⟩
  · intro a b hab
    exact (IsFractionRing.injective A X.functionField) (congrArg Subtype.val hab)
  · intro b
    have hb : (b : X.functionField) ∈ (algebraMap A X.functionField).range := by
      rw [closedPointPlace_range c x]
      exact b.property
    obtain ⟨a, ha⟩ := hb
    exact ⟨a, Subtype.ext ha⟩

/-- The constructed ring equivalence retains the original coefficient
inclusion into the function field. -/
theorem closedPointStalkValuationEquiv_toFunctionField
    (x : closedPoints X) (a : X.presheaf.stalk x.val) :
    let _ : Algebra k X.functionField := (baseToFunctionField c).toAlgebra
    algebraMap (closedPointPlace c x).toValuationSubring X.functionField
        (closedPointStalkValuationEquiv c x a) =
      algebraMap (X.presheaf.stalk x.val) X.functionField a := by
  intro baseAlgebra
  rfl

section AbelianInertia

variable [Finite k]

/-- Every original maximal-prime inertia of a closed-point stalk has the
same abelian image as the ordinary units of its actual completed place.
The prime at the place is constructed by the literal normalization
equivalence, and both actions are compared before applying reciprocity. -/
theorem closedPointNormalizationInertia_image (x : closedPoints X) :
    let _ : Algebra k X.functionField := (baseToFunctionField c).toAlgebra
    ∀ [Algebra (RatFunc k) X.functionField]
      [IsScalarTower k (RatFunc k) X.functionField]
      [FunctionField k X.functionField] [HasPrincipalDivisors k X.functionField],
    let A := X.presheaf.stalk x.val
    let Ω := SeparableClosure X.functionField
    let : Algebra A Ω := X.stalkExtensionAlgebra x.val Ω
    let : IsScalarTower A X.functionField Ω :=
      IsScalarTower.of_algebraMap_eq' rfl
    let : MulSemiringAction Gal(Ω/X.functionField) (integralClosure A Ω) :=
      IsIntegralClosure.MulSemiringAction A X.functionField Ω (integralClosure A Ω)
    ∀ Q : MaximalSpectrum (integralClosure A Ω),
      (Q.asIdeal.inertia Gal(Ω/X.functionField)).map
        (ProCGroups.Abelian.TopologicalAbelianization.mk Gal(Ω/X.functionField)) =
      FunctionField.RayClass.placeArtinUnitImage (closedPointPlace c x) 0 := by
  intro baseAlgebra rationalAlgebra rationalTower functionField principalDivisors
    A Ω instAΩ instAFΩ instAction Q
  let F := X.functionField
  let v := closedPointPlace c x
  let R := v.toValuationSubring
  let e := closedPointStalkValuationEquiv c x
  let : Algebra A R := e.toRingHom.toAlgebra
  let : Algebra R Ω := Algebra.ofSubsemiring v.toValuationSubring
  have : IsScalarTower R F Ω := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  have : IsScalarTower A R Ω := by
    apply IsScalarTower.of_algebraMap_eq
    intro a
    change algebraMap F Ω (algebraMap A F a) =
      algebraMap F Ω (algebraMap R F (e a))
    exact congrArg (algebraMap F Ω)
      (closedPointStalkValuationEquiv_toFunctionField c x a).symm
  have : Algebra.IsIntegral A R := by
    constructor
    intro b
    obtain ⟨a, rfl⟩ := e.surjective b
    exact isIntegral_algebraMap
  let eN := normalizationIntegralBaseRingEquiv A R Ω
  let Qv : Ideal (normalizationCommAlgCat R Ω) := Q.asIdeal.comap eN.toRingHom
  have : Q.asIdeal.IsMaximal := Q.isMaximal
  have hQvmax : Qv.IsMaximal :=
    Ideal.comap_isMaximal_of_surjective eN.toRingHom eN.surjective
  have : Algebra.IsIntegral R (normalizationCommAlgCat R Ω) :=
    inferInstanceAs (Algebra.IsIntegral R (integralClosure R Ω))
  have : (show Ideal (integralClosure R Ω) from Qv).IsPrime := hQvmax.isPrime
  have : Qv.LiesOver (IsLocalRing.maximalIdeal R) :=
    ⟨(IsLocalRing.eq_maximalIdeal (Ideal.IsMaximal.under R Qv)).symm⟩
  have hI : Q.asIdeal.inertia Gal(Ω/F) = Qv.inertia Gal(Ω/F) := by
    have hraw := normalizationIntegralBase_inertia_comap
      (A := A) (B := R) (Ω := Ω) F F Q.asIdeal
    have hnative := normalizationCommAlg_inertia_eq_fractionFieldInertia
      (A := R) (F := F) (Ω := Ω) Qv
    rw [hnative]
    apply Subgroup.ext
    intro σ
    have hσ : σ.restrictScalars F = σ := by
      apply AlgEquiv.ext
      intro z
      rfl
    have h := congrArg (fun H : Subgroup Gal(Ω/F) => σ ∈ H) hraw
    change (σ.restrictScalars F ∈ Q.asIdeal.inertia Gal(Ω/F)) =
      (σ ∈ (let : MulSemiringAction Gal(Ω/F) (integralClosure R Ω) :=
        IsIntegralClosure.MulSemiringAction R F Ω (integralClosure R Ω)
       Qv.inertia Gal(Ω/F))) at h
    rw [hσ] at h
    exact h.to_iff
  have : (show Ideal (integralClosure R Ω) from Qv).LiesOver
      (IsLocalRing.maximalIdeal R) := inferInstanceAs (Qv.LiesOver (IsLocalRing.maximalIdeal R))
  rw [hI]
  change FunctionField.placeAbsoluteInertia v Qv =
    FunctionField.RayClass.placeArtinUnitImage v 0
  exact FunctionField.RayClass.placeAbsoluteInertia_eq_placeArtinUnitImage v Qv

/-- Abelianizing the original stalk-inertia subgroup gives exactly the
actual ordinary-unit Artin image at its constructed place. -/
theorem absoluteStalkInertiaImage_closedPoint (x : closedPoints X) :
    let _ : Algebra k X.functionField := (baseToFunctionField c).toAlgebra
    ∀ [Algebra (RatFunc k) X.functionField]
      [IsScalarTower k (RatFunc k) X.functionField]
      [FunctionField k X.functionField] [HasPrincipalDivisors k X.functionField],
    (absoluteStalkInertiaImage X x.val).map
        (ProCGroups.Abelian.TopologicalAbelianization.mk
          Gal(SeparableClosure X.functionField/X.functionField)) =
      FunctionField.RayClass.placeArtinUnitImage (closedPointPlace c x) 0 := by
  intro baseAlgebra rationalAlgebra rationalTower functionField principalDivisors
  let A := X.presheaf.stalk x.val
  let Ω := SeparableClosure X.functionField
  let : Algebra A Ω := X.stalkExtensionAlgebra x.val Ω
  have : IsScalarTower A X.functionField Ω := IsScalarTower.of_algebraMap_eq' rfl
  let : MulSemiringAction Gal(Ω/X.functionField) (integralClosure A Ω) :=
    IsIntegralClosure.MulSemiringAction A X.functionField Ω (integralClosure A Ω)
  let a := ProCGroups.Abelian.TopologicalAbelianization.mk Gal(Ω/X.functionField)
  let U := FunctionField.RayClass.placeArtinUnitImage (closedPointPlace c x) 0
  change (⨆ Q : MaximalSpectrum (integralClosure A Ω),
    Q.asIdeal.inertia Gal(Ω/X.functionField)).map a = U
  have hQ (Q : MaximalSpectrum (integralClosure A Ω)) :
      (Q.asIdeal.inertia Gal(Ω/X.functionField)).map a = U :=
    closedPointNormalizationInertia_image c x Q
  apply le_antisymm
  · have hle :
        (⨆ Q : MaximalSpectrum (integralClosure A Ω),
          Q.asIdeal.inertia Gal(Ω/X.functionField)) ≤ U.comap a := by
      apply iSup_le
      intro Q σ hσ
      have hmem : a σ ∈ (Q.asIdeal.inertia Gal(Ω/X.functionField)).map a :=
        ⟨σ, hσ, rfl⟩
      rw [hQ Q] at hmem
      exact hmem
    rintro σ ⟨τ, hτ, rfl⟩
    exact hle hτ
  · obtain ⟨Q, hmax⟩ := Ideal.exists_maximal (integralClosure A Ω)
    rw [← hQ ⟨Q, hmax⟩]
    rintro σ ⟨τ, hτ, rfl⟩
    refine ⟨τ, ?_, rfl⟩
    exact (le_iSup (fun P : MaximalSpectrum (integralClosure A Ω) =>
      P.asIdeal.inertia Gal(Ω/X.functionField)) ⟨Q, hmax⟩) hτ

variable [IsNormalIntegral X]

/-- The actual supplied generic Galois map has abelian kernel generated
by the ordinary-unit Artin images at exactly the actual closed points of
the original smooth curve. -/
theorem canonicalFieldSourceAbsoluteGaloisHom_ker_localUnits :
    let _ : Algebra k X.functionField := (baseToFunctionField c).toAlgebra
    ∀ [Algebra (RatFunc k) X.functionField]
      [IsScalarTower k (RatFunc k) X.functionField]
      [FunctionField k X.functionField] [HasPrincipalDivisors k X.functionField],
    ((fieldSourceAbsoluteGaloisHom X.functionField (SeparableClosure X.functionField)
      (X.fromSpecStalk (genericPoint X))).toMonoidHom.ker).map
        (ProCGroups.Abelian.TopologicalAbelianization.mk
          Gal(SeparableClosure X.functionField/X.functionField)) =
      (⨆ x : closedPoints X,
        FunctionField.RayClass.placeArtinUnitImage
          (closedPointPlace c x) 0).topologicalClosure := by
  intro baseAlgebra rationalAlgebra rationalTower functionField principalDivisors
  rw [canonicalFieldSourceAbsoluteGaloisHom_ker_closedPoint_image X c]
  congr 1
  apply iSup_congr
  intro x
  exact absoluteStalkInertiaImage_closedPoint c x

end AbelianInertia

end EtaleFundamentalGroups.Inertia
