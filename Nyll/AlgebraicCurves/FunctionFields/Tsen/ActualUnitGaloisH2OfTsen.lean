/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.AlgebraicCurves.FunctionFields.Tsen.GaloisH2OfTsen
public import Nyll.EtaleCohomology.Classical.LiftedFieldSectionRepresentations
public import Mathlib.RepresentationTheory.Homological.GroupCohomology.LongExactSequence
public import Nyll.GaloisCohomology.GroupTheory.CoefficientRingEquivalence

/-!
# Tsen vanishing for the actual unit-section representation

The geometric unit-section comparison transports the existing Tsen
theorem. Actual injective-sheaf acyclicity and exact field sections then
give degree-one vanishing for the quotient of an injective sheaf by Gm.
This is the dimension-shifting input for actual derived etale H2.
-/

@[expose] public section

noncomputable section

universe u

open CategoryTheory Limits AlgebraicGeometry
open EtaleCohomology

namespace AlgebraicCurve

open ClassFieldTower.Cohomology

/-- Tsen's existing theorem applies to the actual geometric Gm-section
representation via the proved equivariant comparison. -/
theorem liftedActualUnitSections_H2_eq_zero_of_tsen
    (K : Type u) [Field K] [IsAlgClosed K]
    {F : Type u} [Field F] [Algebra K F]
    (x : F) (hx : Transcendental K x)
    (hfin : FiniteDimensional (IntermediateField.adjoin K ({x} : Set F)) F)
    (E : Type u) [Field E] [Algebra F E] [FiniteDimensional F E] [IsGalois F E]
    (a : groupCohomology
      (liftedFieldGaloisSheafSectionsRep F E (etaleMultiplicativeGroupSheaf (Spec (.of F)))) 2) :
    a = 0 := by
  let e : groupCohomology
      (liftedFieldGaloisSheafSectionsRep F E (etaleMultiplicativeGroupSheaf (Spec (.of F)))) 2 ≅
      groupCohomology (liftedGaloisUnitsRep F E) 2 :=
    (groupCohomology.functor (ULift.{u} ℤ) Gal(E/F) 2).mapIso
      (liftedFieldGaloisSheafSectionsUnitsIso F E)
  apply (ModuleCat.mono_iff_injective e.hom).mp inferInstance
  change e.hom.hom a = e.hom.hom 0
  rw [e.hom.hom.map_zero]
  exact liftedGaloisUnitsH2_eq_zero_of_transcendental_of_finiteDimensional
    K x hx hfin E (e.hom.hom a)

/-- The original integer-coefficient unit-section statement follows from
the same sections after the actual coefficient-complex comparison. -/
theorem actualUnitSections_H2_eq_zero_of_tsen
    (K : Type) [Field K] [IsAlgClosed K]
    {F : Type} [Field F] [Algebra K F]
    (x : F) (hx : Transcendental K x)
    (hfin : FiniteDimensional (IntermediateField.adjoin K ({x} : Set F)) F)
    (E : Type) [Field E] [Algebra F E] [FiniteDimensional F E] [IsGalois F E]
    (a : groupCohomology
      (fieldGaloisSheafSectionsRep F E (etaleMultiplicativeGroupSheaf (Spec (.of F)))) 2) :
    a = 0 := by
  let e := groupCohomology.coefficientRingIso
    (ULift.ringEquiv : ULift.{0} ℤ ≃+* ℤ)
    (fieldGaloisSheafSectionsRep F E (etaleMultiplicativeGroupSheaf (Spec (.of F)))) 2
  apply (ModuleCat.mono_iff_injective e.hom).mp inferInstance
  change e.hom.hom a = e.hom.hom 0
  rw [e.hom.hom.map_zero]
  exact liftedActualUnitSections_H2_eq_zero_of_tsen
    K x hx hfin E (e.hom.hom a)

/-- For the actual quotient of an injective sheaf by Gm on a
curve function field in any characteristic, the finite-Galois section
representation has zero H1. -/
theorem liftedActualUnitInjectiveQuotient_sections_H1_eq_zero_of_tsen
    (K : Type u) [Field K] [IsAlgClosed K]
    {F : Type u} [Field F] [Algebra K F]
    (x : F) (hx : Transcendental K x)
    (hfin : FiniteDimensional (IntermediateField.adjoin K ({x} : Set F)) F)
    (E : Type u) [Field E] [Algebra F E] [FiniteDimensional F E] [IsGalois F E]
    {I Q : Sheaf (Spec (.of F)).smallEtaleTopology AddCommGrpCat.{u}} [Injective I]
    (i : etaleMultiplicativeGroupSheaf (Spec (.of F)) ⟶ I) (p : I ⟶ Q)
    (hz : i ≫ p = 0) (hS : (ShortComplex.mk i p hz).ShortExact)
    (a : groupCohomology (liftedFieldGaloisSheafSectionsRep F E Q) 1) : a = 0 := by
  let S := (ShortComplex.mk i p hz).map (liftedFieldGaloisSheafSectionsFunctor F E)
  have hs : S.ShortExact :=
    liftedFieldGaloisSheafSections_unitsKernel_shortExact F E i p hz hS
  have hI : IsZero (groupCohomology S.X₂ 1) := by
    have : Subsingleton (groupCohomology S.X₂ 1) :=
      ⟨fun b c =>
        (liftedFieldGaloisSheafSections_H1_eq_zero_of_injective F E I b).trans
          (liftedFieldGaloisSheafSections_H1_eq_zero_of_injective F E I c).symm⟩
    exact ModuleCat.isZero_of_subsingleton _
  have hU : IsZero (groupCohomology S.X₁ 2) := by
    have : Subsingleton (groupCohomology S.X₁ 2) :=
      ⟨fun b c => (liftedActualUnitSections_H2_eq_zero_of_tsen K x hx hfin E b).trans
        (liftedActualUnitSections_H2_eq_zero_of_tsen K x hx hfin E c).symm⟩
    exact ModuleCat.isZero_of_subsingleton _
  have hQ : IsZero (groupCohomology S.X₃ 1) :=
    (groupCohomology.mapShortComplex₃_exact
      hs (show 1 + 1 = 2 from rfl)).isZero_of_both_isZero hI hU
  exact ConcreteCategory.congr_hom (hQ.eq_of_src (𝟙 _) 0) a

/-- The original integer-coefficient quotient-section statement follows
from the same short exact sequence after coefficient comparison. -/
theorem actualUnitInjectiveQuotient_sections_H1_eq_zero_of_tsen
    (K : Type) [Field K] [IsAlgClosed K]
    {F : Type} [Field F] [Algebra K F]
    (x : F) (hx : Transcendental K x)
    (hfin : FiniteDimensional (IntermediateField.adjoin K ({x} : Set F)) F)
    (E : Type) [Field E] [Algebra F E] [FiniteDimensional F E] [IsGalois F E]
    {I Q : Sheaf (Spec (.of F)).smallEtaleTopology AddCommGrpCat} [Injective I]
    (i : etaleMultiplicativeGroupSheaf (Spec (.of F)) ⟶ I) (p : I ⟶ Q)
    (hz : i ≫ p = 0) (hS : (ShortComplex.mk i p hz).ShortExact)
    (a : groupCohomology (fieldGaloisSheafSectionsRep F E Q) 1) : a = 0 := by
  let e := groupCohomology.coefficientRingIso
    (ULift.ringEquiv : ULift.{0} ℤ ≃+* ℤ)
    (fieldGaloisSheafSectionsRep F E Q) 1
  apply (ModuleCat.mono_iff_injective e.hom).mp inferInstance
  change e.hom.hom a = e.hom.hom 0
  rw [e.hom.hom.map_zero]
  exact liftedActualUnitInjectiveQuotient_sections_H1_eq_zero_of_tsen
    K x hx hfin E i p hz hS (e.hom.hom a)

end AlgebraicCurve
