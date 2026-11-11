/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.GaloisCohomology.GroupTheory.CoefficientRingEquivalence
public import Nyll.GaloisCohomology.Kummer.LiftedUnitsCohomology
public import Nyll.EtaleCohomology.Classical.FieldSectionRepresentations
public import Nyll.EtaleCohomology.Classical.FieldSectionExactness
public import Nyll.EtaleCohomology.Classical.InjectiveFieldGaloisH1
public import Mathlib.Algebra.Homology.ShortComplex.ShortExact
public import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor

/-!
# Native Galois cohomology of field sections in every universe

The actual section functor is transported through the integer ring equivalence.
Its exact sequences and unit-section comparison are transported by that same
functor. Injective acyclicity follows from the geometric cocycle primitive.
-/

@[expose] public section

noncomputable section
universe u
open CategoryTheory AlgebraicGeometry

namespace EtaleCohomology

variable (K L : Type u) [Field K] [Field L] [Algebra K L]
  [FiniteDimensional K L] [IsGalois K L]

/-- Actual field sections, with integer coefficients in the field's universe. -/
def liftedFieldGaloisSheafSectionsRep
    (F : Sheaf (Spec (.of K)).smallEtaleTopology AddCommGrpCat.{u}) :
    Rep.{u} (ULift.{u} ℤ) Gal(L/K) :=
  (Rep.coefficientRingEquivalence
    (ULift.ringEquiv : ULift.{u} ℤ ≃+* ℤ) Gal(L/K)).functor.obj
      (fieldGaloisSheafSectionsRep K L F)

/-- The actual field-section functor followed by the same scalar restriction. -/
def liftedFieldGaloisSheafSectionsFunctor :
    Sheaf (Spec (.of K)).smallEtaleTopology AddCommGrpCat.{u} ⥤
      Rep.{u} (ULift.{u} ℤ) Gal(L/K) :=
  fieldGaloisSheafSectionsFunctor K L ⋙
    (Rep.coefficientRingEquivalence
      (ULift.ringEquiv : ULift.{u} ℤ ≃+* ℤ) Gal(L/K)).functor

/-- Scalar restriction preserves the additivity of the actual field-section functor. -/
instance liftedFieldGaloisSheafSectionsFunctor_additive :
    (liftedFieldGaloisSheafSectionsFunctor K L).Additive :=
  inferInstanceAs ((fieldGaloisSheafSectionsFunctor K L ⋙
    (Rep.coefficientRingEquivalence
      (ULift.ringEquiv : ULift.{u} ℤ ≃+* ℤ) Gal(L/K)).functor).Additive)

/-- The geometric unit-section comparison retains the actual unit action
under scalar restriction. -/
def liftedFieldGaloisSheafSectionsUnitsIso :
    liftedFieldGaloisSheafSectionsRep K L
        (etaleMultiplicativeGroupSheaf (Spec (.of K))) ≅
      ClassFieldTower.Cohomology.liftedGaloisUnitsRep K L :=
  (Rep.coefficientRingEquivalence
    (ULift.ringEquiv : ULift.{u} ℤ ≃+* ℤ) Gal(L/K)).functor.mapIso
      (fieldGaloisSheafSectionsUnitsIso K L)

/-- The same field-section short exact sequence remains exact after the
coefficient equivalence. -/
theorem liftedFieldGaloisSheafSections_unitsKernel_shortExact
    {B Q : Sheaf (Spec (.of K)).smallEtaleTopology AddCommGrpCat.{u}}
    (i : etaleMultiplicativeGroupSheaf (Spec (.of K)) ⟶ B) (p : B ⟶ Q)
    (hz : i ≫ p = 0) (hS : (ShortComplex.mk i p hz).ShortExact) :
    ((ShortComplex.mk i p hz).map
      (liftedFieldGaloisSheafSectionsFunctor K L)).ShortExact := by
  exact (fieldGaloisSheafSections_unitsKernel_shortExact K L i p hz hS).map_of_exact
    (Rep.coefficientRingEquivalence
      (ULift.ringEquiv : ULift.{u} ℤ ≃+* ℤ) Gal(L/K)).functor

/-- Injective sheaf sections have zero native first Galois cohomology,
using their actual geometric cocycle primitive. -/
theorem liftedFieldGaloisSheafSections_H1_eq_zero_of_injective
    (F : Sheaf (Spec (.of K)).smallEtaleTopology AddCommGrpCat.{u}) [Injective F]
    (x : groupCohomology (liftedFieldGaloisSheafSectionsRep K L F) 1) : x = 0 := by
  refine groupCohomology.H1_induction_on x ?_
  intro c
  apply (groupCohomology.H1π_eq_zero_iff c).mpr
  obtain ⟨s, hs⟩ := exists_injective_fieldGalois_cocycle_primitive K L F c
    ((groupCohomology.mem_cocycles₁_iff c).mp c.property)
  refine ⟨s, ?_⟩
  funext σ
  exact hs σ

end EtaleCohomology
