/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.SchemeTheory.Divisors.SubschemeStalk
public import Mathlib.AlgebraicGeometry.Morphisms.FormallyUnramified
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.AlgebraicGeometry.Stalk
public import Mathlib.RingTheory.Unramified.LocalRing
public import Mathlib.RingTheory.Length
public import Mathlib.RingTheory.SimpleModule.Basic

/-!
# Local multiplicity of a closed subscheme unramified over a field

Unramified stalk maps carry the maximal ideal of the base onto the maximal
ideal of the source. Over a field the latter is therefore zero. A closed
immersion from such a scheme has the maximal ideal as its actual stalk
kernel, and its defining local quotient has length one.
-/

@[expose] public section

noncomputable section

open CategoryTheory IsLocalRing

namespace AlgebraicGeometry.Scheme

universe u

/-- The actual local rings of a scheme unramified and locally of finite type
over a field are fields. No reducedness or dimension comparison is assumed. -/
theorem isField_stalk_of_unramified_over_field
    {K : Type u} [Field K] {X : Scheme.{u}}
    (f : X ⟶ Spec (.of K)) [FormallyUnramified f] [LocallyOfFiniteType f]
    (x : X) : IsField (X.presheaf.stalk x) := by
  let R := (Spec (.of K)).presheaf.stalk (f x)
  let S := X.presheaf.stalk x
  let : Algebra R S := (f.stalkMap x).hom.toAlgebra
  have : IsLocalHom (algebraMap R S) :=
    inferInstanceAs (IsLocalHom (f.stalkMap x).hom)
  have : Algebra.FormallyUnramified R S := FormallyUnramified.stalkMap f x
  have : Algebra.EssFiniteType R S := LocallyOfFiniteType.stalkMap f x
  have hR : IsField R := by
    change IsField ((Spec (.of K)).presheaf.stalk (f x))
    rw [show f x = IsLocalRing.closedPoint K from Subsingleton.elim _ _]
    exact (stalkClosedPointIso (.of K)).commRingCatIsoToRingEquiv.isField
      (Field.toIsField K)
  apply IsLocalRing.isField_iff_maximalIdeal_eq.mpr
  rw [← Algebra.FormallyUnramified.map_maximalIdeal (R := R),
    IsLocalRing.isField_iff_maximalIdeal_eq.mp hR, Ideal.map_bot]

/-- A closed immersion with source unramified over a field has the maximal
ideal as the stalk of its original kernel ideal sheaf. -/
theorem Hom.ker_stalkIdeal_eq_maximalIdeal_of_unramified_over_field
    {K : Type u} [Field K] {X Y : Scheme.{u}}
    (i : X ⟶ Y) [IsClosedImmersion i]
    (f : X ⟶ Spec (.of K)) [FormallyUnramified f] [LocallyOfFiniteType f]
    (x : X) :
    i.ker.stalkIdeal (i x) = IsLocalRing.maximalIdeal (Y.presheaf.stalk (i x)) := by
  let : Field (X.presheaf.stalk x) :=
    (isField_stalk_of_unramified_over_field f x).toField
  rw [← i.ker_stalkMap_eq_stalkIdeal x]
  exact IsLocalRing.ker_eq_maximalIdeal (i.stalkMap x).hom (i.stalkMap_surjective x)

/-- The quotient of the ambient local ring by the actual defining ideal has
length one at each point of a closed subscheme unramified over a field. -/
theorem Hom.length_quotient_ker_stalkIdeal_eq_one_of_unramified_over_field
    {K : Type u} [Field K] {X Y : Scheme.{u}}
    (i : X ⟶ Y) [IsClosedImmersion i]
    (f : X ⟶ Spec (.of K)) [FormallyUnramified f] [LocallyOfFiniteType f]
    (x : X) :
    Module.length (Y.presheaf.stalk (i x))
      (Y.presheaf.stalk (i x) ⧸ i.ker.stalkIdeal (i x)) = 1 := by
  rw [i.ker_stalkIdeal_eq_maximalIdeal_of_unramified_over_field f x]
  rw [Module.length_eq_one_iff, isSimpleModule_iff_quot_maximal]
  exact ⟨maximalIdeal (Y.presheaf.stalk (i x)), inferInstance,
    ⟨LinearEquiv.refl _ _⟩⟩

end AlgebraicGeometry.Scheme
