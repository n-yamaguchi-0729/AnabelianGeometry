/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.SchemeTheory.CategoryTheory.SchemeHomOver
public import Nyll.SchemeTheory.Divisors.IrreducibleComponentDecomposition
public import Nyll.SchemeTheory.Divisors.IrreducibleComponentIsomorphism
public import Nyll.SchemeTheory.Morphisms.FiniteFieldConstantAction
public import Nyll.SchemeTheory.Morphisms.FiniteFieldDegreeFixedPoints
public import Nyll.SchemeTheory.Morphisms.FiniteSchemePoints
public import Nyll.SchemeTheory.Morphisms.FrobeniusComponentPoints
public import Nyll.SchemeTheory.Morphisms.FrobeniusComponents
public import Nyll.SchemeTheory.RingTheory.FieldExtensions.FiniteIntermediateFieldDegree
public import Mathlib.Algebra.BigOperators.Finprod
public import Mathlib.Data.Sigma.Basic
public import Mathlib.RingTheory.Finiteness.Cardinality
public import Mathlib.SetTheory.Cardinal.Finite

/-!
# Original finite-field point counts on the actual fixed components

The original finite-extension point dictionary and the original
component point equivalence identify the rational points in every
positive degree with actual fixed points on the actual fixed
components. Finiteness comes from the original finite-type scheme
point theorem. Taking cardinalities gives the component sum for the
same geometric endomorphisms that act on component cohomology.
-/

@[expose] public section

noncomputable section

open CategoryTheory Limits TopologicalSpace NeronModelInfra

namespace AlgebraicGeometry

universe u

section Dictionary

variable (k Ω : Type u) [Field k] [Fintype k] [Field Ω] [Algebra k Ω]
  [Algebra.IsAlgebraic k Ω] [IsAlgClosed Ω]
  (X : Scheme.{u}) [X.Over (Spec (CommRingCat.of k))] (m : ℕ) [NeZero m]

local notation "b" => Spec.algebraMap k Ω
local notation "f" => X ↘ Spec (CommRingCat.of k)
local notation "Y" => (pullback (C := Scheme) f b)
local notation "g" => pullback.snd f b
local notation "v" => End.asHom ((End.of (Scheme.constantBaseChangeFrobenius k Ω X)) ^ m)
local notation "e" => Scheme.constantFieldTwistIso k Ω X
  (AlgEquiv.symm (FiniteField.frobeniusAlgEquivOfAlgebraic k Ω) ^ m)
local notation "E" => LocalClassFieldTheory.finiteResidueGaloisIntermediateFieldIn k Ω m

/-- The original extension-field points are exactly the original
fixed points on the actual fixed geometric components. -/
def finiteFieldPointsEquivFrobeniusFixedComponents
    [hY : IsLocallyNoetherian Y] (hdom : ∀ x : Y, IsDomain ((Y).presheaf.stalk x)) :
    SchemeHomOver (Spec.algebraMap k E) f ≃
      (Σ Z : {Z : irreducibleComponents Y // Scheme.irreducibleComponentsIsoEquiv e Z = Z},
        {s : Spec (CommRingCat.of Ω) ⟶ (Y).reducedIrreducibleComponent Z.val.1 Z.val.2 //
          s ≫ ((Y).reducedIrreducibleComponentι Z.val.1 Z.val.2 ≫ g) = 𝟙 _ ∧
            s ≫ Scheme.constantBaseChangeFrobeniusFixedComponent k Ω X m
              Z.val Z.property = s}) := by
  let flatten : {x : SchemeHomOver (𝟙 (Spec (CommRingCat.of Ω))) g // x.val ≫ v = x.val} ≃
      {p : Spec (CommRingCat.of Ω) ⟶ Y // p ≫ g = 𝟙 _ ∧ p ≫ v = p} :=
    { toFun := fun p => ⟨p.val.val, p.val.property, p.property⟩
      invFun := fun p => ⟨⟨p.val, p.property.1⟩, p.property.2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  exact (finiteFieldPointsEquivRelativeFrobeniusPowFixedDegree k Ω X m).trans
    (flatten.trans (Scheme.frobeniusFixedComponentPointEquiv k Ω X m hdom).symm)

end Dictionary

section Cardinality

variable (k Ω : Type u) [Field k] [Fintype k] [Field Ω] [Algebra k Ω]
  [Algebra.IsAlgebraic k Ω] [IsAlgClosed Ω]
  (X : Scheme.{u}) [X.Over (Spec (CommRingCat.of k))] [CompactSpace X]
  [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of k))] (m : ℕ) [NeZero m]

local notation "b" => Spec.algebraMap k Ω
local notation "f" => X ↘ Spec (CommRingCat.of k)
local notation "Y" => (pullback (C := Scheme) f b)
local notation "g" => pullback.snd f b
local notation "e" => Scheme.constantFieldTwistIso k Ω X
  (AlgEquiv.symm (FiniteField.frobeniusAlgEquivOfAlgebraic k Ω) ^ m)
local notation "E" => LocalClassFieldTheory.finiteResidueGaloisIntermediateFieldIn k Ω m
local notation "B" =>
  {Z : irreducibleComponents Y // Scheme.irreducibleComponentsIsoEquiv e Z = Z}
local notation "P" => fun Z : B =>
  {s : Spec (CommRingCat.of Ω) ⟶
      Scheme.reducedIrreducibleComponent Y
        (Subtype.val (Subtype.val Z)) (Subtype.property (Subtype.val Z)) //
    s ≫ (Scheme.reducedIrreducibleComponentι Y
      (Subtype.val (Subtype.val Z)) (Subtype.property (Subtype.val Z)) ≫ g) = 𝟙 _ ∧
      s ≫ Scheme.constantBaseChangeFrobeniusFixedComponent k Ω X m
        (Subtype.val Z) (Subtype.property Z) = s}

/-- The actual disjoint union of fixed-component points is finite,
using the original finite extension and the original point dictionary. -/
theorem finite_frobeniusFixedComponentPoints_sigma
    [hY : IsLocallyNoetherian Y] (hdom : ∀ x : Y, IsDomain ((Y).presheaf.stalk x)) :
    Finite (Σ Z : B, P Z) := by
  have : Finite E := Module.finite_of_finite k
  have : Finite (SchemeHomOver (Spec.algebraMap k E) f) :=
    finite_scheme_points_of_finite k E X f
  let a := finiteFieldPointsEquivFrobeniusFixedComponents k Ω X m hdom
  exact Finite.of_surjective a a.surjective

/-- Each actual component restriction has finitely many original
geometric fixed points, as a fiber of the original finite point type. -/
theorem finite_frobeniusFixedComponentPoints
    [hY : IsLocallyNoetherian Y] (hdom : ∀ x : Y, IsDomain ((Y).presheaf.stalk x))
    (Z : B) : Finite (P Z) := by
  have : Finite (Σ Z : B, P Z) := finite_frobeniusFixedComponentPoints_sigma k Ω X m hdom
  exact Finite.of_injective (@Sigma.mk B P Z) (@sigma_mk_injective B P Z)

/-- The original finite-extension point count is the sum of the
actual fixed-point counts of the actual fixed component restrictions. -/
theorem finiteFieldPointCount_eq_sum_fixedComponents [IsNoetherian Y]
    (hdom : ∀ x : Y, IsDomain ((Y).presheaf.stalk x)) :
    Nat.card (SchemeHomOver (Spec.algebraMap k E) f) = ∑ᶠ Z : B, Nat.card (P Z) := by
  classical
  let : Fintype (irreducibleComponents Y) := (Y).irreducibleComponentsFintype
  have (Z : B) : Finite (P Z) := finite_frobeniusFixedComponentPoints k Ω X m hdom Z
  rw [Nat.card_congr (finiteFieldPointsEquivFrobeniusFixedComponents k Ω X m hdom),
    Nat.card_sigma, finsum_eq_sum_of_fintype]

end Cardinality

end AlgebraicGeometry
