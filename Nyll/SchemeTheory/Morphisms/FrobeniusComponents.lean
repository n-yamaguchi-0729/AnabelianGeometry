/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.SchemeTheory.Divisors.IrreducibleComponentIsomorphism
public import Nyll.SchemeTheory.Divisors.IrreducibleComponentMap
public import Nyll.SchemeTheory.Morphisms.FiniteFieldConstantAction
public import Nyll.SchemeTheory.Morphisms.FrobeniusBaseChange
public import Nyll.SchemeTheory.Morphisms.FrobeniusBaseChangePoints
public import Mathlib.CategoryTheory.Endomorphism

/-!
# Actual geometric Frobenius on reduced components

Absolute Frobenius is the identity on the underlying topological space.
Consequently every power of the original geometric Frobenius has the
same actual component image as the inverse arithmetic power. The
original reduced-component map therefore restricts geometric Frobenius
itself to the actual components. These morphisms retain the original
inclusions and the original extended-base structure maps.
-/

@[expose] public section

noncomputable section

universe u

open CategoryTheory Limits TopologicalSpace

namespace AlgebraicGeometry.Scheme

variable (k Ω : Type u) [Field k] [Fintype k] [Field Ω] [Algebra k Ω]
  [Algebra.IsAlgebraic k Ω] (X : Scheme.{u}) [X.Over (Spec (CommRingCat.of k))]

local notation "b" => Spec.algebraMap k Ω
local notation "f" => X ↘ Spec (CommRingCat.of k)
local notation "Y" => (pullback (C := Scheme) f b)
local notation "F" => constantBaseChangeFrobenius k Ω X
local notation "σ" => AlgEquiv.symm (FiniteField.frobeniusAlgEquivOfAlgebraic k Ω)

/-- The original geometric and inverse arithmetic Frobenius maps
agree on the actual underlying points. -/
theorem constantBaseChangeFrobenius_apply_eq_inverseTwist (x : Y) :
    F x = constantFieldTwist k Ω X σ x := by
  have h := congrArg (fun g : Y ⟶ Y => g x)
    (baseChangeFrobenius_eq_absolute_comp_inverseConstantTwist k Ω X)
  simp only [Hom.comp_apply] at h
  change F x = constantFieldTwist k Ω X σ x at h
  exact h

/-- The same pointwise comparison holds for every native power of
the original scheme Frobenius. -/
theorem constantBaseChangeFrobenius_pow_apply_eq_inverseTwist (m : ℕ) (x : Y) :
    ((End.of F) ^ m).asHom x = constantFieldTwist k Ω X (σ ^ m) x := by
  induction m generalizing x with
  | zero =>
      exact (congrArg (fun g : Y ⟶ Y => g x) (constantFieldTwist_one k Ω X)).symm
  | succ m ih =>
      calc
        ((End.of F) ^ (m + 1)).asHom x = F (((End.of F) ^ m).asHom x) := by
          rw [pow_succ', End.mul_asHom, Hom.comp_apply]
        _ = constantFieldTwist k Ω X σ (constantFieldTwist k Ω X (σ ^ m) x) :=
          (constantBaseChangeFrobenius_apply_eq_inverseTwist k Ω X _).trans
            (congrArg (constantFieldTwist k Ω X σ) (ih x))
        _ = constantFieldTwist k Ω X (σ ^ (m + 1)) x := by
          rw [pow_succ, constantFieldTwist_mul, Hom.comp_apply]

/-- The actual image of every component under original geometric
Frobenius is the actual inverse arithmetic component permutation. -/
theorem constantBaseChangeFrobenius_pow_component_image (m : ℕ)
    (Z : irreducibleComponents Y) :
    ((End.of F) ^ m).asHom '' Z.1 =
      (irreducibleComponentsIsoEquiv (constantFieldTwistIso k Ω X (σ ^ m)) Z).1 := by
  rw [irreducibleComponentsIsoEquiv_coe]
  apply congrArg (fun g : Y → Y => g '' Z.1)
  funext x
  exact constantBaseChangeFrobenius_pow_apply_eq_inverseTwist k Ω X m x

/-- The actual geometric Frobenius power restricted to its actual
source and image components. -/
def constantBaseChangeFrobeniusComponent (m : ℕ) (Z : irreducibleComponents Y) :
    (Y).reducedIrreducibleComponent Z.1 Z.2 ⟶
      (Y).reducedIrreducibleComponent
        (irreducibleComponentsIsoEquiv (constantFieldTwistIso k Ω X (σ ^ m)) Z).1
        (irreducibleComponentsIsoEquiv (constantFieldTwistIso k Ω X (σ ^ m)) Z).2 :=
  (Y).reducedIrreducibleComponentMap ((End.of F) ^ m).asHom Z.1 Z.2
    (irreducibleComponentsIsoEquiv (constantFieldTwistIso k Ω X (σ ^ m)) Z).1
    (irreducibleComponentsIsoEquiv (constantFieldTwistIso k Ω X (σ ^ m)) Z).2
    (constantBaseChangeFrobenius_pow_component_image k Ω X m Z)

/-- The actual component map commutes with the original geometric
Frobenius power and the original component inclusions. -/
theorem constantBaseChangeFrobeniusComponent_ι (m : ℕ) (Z : irreducibleComponents Y) :
    constantBaseChangeFrobeniusComponent k Ω X m Z ≫
        (Y).reducedIrreducibleComponentι
          (irreducibleComponentsIsoEquiv (constantFieldTwistIso k Ω X (σ ^ m)) Z).1
          (irreducibleComponentsIsoEquiv (constantFieldTwistIso k Ω X (σ ^ m)) Z).2 =
      (Y).reducedIrreducibleComponentι Z.1 Z.2 ≫ ((End.of F) ^ m).asHom :=
  reducedIrreducibleComponentMap_ι ((End.of F) ^ m).asHom Z.1 Z.2
    (irreducibleComponentsIsoEquiv (constantFieldTwistIso k Ω X (σ ^ m)) Z).1
    (irreducibleComponentsIsoEquiv (constantFieldTwistIso k Ω X (σ ^ m)) Z).2
    (constantBaseChangeFrobenius_pow_component_image k Ω X m Z)

/-- The actual geometric component map preserves the original
extended-base structure morphism. -/
theorem constantBaseChangeFrobeniusComponent_toBase (m : ℕ) (Z : irreducibleComponents Y) :
    constantBaseChangeFrobeniusComponent k Ω X m Z ≫
        ((Y).reducedIrreducibleComponentι
          (irreducibleComponentsIsoEquiv (constantFieldTwistIso k Ω X (σ ^ m)) Z).1
          (irreducibleComponentsIsoEquiv (constantFieldTwistIso k Ω X (σ ^ m)) Z).2 ≫
            pullback.snd f b) =
      (Y).reducedIrreducibleComponentι Z.1 Z.2 ≫ pullback.snd f b := by
  rw [← Category.assoc, constantBaseChangeFrobeniusComponent_ι, Category.assoc,
    constantBaseChangeFrobenius_pow_snd]

/-- On an actually fixed component, the original geometric power
restricts to an actual endomorphism of that same reduced curve. -/
def constantBaseChangeFrobeniusFixedComponent (m : ℕ) (Z : irreducibleComponents Y)
    (hZ : irreducibleComponentsIsoEquiv (constantFieldTwistIso k Ω X (σ ^ m)) Z = Z) :
    (Y).reducedIrreducibleComponent Z.1 Z.2 ⟶ (Y).reducedIrreducibleComponent Z.1 Z.2 :=
  (Y).reducedIrreducibleComponentMap ((End.of F) ^ m).asHom Z.1 Z.2 Z.1 Z.2
    ((constantBaseChangeFrobenius_pow_component_image k Ω X m Z).trans
      (congrArg Subtype.val hZ))

/-- The fixed-component endomorphism retains its original inclusion. -/
theorem constantBaseChangeFrobeniusFixedComponent_ι (m : ℕ) (Z : irreducibleComponents Y)
    (hZ : irreducibleComponentsIsoEquiv (constantFieldTwistIso k Ω X (σ ^ m)) Z = Z) :
    constantBaseChangeFrobeniusFixedComponent k Ω X m Z hZ ≫
        (Y).reducedIrreducibleComponentι Z.1 Z.2 =
      (Y).reducedIrreducibleComponentι Z.1 Z.2 ≫ ((End.of F) ^ m).asHom :=
  reducedIrreducibleComponentMap_ι ((End.of F) ^ m).asHom Z.1 Z.2 Z.1 Z.2
    ((constantBaseChangeFrobenius_pow_component_image k Ω X m Z).trans
      (congrArg Subtype.val hZ))

/-- The actual fixed-component endomorphism is over the original
extended constant field. -/
theorem constantBaseChangeFrobeniusFixedComponent_toBase (m : ℕ) (Z : irreducibleComponents Y)
    (hZ : irreducibleComponentsIsoEquiv (constantFieldTwistIso k Ω X (σ ^ m)) Z = Z) :
    constantBaseChangeFrobeniusFixedComponent k Ω X m Z hZ ≫
        ((Y).reducedIrreducibleComponentι Z.1 Z.2 ≫ pullback.snd f b) =
      (Y).reducedIrreducibleComponentι Z.1 Z.2 ≫ pullback.snd f b := by
  rw [← Category.assoc, constantBaseChangeFrobeniusFixedComponent_ι, Category.assoc,
    constantBaseChangeFrobenius_pow_snd]

end AlgebraicGeometry.Scheme
