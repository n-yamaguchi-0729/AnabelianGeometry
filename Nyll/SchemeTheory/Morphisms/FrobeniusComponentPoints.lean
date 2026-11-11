/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.SchemeTheory.Divisors.IrreducibleComponentPoints
public import Nyll.SchemeTheory.Divisors.IrreducibleComponentDecomposition
public import Nyll.SchemeTheory.Morphisms.FrobeniusComponents
public import Mathlib.AlgebraicGeometry.Scheme

/-!
# Actual Frobenius-fixed points on the fixed components

Every actual field-valued fixed point lies in a unique original
component. Its fixed-point equation forces that component to be fixed
by the actual geometric Frobenius power. The original open-immersion
lift then satisfies the fixed-point equation for the actual restricted
endomorphism, by cancellation of the original component inclusion.
This gives a bijection of the original fixed-point types.
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
local notation "g" => pullback.snd f b
local notation "σ" => AlgEquiv.symm (FiniteField.frobeniusAlgEquivOfAlgebraic k Ω)

variable (m : ℕ)

local notation "v" => End.asHom ((End.of (constantBaseChangeFrobenius k Ω X)) ^ m)
local notation "e" => constantFieldTwistIso k Ω X (σ ^ m)

/-- Actual fixed points of actual fixed components map to original
geometric fixed points through the original inclusions. -/
def frobeniusFixedComponentPointMap :
    (Σ Z : {Z : irreducibleComponents Y // irreducibleComponentsIsoEquiv e Z = Z},
      {s : Spec (CommRingCat.of Ω) ⟶ (Y).reducedIrreducibleComponent Z.val.1 Z.val.2 //
        s ≫ ((Y).reducedIrreducibleComponentι Z.val.1 Z.val.2 ≫ g) = 𝟙 _ ∧
          s ≫ constantBaseChangeFrobeniusFixedComponent k Ω X m Z.val Z.property = s}) →
      {p : Spec (CommRingCat.of Ω) ⟶ Y // p ≫ g = 𝟙 _ ∧ p ≫ v = p} := fun p =>
  ⟨p.2.val ≫ (Y).reducedIrreducibleComponentι p.1.val.1 p.1.val.2,
    (Category.assoc _ _ _).trans p.2.property.1, by
      rw [Category.assoc,
        ← constantBaseChangeFrobeniusFixedComponent_ι k Ω X m p.1.val p.1.property,
        ← Category.assoc, p.2.property.2]⟩

/-- Disjoint original components and their original mono immersions
make the actual fixed-component point map injective. -/
theorem frobeniusFixedComponentPointMap_injective
    [hY : IsLocallyNoetherian Y] (hdom : ∀ x : Y, IsDomain ((Y).presheaf.stalk x)) :
    Function.Injective (frobeniusFixedComponentPointMap k Ω X m) := by
  intro p q hpq
  rcases p with ⟨Z, p⟩
  rcases q with ⟨W, q⟩
  have hhom : reducedComponentHomMap Ω Y ⟨Z.val, p.val⟩ =
      reducedComponentHomMap Ω Y ⟨W.val, q.val⟩ := congrArg Subtype.val hpq
  have hZW : Z.val = W.val := congrArg Sigma.fst
    (@reducedComponentHomMap_injective Ω _ Y hY hdom
      ⟨Z.val, p.val⟩ ⟨W.val, q.val⟩ hhom)
  have hfixed : Z = W := Subtype.ext hZW
  cases hfixed
  have hpq' : p.val = q.val :=
    (cancel_mono ((Y).reducedIrreducibleComponentι Z.val.1 Z.val.2)).mp hhom
  have hpq'' : p = q := Subtype.ext hpq'
  cases hpq''
  rfl

/-- An original fixed point forces its actual component to be fixed,
and its original component lift is fixed by the actual restriction. -/
theorem frobeniusFixedComponentPointMap_surjective
    [hY : IsLocallyNoetherian Y] (hdom : ∀ x : Y, IsDomain ((Y).presheaf.stalk x)) :
    Function.Surjective (frobeniusFixedComponentPointMap k Ω X m) := by
  intro p
  obtain ⟨⟨Z, s⟩, hs⟩ := @reducedComponentHomMap_surjective Ω _ Y hY hdom p.val
  change s ≫ (Y).reducedIrreducibleComponentι Z.1 Z.2 = p.val at hs
  have hxZ : p.val default ∈ Z.1 := by
    rw [← hs]
    exact Eq.mp
      (congrArg (fun S : Set Y =>
        (s ≫ (Y).reducedIrreducibleComponentι Z.1 Z.2) default ∈ S)
        (range_reducedIrreducibleComponentι Y Z.1 Z.2)) ⟨s default, rfl⟩
  have hxW : p.val default ∈ (irreducibleComponentsIsoEquiv e Z).1 := by
    rw [← constantBaseChangeFrobenius_pow_component_image k Ω X m Z]
    exact ⟨p.val default, hxZ, congrArg (fun a : Spec (CommRingCat.of Ω) ⟶ Y => a default)
      p.property.2⟩
  have hZ : irreducibleComponentsIsoEquiv e Z = Z :=
    @irreducibleComponents_eq_of_mem Y hY hdom
      (irreducibleComponentsIsoEquiv e Z) Z (p.val default) hxW hxZ
  have hsbase : s ≫ ((Y).reducedIrreducibleComponentι Z.1 Z.2 ≫ g) = 𝟙 _ := by
    rw [← Category.assoc, hs]
    exact p.property.1
  have hsfix : s ≫ constantBaseChangeFrobeniusFixedComponent k Ω X m Z hZ = s := by
    apply (cancel_mono ((Y).reducedIrreducibleComponentι Z.1 Z.2)).mp
    calc
      _ = s ≫ ((Y).reducedIrreducibleComponentι Z.1 Z.2 ≫ v) := by
        rw [Category.assoc, constantBaseChangeFrobeniusFixedComponent_ι]
      _ = (s ≫ (Y).reducedIrreducibleComponentι Z.1 Z.2) ≫ v := (Category.assoc _ _ _).symm
      _ = p.val ≫ v := congrArg (fun a => a ≫ v) hs
      _ = p.val := p.property.2
      _ = s ≫ (Y).reducedIrreducibleComponentι Z.1 Z.2 := hs.symm
  exact ⟨⟨⟨Z, hZ⟩, ⟨s, hsbase, hsfix⟩⟩, Subtype.ext hs⟩

/-- The original geometric fixed-point type is exactly the actual
disjoint union of the original fixed points on the fixed components. -/
def frobeniusFixedComponentPointEquiv
    [hY : IsLocallyNoetherian Y] (hdom : ∀ x : Y, IsDomain ((Y).presheaf.stalk x)) :
    (Σ Z : {Z : irreducibleComponents Y // irreducibleComponentsIsoEquiv e Z = Z},
      {s : Spec (CommRingCat.of Ω) ⟶ (Y).reducedIrreducibleComponent Z.val.1 Z.val.2 //
        s ≫ ((Y).reducedIrreducibleComponentι Z.val.1 Z.val.2 ≫ g) = 𝟙 _ ∧
          s ≫ constantBaseChangeFrobeniusFixedComponent k Ω X m Z.val Z.property = s}) ≃
      {p : Spec (CommRingCat.of Ω) ⟶ Y // p ≫ g = 𝟙 _ ∧ p ≫ v = p} :=
  Equiv.ofBijective (frobeniusFixedComponentPointMap k Ω X m)
    ⟨frobeniusFixedComponentPointMap_injective k Ω X m hdom,
      frobeniusFixedComponentPointMap_surjective k Ω X m hdom⟩

end AlgebraicGeometry.Scheme
