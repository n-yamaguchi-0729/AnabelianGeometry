/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.SchemeTheory.Morphisms.FrobeniusBaseChange
public import Mathlib.AlgebraicGeometry.Pullbacks
public import Mathlib.FieldTheory.Finite.Basic

/-!
# Constant-field automorphisms and finite-field Frobenius

A field automorphism over the ground field gives an actual automorphism of
any scheme after extending constants. Absolute q-power Frobenius factors
as base change of the original scheme Frobenius followed by the constant
automorphism induced by arithmetic Frobenius. This distinguishes the two
geometric morphisms before passing to cohomology.
-/

@[expose] public section

noncomputable section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry.Scheme

variable (k Ω : Type u) [Field k] [Field Ω] [Algebra k Ω]
  (X : Scheme.{u}) [X.Over (Spec (.of k))]

local notation "b" => Spec.map (CommRingCat.ofHom (algebraMap k Ω))
local notation "f" => (X ↘ Spec (CommRingCat.of k))
local notation "Y" => pullback f b

private theorem specConstantAutomorphism_comp (σ : Ω ≃ₐ[k] Ω) :
    Spec.map (CommRingCat.ofHom σ.toRingHom) ≫ b = b := by
  rw [← Spec.map_comp]
  congr 1
  apply CommRingCat.hom_ext
  ext a
  exact σ.commutes a

/-- An automorphism of the extended constants acts on the actual scheme pullback. -/
def constantFieldTwist (σ : Ω ≃ₐ[k] Ω) : Y ⟶ Y :=
  pullback.lift (pullback.fst f b)
    (pullback.snd f b ≫ Spec.map (CommRingCat.ofHom σ.toRingHom)) (by
      rw [Category.assoc, specConstantAutomorphism_comp]
      exact pullback.condition)

@[reassoc]
theorem constantFieldTwist_fst (σ : Ω ≃ₐ[k] Ω) :
    constantFieldTwist k Ω X σ ≫ pullback.fst f b = pullback.fst f b :=
  pullback.lift_fst _ _ _

@[reassoc]
theorem constantFieldTwist_snd (σ : Ω ≃ₐ[k] Ω) :
    constantFieldTwist k Ω X σ ≫ pullback.snd f b =
      pullback.snd f b ≫ Spec.map (CommRingCat.ofHom σ.toRingHom) :=
  pullback.lift_snd _ _ _

/-- The identity of the constant field induces the identity of the scheme. -/
theorem constantFieldTwist_one :
    constantFieldTwist k Ω X (1 : Ω ≃ₐ[k] Ω) = 𝟙 Y := by
  apply pullback.hom_ext
  · rw [constantFieldTwist_fst, Category.id_comp]
  · rw [constantFieldTwist_snd, Category.id_comp]
    have h : CommRingCat.ofHom (1 : Ω ≃ₐ[k] Ω).toRingHom = 𝟙 (CommRingCat.of Ω) := rfl
    rw [h, Spec.map_id, Category.comp_id]

/-- The constant-field morphisms compose in the contravariant scheme order.
Their induced pullbacks on cohomology therefore have the usual Galois order. -/
theorem constantFieldTwist_mul (σ τ : Ω ≃ₐ[k] Ω) :
    constantFieldTwist k Ω X (σ * τ) =
      constantFieldTwist k Ω X σ ≫ constantFieldTwist k Ω X τ := by
  apply pullback.hom_ext
  · rw [constantFieldTwist_fst, Category.assoc, constantFieldTwist_fst,
      constantFieldTwist_fst]
  · rw [constantFieldTwist_snd, Category.assoc, constantFieldTwist_snd,
      ← Category.assoc, constantFieldTwist_snd, Category.assoc, ← Spec.map_comp]
    have h : CommRingCat.ofHom (σ * τ).toRingHom =
        CommRingCat.ofHom τ.toRingHom ≫ CommRingCat.ofHom σ.toRingHom := by
      apply CommRingCat.hom_ext
      ext a
      rfl
    rw [h]

/-- The constant-field twist and its inverse cancel on the original pullback. -/
theorem constantFieldTwist_comp_symm (σ : Ω ≃ₐ[k] Ω) :
    constantFieldTwist k Ω X σ ≫ constantFieldTwist k Ω X σ.symm = 𝟙 Y := by
  apply pullback.hom_ext
  · rw [Category.assoc, constantFieldTwist_fst, constantFieldTwist_fst, Category.id_comp]
  · rw [Category.assoc, constantFieldTwist_snd, ← Category.assoc, constantFieldTwist_snd,
      Category.assoc, ← Spec.map_comp, Category.id_comp]
    have hσ : CommRingCat.ofHom σ.symm.toRingHom ≫ CommRingCat.ofHom σ.toRingHom =
        𝟙 (CommRingCat.of Ω) := by
      apply CommRingCat.hom_ext
      ext a
      exact σ.apply_symm_apply a
    rw [hσ, Spec.map_id, Category.comp_id]

/-- The constant-field action is an isomorphism, with inverse induced by
inverse arithmetic on the coefficient field. -/
def constantFieldTwistIso (σ : Ω ≃ₐ[k] Ω) : Y ≅ Y where
  hom := constantFieldTwist k Ω X σ
  inv := constantFieldTwist k Ω X σ.symm
  hom_inv_id := constantFieldTwist_comp_symm k Ω X σ
  inv_hom_id := by
    simpa only [AlgEquiv.symm_symm] using constantFieldTwist_comp_symm k Ω X σ.symm

section FiniteField

variable [Fintype k] [Algebra.IsAlgebraic k Ω]

attribute [local instance] constantPullbackOver

private local instance constantSpecOver : (Spec (.of Ω)).Over (Spec (.of k)) := ⟨b⟩

/-- Frobenius defined over the ground field commutes with the actual action
of every automorphism of the extended constants. -/
theorem constantBaseChangeFrobenius_constantFieldTwist_comm (σ : Ω ≃ₐ[k] Ω) :
    constantBaseChangeFrobenius k Ω X ≫ constantFieldTwist k Ω X σ =
      constantFieldTwist k Ω X σ ≫ constantBaseChangeFrobenius k Ω X := by
  apply pullback.hom_ext
  · rw [Category.assoc, constantFieldTwist_fst, constantBaseChangeFrobenius_fst,
      Category.assoc, constantBaseChangeFrobenius_fst, ← Category.assoc,
      constantFieldTwist_fst]
  · rw [Category.assoc, constantFieldTwist_snd, ← Category.assoc,
      constantBaseChangeFrobenius_snd, Category.assoc,
      constantBaseChangeFrobenius_snd, constantFieldTwist_snd]

/-- Absolute q-power Frobenius is the composite of Frobenius on the original
scheme after base change and arithmetic q-power Frobenius on the constants. -/
theorem absoluteFrobenius_eq_baseChange_comp_constantFieldTwist :
    (Y).finiteFieldFrobenius k = constantBaseChangeFrobenius k Ω X ≫
      constantFieldTwist k Ω X (FiniteField.frobeniusAlgEquivOfAlgebraic k Ω) := by
  apply pullback.hom_ext
  · rw [Category.assoc, constantFieldTwist_fst, constantBaseChangeFrobenius_fst]
    exact finiteFieldFrobenius_naturality Y k X (pullback.fst f b)
  · rw [Category.assoc, constantFieldTwist_snd, ← Category.assoc,
      constantBaseChangeFrobenius_snd]
    rw [finiteFieldFrobenius_naturality, finiteFieldFrobenius_spec]
    rfl

/-- Base-changed Frobenius is absolute q-power Frobenius followed by the
inverse of arithmetic Frobenius on the extended constants. -/
theorem baseChangeFrobenius_eq_absolute_comp_inverseConstantTwist :
    constantBaseChangeFrobenius k Ω X = (Y).finiteFieldFrobenius k ≫
      constantFieldTwist k Ω X (FiniteField.frobeniusAlgEquivOfAlgebraic k Ω).symm := by
  symm
  calc
    _ = (constantBaseChangeFrobenius k Ω X ≫
        constantFieldTwist k Ω X (FiniteField.frobeniusAlgEquivOfAlgebraic k Ω)) ≫
          constantFieldTwist k Ω X (FiniteField.frobeniusAlgEquivOfAlgebraic k Ω).symm :=
      congrArg
        (fun q : Y ⟶ Y => q ≫ constantFieldTwist k Ω X
          (FiniteField.frobeniusAlgEquivOfAlgebraic k Ω).symm)
        (absoluteFrobenius_eq_baseChange_comp_constantFieldTwist k Ω X)
    _ = constantBaseChangeFrobenius k Ω X := by
      rw [Category.assoc, constantFieldTwist_comp_symm, Category.comp_id]

end FiniteField

end AlgebraicGeometry.Scheme
