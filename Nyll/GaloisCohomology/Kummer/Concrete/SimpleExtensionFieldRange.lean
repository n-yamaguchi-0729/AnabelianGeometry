/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.GaloisCohomology.Kummer.Concrete.FiniteGeneration
public import Nyll.GaloisCohomology.Kummer.Concrete.RootCharacters
public import Nyll.GaloisCohomology.Kummer.Concrete.SimpleExtension
public import Mathlib.Algebra.Group.Units.Hom
public import Mathlib.FieldTheory.IntermediateField.Basic
public import Mathlib.RingTheory.RootsOfUnity.Basic

/-!
# Chosen Kummer roots in the image of an actual field

An embedded field containing an actual root contains the chosen simple
Kummer extension as well. The proof retains the precise root-of-unity
scalar relating the two roots in the supplied embedding.
-/

@[expose] public section

universe u

noncomputable section

namespace KummerTheory

/-- An actual embedded root differs from the chosen root by a base-field
root of unity. Consequently the chosen simple extension lies in the
image of the supplied embedding. -/
theorem exists_chosenSimpleKummerRootScale_fieldRange
    (F : Type u) [Field F] (n : ℕ+) (hnF : ((n : ℕ) : F) ≠ 0)
    (hmu : (primitiveRoots (n : ℕ) F).Nonempty) (b : Fˣ)
    {L : Type*} [Field L] [Algebra F L]
    (φ : L →ₐ[F] SeparableClosure F) (β : Lˣ)
    (hβ : β ^ (n : ℕ) = Units.map (algebraMap F L).toMonoidHom b) :
    ∃ ζ : rootsOfUnity (n : ℕ) F,
      chosenSimpleKummerRoot F n hnF b =
        algebraMap F (SeparableClosure F) ((ζ : Fˣ) : F) * φ (β : L) ∧
      chosenSimpleKummerExtension F n hnF b ≤ φ.fieldRange := by
  let E := chosenSimpleKummerExtension F n hnF b
  let r : (SeparableClosure F)ˣ :=
    Units.map E.val.toMonoidHom (chosenSimpleKummerRootUnit F n hnF b)
  let βΩ : (SeparableClosure F)ˣ := Units.map φ.toMonoidHom β
  have hrpow : r ^ (n : ℕ) =
      Units.map (algebraMap F (SeparableClosure F)).toMonoidHom b := by
    change (Units.map E.val.toMonoidHom (chosenSimpleKummerRootUnit F n hnF b)) ^
      (n : ℕ) = _
    rw [← map_pow, chosenSimpleKummerRootUnit_pow]
    apply Units.ext
    exact E.val.commutes (b : F)
  have hβpow : βΩ ^ (n : ℕ) =
      Units.map (algebraMap F (SeparableClosure F)).toMonoidHom b := by
    change (Units.map φ.toMonoidHom β) ^ (n : ℕ) = _
    rw [← map_pow, hβ]
    apply Units.ext
    exact φ.commutes (b : F)
  have hratio : (r / βΩ) ^ (n : ℕ) = 1 :=
    div_pow_eq_one_of_pow_eq_pow (hrpow.trans hβpow.symm)
  obtain ⟨ζ, hζ⟩ := nthRootsOfUnityInBase_of_primitiveRoots
    (K := F) (L := SeparableClosure F) n hmu (r / βΩ) hratio
  have hζpow : ζ ^ (n : ℕ) = 1 := by
    apply Units.map_injective
      (f := (algebraMap F (SeparableClosure F)).toMonoidHom)
      (algebraMap F (SeparableClosure F)).injective
    rw [map_pow, hζ, hratio, map_one]
  have hmul : Units.map (algebraMap F (SeparableClosure F)).toMonoidHom ζ * βΩ = r :=
    eq_div_iff_mul_eq'.mp hζ
  have hroot : chosenSimpleKummerRoot F n hnF b =
      algebraMap F (SeparableClosure F) (ζ : F) * φ (β : L) :=
    (congrArg Units.val hmul).symm
  refine ⟨⟨ζ, hζpow⟩, hroot, ?_⟩
  change IntermediateField.adjoin F {chosenSimpleKummerRoot F n hnF b} ≤ φ.fieldRange
  apply IntermediateField.adjoin_le_iff.mpr
  intro x hx
  obtain rfl := Set.mem_singleton_iff.mp hx
  rw [hroot]
  exact φ.fieldRange.mul_mem (φ.fieldRange.algebraMap_mem (ζ : F))
    (AlgHom.mem_fieldRange.mpr ⟨(β : L), rfl⟩)

end KummerTheory
