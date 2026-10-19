/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.AnabelianGeometry.GeometricFundamentalGroup.FiniteConstantField
import Mathlib.FieldTheory.IntermediateField.Adjoin.Defs
import Mathlib.FieldTheory.Galois.GaloisClosure
import Mathlib.FieldTheory.RatFunc.AsPolynomial

/-! # A rational coordinate over a finite field of constants

If a finitely generated original field becomes rational after an algebraic
Galois extension of constants, a finite Galois extension already contains a
rational coordinate and all coefficients needed to express the original
field generators. The resulting equality is in the original ambient field.
-/

noncomputable section

namespace AnabelianGeometry.GeometricFundamentalGroup

/-- A geometric rational coordinate generates the actual original function
field after some finite Galois extension of constants. The two inclusions are
proved using finite supports of the coordinate and of the original generators. -/
theorem exists_finiteGalois_rational_coordinate_compositum
    (k K F : Type*) [Field k] [Field K] [Field F]
    [Algebra k K] [IsGalois k K] [Algebra K F] [Algebra k F]
    [IsScalarTower k K F]
    (A : IntermediateField k F) (hA : A.FG)
    (hgen : IntermediateField.adjoin A (Set.range (algebraMap K F)) = ⊤)
    (z : F) (hz : IntermediateField.adjoin K ({z} : Set F) = ⊤) :
    ∃ E : FiniteGaloisIntermediateField k K,
      A ⊔ IntermediateField.adjoin k
          ((algebraMap K F) '' (E.toIntermediateField : Set K)) =
        IntermediateField.adjoin k ({z} : Set F) ⊔
          IntermediateField.adjoin k
            ((algebraMap K F) '' (E.toIntermediateField : Set K)) := by
  classical
  let Z : IntermediateField k F := IntermediateField.adjoin k ({z} : Set F)
  have hzgen : IntermediateField.adjoin Z (Set.range (algebraMap K F)) = ⊤ := by
    apply top_unique
    intro x _hx
    have hx : x ∈ IntermediateField.adjoin K ({z} : Set F) := by
      rw [hz]
      exact IntermediateField.mem_top
    refine IntermediateField.adjoin_induction K (p := fun x _ =>
      x ∈ IntermediateField.adjoin Z (Set.range (algebraMap K F)))
      ?_ ?_ ?_ ?_ ?_ hx
    · intro x hx
      have hxs : x = z := Set.mem_singleton_iff.mp hx
      subst x
      exact (IntermediateField.adjoin Z (Set.range (algebraMap K F))).algebraMap_mem
        ⟨z, IntermediateField.mem_adjoin_simple_self k z⟩
    · intro a
      exact IntermediateField.subset_adjoin Z _ ⟨a, rfl⟩
    · intro x y _hx _hy hx hy
      exact IntermediateField.add_mem _ hx hy
    · intro x _hx hx
      exact IntermediateField.inv_mem _ hx
    · intro x y _hx _hy hx hy
      exact IntermediateField.mul_mem _ hx hy
  obtain ⟨T, hT⟩ := hA
  obtain ⟨E₁, hE₁⟩ := exists_finiteGalois_constants_of_adjoin_eq_top
    k K A F hgen {z}
  obtain ⟨E₂, hE₂⟩ := exists_finiteGalois_constants_of_adjoin_eq_top
    k K Z F hzgen T
  let E : FiniteGaloisIntermediateField k K := E₁ ⊔ E₂
  have h₁ : E₁.toIntermediateField ≤ E.toIntermediateField :=
    (FiniteGaloisIntermediateField.le_iff E₁ E).mp le_sup_left
  have h₂ : E₂.toIntermediateField ≤ E.toIntermediateField :=
    (FiniteGaloisIntermediateField.le_iff E₂ E).mp le_sup_right
  let C : IntermediateField k F := IntermediateField.adjoin k
    ((algebraMap K F) '' (E.toIntermediateField : Set K))
  have hzE : z ∈ IntermediateField.adjoin A
      ((algebraMap K F) '' (E.toIntermediateField : Set K)) :=
    IntermediateField.adjoin.mono A _ _ (Set.image_mono h₁)
      (hE₁ z (Finset.mem_singleton_self z))
  have hzAC : z ∈ A ⊔ C := by
    have hmem : z ∈ (IntermediateField.adjoin A
        ((algebraMap K F) '' (E.toIntermediateField : Set K))).restrictScalars k := hzE
    rw [IntermediateField.restrictScalars_adjoin_eq_sup] at hmem
    exact hmem
  have hAZC : A ≤ Z ⊔ C := by
    rw [← hT]
    apply IntermediateField.adjoin_le_iff.mpr
    intro x hx
    have hmem : x ∈ (IntermediateField.adjoin Z
        ((algebraMap K F) '' (E.toIntermediateField : Set K))).restrictScalars k :=
      IntermediateField.adjoin.mono Z _ _ (Set.image_mono h₂) (hE₂ x hx)
    rw [IntermediateField.restrictScalars_adjoin_eq_sup] at hmem
    exact hmem
  refine ⟨E, le_antisymm (sup_le hAZC le_sup_right) ?_⟩
  exact sup_le (IntermediateField.adjoin_simple_le_iff.mpr hzAC) le_sup_right

/-- The splitting field can be chosen to contain any prescribed finite
Galois field of constants, for example the fields of definition of punctures. -/
theorem exists_finiteGalois_rational_coordinate_compositum_above
    (k K F : Type*) [Field k] [Field K] [Field F]
    [Algebra k K] [IsGalois k K] [Algebra K F] [Algebra k F]
    [IsScalarTower k K F]
    (A : IntermediateField k F) (hA : A.FG)
    (hgen : IntermediateField.adjoin A (Set.range (algebraMap K F)) = ⊤)
    (z : F) (hz : IntermediateField.adjoin K ({z} : Set F) = ⊤)
    (D : FiniteGaloisIntermediateField k K) :
    ∃ E : FiniteGaloisIntermediateField k K, D ≤ E ∧
      A ⊔ IntermediateField.adjoin k
          ((algebraMap K F) '' (E.toIntermediateField : Set K)) =
        IntermediateField.adjoin k ({z} : Set F) ⊔
          IntermediateField.adjoin k
            ((algebraMap K F) '' (E.toIntermediateField : Set K)) := by
  obtain ⟨E₀, hE₀⟩ := exists_finiteGalois_rational_coordinate_compositum
    k K F A hA hgen z hz
  let E : FiniteGaloisIntermediateField k K := E₀ ⊔ D
  let C₀ : IntermediateField k F := IntermediateField.adjoin k
    ((algebraMap K F) '' (E₀.toIntermediateField : Set K))
  let C : IntermediateField k F := IntermediateField.adjoin k
    ((algebraMap K F) '' (E.toIntermediateField : Set K))
  have hC : C₀ ≤ C := IntermediateField.adjoin.mono k _ _ (Set.image_mono
    ((FiniteGaloisIntermediateField.le_iff E₀ E).mp le_sup_left))
  refine ⟨E, le_sup_right, ?_⟩
  change A ⊔ C = IntermediateField.adjoin k ({z} : Set F) ⊔ C
  calc
    A ⊔ C = (A ⊔ C₀) ⊔ C := by rw [sup_assoc, sup_of_le_right hC]
    _ = (IntermediateField.adjoin k ({z} : Set F) ⊔ C₀) ⊔ C :=
      congrArg (fun T : IntermediateField k F => T ⊔ C) hE₀
    _ = IntermediateField.adjoin k ({z} : Set F) ⊔ C := by
      rw [sup_assoc, sup_of_le_right hC]

/-- The finite split field is the actual subfield E(z) of the original
geometric function field, isomorphic to RatFunc E. Its underlying k-subfield
is exactly the compositum of E and the original finitely generated field. -/
theorem exists_finiteGalois_ratFunc_coordinate_above
    (k K F : Type*) [Field k] [Field K] [Field F]
    [Algebra k K] [IsGalois k K] [Algebra K F] [Algebra k F]
    [IsScalarTower k K F]
    (A : IntermediateField k F) (hA : A.FG)
    (hgen : IntermediateField.adjoin A (Set.range (algebraMap K F)) = ⊤)
    (z : F) (htr : Transcendental K z)
    (hz : IntermediateField.adjoin K ({z} : Set F) = ⊤)
    (D : FiniteGaloisIntermediateField k K) :
    ∃ E : FiniteGaloisIntermediateField k K, D ≤ E ∧
      Nonempty (RatFunc E ≃ₐ[E] IntermediateField.adjoin E ({z} : Set F)) ∧
      (IntermediateField.adjoin E ({z} : Set F)).restrictScalars k =
        A ⊔ IntermediateField.adjoin k
          ((algebraMap K F) '' (E.toIntermediateField : Set K)) := by
  obtain ⟨E, hDE, hE⟩ := exists_finiteGalois_rational_coordinate_compositum_above
    k K F A hA hgen z hz D
  let j : E →ₐ[k] F := IsScalarTower.toAlgHom k E F
  have hC : j.fieldRange = IntermediateField.adjoin k
      ((algebraMap K F) '' (E.toIntermediateField : Set K)) := by
    have himage : (algebraMap K F) '' (E.toIntermediateField : Set K) =
        (j.fieldRange : Set F) := by
      ext x
      constructor
      · rintro ⟨a, ha, rfl⟩
        exact ⟨⟨a, ha⟩, rfl⟩
      · rintro ⟨a, rfl⟩
        exact ⟨a.val, a.property, rfl⟩
    rw [himage, IntermediateField.adjoin_self]
  have hmap : algebraMap E F = (algebraMap j.fieldRange F) ∘ j.equivFieldRange := rfl
  have hrestrict := IntermediateField.restrictScalars_adjoin_of_algEquiv
    (F := k) (E := F) j.equivFieldRange hmap ({z} : Set F)
  rw [IntermediateField.restrictScalars_adjoin_eq_sup, hC] at hrestrict
  refine ⟨E, hDE, ⟨RatFunc.algEquivOfTranscendental z (htr.of_tower_top E)⟩, ?_⟩
  exact hrestrict.trans ((sup_comm _ _).trans hE.symm)

/-- Without a prescribed lower bound, some finite Galois constant field
already realizes the rational coordinate and the original compositum. -/
theorem exists_finiteGalois_ratFunc_coordinate
    (k K F : Type*) [Field k] [Field K] [Field F]
    [Algebra k K] [IsGalois k K] [Algebra K F] [Algebra k F]
    [IsScalarTower k K F]
    (A : IntermediateField k F) (hA : A.FG)
    (hgen : IntermediateField.adjoin A (Set.range (algebraMap K F)) = ⊤)
    (z : F) (htr : Transcendental K z)
    (hz : IntermediateField.adjoin K ({z} : Set F) = ⊤) :
    ∃ E : FiniteGaloisIntermediateField k K,
      Nonempty (RatFunc E ≃ₐ[E] IntermediateField.adjoin E ({z} : Set F)) ∧
      (IntermediateField.adjoin E ({z} : Set F)).restrictScalars k =
        A ⊔ IntermediateField.adjoin k
          ((algebraMap K F) '' (E.toIntermediateField : Set K)) := by
  obtain ⟨E, _hbot, hE⟩ := exists_finiteGalois_ratFunc_coordinate_above
    k K F A hA hgen z htr hz ⊥
  exact ⟨E, hE⟩

end AnabelianGeometry.GeometricFundamentalGroup
