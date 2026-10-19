/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.SchemeTheory.Morphisms.AlgebraicPointFiniteField
import Mathlib.FieldTheory.IntermediateField.Adjoin.Basic
import Mathlib.FieldTheory.Normal.Closure
import Mathlib.FieldTheory.Galois.Basic

/-! # A common finite Galois field for finitely many geometric points

The points themselves, including their maps to the original scheme, are
retained. Taking the normal closure of the compositum of their finite fields
of definition gives one finite Galois extension for all labels.
-/

noncomputable section

universe u v

open CategoryTheory AlgebraicGeometry

namespace AnabelianGeometry.GeometricFundamentalGroup

/-- Finitely many specified algebraic points are simultaneously defined over
one finite Galois intermediate field. In particular this applies to the
geometric points of a finite boundary on a smooth proper curve. -/
theorem exists_finiteGalois_field_of_point_family
    (k Ω : Type u) [Field k] [Field Ω] [Algebra k Ω] [IsGalois k Ω]
    {X : Scheme.{u}} (f : X ⟶ Spec (.of k))
    [LocallyOfFiniteType f] [IsSeparated f]
    {ι : Type v} [Finite ι]
    (p : ι → (Spec (.of Ω) ⟶ X))
    (hp : ∀ i, p i ≫ f = Spec.map (CommRingCat.ofHom (algebraMap k Ω))) :
    ∃ E : IntermediateField k Ω, Module.Finite k E ∧ IsGalois k E ∧
      ∃ q : ι → (Spec (.of E) ⟶ X),
        (∀ i, q i ≫ f = Spec.map (CommRingCat.ofHom (algebraMap k E))) ∧
        ∀ i, Spec.map (CommRingCat.ofHom E.val.toRingHom) ≫ q i = p i := by
  classical
  have hpoint (i : ι) :=
    exists_finite_intermediateField_point_factorization k Ω f (p i) (hp i)
  choose F hF q hq hpoint using hpoint
  let : ∀ i, Module.Finite k (F i) := hF
  let D : IntermediateField k Ω := ⨆ i, F i
  let : Module.Finite k D :=
    IntermediateField.finiteDimensional_iSup_of_finite
  let E : IntermediateField k Ω := IntermediateField.normalClosure k D Ω
  let : Module.Finite k E := normalClosure.is_finiteDimensional k D Ω
  let : IsGalois k E := IsGalois.normalClosure k D Ω
  have hFE (i : ι) : F i ≤ E :=
    (le_iSup F i).trans (IntermediateField.le_normalClosure D)
  let j (i : ι) : F i →ₐ[k] E := IntermediateField.inclusion (hFE i)
  let qE (i : ι) : Spec (.of E) ⟶ X :=
    Spec.map (CommRingCat.ofHom (j i).toRingHom) ≫ q i
  refine ⟨E, inferInstance, inferInstance, qE, ?_, ?_⟩
  · intro i
    change (Spec.map (CommRingCat.ofHom (j i).toRingHom) ≫ q i) ≫ f = _
    rw [Category.assoc, hq, ← Spec.map_comp]
    congr 1
  · intro i
    change Spec.map (CommRingCat.ofHom E.val.toRingHom) ≫
      (Spec.map (CommRingCat.ofHom (j i).toRingHom) ≫ q i) = p i
    rw [← Category.assoc, ← Spec.map_comp]
    exact hpoint i

end AnabelianGeometry.GeometricFundamentalGroup
