/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.EtaleFundamentalGroups.GeometricFiber.FieldSourceGalois
public import Nyll.EtaleFundamentalGroups.GeometricFiber.GenericPointEssentialImage
public import Nyll.EtaleFundamentalGroups.Inertia.NormalSubgroupEmbeddings
public import Mathlib.AlgebraicGeometry.GammaSpecAdjunction
public import Mathlib.RingTheory.Etale.Field
public import Nyll.SchemeTheory.Pi1.FiniteEtale.Basic

/-!
# Finite subfields fixed by the generic Galois kernel

A finite subfield of the separable closure is fixed by the generic kernel
exactly when its spectrum occurs as the generic fiber of a finite étale cover.
The comparison uses the literal spectrum and postcomposition of field embeddings.
-/

@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.PreGaloisCategory
open scoped FintypeCatDiscrete

namespace AlgebraicGeometry.FiniteEtale

universe u

private theorem subfieldCover_essImage_iff (X : Scheme.{u})
    [IsIntegral X] [IsNormalIntegral X]
    (L : IntermediateField X.functionField (SeparableClosure X.functionField))
    [FiniteDimensional X.functionField L] :
    (pullback (X.fromSpecStalk (genericPoint X))).essImage
      (fieldSourceFiniteSubfieldCover X.functionField (SeparableClosure X.functionField) L) ↔
        (genericAbsoluteGaloisHom X).toMonoidHom.ker ≤ L.fixingSubgroup := by
  rw [genericPullback_obj_essImage_iff_ker_le_ker_ρAut]
  rw [← EtaleFundamentalGroups.normalSubgroup_fixes_embeddings_iff_le_fixingSubgroup]
  constructor
  · intro h g hg
    exact (fieldSourceSubfieldAction_ker_iff X.functionField
      (SeparableClosure X.functionField) L g).mp (h hg)
  · intro h g hg
    exact (fieldSourceSubfieldAction_ker_iff X.functionField
      (SeparableClosure X.functionField) L g).mpr (h g hg)

/-- A finite intermediate field is fixed by the generic Galois kernel
exactly when its literal spectrum is the generic fiber of a finite étale
cover. The cover and its generic-fiber isomorphism are actually constructed. -/
theorem genericKernel_le_fixingSubgroup_iff_exists_finiteEtale_genericFiber
    (X : Scheme.{u}) [IsIntegral X] [IsNormalIntegral X]
    (L : IntermediateField X.functionField (SeparableClosure X.functionField))
    [FiniteDimensional X.functionField L] :
    (genericAbsoluteGaloisHom X).toMonoidHom.ker ≤ L.fixingSubgroup ↔
      ∃ (Y : Scheme.{u}) (f : Y ⟶ X), IsFinite f ∧ Etale f ∧
        ∃ e : Limits.pullback f (X.fromSpecStalk (genericPoint X)) ≅ Spec (.of L),
          e.hom ≫ Spec.map (CommRingCat.ofHom (algebraMap X.functionField L)) =
            Limits.pullback.snd f (X.fromSpecStalk (genericPoint X)) := by
  rw [← subfieldCover_essImage_iff X L]
  constructor
  · rintro ⟨Z, ⟨e⟩⟩
    refine ⟨Z.left, Z.hom, inferInstance, inferInstance, ?_⟩
    exact ⟨((forget _).comp (Over.forget _)).mapIso e, e.hom.w⟩
  · rintro ⟨Y, f, hFinite, hEtale, e, he⟩
    let : IsFinite f := hFinite
    let : Etale f := hEtale
    let : IsFiniteEtale f := ⟨⟩
    exact ⟨FiniteEtale.mk f, ⟨MorphismProperty.Over.isoMk e he⟩⟩

end AlgebraicGeometry.FiniteEtale
