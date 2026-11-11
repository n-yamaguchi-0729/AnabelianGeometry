/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.EtaleCohomology.Sites.EtaleRestriction
public import Nyll.EtaleCohomology.Sites.EtaleSlice
public import Nyll.EtaleFundamentalGroups.Cohomology.IntegralAffineEtaleBasis
public import Mathlib.AlgebraicGeometry.Sites.Etale
public import Mathlib.CategoryTheory.MorphismProperty.Comma
public import Mathlib.RingTheory.DedekindDomain.Basic

/-!
# Integral affine covers retained in the original small site

An object mapping to a Dedekind chart has an integral affine open cover.
The covering arrows below remain objects and arrows of the original small
étale site. This permits sheaf separatedness to compare chart maps without
changing the original source object.
-/

@[expose] public section

noncomputable section

universe u

open AlgebraicGeometry CategoryTheory

namespace EtaleCohomology

/-- Pull the integral affine neighborhoods of a Dedekind chart back to
the original site, keeping their actual open immersion maps. -/
theorem exists_integral_affine_etale_cover_of_dedekind_chart
    (R : Type u) [CommRing R] [IsDedekindDomain R]
    {X : Scheme.{u}} (i : Spec (CommRingCat.of R) ⟶ X) [Etale i]
    (V : X.Etale) (m : V ⟶ Scheme.Etale.mk i) :
    ∃ (A : V.left → X.Etale) (l : ∀ x, A x ⟶ V),
      (∀ x, IsAffine (A x).left ∧ IsIntegral (A x).left) ∧
        Sieve.ofArrows A l ∈ X.smallEtaleTopology V := by
  classical
  let V' := (etaleSliceEquiv (Scheme.Etale.mk i)).functor.obj (Over.mk m)
  let W (x : V.left) : V.left.Opens :=
    Classical.choose (exists_integral_affine_etale_neighborhood R V' x)
  have hW (x : V.left) :
      IsAffineOpen (W x) ∧ x ∈ W x ∧ IsIntegral (W x : Scheme) :=
    Classical.choose_spec (exists_integral_affine_etale_neighborhood R V' x)
  let A (x : V.left) : X.Etale := Scheme.Etale.mk ((W x).ι ≫ V.hom)
  let l (x : V.left) : A x ⟶ V :=
    MorphismProperty.Over.homMk (W x).ι rfl
  refine ⟨A, l, fun x => ⟨(hW x).1, (hW x).2.2⟩, ?_⟩
  rw [Scheme.ofArrows_mem_smallEtaleTopology_iff]
  ext y
  simp only [Set.mem_iUnion, Set.mem_range, Set.mem_univ, iff_true]
  exact ⟨y, ⟨y, (hW y).2.1⟩, rfl⟩

end EtaleCohomology
