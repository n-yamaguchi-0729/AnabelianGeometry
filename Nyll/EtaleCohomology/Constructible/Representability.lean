/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.EtaleCohomology.Constructible.AffineRepresentability
public import Nyll.EtaleCohomology.Constructible.FiniteEtaleSheaf
public import Nyll.EtaleCohomology.Constructible.FiniteLocallyConstantSet
public import Nyll.EtaleCohomology.Constructible.GluedRepresentability
public import Nyll.EtaleCohomology.Constructible.LocalRepresenterGluing
public import Nyll.EtaleCohomology.Sites.EtaleRestriction
public import Nyll.SchemeTheory.Pi1.FiniteEtale.Basic
public import Mathlib.AlgebraicGeometry.AffineScheme
public import Mathlib.AlgebraicGeometry.Cover.Directed
public import Mathlib.AlgebraicGeometry.Sites.Etale
public import Mathlib.CategoryTheory.Functor.FullyFaithful
public import Mathlib.CategoryTheory.Sites.Sheaf
public import Mathlib.CategoryTheory.Yoneda

/-!
# Finite étale representability of finite locally constant sheaves

Every finite locally constant sheaf of sets on the small étale site of an
arbitrary scheme is represented by a finite étale scheme. Restricting to the
directed affine open cover supplies affine representers by effective descent.
Their canonical gluing represents the original sheaf.

No connectedness, quasi-compactness, quasi-separatedness, or ground field
hypothesis is imposed on the base. The result also gives an actual isomorphism
with the sheaf associated to the finite étale representer.
-/

@[expose] public section

noncomputable section

universe u

open AlgebraicGeometry CategoryTheory

namespace EtaleCohomology

/-- Every finite locally constant sheaf on an arbitrary scheme has a finite
étale representer, obtained by gluing its affine representers. -/
theorem IsEtaleFiniteLocallyConstantSet.exists_representer
    {X : Scheme.{u}} {G : Sheaf X.smallEtaleTopology (Type u)}
    (hG : IsEtaleFiniteLocallyConstantSet G) :
    ∃ Z : FiniteEtale X,
      Nonempty (G.obj.RepresentableBy ((finiteEtaleToEtale X).obj Z)) := by
  have hl (i : X.directedAffineCover.I₀) :
      ∃ W : FiniteEtale (X.directedAffineCover.X i),
        Nonempty (((etalePostcompose (X.directedAffineCover.f i)).op ⋙ G.obj).RepresentableBy
          ((finiteEtaleToEtale (X.directedAffineCover.X i)).obj W)) := by
    have : IsAffine (X.directedAffineCover.X i) := i.2
    have hi : IsEtaleFiniteLocallyConstantSet
        ((etaleRestriction (X.directedAffineCover.f i) (Type u)).obj G) :=
      (hG.pullback (X.directedAffineCover.f i)).of_iso
        ((etaleSetPullbackRestrictionIso (X.directedAffineCover.f i)).app G)
    exact hi.exists_affine_representer
  let W : ∀ i : X.directedAffineCover.I₀, FiniteEtale (X.directedAffineCover.X i) :=
    fun i => Classical.choose (hl i)
  let h (i : X.directedAffineCover.I₀) :
      ((etalePostcompose (X.directedAffineCover.f i)).op ⋙ G.obj).RepresentableBy
        ((finiteEtaleToEtale (X.directedAffineCover.X i)).obj (W i)) :=
    Classical.choice (Classical.choose_spec (hl i))
  exact ⟨etaleGluedLocalRepresenter G X.directedAffineCover W h,
    ⟨etaleGluedLocalRepresentable G X.directedAffineCover W h⟩⟩

/-- A finite locally constant sheaf is isomorphic to the actual sheaf of
sections of a finite étale scheme over its base. -/
theorem IsEtaleFiniteLocallyConstantSet.exists_finiteEtaleSheaf_iso
    {X : Scheme.{u}} {G : Sheaf X.smallEtaleTopology (Type u)}
    (hG : IsEtaleFiniteLocallyConstantSet G) :
    ∃ Z : FiniteEtale X, Nonempty ((finiteEtaleSheaf X).obj Z ≅ G) := by
  obtain ⟨Z, ⟨hZ⟩⟩ := hG.exists_representer
  exact ⟨Z, ⟨(fullyFaithfulSheafToPresheaf X.smallEtaleTopology (Type u)).preimageIso
    hZ.toIso⟩⟩

end EtaleCohomology
