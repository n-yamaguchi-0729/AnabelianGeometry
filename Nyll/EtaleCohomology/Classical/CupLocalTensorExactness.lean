/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.EtaleCohomology.Classical.CupTensorSheaves
public import Nyll.EtaleCohomology.Classical.CupTensorAdditive
public import Nyll.EtaleCohomology.Sites.Stalks
public import Mathlib.Algebra.Category.ModuleCat.Projective
public import Mathlib.Algebra.Homology.ShortComplex.Exact
public import Mathlib.Algebra.Homology.ShortComplex.ShortExact
public import Mathlib.CategoryTheory.Monoidal.Closed.Braided
public import Mathlib.CategoryTheory.Monoidal.Functor
public import Mathlib.CategoryTheory.Monoidal.Preadditive
public import Mathlib.CategoryTheory.Sites.Point.Monoidal

/-!
# Actual tensor exactness for extensions of the constant unit

The original geometric stalk functors are monoidal for the original
sheafified tensor. Their native tensorators compare the stalk of each
tensor sequence with the tensor of its original stalk sequence.

A short exact sequence with the original constant regular sheaf as
quotient splits at every geometric stalk: the stalk of that quotient is
the regular coefficient module, which is projective. Tensor preserves
these actual split sequences, and the existing conservative geometric
stalk family detects their short exactness on the original site.

No flatness of an arbitrary coefficient sheaf or preservation of
arbitrary quasi-isomorphisms is assumed.
-/

@[expose] public section

noncomputable section

universe u

open AlgebraicGeometry CategoryTheory MonoidalCategory

namespace EtaleCohomology.ModuleTensor

variable (X : Scheme.{u}) (R : Type u) [CommRing R]

/-- The actual original geometric stalk has the native monoidal
structure of the corresponding point of the small étale site. -/
scoped instance residueStalkMonoidal (x : X) :
    (residueStalk X R x).Monoidal :=
  inferInstanceAs (GrothendieckTopology.Point.sheafFiber _).Monoidal

/-- The native tensorator compares left tensoring before and after
taking the actual original geometric stalk. -/
def residueStalkTensorLeftIso (x : X)
    (G : Sheaf X.smallEtaleTopology (ModuleCat.{u} R)) :
    residueStalk X R x ⋙ tensorLeft ((residueStalk X R x).obj G) ≅
      tensorLeft G ⋙ residueStalk X R x :=
  NatIso.ofComponents
    (fun F => Functor.Monoidal.μIso (residueStalk X R x) G F)
    (by
      intro F H f
      exact Functor.LaxMonoidal.μ_natural_right (residueStalk X R x) G f)

/-- The same original tensorator compares right tensoring with the
actual original geometric stalk. -/
def residueStalkTensorRightIso (x : X)
    (G : Sheaf X.smallEtaleTopology (ModuleCat.{u} R)) :
    residueStalk X R x ⋙ tensorRight ((residueStalk X R x).obj G) ≅
      tensorRight G ⋙ residueStalk X R x :=
  NatIso.ofComponents
    (fun F => Functor.Monoidal.μIso (residueStalk X R x) F G)
    (by
      intro F H f
      exact Functor.LaxMonoidal.μ_natural_left (residueStalk X R x) f G)

/-- Tensoring a short exact sequence whose original geometric quotient
stalks are projective preserves short exactness on the original site. -/
theorem tensorLeft_shortExact_of_projective_stalks
    {S : ShortComplex (Sheaf X.smallEtaleTopology (ModuleCat.{u} R))}
    (hS : S.ShortExact) (hP : ∀ x : X, Projective ((residueStalk X R x).obj S.X₃))
    (G : Sheaf X.smallEtaleTopology (ModuleCat.{u} R)) :
    (S.map (tensorLeft G)).ShortExact := by
  apply (shortExact_iff_residueStalk X R _).mpr
  intro x
  have : Projective ((S.map (residueStalk X R x)).X₃) := hP x
  let s := (hS.map_of_exact (residueStalk X R x)).splittingOfProjective
  exact ShortComplex.shortExact_of_iso
    (S.mapNatIso (residueStalkTensorLeftIso X R x G))
    (s.map (tensorLeft ((residueStalk X R x).obj G))).shortExact

/-- Right tensoring has the same actual exactness property, detected
by the original conservative geometric stalk family. -/
theorem tensorRight_shortExact_of_projective_stalks
    {S : ShortComplex (Sheaf X.smallEtaleTopology (ModuleCat.{u} R))}
    (hS : S.ShortExact) (hP : ∀ x : X, Projective ((residueStalk X R x).obj S.X₃))
    (G : Sheaf X.smallEtaleTopology (ModuleCat.{u} R)) :
    (S.map (tensorRight G)).ShortExact := by
  apply (shortExact_iff_residueStalk X R _).mpr
  intro x
  have : Projective ((S.map (residueStalk X R x)).X₃) := hP x
  let s := (hS.map_of_exact (residueStalk X R x)).splittingOfProjective
  exact ShortComplex.shortExact_of_iso
    (S.mapNatIso (residueStalkTensorRightIso X R x G))
    (s.map (tensorRight ((residueStalk X R x).obj G))).shortExact

/-- Every original extension with the regular constant sheaf as
quotient remains short exact after left tensoring by any original
coefficient sheaf. The required stalk projectivity is supplied here. -/
theorem tensorLeft_shortExact_of_unit_quotient
    {F E : Sheaf X.smallEtaleTopology (ModuleCat.{u} R)}
    (i : F ⟶ E) (p : E ⟶ 𝟙_ (Sheaf X.smallEtaleTopology (ModuleCat.{u} R)))
    (h : i ≫ p = 0) (hS : (ShortComplex.mk i p h).ShortExact)
    (G : Sheaf X.smallEtaleTopology (ModuleCat.{u} R)) :
    ((ShortComplex.mk i p h).map (tensorLeft G)).ShortExact := by
  refine tensorLeft_shortExact_of_projective_stalks X R hS ?_ G
  intro x
  exact Projective.of_iso (Functor.Monoidal.εIso (residueStalk X R x))
    (inferInstance : Projective (𝟙_ (ModuleCat.{u} R)))

/-- Every original extension with regular constant quotient remains
short exact after right tensoring by any original coefficient sheaf. -/
theorem tensorRight_shortExact_of_unit_quotient
    {F E : Sheaf X.smallEtaleTopology (ModuleCat.{u} R)}
    (i : F ⟶ E) (p : E ⟶ 𝟙_ (Sheaf X.smallEtaleTopology (ModuleCat.{u} R)))
    (h : i ≫ p = 0) (hS : (ShortComplex.mk i p h).ShortExact)
    (G : Sheaf X.smallEtaleTopology (ModuleCat.{u} R)) :
    ((ShortComplex.mk i p h).map (tensorRight G)).ShortExact := by
  refine tensorRight_shortExact_of_projective_stalks X R hS ?_ G
  intro x
  exact Projective.of_iso (Functor.Monoidal.εIso (residueStalk X R x))
    (inferInstance : Projective (𝟙_ (ModuleCat.{u} R)))

end EtaleCohomology.ModuleTensor
