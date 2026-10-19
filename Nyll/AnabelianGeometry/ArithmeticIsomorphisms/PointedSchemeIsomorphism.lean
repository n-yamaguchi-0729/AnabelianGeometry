/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.AnabelianGeometry.ArithmeticIsomorphisms.Basic
import Nyll.EtaleFundamentalGroups.GeometricFiber.ArithmeticNaturality
import Nyll.EtaleFundamentalGroups.GeometricFiber.CanonicalPointedMaps
import Nyll.EtaleFundamentalGroups.GeometricFiber.PullbackEquivalence

/-! # The arithmetic isomorphism induced by an actual pointed scheme isomorphism

The input is a scheme isomorphism over the field, with its equality on the
chosen geometric points. No equivalence of cover categories or compatibility
of induced fundamental groups is assumed: these are supplied by pullback.
-/

noncomputable section

open CategoryTheory AlgebraicGeometry

namespace AnabelianGeometry.ArithmeticIsomorphisms

universe u

variable (k κ : Type u) [Field k] [Field κ] [Algebra k κ] [IsSepClosure k κ]
  {X Y : Scheme.{u}} [ConnectedSpace X] [ConnectedSpace Y]
  (fX : X ⟶ Spec (.of k)) (fY : Y ⟶ Spec (.of k))
  {Ω : Type u} [Field Ω] [IsSepClosed Ω]
  (x : Spec (.of Ω) ⟶ X) (y : Spec (.of Ω) ⟶ Y)

/-- A pointed scheme isomorphism over k induces an actual continuous
isomorphism over the specified absolute Galois group. -/
def ofPointedSchemeIso (i : X ≅ Y) (hi : i.hom ≫ fY = fX)
    (hpoint : x ≫ i.hom = y) :
    OverQuotientEquiv
      (FiniteEtale.arithmeticFundamentalGroupHom k κ fX x).toMonoidHom
      (FiniteEtale.arithmeticFundamentalGroupHom k κ fY y).toMonoidHom := by
  subst y
  let E : FiniteEtale Y ≌ FiniteEtale X :=
    MorphismProperty.Over.pullbackIso (@IsFiniteEtale : MorphismProperty Scheme.{u}) ⊤ i.symm
  have : (FiniteEtale.pullback i.hom).IsEquivalence := E.isEquivalence_functor
  refine ⟨FiniteEtale.fundamentalGroupEquivOfPullbackEquivalence i.hom x, ?_⟩
  intro g
  change FiniteEtale.arithmeticFundamentalGroupHom k κ fY (x ≫ i.hom)
      (FiniteEtale.fundamentalGroupHom i.hom x g) =
    FiniteEtale.arithmeticFundamentalGroupHom k κ fX x g
  rw [FiniteEtale.arithmeticFundamentalGroupHom_comp, hi]

/-- The construction has the original pointed scheme-induced homomorphism as its map. -/
theorem ofPointedSchemeIso_apply (i : X ≅ Y) (hi : i.hom ≫ fY = fX)
    (hpoint : x ≫ i.hom = y) (g : Aut (FiniteEtale.fiber x)) :
    (ofPointedSchemeIso k κ fX fY x y i hi hpoint).1 g =
      FiniteEtale.pointedFundamentalGroupHom i.hom x y hpoint g := by
  subst y
  rfl

end AnabelianGeometry.ArithmeticIsomorphisms
