/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Mathlib.AlgebraicGeometry.GammaSpecAdjunction
public import Mathlib.Algebra.Group.Units.Hom

/-!
# Evaluation of original unit sections at geometric points

Evaluation uses the actual scheme map on global sections followed by the
canonical Gamma-Spec isomorphism. Pullback and source field maps retain
their actual ring homomorphisms. These formulas will evaluate the root
section of an original finite étale representer.
-/

@[expose] public section

noncomputable section

universe u

open AlgebraicGeometry CategoryTheory

namespace EtaleFundamentalGroups.Cohomology

/-- The actual unit section evaluated at a field-valued point. -/
def geometricUnitEvaluation {X : Scheme.{u}} {Ω : Type u} [Field Ω]
    (ξ : Spec (.of Ω) ⟶ X) : (Γ(X, ⊤) : Type u)ˣ →* Ωˣ :=
  Units.map ((ξ.appTop ≫ (Scheme.ΓSpecIso (.of Ω)).hom).hom.toMonoidHom)

/-- Evaluation of an actual pulled-back unit equals evaluation at
the composite of the same original scheme maps. -/
theorem geometricUnitEvaluation_pullback {X Y : Scheme.{u}}
    {Ω : Type u} [Field Ω] (ξ : Spec (.of Ω) ⟶ X) (f : X ⟶ Y)
    (a : (Γ(Y, ⊤) : Type u)ˣ) :
    geometricUnitEvaluation ξ (Units.map f.appTop.hom.toMonoidHom a) =
      geometricUnitEvaluation (ξ ≫ f) a := by
  apply Units.ext
  rfl

/-- Changing the source field through its original spectrum map
acts on the evaluated unit through that same field homomorphism. -/
theorem geometricUnitEvaluation_specMap {X : Scheme.{u}}
    {Ω Ω' : Type u} [Field Ω] [Field Ω']
    (ξ : Spec (.of Ω) ⟶ X) (σ : Ω →+* Ω')
    (a : (Γ(X, ⊤) : Type u)ˣ) :
    geometricUnitEvaluation (Spec.map (CommRingCat.ofHom σ) ≫ ξ) a =
      Units.map σ.toMonoidHom (geometricUnitEvaluation ξ a) := by
  apply Units.ext
  change (Scheme.ΓSpecIso (.of Ω')).hom
      ((Spec.map (CommRingCat.ofHom σ)).appTop (ξ.appTop a.val)) =
    σ ((Scheme.ΓSpecIso (.of Ω)).hom (ξ.appTop a.val))
  exact ConcreteCategory.congr_hom
    (Scheme.ΓSpecIso_naturality (CommRingCat.ofHom σ)) (ξ.appTop a.val)

/-- A structural root of unity is evaluated through the original
structural map at the same field-valued point. -/
theorem geometricUnitEvaluation_structural
    {K Ω : Type u} [Field K] [Field Ω] {X : Scheme.{u}}
    (c : X ⟶ Spec (.of K)) (ξ : Spec (.of Ω) ⟶ X) (ζ : Kˣ) :
    geometricUnitEvaluation ξ
        (Units.map (((Scheme.ΓSpecIso (.of K)).inv ≫ c.appTop).hom.toMonoidHom) ζ) =
      Units.map (((Scheme.ΓSpecIso (.of K)).inv ≫ (ξ ≫ c).appTop ≫
        (Scheme.ΓSpecIso (.of Ω)).hom).hom.toMonoidHom) ζ := by
  apply Units.ext
  rfl

end EtaleFundamentalGroups.Cohomology
