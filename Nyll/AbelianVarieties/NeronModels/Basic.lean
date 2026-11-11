/-
Anthropic FLT source port.
Original copyright, authors, license and pinned sources are retained per unit below.
-/

module

public import Mathlib.AlgebraicGeometry.Morphisms.Separated
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.RingTheory.DedekindDomain.Basic
public import Mathlib.RingTheory.Localization.FractionRing
public import Nyll.SchemeTheory.BaseChange.SchemeHomOver

/-!
# The Néron mapping property

The property below uses actual morphisms over the base and their existing generic-fibre
restriction. A Néron model extends every generic-fibre morphism from a smooth test scheme
uniquely. The definition does not assert the existence of a model.
-/

@[expose] public section

section
/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted from:
https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/Definitions/Def_AlgebraicGeometry_NeronModelPropertyBundleCarrier.lean
Upstream NOTICE:
https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/NOTICE
Upstream per-file ATTRIBUTION:
https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace NeronModelInfra

variable (R K : Type u) [CommRing R] [Field K] [Algebra R K]
variable {X Y : Scheme.{u}}

/-- Every morphism from the generic fibre of a smooth test scheme extends uniquely. -/
def NeronUniqueExtension (f : X ⟶ Spec (CommRingCat.of R)) : Prop :=
  ∀ (T : Scheme.{u}) (t : T ⟶ Spec (CommRingCat.of R)), Smooth t →
    Function.Bijective (genericFibreRestrict R K f t)

/-- Geometric properties and the mapping property of an actual Néron model. -/
structure NeronModelPropertyBundle [IsDedekindDomain R] [IsFractionRing R K]
    (f : X ⟶ Spec (CommRingCat.of R)) : Prop where
  /-- The model is smooth over the base. -/
  smooth : Smooth f
  /-- The model is separated over the base. -/
  separated : IsSeparated f
  /-- The model is locally of finite type over the base. -/
  locallyOfFiniteType : LocallyOfFiniteType f
  /-- The model is quasi-compact over the base. -/
  quasiCompact : QuasiCompact f
  /-- Restriction to the generic fibre is bijective on every smooth test scheme. -/
  neronMapping : NeronUniqueExtension R K f

section Extension

variable {R K}
variable [IsDedekindDomain R] [IsFractionRing R K]
variable {f : X ⟶ Spec (CommRingCat.of R)}

/-- A generic-fibre morphism from a smooth test scheme has a unique extension. -/
theorem NeronModelPropertyBundle.existsUnique_extension
    (h : NeronModelPropertyBundle R K f) {T : Scheme.{u}}
    {t : T ⟶ Spec (CommRingCat.of R)} (ht : Smooth t)
    (v : SchemeHomOver (pullback.snd t (specGenericFibreInclusion R K))
      (pullback.snd f (specGenericFibreInclusion R K))) :
    ∃! φ : SchemeHomOver t f, genericFibreRestrict R K f t φ = v :=
  (h.neronMapping T t ht).existsUnique v

end Extension

section Restriction

variable {R K}

/-- Generic-fibre restriction is the usual map between the actual pullback schemes. -/
theorem genericFibreRestrict_coe_eq_pullbackMap
    (f : X ⟶ Spec (CommRingCat.of R)) (g : Y ⟶ Spec (CommRingCat.of R))
    (φ : SchemeHomOver g f)
    (eq₁ : g ≫ 𝟙 (Spec (CommRingCat.of R)) = φ.1 ≫ f)
    (eq₂ : specGenericFibreInclusion R K ≫ 𝟙 (Spec (CommRingCat.of R)) =
      𝟙 (Spec (CommRingCat.of K)) ≫ specGenericFibreInclusion R K) :
    (genericFibreRestrict R K f g φ).1 =
      pullback.map g (specGenericFibreInclusion R K) f (specGenericFibreInclusion R K)
        φ.1 (𝟙 (Spec (CommRingCat.of K))) (𝟙 (Spec (CommRingCat.of R))) eq₁ eq₂ :=
  fibreRestrictAlong_coe_eq_pullbackMap (specGenericFibreInclusion R K) f g φ eq₁ eq₂

end Restriction

/-- An isomorphism over the base has bijective restriction on relative morphisms. -/
theorem genericFibreRestrict_bijective_of_isIso
    (f : X ⟶ Spec (CommRingCat.of R)) [IsIso f]
    (g : Y ⟶ Spec (CommRingCat.of R)) :
    Function.Bijective (genericFibreRestrict R K f g) := by
  constructor
  · intro a b _
    exact (subsingleton_schemeHomOver_of_isIso g f).allEq a b
  · intro v
    obtain ⟨φ⟩ := nonempty_schemeHomOver_of_isIso g f
    exact ⟨φ, (subsingleton_schemeHomOver_of_isIso
      (pullback.snd g (specGenericFibreInclusion R K))
      (pullback.snd f (specGenericFibreInclusion R K))).allEq _ v⟩

/-- The mapping property holds for a scheme isomorphic to its base. -/
theorem neronUniqueExtension_of_isIso
    (f : X ⟶ Spec (CommRingCat.of R)) [IsIso f] :
    NeronUniqueExtension R K f :=
  fun _ t _ => genericFibreRestrict_bijective_of_isIso R K f t

end NeronModelInfra

end
end
