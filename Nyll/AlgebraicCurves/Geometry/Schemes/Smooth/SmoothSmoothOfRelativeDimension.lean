/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_AlgebraicGeometry_Smooth_exists_smoothOfRelativeDimension_of_preconnectedSpace.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

module

public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Nyll.SchemeTheory.Morphisms.SmoothDimensionCharts
public import Mathlib.AlgebraicGeometry.Morphisms.RingHomProperties
public import Mathlib.RingTheory.Smooth.StandardSmoothCotangent
public import Mathlib.Tactic.Algebraize

/-!
# Smooth exists smooth Of Relative Dimension of preconnected Space
-/

@[expose] public section

section ProofImplementation

namespace AlgebraicCurves.Geometry.Schemes.Proofs
namespace Smooth_exists_smoothOfRelativeDimension_of_preconnectedSpace

universe u

namespace R1NeronObjE7

open AlgebraicGeometry CategoryTheory RingHom

section descend

variable {P : ∀ {R S : Type u} [CommRing R] [CommRing S], (R →+* S) → Prop}

theorem appLE_basicOpen_basicOpen
    (hPa : StableUnderCompositionWithLocalizationAwayTarget P) (hPl : LocalizationAwayPreserves P)
    {X Y : Scheme.{u}} (f : X ⟶ Y) (U : Y.affineOpens) (V : X.affineOpens)
    (e : V.1 ≤ f ⁻¹ᵁ U.1) (h : P (f.appLE U V e).hom)
    (r : Γ(Y, U)) (s : Γ(X, X.basicOpen (f.appLE U V e r)))
    (e' : X.basicOpen s ≤ f ⁻¹ᵁ Y.basicOpen r) :
    P (f.appLE (Y.basicOpen r) (X.basicOpen s) e').hom :=
  _root_.AlgebraicGeometry.SmoothDimensionCharts.appLE_basicOpen_basicOpen
    (P := P) hPa hPl f U V e h r s e'

end descend

theorem eq_of_isStandardSmoothOfRelativeDimension_appLE {X Y : Scheme.{u}} (f : X ⟶ Y) (x : X)
    {n n' : ℕ}
    (U : Y.affineOpens) (V : X.affineOpens) (hx : x ∈ V.1) (e : V.1 ≤ f ⁻¹ᵁ U.1)
    (h : (f.appLE U V e).hom.IsStandardSmoothOfRelativeDimension n)
    (U' : Y.affineOpens) (V' : X.affineOpens) (hx' : x ∈ V'.1) (e' : V'.1 ≤ f ⁻¹ᵁ U'.1)
    (h' : (f.appLE U' V' e').hom.IsStandardSmoothOfRelativeDimension n') : n = n' :=
  _root_.AlgebraicGeometry.SmoothDimensionCharts.eq_of_isStandardSmoothOfRelativeDimension_appLE
    f x U V hx e h U' V' hx' e' h'

theorem exists_chart {X Y : Scheme.{u}} (f : X ⟶ Y) [Smooth f] (x : X) :
    ∃ (n : ℕ) (U : Y.affineOpens) (V : X.affineOpens) (_ : x ∈ V.1) (e : V.1 ≤ f ⁻¹ᵁ U.1),
      (f.appLE U V e).hom.IsStandardSmoothOfRelativeDimension n :=
  _root_.AlgebraicGeometry.SmoothDimensionCharts.exists_chart f x

theorem exists_smoothOfRelativeDimension_of_preconnectedSpace {X Y : Scheme.{u}} (f : X ⟶ Y)
    [Smooth f] [PreconnectedSpace X] : ∃ n : ℕ, SmoothOfRelativeDimension n f := by
  rcases isEmpty_or_nonempty X with hX | ⟨⟨x₀⟩⟩
  · exact ⟨0, ⟨fun x => (IsEmpty.false x).elim⟩⟩
  obtain ⟨n₀, U₀, V₀, hx₀, e₀, h₀⟩ := exists_chart f x₀
  let S : Set X := {x | ∃ (U : Y.affineOpens) (V : X.affineOpens) (_ : x ∈ V.1)
    (e : V.1 ≤ f ⁻¹ᵁ U.1), (f.appLE U V e).hom.IsStandardSmoothOfRelativeDimension n₀}
  have hSopen : IsOpen S := by
    rw [isOpen_iff_forall_mem_open]
    rintro x ⟨U, V, hxV, e, h⟩
    exact ⟨V.1, fun y hy => ⟨U, V, hy, e, h⟩, V.1.isOpen, hxV⟩
  have hSclosed : IsClosed S := by
    rw [← isOpen_compl_iff, isOpen_iff_forall_mem_open]
    intro x hxS
    obtain ⟨m, U, V, hxV, e, h⟩ := exists_chart f x
    refine ⟨V.1, fun y hy hyS => ?_, V.1.isOpen, hxV⟩
    obtain ⟨U', V', hyV', e', h'⟩ := hyS
    have hm : m = n₀ :=
      eq_of_isStandardSmoothOfRelativeDimension_appLE f y U V hy e h U' V' hyV' e' h'
    subst hm
    exact hxS ⟨U, V, hxV, e, h⟩
  have hS : S = Set.univ := IsClopen.eq_univ ⟨hSclosed, hSopen⟩ ⟨x₀, U₀, V₀, hx₀, e₀, h₀⟩
  refine ⟨n₀, ⟨fun x => ?_⟩⟩
  have hxS : x ∈ S := hS ▸ Set.mem_univ x
  obtain ⟨U, V, hxV, e, h⟩ := hxS
  exact ⟨U.1, U.2, V.1, V.2, hxV, e, h⟩

end R1NeronObjE7

open AlgebraicGeometry CategoryTheory in
theorem _root_.AlgebraicGeometry.Smooth.exists_smoothOfRelativeDimension_of_preconnectedSpace
    {X Y : Scheme.{u}} (f : X ⟶ Y) [Smooth f] [PreconnectedSpace X] :
    ∃ n : ℕ, SmoothOfRelativeDimension n f :=
  R1NeronObjE7.exists_smoothOfRelativeDimension_of_preconnectedSpace f
end Smooth_exists_smoothOfRelativeDimension_of_preconnectedSpace
end AlgebraicCurves.Geometry.Schemes.Proofs
end ProofImplementation
