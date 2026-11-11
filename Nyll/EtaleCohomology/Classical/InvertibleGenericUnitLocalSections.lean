/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.AlgebraicCurves.Geometry.Sheaves.Invertible.InvertibleRationalFrames
public import Nyll.EtaleCohomology.Classical.GenericUnitRationalSections
public import Nyll.EtaleCohomology.Classical.GenericUnitRegularOpenSections
public import Nyll.EtaleCohomology.Sites.ZariskiRestriction
public import Nyll.SchemeTheory.Modules.Frames.Frames
public import Mathlib.Topology.Irreducible

/-!
# Actual line-bundle frames in the original generic-unit quotient

Each genuine local frame of an original invertible module gives a
rational-unit quotient section. Changes of frame are the original
regular units, whose quotient sections vanish. Restriction and overlap
compatibility follow from the actual rational-frame formulas, so these
sections can be glued without any new cohomological comparison premise.
-/

@[expose] public section

noncomputable section

universe u

open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace
open Scheme.Modules

namespace EtaleCohomology

variable {X : Scheme.{u}} [IsIntegral X] {M : X.Modules}
  (hM : Scheme.Modules.IsInvertible M)

/-- The original quotient section of the literal rational value of
an actual local frame. -/
def invertibleFrameGenericUnitQuotient
    (U : X.Opens) [Nonempty U] (s : Γ(M, U)) (hs : IsFrameOn s U) :
    (etaleGenericUnitQuotient X).obj.obj (op ((zariskiToEtale X).obj U)) :=
  genericPointRationalUnitQuotientHom X ((zariskiToEtale X).obj U)
    (Additive.ofMul (hM.frameRationalUnit U s hs))

/-- The original restriction map takes an actual frame class to the
class of its actual restricted frame. -/
theorem invertibleFrameGenericUnitQuotient_restrict
    {U V : X.Opens} [Nonempty U] [Nonempty V] (h : V ≤ U)
    (s : Γ(M, U)) (hs : IsFrameOn s U) :
    (etaleGenericUnitQuotient X).obj.map
        ((zariskiToEtale X).map (homOfLE h)).op
          (invertibleFrameGenericUnitQuotient hM U s hs) =
      invertibleFrameGenericUnitQuotient hM V (M.presheaf.map (homOfLE h).op s)
        ((hs.map (homOfLE h)).mono h) := by
  change (etaleGenericUnitQuotient X).obj.map
      ((zariskiToEtale X).map (homOfLE h)).op
        (genericPointRationalUnitQuotientSection X ((zariskiToEtale X).obj U)
          (Additive.ofMul (hM.frameRationalUnit U s hs))) =
    genericPointRationalUnitQuotientSection X ((zariskiToEtale X).obj V)
      (Additive.ofMul (hM.frameRationalUnit V (M.presheaf.map (homOfLE h).op s)
        ((hs.map (homOfLE h)).mono h)))
  rw [genericPointRationalUnitQuotientSection_naturality,
    hM.frameRationalUnit_restrict]

/-- All actual frames on the same nonempty open define the same
original quotient section. -/
theorem invertibleFrameGenericUnitQuotient_eq
    (U : X.Opens) [Nonempty U] (s t : Γ(M, U))
    (hs : IsFrameOn s U) (ht : IsFrameOn t U) :
    invertibleFrameGenericUnitQuotient hM U s hs =
      invertibleFrameGenericUnitQuotient hM U t ht := by
  obtain ⟨a, ha⟩ := hM.frameRationalUnit_transition U s t hs ht
  unfold invertibleFrameGenericUnitQuotient
  rw [ha]
  change genericPointRationalUnitQuotientHom X ((zariskiToEtale X).obj U)
      (Additive.ofMul (hM.frameRationalUnit U s hs)) =
    genericPointRationalUnitQuotientHom X ((zariskiToEtale X).obj U)
      (Additive.ofMul (Units.map (X.germToFunctionField U).hom.toMonoidHom a) +
        Additive.ofMul (hM.frameRationalUnit U s hs))
  rw [map_add, genericPointRationalUnitQuotientHom_open_unit, zero_add]

/-- The actual local-frame sections are compatible on their original
open intersections. Integrality supplies the nonempty intersection. -/
theorem invertibleFrames_genericUnit_overlap
    (U V : X.Opens) [Nonempty U] [Nonempty V]
    (s : Γ(M, U)) (t : Γ(M, V)) (hs : IsFrameOn s U) (ht : IsFrameOn t V) :
    (etaleGenericUnitQuotient X).obj.map
        ((zariskiToEtale X).map (Opens.infLELeft U V)).op
          (invertibleFrameGenericUnitQuotient hM U s hs) =
      (etaleGenericUnitQuotient X).obj.map
        ((zariskiToEtale X).map (Opens.infLERight U V)).op
          (invertibleFrameGenericUnitQuotient hM V t ht) := by
  obtain ⟨x⟩ := (show Nonempty U from inferInstance)
  obtain ⟨y⟩ := (show Nonempty V from inferInstance)
  obtain ⟨z, hz⟩ := nonempty_preirreducible_inter U.isOpen V.isOpen
    ⟨x.1, x.2⟩ ⟨y.1, y.2⟩
  have : Nonempty (U ⊓ V : X.Opens) := ⟨⟨z, hz⟩⟩
  have hleft := invertibleFrameGenericUnitQuotient_restrict hM
    (U := U) (V := U ⊓ V) inf_le_left s hs
  have hright := invertibleFrameGenericUnitQuotient_restrict hM
    (U := V) (V := U ⊓ V) inf_le_right t ht
  refine (hleft.trans ?_).trans hright.symm
  exact invertibleFrameGenericUnitQuotient_eq hM (U ⊓ V) _ _ _ _

end EtaleCohomology
