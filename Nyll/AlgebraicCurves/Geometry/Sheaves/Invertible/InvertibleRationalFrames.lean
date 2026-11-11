/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.AlgebraicCurves.Geometry.Sheaves.Invertible.InvertibleFunctionFieldPresentation
public import Nyll.SchemeTheory.Modules.Frames.FrameFromTrivialization
public import Nyll.SchemeTheory.Modules.Frames.FrameLocality
public import Nyll.SchemeTheory.Modules.Frames.Frames
public import Nyll.SchemeTheory.Modules.Invertible.Invertible
public import Mathlib.AlgebraicGeometry.FunctionField

/-!
# Actual rational values of local line-bundle frames

The existing function-field presentation theorem supplies an injective
rational realization of every original invertible module. Its genuine
local frames have nonzero rational values. A change of frame multiplies
the value by the germ of the original regular transition unit. These
identities provide the local input for native generic-unit gluing.
-/

@[expose] public section

noncomputable section

universe u

open AlgebraicGeometry CategoryTheory Opposite

namespace AlgebraicGeometry.Scheme.Modules

variable {X : Scheme.{u}} {M : X.Modules}

/-- A frame on its own open gives the actual free rank-one coordinate
map on sections of that open. -/
theorem frameSection_bijective {U : X.Opens} {s : Γ(M, U)}
    (hs : IsFrameOn s U) : Function.Bijective (fun a : Γ(X, U) => a • s) := by
  have hid : M.presheaf.map (homOfLE (le_refl U)).op s = s := by
    rw [show homOfLE (le_refl U) = 𝟙 U from Subsingleton.elim _ _,
      op_id, M.presheaf.map_id]
    rfl
  simpa only [hid] using hs (le_refl U) (le_refl U)

/-- An actual frame is nonzero whenever the open has a nontrivial
ring of regular functions. -/
theorem frameSection_ne_zero {U : X.Opens} [Nontrivial Γ(X, U)]
    {s : Γ(M, U)} (hs : IsFrameOn s U) : s ≠ 0 := by
  intro hz
  apply (zero_ne_one : (0 : Γ(X, U)) ≠ 1)
  apply (frameSection_bijective hs).1
  change (0 : Γ(X, U)) • s = (1 : Γ(X, U)) • s
  rw [hz, smul_zero, smul_zero]

/-- Two actual frames differ by a genuine unit of the original
section ring. -/
theorem frameSection_unit_smul {U : X.Opens} {s t : Γ(M, U)}
    (hs : IsFrameOn s U) (ht : IsFrameOn t U) :
    ∃ a : (Γ(X, U) : Type u)ˣ, a.val • s = t := by
  obtain ⟨a, ha, h⟩ := hs.exists_isUnit_smul_eq ht (le_refl U) (le_refl U)
  have hid (m : Γ(M, U)) : M.presheaf.map (homOfLE (le_refl U)).op m = m := by
    rw [show homOfLE (le_refl U) = 𝟙 U from Subsingleton.elim _ _,
      op_id, M.presheaf.map_id]
    rfl
  rw [hid s, hid t] at h
  obtain ⟨b, hb⟩ := ha
  exact ⟨b, by simpa only [hb] using h⟩

/-- The original local trivializations supply actual section frames
around every point. -/
theorem IsInvertible.exists_frameSection (hM : IsInvertible M) (x : X) :
    ∃ (U : X.Opens) (s : Γ(M, U)), x ∈ U ∧ IsFrameOn s U := by
  obtain ⟨U, hxU, ⟨e⟩⟩ := hM.exists_trivialization x
  obtain ⟨s, hs⟩ := exists_isFrameOn_of_pullback_iso_unit U e
  exact ⟨U, s, hxU, hs⟩

variable [IsIntegral X]

/-- A chosen realization furnished by the original existence theorem.
It is a map of actual module sections into the original function field. -/
def IsInvertible.functionFieldHom (hM : IsInvertible M) (U : X.Opens) :
    Γ(M, U) →+ (X.functionField : Type u) :=
  Classical.choose (IsInvertible.exists_functionField_presentation M hM) U

theorem IsInvertible.functionFieldHom_restrict (hM : IsInvertible M)
    {U V : X.Opens} [Nonempty V] (h : V ≤ U) (s : Γ(M, U)) :
    hM.functionFieldHom V (M.presheaf.map (homOfLE h).op s) =
      hM.functionFieldHom U s :=
  (Classical.choose_spec (IsInvertible.exists_functionField_presentation M hM)).1
    U V h inferInstance s

theorem IsInvertible.functionFieldHom_smul (hM : IsInvertible M)
    (U : X.Opens) [Nonempty U] (a : Γ(X, U)) (s : Γ(M, U)) :
    hM.functionFieldHom U (a • s) =
      algebraMap Γ(X, U) X.functionField a * hM.functionFieldHom U s :=
  (Classical.choose_spec (IsInvertible.exists_functionField_presentation M hM)).2.1 U a s

theorem IsInvertible.functionFieldHom_injective (hM : IsInvertible M)
    (U : X.Opens) [Nonempty U] : Function.Injective (hM.functionFieldHom U) :=
  (Classical.choose_spec (IsInvertible.exists_functionField_presentation M hM)).2.2
    U inferInstance

/-- The literal rational unit defined by a local frame in the original
function-field presentation. -/
def IsInvertible.frameRationalUnit (hM : IsInvertible M)
    (U : X.Opens) [Nonempty U] (s : Γ(M, U)) (hs : IsFrameOn s U) :
    X.functionFieldˣ :=
  Units.mk0 (hM.functionFieldHom U s) (by
    intro h
    exact frameSection_ne_zero hs
      (hM.functionFieldHom_injective U (h.trans (map_zero _).symm)))

/-- Restricting an actual frame leaves its original rational unit
unchanged. -/
theorem IsInvertible.frameRationalUnit_restrict (hM : IsInvertible M)
    {U V : X.Opens} [Nonempty U] [Nonempty V] (h : V ≤ U)
    (s : Γ(M, U)) (hs : IsFrameOn s U) :
    hM.frameRationalUnit V (M.presheaf.map (homOfLE h).op s)
        ((hs.map (homOfLE h)).mono h) = hM.frameRationalUnit U s hs := by
  apply Units.ext
  exact hM.functionFieldHom_restrict h s

/-- A specified regular change of frame multiplies the actual
rational value by the germ of that same unit. -/
theorem IsInvertible.frameRationalUnit_of_unit_smul (hM : IsInvertible M)
    (U : X.Opens) [Nonempty U] (s t : Γ(M, U))
    (hs : IsFrameOn s U) (ht : IsFrameOn t U)
    (a : (Γ(X, U) : Type u)ˣ) (ha : a.val • s = t) :
    hM.frameRationalUnit U t ht =
      Units.map (X.germToFunctionField U).hom.toMonoidHom a *
        hM.frameRationalUnit U s hs := by
  apply Units.ext
  change hM.functionFieldHom U t =
    algebraMap Γ(X, U) X.functionField a.val * hM.functionFieldHom U s
  rw [← ha, hM.functionFieldHom_smul]

/-- The actual transition of two frames is the germ of a regular unit,
before taking any generic-unit quotient. -/
theorem IsInvertible.frameRationalUnit_transition (hM : IsInvertible M)
    (U : X.Opens) [Nonempty U] (s t : Γ(M, U))
    (hs : IsFrameOn s U) (ht : IsFrameOn t U) :
    ∃ a : (Γ(X, U) : Type u)ˣ,
      hM.frameRationalUnit U t ht =
        Units.map (X.germToFunctionField U).hom.toMonoidHom a *
          hM.frameRationalUnit U s hs := by
  obtain ⟨a, ha⟩ := frameSection_unit_smul hs ht
  exact ⟨a, hM.frameRationalUnit_of_unit_smul U s t hs ht a ha⟩

end AlgebraicGeometry.Scheme.Modules
