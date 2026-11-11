/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.AlgebraicCurves.Geometry.Sheaves.Invertible.InvertibleRationalFrames
public import Nyll.AlgebraicCurves.Geometry.Sheaves.Tensor.InvertibleTensor
public import Nyll.SchemeTheory.Modules.Frames.Frames
public import Nyll.SchemeTheory.Modules.Tensor.TensorFrames
public import Nyll.SchemeTheory.Modules.Tensor.TensorSections
public import Mathlib.Algebra.Group.Basic
public import Mathlib.Topology.Irreducible

/-!
# Actual rational values of tensor frames

The rational realization of a tensor product and the product of the
two original rational realizations differ by one global rational unit.
This is proved on actual local frames: both expressions transform by
the same product of regular transition units, and their restrictions
retain the same original function-field values. The conclusion is an
identity of actual rational units before taking any cohomology.
-/

@[expose] public section

noncomputable section

universe u

open AlgebraicGeometry CategoryTheory MonoidalCategory Opposite TopologicalSpace

namespace AlgebraicGeometry.Scheme.Modules

variable {X : Scheme.{u}} {L M : X.Modules}

/-- Two actual invertible modules have genuine section frames on a
common neighborhood of every point. -/
theorem IsInvertible.exists_common_frameSections
    (hL : IsInvertible L) (hM : IsInvertible M) (x : X) :
    ∃ (U : X.Opens) (s : Γ(L, U)) (t : Γ(M, U)),
      x ∈ U ∧ IsFrameOn s U ∧ IsFrameOn t U := by
  obtain ⟨U, s, hxU, hs⟩ := hL.exists_frameSection x
  obtain ⟨V, t, hxV, ht⟩ := hM.exists_frameSection x
  exact ⟨U ⊓ V, L.presheaf.map (homOfLE inf_le_left).op s,
    M.presheaf.map (homOfLE inf_le_right).op t, ⟨hxU, hxV⟩,
    (hs.map (homOfLE inf_le_left)).mono inf_le_left,
    (ht.map (homOfLE inf_le_right)).mono inf_le_right⟩

variable [IsIntegral X] (hL : IsInvertible L) (hM : IsInvertible M)

private def tensorFrameRationalRatio (U : X.Opens) [Nonempty U]
    (s : Γ(L, U)) (t : Γ(M, U)) (hs : IsFrameOn s U) (ht : IsFrameOn t U) :
    X.functionFieldˣ :=
  (hL.tensor hM).frameRationalUnit U (tensorSections s t) (hs.tensorSections ht) /
    (hL.frameRationalUnit U s hs * hM.frameRationalUnit U t ht)

private theorem tensorFrameRationalRatio_change
    (U : X.Opens) [Nonempty U] (s s' : Γ(L, U)) (t t' : Γ(M, U))
    (hs : IsFrameOn s U) (hs' : IsFrameOn s' U)
    (ht : IsFrameOn t U) (ht' : IsFrameOn t' U) :
    tensorFrameRationalRatio hL hM U s' t' hs' ht' =
      tensorFrameRationalRatio hL hM U s t hs ht := by
  obtain ⟨a, ha⟩ := frameSection_unit_smul hs hs'
  obtain ⟨b, hb⟩ := frameSection_unit_smul ht ht'
  let A := Units.map (X.germToFunctionField U).hom.toMonoidHom a
  let B := Units.map (X.germToFunctionField U).hom.toMonoidHom b
  have h₁ : hL.frameRationalUnit U s' hs' = A * hL.frameRationalUnit U s hs :=
    hL.frameRationalUnit_of_unit_smul U s s' hs hs' a ha
  have h₂ : hM.frameRationalUnit U t' ht' = B * hM.frameRationalUnit U t ht :=
    hM.frameRationalUnit_of_unit_smul U t t' ht ht' b hb
  have h₃ : (hL.tensor hM).frameRationalUnit U (tensorSections s' t')
        (hs'.tensorSections ht') =
      (A * B) * (hL.tensor hM).frameRationalUnit U (tensorSections s t)
        (hs.tensorSections ht) := by
    apply Units.ext
    change (hL.tensor hM).functionFieldHom U (tensorSections s' t') =
      (algebraMap Γ(X, U) X.functionField a.val *
        algebraMap Γ(X, U) X.functionField b.val) *
          (hL.tensor hM).functionFieldHom U (tensorSections s t)
    rw [← ha, ← hb, tensorSections_smul_left, tensorSections_smul_right,
      (hL.tensor hM).functionFieldHom_smul, (hL.tensor hM).functionFieldHom_smul,
      mul_assoc]
  unfold tensorFrameRationalRatio
  rw [h₁, h₂, h₃,
    mul_mul_mul_comm A (hL.frameRationalUnit U s hs) B (hM.frameRationalUnit U t ht),
    mul_div_mul_left_eq_div]

private theorem tensorFrameRationalRatio_restrict
    {U V : X.Opens} [Nonempty U] [Nonempty V] (h : V ≤ U)
    (s : Γ(L, U)) (t : Γ(M, U)) (hs : IsFrameOn s U) (ht : IsFrameOn t U) :
    tensorFrameRationalRatio hL hM V
        (L.presheaf.map (homOfLE h).op s) (M.presheaf.map (homOfLE h).op t)
        ((hs.map (homOfLE h)).mono h) ((ht.map (homOfLE h)).mono h) =
      tensorFrameRationalRatio hL hM U s t hs ht := by
  apply Units.ext
  simp only [tensorFrameRationalRatio, Units.val_div_eq_div_val, Units.val_mul]
  change (hL.tensor hM).functionFieldHom V
      (tensorSections (L.presheaf.map (homOfLE h).op s)
        (M.presheaf.map (homOfLE h).op t)) /
      (hL.functionFieldHom V (L.presheaf.map (homOfLE h).op s) *
        hM.functionFieldHom V (M.presheaf.map (homOfLE h).op t)) =
    (hL.tensor hM).functionFieldHom U (tensorSections s t) /
      (hL.functionFieldHom U s * hM.functionFieldHom U t)
  rw [← map_tensorSections, (hL.tensor hM).functionFieldHom_restrict,
    hL.functionFieldHom_restrict, hM.functionFieldHom_restrict]

private theorem tensorFrameRationalRatio_independent
    (U V : X.Opens) [Nonempty U] [Nonempty V]
    (s : Γ(L, U)) (t : Γ(M, U)) (s' : Γ(L, V)) (t' : Γ(M, V))
    (hs : IsFrameOn s U) (ht : IsFrameOn t U)
    (hs' : IsFrameOn s' V) (ht' : IsFrameOn t' V) :
    tensorFrameRationalRatio hL hM U s t hs ht =
      tensorFrameRationalRatio hL hM V s' t' hs' ht' := by
  obtain ⟨x⟩ := (show Nonempty U from inferInstance)
  obtain ⟨y⟩ := (show Nonempty V from inferInstance)
  obtain ⟨z, hz⟩ := nonempty_preirreducible_inter U.isOpen V.isOpen
    ⟨x.1, x.2⟩ ⟨y.1, y.2⟩
  have : Nonempty (U ⊓ V : X.Opens) := ⟨⟨z, hz⟩⟩
  let a : U ⊓ V ≤ U := inf_le_left
  let b : U ⊓ V ≤ V := inf_le_right
  calc
    _ = tensorFrameRationalRatio hL hM (U ⊓ V)
        (L.presheaf.map (homOfLE a).op s) (M.presheaf.map (homOfLE a).op t)
        ((hs.map (homOfLE a)).mono a) ((ht.map (homOfLE a)).mono a) :=
      (tensorFrameRationalRatio_restrict hL hM a s t hs ht).symm
    _ = tensorFrameRationalRatio hL hM (U ⊓ V)
        (L.presheaf.map (homOfLE b).op s') (M.presheaf.map (homOfLE b).op t')
        ((hs'.map (homOfLE b)).mono b) ((ht'.map (homOfLE b)).mono b) :=
      tensorFrameRationalRatio_change hL hM (U ⊓ V) _ _ _ _ _ _ _ _
    _ = _ := tensorFrameRationalRatio_restrict hL hM b s' t' hs' ht'

/-- The actual tensor-frame rational value is the product of the two
original frame values times one original global rational unit. -/
theorem IsInvertible.exists_unit_tensorFrameRationalUnit_eq_mul :
    ∃ a : X.functionFieldˣ,
      ∀ (U : X.Opens) [Nonempty U] (s : Γ(L, U)) (t : Γ(M, U))
        (hs : IsFrameOn s U) (ht : IsFrameOn t U),
        (hL.tensor hM).frameRationalUnit U (tensorSections s t) (hs.tensorSections ht) =
          a * (hL.frameRationalUnit U s hs * hM.frameRationalUnit U t ht) := by
  obtain ⟨U, s, t, hxU, hs, ht⟩ :=
    hL.exists_common_frameSections hM (genericPoint X)
  have : Nonempty U := ⟨⟨genericPoint X, hxU⟩⟩
  refine ⟨tensorFrameRationalRatio hL hM U s t hs ht, ?_⟩
  intro V hV s' t' hs' ht'
  have h := tensorFrameRationalRatio_independent hL hM V U s' t' s t hs' ht' hs ht
  exact div_eq_iff_eq_mul.mp h

end AlgebraicGeometry.Scheme.Modules
