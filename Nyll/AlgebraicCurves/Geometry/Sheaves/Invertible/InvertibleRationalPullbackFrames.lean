/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.AlgebraicCurves.Geometry.Sheaves.Invertible.InvertibleRationalFrames
public import Nyll.SchemeTheory.FunctionFields.Functoriality
public import Nyll.SchemeTheory.FunctionFields.StalkFunctoriality
public import Nyll.SchemeTheory.Modules.Frames.Frames
public import Nyll.SchemeTheory.Modules.Frames.IsFrameOnPullbackLocalSection
public import Nyll.SchemeTheory.Modules.Functoriality.PullbackLocalSection
public import Nyll.SchemeTheory.Modules.Invertible.Invertible
public import Mathlib.Algebra.Group.Basic
public import Mathlib.Topology.Irreducible

/-!
# Actual rational values of pulled-back frames

For a dominant morphism of integral schemes, the chosen rational
realization of a pulled-back invertible module differs from the
pulled-back original realization by one global rational unit. The
comparison is proved on actual local frames: both values change by
the same original regular transition unit, using the original
function-field map and its compatibility with germs.
-/

@[expose] public section

noncomputable section

universe u

open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace

namespace AlgebraicGeometry.Scheme.Modules

variable {X Y : Scheme.{u}} [IsIntegral X] [IsIntegral Y]
  {L : X.Modules} (hL : IsInvertible L) (f : Y ⟶ X) (hf : DenseRange f)

private def pullbackFrameRationalRatio
    (U : X.Opens) [Nonempty U] [Nonempty (f ⁻¹ᵁ U)]
    (s : Γ(L, U)) (hs : IsFrameOn s U) : Y.functionFieldˣ :=
  (hL.pullback f).frameRationalUnit (f ⁻¹ᵁ U)
      (pullbackLocalSection f s) (hs.pullbackLocalSection f) /
    Units.map (f.functionFieldMap hf).toMonoidHom (hL.frameRationalUnit U s hs)

private theorem pullbackFrameRationalRatio_change
    (U : X.Opens) [Nonempty U] [Nonempty (f ⁻¹ᵁ U)]
    (s t : Γ(L, U)) (hs : IsFrameOn s U) (ht : IsFrameOn t U) :
    pullbackFrameRationalRatio hL f hf U t ht =
      pullbackFrameRationalRatio hL f hf U s hs := by
  obtain ⟨a, ha⟩ := frameSection_unit_smul hs ht
  let A := Units.map (X.germToFunctionField U).hom.toMonoidHom a
  let b := Units.map (f.app U).hom.toMonoidHom a
  let B := Units.map (Y.germToFunctionField (f ⁻¹ᵁ U)).hom.toMonoidHom b
  have hfield : Units.map (f.functionFieldMap hf).toMonoidHom A = B := by
    apply Units.ext
    exact DFunLike.congr_fun (f.functionFieldMap_comp_germToFunctionField hf U) a.val
  have h₁ : hL.frameRationalUnit U t ht = A * hL.frameRationalUnit U s hs :=
    hL.frameRationalUnit_of_unit_smul U s t hs ht a ha
  have hb : b.val • pullbackLocalSection f s = pullbackLocalSection f t := by
    change f.app U a.val • pullbackLocalSection f s = pullbackLocalSection f t
    exact (pullbackLocalSection_smul f a.val s).symm.trans
      (congrArg (pullbackLocalSection f) ha)
  have h₂ : (hL.pullback f).frameRationalUnit (f ⁻¹ᵁ U)
        (pullbackLocalSection f t) (ht.pullbackLocalSection f) =
      B * (hL.pullback f).frameRationalUnit (f ⁻¹ᵁ U)
        (pullbackLocalSection f s) (hs.pullbackLocalSection f) :=
    (hL.pullback f).frameRationalUnit_of_unit_smul (f ⁻¹ᵁ U)
      (pullbackLocalSection f s) (pullbackLocalSection f t)
      (hs.pullbackLocalSection f) (ht.pullbackLocalSection f) b hb
  unfold pullbackFrameRationalRatio
  rw [h₁, h₂, map_mul, hfield, mul_div_mul_left_eq_div]

private theorem pullbackFrameRationalRatio_restrict
    {U V : X.Opens} [Nonempty U] [Nonempty V]
    [Nonempty (f ⁻¹ᵁ U)] [Nonempty (f ⁻¹ᵁ V)] (h : V ≤ U)
    (s : Γ(L, U)) (hs : IsFrameOn s U) :
    pullbackFrameRationalRatio hL f hf V (L.presheaf.map (homOfLE h).op s)
        ((hs.map (homOfLE h)).mono h) =
      pullbackFrameRationalRatio hL f hf U s hs := by
  apply Units.ext
  simp only [pullbackFrameRationalRatio, Units.val_div_eq_div_val, Units.coe_map]
  change (hL.pullback f).functionFieldHom (f ⁻¹ᵁ V)
      (pullbackLocalSection f (L.presheaf.map (homOfLE h).op s)) /
        f.functionFieldMap hf (hL.functionFieldHom V (L.presheaf.map (homOfLE h).op s)) =
    (hL.pullback f).functionFieldHom (f ⁻¹ᵁ U) (pullbackLocalSection f s) /
      f.functionFieldMap hf (hL.functionFieldHom U s)
  rw [← map_homOfLE_pullbackLocalSection,
    (hL.pullback f).functionFieldHom_restrict, hL.functionFieldHom_restrict]

private theorem pullbackFrameRationalRatio_independent
    (U V : X.Opens) [Nonempty U] [Nonempty V]
    [Nonempty (f ⁻¹ᵁ U)] [Nonempty (f ⁻¹ᵁ V)]
    (s : Γ(L, U)) (t : Γ(L, V)) (hs : IsFrameOn s U) (ht : IsFrameOn t V) :
    pullbackFrameRationalRatio hL f hf U s hs =
      pullbackFrameRationalRatio hL f hf V t ht := by
  obtain ⟨x⟩ := (show Nonempty (f ⁻¹ᵁ U) from inferInstance)
  obtain ⟨y⟩ := (show Nonempty (f ⁻¹ᵁ V) from inferInstance)
  obtain ⟨z, hz⟩ := nonempty_preirreducible_inter (f ⁻¹ᵁ U).isOpen (f ⁻¹ᵁ V).isOpen
    ⟨x.1, x.2⟩ ⟨y.1, y.2⟩
  have : Nonempty (f ⁻¹ᵁ (U ⊓ V)) := ⟨⟨z, hz⟩⟩
  have : Nonempty (U ⊓ V : X.Opens) := ⟨⟨f z, hz⟩⟩
  let a : U ⊓ V ≤ U := inf_le_left
  let b : U ⊓ V ≤ V := inf_le_right
  calc
    _ = pullbackFrameRationalRatio hL f hf (U ⊓ V)
        (L.presheaf.map (homOfLE a).op s) ((hs.map (homOfLE a)).mono a) :=
      (pullbackFrameRationalRatio_restrict hL f hf a s hs).symm
    _ = pullbackFrameRationalRatio hL f hf (U ⊓ V)
        (L.presheaf.map (homOfLE b).op t) ((ht.map (homOfLE b)).mono b) :=
      pullbackFrameRationalRatio_change hL f hf (U ⊓ V) _ _ _ _
    _ = _ := pullbackFrameRationalRatio_restrict hL f hf b t ht

/-- The original function-field pullback carries every local frame
value to the actual pulled frame value, up to one fixed global unit.
The nonempty inverse-image chart is the chart on which that frame is
evaluated; no frame compatibility is an additional input. -/
theorem IsInvertible.exists_unit_pullbackFrameRationalUnit_eq_mul :
    ∃ a : Y.functionFieldˣ,
      ∀ (U : X.Opens) [Nonempty U] [Nonempty (f ⁻¹ᵁ U)]
        (s : Γ(L, U)) (hs : IsFrameOn s U),
        (hL.pullback f).frameRationalUnit (f ⁻¹ᵁ U)
            (pullbackLocalSection f s) (hs.pullbackLocalSection f) =
          a * Units.map (f.functionFieldMap hf).toMonoidHom (hL.frameRationalUnit U s hs) := by
  obtain ⟨U, s, hxU, hs⟩ := hL.exists_frameSection (f (genericPoint Y))
  have : Nonempty U := ⟨⟨f (genericPoint Y), hxU⟩⟩
  have : Nonempty (f ⁻¹ᵁ U) := ⟨⟨genericPoint Y, hxU⟩⟩
  refine ⟨pullbackFrameRationalRatio hL f hf U s hs, ?_⟩
  intro V hV hpreV t ht
  have h := pullbackFrameRationalRatio_independent hL f hf V U t s ht hs
  exact div_eq_iff_eq_mul.mp h

end AlgebraicGeometry.Scheme.Modules
