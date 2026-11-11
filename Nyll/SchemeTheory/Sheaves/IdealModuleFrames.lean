/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.SchemeTheory.Modules.Frames.Frames
public import Nyll.SchemeTheory.Sheaves.IdealModuleLocalGenerators
public import Nyll.SchemeTheory.Sheaves.IdealSheafDataRangeModuleIotaAppInjective
public import Mathlib.RingTheory.Ideal.Span

/-!
# Actual ideal generators furnished by module frames

The original inclusion of an ideal module identifies its affine section
image with the original ideal. Hence any genuine frame of that module
on an affine open supplies a generator of the same original ideal.
-/

@[expose] public section

noncomputable section

universe u

open AlgebraicGeometry CategoryTheory Opposite

namespace AlgebraicGeometry.Scheme.IdealSheafData

/-- The actual regular function underlying an ideal-module frame
generates the original affine ideal. -/
theorem ideal_eq_span_moduleIota_of_frame
    {X : Scheme.{u}} (I : X.IdealSheafData) (U : X.affineOpens)
    (s : Γ(I.module, U.1)) (hs : Scheme.Modules.IsFrameOn s U.1) :
    I.ideal U = Ideal.span {show Γ(X, U.1) from I.moduleι.app U.1 s} := by
  have hid : I.module.presheaf.map (homOfLE (le_refl U.1)).op s = s := by
    rw [Subsingleton.elim (homOfLE (le_refl U.1)) (𝟙 U.1), op_id,
      I.module.presheaf.map_id]
    rfl
  have hsurj : Function.Surjective (fun a : Γ(X, U.1) => a • s) := by
    simpa only [hid] using (hs (le_refl U.1) (le_refl U.1)).2
  apply le_antisymm
  · intro y hy
    have hy' : y ∈ Set.range (I.moduleι.app U) := by
      rw [(I.range_moduleIota_app_and_injective U).1]
      exact hy
    obtain ⟨t, ht⟩ := hy'
    obtain ⟨a, ha⟩ := hsurj t
    refine Ideal.mem_span_singleton'.mpr ⟨a, ?_⟩
    calc
      a * (show Γ(X, U.1) from I.moduleι.app U.1 s) =
          (show Γ(X, U.1) from I.moduleι.app U.1 (a • s)) :=
        (Scheme.Modules.Hom.app_smul I.moduleι a s).symm
      _ = (show Γ(X, U.1) from I.moduleι.app U.1 t) :=
        congrArg (I.moduleι.app U.1) ha
      _ = y := ht
  · apply Ideal.span_le.mpr
    intro y hy
    rw [Set.mem_singleton_iff.mp hy]
    exact I.moduleIota_app_mem U s

end AlgebraicGeometry.Scheme.IdealSheafData
