/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.SchemeTheory.Divisors.SubschemeStalk

/-! # The support of an ideal sheaf detected by its actual stalk ideal -/

@[expose] public section

noncomputable section

universe u

open AlgebraicGeometry

namespace AlgebraicGeometry.Scheme.IdealSheafData

/-- An ideal sheaf is the unit ideal in the stalk precisely off its support. -/
theorem stalkIdeal_eq_top_iff_notMem_support {X : Scheme.{u}}
    (I : X.IdealSheafData) (x : X) : I.stalkIdeal x = ⊤ ↔ x ∉ I.support := by
  classical
  constructor
  · intro h hx
    have hle := I.stalkIdeal_le_maximalIdeal_of_mem_support x hx
    rw [h] at hle
    exact (IsLocalRing.maximalIdeal.isMaximal (X.presheaf.stalk x)).ne_top
      (top_le_iff.mp hle)
  · intro hx
    obtain ⟨U, hU, hxU, _⟩ :=
      exists_isAffineOpen_mem_and_subset (X := X) (U := ⊤) (x := x)
        (show x ∈ (⊤ : X.Opens) from trivial)
    have hn : x ∉ X.zeroLocus (U := U) (I.ideal ⟨U, hU⟩ : Set Γ(X, U)) := by
      intro hz
      exact hx ((Scheme.IdealSheafData.mem_support_iff_of_mem
        (I := I) (U := ⟨U, hU⟩) hxU).mpr hz)
    simp only [Scheme.mem_zeroLocus_iff, not_forall, not_not] at hn
    obtain ⟨f, hf, hxf⟩ := hn
    exact Ideal.eq_top_of_isUnit_mem _
      (I.map_ideal_le_stalkIdeal x ⟨U, hU⟩ hxU
        (Ideal.mem_map_of_mem (X.presheaf.germ U x hxU).hom hf))
      ((X.mem_basicOpen f x hxU).mp hxf)

end AlgebraicGeometry.Scheme.IdealSheafData
