/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.EtaleFundamentalGroups.Inertia.PrimeToRootsCommonUnit
import Nyll.AnabelianGeometry.CuspidalInertia.BoundaryCommonCoefficient

/-! # A common finite unit on actual boundary characters -/

noncomputable section

namespace AnabelianGeometry.CuspidalInertia
open EtaleFundamentalGroups.Inertia

/-- Inertia range correspondence and the actual diagonal relations force
one unit power on the restriction of EVERY finite root character at EVERY
cusp. Neither a common parameter automorphism nor an exponent is assumed. -/
theorem exists_common_unit_on_boundary_characters
    {ι B C : Type*} [Fintype ι] [CommGroup B] [CommGroup C]
    (k E : Type*) [Field k] [Field E] [CharZero E] [IsAlgClosed E]
    (b : ι → (primeToRootsSystem k E).inverseLimit →* B)
    (c : ι → (primeToRootsSystem k E).inverseLimit →* C)
    (hb : ∀ i, Function.Injective (b i))
    (hc : ∀ i, Function.Injective (c i))
    (α : B ≃* C)
    (hrange : ∀ i, (b i).range.map α.toMonoidHom = (c i).range)
    (hsource : ∀ t, (∏ i, b i t) = 1)
    (htarget : ∀ u : ι → (primeToRootsSystem k E).inverseLimit,
      (∏ i, c i (u i)) = 1 → ∀ i j, u i = u j)
    (i₀ : ι) (n : InvertibleExponent k) :
    ∃ u : (ZMod n.val)ˣ,
      ∀ (i : ι) (χ : C →* rootsOfUnity n.val E)
        (t : (primeToRootsSystem k E).inverseLimit),
        χ (α (b i t)) = χ (c i t) ^ (u : ZMod n.val).val := by
  obtain ⟨β, hβ⟩ := exists_common_parameter_equiv_of_diagonal_relations
    b c hb hc α hrange hsource htarget i₀
  obtain ⟨u, hu⟩ := exists_unit_power_of_primeToRoots_equiv k E n β
  refine ⟨u, ?_⟩
  intro i χ t
  rw [hβ]
  have hpow (a : rootsOfUnity n.val E) : a ^ n.val = 1 :=
    Subtype.ext ((mem_rootsOfUnity n.val a.val).mp a.property)
  exact primeToRoots_character_scalar_of_projection n (χ.comp (c i)) hpow
    β (u : ZMod n.val).val t (hu t)

end AnabelianGeometry.CuspidalInertia
