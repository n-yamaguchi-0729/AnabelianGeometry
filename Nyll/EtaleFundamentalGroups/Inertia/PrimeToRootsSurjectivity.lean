/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.EtaleFundamentalGroups.Inertia.PrimeToRootsInverseSystem
import Nyll.ProCGroups.InverseSystems.CofinalityAndDensity
import Mathlib.FieldTheory.IsAlgClosed.Basic
import Mathlib.RingTheory.RootsOfUnity.AlgebraicallyClosed

/-!
# Surjectivity of actual roots coordinates

Over an algebraically closed target field, each power transition and each
projection from the actual roots inverse limit is surjective.
-/

namespace EtaleFundamentalGroups.Inertia

open ProCGroups.InverseSystems

theorem rootsOfUnityPowerTransition_surjective
    (E : Type*) [Field E] [IsAlgClosed E]
    {m n : ℕ} (h : m ∣ n) (hm : 0 < m) (hn : 0 < n) :
    Function.Surjective (rootsOfUnityPowerTransition E h) := by
  intro ζ
  have hdiv : 0 < n / m := Nat.div_pos (Nat.le_of_dvd hn h) hm
  obtain ⟨z, hz⟩ := IsAlgClosed.exists_pow_nat_eq (((ζ : Eˣ) : E)) hdiv
  have hzn : z ^ n = 1 := by
    calc
      z ^ n = (z ^ (n / m)) ^ m := by
        rw [← pow_mul, Nat.div_mul_cancel h]
      _ = (((ζ : Eˣ) : E)) ^ m := by rw [hz]
      _ = 1 := (mem_rootsOfUnity' m (ζ : Eˣ)).mp ζ.property
  have : NeZero n := ⟨hn.ne'⟩
  refine ⟨rootsOfUnity.mkOfPowEq z hzn, ?_⟩
  apply rootsOfUnity.coe_injective
  change z ^ (n / m) = ((ζ : Eˣ) : E)
  exact hz

theorem primeToRoots_projection_surjective
    (k E : Type*) [Field k] [Field E] [IsAlgClosed E]
    (n : InvertibleExponent k) :
    Function.Surjective ((primeToRootsSystem k E).projection n) := by
  refine (primeToRootsSystem k E).surjective_π
    (InvertibleExponent.directed k) ?_ n
  intro m r h
  exact rootsOfUnityPowerTransition_surjective E
    (show m.val ∣ r.val from h)
    (InvertibleExponent.pos k m)
    (InvertibleExponent.pos k r)

/-- The existing inverse-limit group is commutative, with its original operations. -/
instance primeToRoots_inverseLimit_commGroup
    (k E : Type*) [Field k] [Field E] :
    CommGroup (primeToRootsSystem k E).inverseLimit where
  toGroup := inferInstance
  mul_comm := by
    intro x y
    apply (primeToRootsSystem k E).ext
    intro n
    change (x.val n : rootsOfUnity n.val E) * (y.val n : rootsOfUnity n.val E) =
      (y.val n : rootsOfUnity n.val E) * (x.val n : rootsOfUnity n.val E)
    exact @mul_comm (rootsOfUnity n.val E) inferInstance (x.val n) (y.val n)

/-- A third root detects a swap even in a two-label reduced boundary group. -/
theorem exists_third_root_ne_one
    (E : Type*) [Field E] [CharZero E] [IsAlgClosed E] :
    ∃ η : rootsOfUnity 3 E, η ^ 3 = 1 ∧ η ≠ 1 ∧ η ^ 2 ≠ 1 := by
  obtain ⟨ζ, hζ⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot E 3
  let η : rootsOfUnity 3 E := hζ.toRootsOfUnity
  have hη : IsPrimitiveRoot η 3 := by
    apply IsPrimitiveRoot.coe_submonoidClass_iff.mp
    apply IsPrimitiveRoot.coe_units_iff.mp
    exact hζ
  exact ⟨η, hη.pow_eq_one, hη.ne_one (by decide),
    hη.pow_ne_one_of_pos_of_lt (by decide : 2 ≠ 0) (by decide : 2 < 3)⟩

end EtaleFundamentalGroups.Inertia
