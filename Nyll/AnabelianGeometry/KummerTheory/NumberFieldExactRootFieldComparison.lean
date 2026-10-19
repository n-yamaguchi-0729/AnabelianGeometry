/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.AnabelianGeometry.KummerTheory.PrimePowerCyclotomicDescent
import Nyll.AnabelianGeometry.KummerTheory.RootFieldPowerClasses
import Nyll.AnabelianGeometry.KummerTheory.NumberFieldPrimePowerSeparation
import Mathlib.RingTheory.RootsOfUnity.AlgebraicallyClosed
import Mathlib.Tactic

/-!
# Exact cyclic subgroup recovery from full root fields

Prime-power cyclotomic descent over a field containing a primitive fourth root,
followed by injective reflection from that finite base extension, recovers the
exact cyclic subgroup. This is the cyclic number-field specialization needed
for the cross-ratio endpoint, not the full finitely-generated-subgroup lemma.
-/

noncomputable section

namespace AnabelianGeometry.KummerTheory

section GoodBase

variable {K L : Type*} [Field K] [NumberField K]
    [Field L] [Algebra K L] [IsSepClosure K L] [IsAlgClosed L] [CharZero L]

/-- Equal full root fields give an exact relation modulo prime powers. -/
theorem exists_zpow_mul_primePower_of_rootField_eq_of_primitive_four
    (hfour : ∃ η : K, IsPrimitiveRoot η 4)
    {p r : ℕ} (hp : p.Prime) (a b : Kˣ)
    (h : rootField (L := L) (p ^ r) (a : K) =
      rootField (L := L) (p ^ r) (b : K)) :
    ∃ j : ℤ, ∃ d : Kˣ, b = a ^ j * d ^ (p ^ r) := by
  let n : ℕ+ := ⟨p ^ r, pow_pos hp.pos r⟩
  let : NeZero (p ^ r) := ⟨pow_ne_zero r hp.ne_zero⟩
  obtain ⟨ζ, hζ⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot L (p ^ r)
  let C : IntermediateField K L := IntermediateField.adjoin K {ζ}
  let : IsCyclotomicExtension {p ^ r} K C :=
    hζ.intermediateField_adjoin_isCyclotomicExtension K
  let : IsSepClosure C L := ⟨inferInstance, inferInstance⟩
  obtain ⟨η, hη⟩ := IsCyclotomicExtension.exists_isPrimitiveRoot
    (S := {p ^ r}) K C rfl (pow_ne_zero r hp.ne_zero)
  have hgen : Algebra.adjoin K ({η} : Set C) = ⊤ :=
    IsCyclotomicExtension.adjoin_primitive_root_eq_top hη
  have hmu : (primitiveRoots (n : ℕ) C).Nonempty :=
    ⟨η, (mem_primitiveRoots n.pos).mpr hη⟩
  have hn : ((n : ℕ) : C) ≠ 0 := Nat.cast_ne_zero.mpr n.ne_zero
  let f : Kˣ →* Cˣ := Units.map (algebraMap K C).toMonoidHom
  have hfields : rootField (L := L) n ((f a : Cˣ) : C) =
      rootField (L := L) n ((f b : Cˣ) : C) :=
    rootField_baseChange_eq C n (a : K) (b : K) h
  obtain ⟨j, c, hc⟩ := exists_zpow_mul_power_of_rootField_eq
    (L := L) n hn hmu (f a) (f b) hfields
  have hcPow : c ^ (n : ℕ) = f (b / a ^ j) := by
    rw [map_div, map_zpow, hc]
    simp only [mul_div_cancel_left]
  have hcRoot : (c : C) ^ (p ^ r) =
      algebraMap K C ((b / a ^ j : Kˣ) : K) := congrArg Units.val hcPow
  obtain ⟨d, hd⟩ := exists_primePower_root_in_base hp hη hgen
    (fun _ _ => hfour) ((b / a ^ j : Kˣ) : K) (c : C) hcRoot
  have hd0 : d ≠ 0 := by
    intro hd0
    apply (b / a ^ j).ne_zero
    rw [← hd, hd0, zero_pow (pow_ne_zero r hp.ne_zero)]
  let dU : Kˣ := Units.mk0 d hd0
  have hdU : dU ^ (p ^ r) = b / a ^ j := by
    apply Units.ext
    simpa [dU] using hd
  refine ⟨j, dU, ?_⟩
  rw [hdU]
  simp [div_eq_mul_inv, mul_left_comm]

/-- Prime-power full root fields recover the cyclic subgroup over a good base. -/
theorem zpowers_eq_of_primePower_rootFields_of_primitive_four
    (hfour : ∃ η : K, IsPrimitiveRoot η 4) (a b : Kˣ)
    (h : ∀ p : ℕ, p.Prime → ∀ r : ℕ,
      rootField (L := L) (p ^ r) (a : K) =
        rootField (L := L) (p ^ r) (b : K)) :
    Subgroup.zpowers a = Subgroup.zpowers b := by
  apply numberField_zpowers_eq_of_forall_sup_prime_powers_eq
  intro p hp r
  let P : Subgroup Kˣ := (powMonoidHom (α := Kˣ) (p ^ r)).range
  have hmem (x y : Kˣ)
      (hxy : rootField (L := L) (p ^ r) (x : K) =
        rootField (L := L) (p ^ r) (y : K)) :
      y ∈ Subgroup.zpowers x ⊔ P := by
    obtain ⟨j, d, hd⟩ :=
      exists_zpow_mul_primePower_of_rootField_eq_of_primitive_four hfour hp x y hxy
    apply Subgroup.mem_sup.mpr
    refine ⟨x ^ j, ?_, d ^ (p ^ r), ⟨d, rfl⟩, hd.symm⟩
    exact Subgroup.zpow_mem (Subgroup.zpowers x) (Subgroup.mem_zpowers x) j
  apply le_antisymm
  · exact sup_le (Subgroup.zpowers_le.mpr (hmem b a (h p hp r).symm)) le_sup_right
  · exact sup_le (Subgroup.zpowers_le.mpr (hmem a b (h p hp r))) le_sup_right

end GoodBase

/-- Cyclic subgroup equality reflects along an injective group homomorphism. -/
theorem zpowers_eq_of_injective_map
    {G H : Type*} [Group G] [Group H] (f : G →* H)
    (hf : Function.Injective f) (a b : G)
    (h : Subgroup.zpowers (f a) = Subgroup.zpowers (f b)) :
    Subgroup.zpowers a = Subgroup.zpowers b := by
  apply le_antisymm
  · apply Subgroup.zpowers_le.mpr
    have ha : f a ∈ Subgroup.zpowers (f b) := by
      rw [← h]
      exact Subgroup.mem_zpowers (f a)
    obtain ⟨j, hj⟩ := Subgroup.mem_zpowers_iff.mp ha
    apply Subgroup.mem_zpowers_iff.mpr
    refine ⟨j, hf ?_⟩
    simpa only [map_zpow] using hj
  · apply Subgroup.zpowers_le.mpr
    have hb : f b ∈ Subgroup.zpowers (f a) := by
      rw [h]
      exact Subgroup.mem_zpowers (f b)
    obtain ⟨j, hj⟩ := Subgroup.mem_zpowers_iff.mp hb
    apply Subgroup.mem_zpowers_iff.mpr
    refine ⟨j, hf ?_⟩
    simpa only [map_zpow] using hj

section NumberField

variable {K : Type*} [Field K] [NumberField K]

/-- Exact cyclic recovery over an arbitrary number field. -/
theorem numberField_zpowers_eq_of_forall_primePower_rootField_eq
    (a b : Kˣ)
    (h : ∀ p : ℕ, p.Prime → ∀ r : ℕ,
      rootField (L := AlgebraicClosure K) (p ^ r) (a : K) =
        rootField (L := AlgebraicClosure K) (p ^ r) (b : K)) :
    Subgroup.zpowers a = Subgroup.zpowers b := by
  let L := AlgebraicClosure K
  obtain ⟨ι, hι⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot L 4
  let F : IntermediateField K L := IntermediateField.adjoin K {ι}
  let : IsCyclotomicExtension {4} K F :=
    hι.intermediateField_adjoin_isCyclotomicExtension K
  let : FiniteDimensional K F := IsCyclotomicExtension.finiteDimensional {4} K F
  let : NumberField F := NumberField.of_module_finite K F
  let : IsSepClosure F L := ⟨inferInstance, inferInstance⟩
  have hfour : ∃ η : F, IsPrimitiveRoot η 4 :=
    IsCyclotomicExtension.exists_isPrimitiveRoot (S := {4}) K F rfl (by decide)
  let f : Kˣ →* Fˣ := Units.map (algebraMap K F).toMonoidHom
  have hfields : ∀ p : ℕ, p.Prime → ∀ r : ℕ,
      rootField (L := L) (p ^ r) ((f a : Fˣ) : F) =
        rootField (L := L) (p ^ r) ((f b : Fˣ) : F) := by
    intro p hp r
    exact rootField_baseChange_eq F (p ^ r) (a : K) (b : K) (h p hp r)
  have hcyclic : Subgroup.zpowers (f a) = Subgroup.zpowers (f b) :=
    zpowers_eq_of_primePower_rootFields_of_primitive_four
      (L := L) hfour (f a) (f b) hfields
  have hf : Function.Injective f := by
    intro x y hxy
    apply Units.ext
    apply (algebraMap K F).injective
    exact congrArg Units.val hxy
  exact zpowers_eq_of_injective_map f hf a b hcyclic

/-- All positive full root fields determine the exact cyclic subgroup, with torsion. -/
theorem numberField_zpowers_eq_of_forall_rootField_eq (a b : Kˣ)
    (h : ∀ n : ℕ+,
      rootField (L := AlgebraicClosure K) n (a : K) =
        rootField (L := AlgebraicClosure K) n (b : K)) :
    Subgroup.zpowers a = Subgroup.zpowers b := by
  apply numberField_zpowers_eq_of_forall_primePower_rootField_eq a b
  intro p hp r
  exact h ⟨p ^ r, pow_pos hp.pos r⟩

end NumberField

end AnabelianGeometry.KummerTheory
