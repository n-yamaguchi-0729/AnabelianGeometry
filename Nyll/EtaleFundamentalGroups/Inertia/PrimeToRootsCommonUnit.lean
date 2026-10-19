/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/
import Nyll.EtaleFundamentalGroups.Inertia.PrimeToRootsCharacters
import Nyll.EtaleFundamentalGroups.Inertia.PrimeToRootsSurjectivity
import Nyll.GaloisCohomology.Kummer.Concrete.PrimitiveRootCoordinates
import Mathlib.Data.ZMod.Basic

/-! # Common finite unit powers of the actual inertia parameters -/

noncomputable section
namespace EtaleFundamentalGroups.Inertia
open ProCGroups.InverseSystems

/-- Every automorphism of the actual roots limit descends to an automorphism
of each finite roots coordinate. Kernel preservation is proved from the
existing nth-power kernel theorem, not supplied as compatibility data. -/
theorem exists_primeToRoots_projection_equiv
    (k E : Type*) [Field k] [Field E] [IsAlgClosed E]
    (n : InvertibleExponent k)
    (β : (primeToRootsSystem k E).inverseLimit ≃*
      (primeToRootsSystem k E).inverseLimit) :
    ∃ e : rootsOfUnity n.val E ≃* rootsOfUnity n.val E,
      ∀ t, e ((primeToRootsSystem k E).projection n t) =
        (primeToRootsSystem k E).projection n (β t) := by
  let T := (primeToRootsSystem k E).inverseLimit
  let U := rootsOfUnity n.val E
  let π : T →* U := projectionHom (primeToRootsSystem k E) n
  have hπ : Function.Surjective π := primeToRoots_projection_surjective k E n
  let s : U → T := fun a => (hπ a).choose
  have hs (a : U) : π (s a) = a := (hπ a).choose_spec
  have hpow (a : U) : a ^ n.val = 1 :=
    Subtype.ext ((mem_rootsOfUnity n.val a.val).mp a.property)
  let f : U → U := fun a => π (β (s a))
  let g : U → U := fun a => π (β.symm (s a))
  have hf (t : T) : f (π t) = π (β t) := by
    exact primeToRoots_character_eq_of_projection_eq n
      (π.comp β.toMonoidHom) hpow (hs (π t))
  have hg (t : T) : g (π t) = π (β.symm t) := by
    exact primeToRoots_character_eq_of_projection_eq n
      (π.comp β.symm.toMonoidHom) hpow (hs (π t))
  let e : U ≃* U :=
    { toFun := f
      invFun := g
      left_inv := by
        intro a
        obtain ⟨t, rfl⟩ := hπ a
        rw [hf, hg, β.symm_apply_apply]
      right_inv := by
        intro a
        obtain ⟨t, rfl⟩ := hπ a
        rw [hg, hf, β.apply_symm_apply]
      map_mul' := by
        intro a b
        obtain ⟨x, rfl⟩ := hπ a
        obtain ⟨y, rfl⟩ := hπ b
        rw [← π.map_mul, hf, β.map_mul, π.map_mul, hf, hf] }
  exact ⟨e, hf⟩

end EtaleFundamentalGroups.Inertia

namespace AnabelianGeometry.CuspidalInertia

/-- An additive automorphism of a finite cyclic coefficient ring determines
an invertible scalar; the scalar and its inverse are constructed from 1. -/
theorem exists_unit_mul_of_zmod_addEquiv (n : ℕ) [NeZero n]
    (e : ZMod n ≃+ ZMod n) :
    ∃ u : (ZMod n)ˣ, ∀ a : ZMod n, e a = (u : ZMod n) * a := by
  have he (a : ZMod n) : e a = a * e 1 := by
    calc
      e a = e (a.val • (1 : ZMod n)) := by
        rw [nsmul_eq_mul, ZMod.natCast_zmod_val, mul_one]
      _ = a.val • e 1 := map_nsmul e _ _
      _ = a * e 1 := by rw [nsmul_eq_mul, ZMod.natCast_zmod_val]
  have hinv : e.symm 1 * e 1 = 1 :=
    (he (e.symm 1)).symm.trans (e.apply_symm_apply 1)
  let u : (ZMod n)ˣ :=
    { val := e 1
      inv := e.symm 1
      val_inv := by rw [mul_comm]; exact hinv
      inv_val := hinv }
  exact ⟨u, fun a => (he a).trans (mul_comm _ _)⟩

/-- Finite roots coordinates identify the root group with additive Z/n. -/
def primitiveRootAddEquiv {E : Type*} [Field E] {n : ℕ} [NeZero n]
    {ζ : Eˣ} (hζ : IsPrimitiveRoot ζ n) :
    ZMod n ≃+ Additive (rootsOfUnity n E) := by
  let f : ZMod n →+ Additive (rootsOfUnity n E) :=
    { toFun := fun a => Additive.ofMul
        ⟨_root_.KummerTheory.primitiveRootCoordinate hζ a,
          (mem_rootsOfUnity n _).mpr
            (_root_.KummerTheory.primitiveRootCoordinate_pow_eq_one hζ a)⟩
      map_zero' := by
        apply Subtype.ext
        change _root_.KummerTheory.primitiveRootCoordinate hζ 0 = (1 : Eˣ)
        simpa only [Nat.cast_zero] using
          (_root_.KummerTheory.primitiveRootCoordinate_natCast hζ 0).trans
            (pow_zero ζ)
      map_add' := by
        intro a b
        apply Subtype.ext
        exact _root_.KummerTheory.primitiveRootCoordinate_add hζ a b }
  apply AddEquiv.ofBijective f
  constructor
  · intro a b hab
    apply _root_.KummerTheory.primitiveRootCoordinate_injective hζ
    exact congrArg (fun z : Additive (rootsOfUnity n E) => z.toMul.val) hab
  · intro z
    obtain ⟨a, ha⟩ := _root_.KummerTheory.primitiveRootCoordinate_surjective_roots hζ z.toMul.val
      ((mem_rootsOfUnity n z.toMul.val).mp z.toMul.property)
    exact ⟨a, Subtype.ext ha⟩

/-- Every automorphism of a finite roots group is one invertible power.
The unit is derived from the automorphism, not an extra input. -/
theorem exists_unit_power_of_roots_equiv {E : Type*} [Field E]
    {n : ℕ} [NeZero n] {ζ : Eˣ} (hζ : IsPrimitiveRoot ζ n)
    (β : rootsOfUnity n E ≃* rootsOfUnity n E) :
    ∃ u : (ZMod n)ˣ, ∀ z : rootsOfUnity n E, β z = z ^ (u : ZMod n).val := by
  let e := primitiveRootAddEquiv hζ
  let βa : Additive (rootsOfUnity n E) ≃+ Additive (rootsOfUnity n E) :=
    { β.toEquiv with map_add' := β.map_mul }
  let f : ZMod n ≃+ ZMod n := (e.trans βa).trans e.symm
  obtain ⟨u, hu⟩ := exists_unit_mul_of_zmod_addEquiv n f
  refine ⟨u, ?_⟩
  intro z
  let a : ZMod n := e.symm (Additive.ofMul z)
  have he : e (f a) = Additive.ofMul (β z) := by
    change e (e.symm (βa (e (e.symm (Additive.ofMul z))))) = _
    rw [e.apply_symm_apply, e.apply_symm_apply]
    rfl
  have hm : e ((u : ZMod n) * a) = (u : ZMod n).val • e a := by
    calc
      e ((u : ZMod n) * a) = e ((u : ZMod n).val • a) := by
        rw [nsmul_eq_mul, ZMod.natCast_zmod_val]
      _ = (u : ZMod n).val • e a := map_nsmul e _ _
  have h := he.symm.trans ((congrArg e (hu a)).trans hm)
  have hea : e a = Additive.ofMul z := e.apply_symm_apply _
  rw [hea] at h
  exact congrArg Additive.toMul h

end AnabelianGeometry.CuspidalInertia

namespace EtaleFundamentalGroups.Inertia

/-- The actual common roots-limit automorphism is one unit power at every
finite exponent. This combines derived coordinate descent and cyclic rigidity. -/
theorem exists_unit_power_of_primeToRoots_equiv
    (k E : Type*) [Field k] [Field E] [CharZero E] [IsAlgClosed E]
    (n : InvertibleExponent k)
    (β : (primeToRootsSystem k E).inverseLimit ≃*
      (primeToRootsSystem k E).inverseLimit) :
    ∃ u : (ZMod n.val)ˣ, ∀ t,
      (primeToRootsSystem k E).projection n (β t) =
        ((primeToRootsSystem k E).projection n t) ^ (u : ZMod n.val).val := by
  let : NeZero n.val := ⟨(InvertibleExponent.pos k n).ne'⟩
  obtain ⟨ζ, hζ⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot E n.val
  let z : Eˣ := hζ.isUnit (NeZero.ne n.val) |>.unit'
  have hz : IsPrimitiveRoot z n.val := hζ.isUnit_unit' (NeZero.ne _)
  obtain ⟨e, he⟩ := exists_primeToRoots_projection_equiv k E n β
  obtain ⟨u, hu⟩ :=
    AnabelianGeometry.CuspidalInertia.exists_unit_power_of_roots_equiv hz e
  exact ⟨u, fun t => (he t).symm.trans (hu _)⟩

end EtaleFundamentalGroups.Inertia
