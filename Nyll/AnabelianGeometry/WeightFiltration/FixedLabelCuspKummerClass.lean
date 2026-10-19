/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/
import Nyll.GaloisCohomology.Kummer.Concrete.ContinuousKummerScalar
import Nyll.EtaleFundamentalGroups.Inertia.PrimeToRootsCommonUnit

/-!
# Descent of the fixed-label cusp comparison

The exponents `v` and `vt` are the finite coefficient powers of the single
fixed label changes `αt * αs⁻¹` and `αt`. They are fixed before the cusp.
The radical `β` is the original arithmetic Isom-torsor radical. The conclusion
retains its scalar, rather than choosing a new scalar at each cusp.

This algebraic leaf consumes the pointwise radical-ratio identity. Supplying
that identity from the same arithmetic Isom and the actual decomposition
specializations is a remaining caller obligation; this is not an assertion
that the geometric reconstruction has already supplied that identity.
-/

noncomputable section
namespace KummerTheory

variable {k κ : Type} [Field k] [Field κ] [Algebra k κ]

/-- The coefficient exponent is constructed from the fixed label, before
choosing a cusp or any radical. -/
theorem exists_unit_power_of_fixed_galois_label
    [CharZero κ] [IsAlgClosed κ] (n : ℕ+) (α : Gal(κ/k)) :
    ∃ v : (ZMod (n : ℕ))ˣ, ∀ ζ : rootsOfUnity (n : ℕ) κ,
      α (ζ.val : κ) = (ζ.val : κ) ^ (v : ZMod (n : ℕ)).val := by
  let e : rootsOfUnity (n : ℕ) κ ≃* rootsOfUnity (n : ℕ) κ := {
    toFun := restrictRootsOfUnity α.toRingHom (n : ℕ)
    invFun := restrictRootsOfUnity α.symm.toRingHom (n : ℕ)
    left_inv := by
      intro ζ
      apply Subtype.ext
      apply Units.ext
      exact α.symm_apply_apply (ζ.val : κ)
    right_inv := by
      intro ζ
      apply Subtype.ext
      apply Units.ext
      exact α.apply_symm_apply (ζ.val : κ)
    map_mul' := (restrictRootsOfUnity α.toRingHom (n : ℕ)).map_mul }
  obtain ⟨ζ, hζ⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot κ (n : ℕ)
  let z : κˣ := hζ.isUnit n.ne_zero |>.unit'
  have hz : IsPrimitiveRoot z (n : ℕ) := hζ.isUnit_unit' n.ne_zero
  obtain ⟨v, hv⟩ :=
    AnabelianGeometry.CuspidalInertia.exists_unit_power_of_roots_equiv hz e
  refine ⟨v, fun ζ => ?_⟩
  exact congrArg (fun x : rootsOfUnity (n : ℕ) κ => (x.val : κ)) (hv ζ)

/-- A fixed label change acts on every radical ratio by its one finite
coefficient power, including the already chosen scalar radical. -/
theorem label_change_radical_ratio_power
    (n v : ℕ) (α : Gal(κ/k))
    (hα : ∀ ζ : rootsOfUnity n κ, α (ζ.val : κ) = (ζ.val : κ) ^ v)
    (a : kˣ) (r : κˣ)
    (hr : r ^ n = Units.map (algebraMap k κ).toMonoidHom a)
    (σ : Gal(κ/k)) :
    α (σ (r : κ) / (r : κ)) = (σ (r : κ) / (r : κ)) ^ v := by
  let z : κˣ := Units.map σ.toRingHom.toMonoidHom r / r
  have hzval : (z : κ) = σ (r : κ) / (r : κ) := by
    simp only [z, Units.val_div_eq_div_val, Units.coe_map]
    rfl
  have hz : z ^ n = 1 := by
    apply Units.ext
    rw [Units.val_pow_eq_pow_val, Units.val_one, hzval]
    have hrval : (r : κ) ^ n = algebraMap k κ (a : k) := congrArg Units.val hr
    rw [div_pow, ← map_pow σ, hrval, σ.commutes,
      div_self ((map_ne_zero (algebraMap k κ)).mpr a.ne_zero)]
  have h : α (z : κ) = (z : κ) ^ v := hα ⟨z, (mem_rootsOfUnity n z).mpr hz⟩
  exact (congrArg α hzval).symm.trans (h.trans (congrArg (· ^ v) hzval))

/-- The same scalar radical and fixed coefficient powers give an actual
base-field nth-power correction at a cusp. -/
theorem cusp_class_of_fixed_label_radical_ratios [IsGalois k κ]
    (n v vt : ℕ) (a f g : kˣ) (β rs rt : κˣ)
    (hβ : β ^ n = Units.map (algebraMap k κ).toMonoidHom a)
    (hs : rs ^ n = Units.map (algebraMap k κ).toMonoidHom f)
    (ht : rt ^ n = Units.map (algebraMap k κ).toMonoidHom g)
    (hratio : ∀ σ : Gal(κ/k),
      σ (rt : κ) / (rt : κ) =
        (σ (β : κ) / (β : κ)) ^ vt * (σ (rs : κ) / (rs : κ)) ^ v) :
    ∃ d : kˣ, g = a ^ vt * f ^ v * d ^ n := by
  let t : κˣ := rt / (β ^ vt * rs ^ v)
  have hfixed (σ : Gal(κ/k)) : σ (t : κ) = (t : κ) := by
    simp only [t, Units.val_div_eq_div_val, Units.val_mul, Units.val_pow_eq_pow_val]
    rw [map_div₀ σ, map_mul σ, map_pow σ, map_pow σ]
    have hr := (div_eq_iff rt.ne_zero).mp (hratio σ)
    simp only [div_pow] at hr
    rw [hr]
    have hb0 : σ (β : κ) ≠ 0 := (map_ne_zero σ).mpr β.ne_zero
    have hs0 : σ (rs : κ) ≠ 0 := (map_ne_zero σ).mpr rs.ne_zero
    field_simp [β.ne_zero, rs.ne_zero, hb0, hs0]
  obtain ⟨d, hd⟩ :=
    (InfiniteGalois.mem_range_algebraMap_iff_fixed (t : κ)).mpr hfixed
  have hd0 : d ≠ 0 := by
    intro h
    rw [h, map_zero] at hd
    exact t.ne_zero hd.symm
  let du : kˣ := Units.mk0 d hd0
  have hdu : t = Units.map (algebraMap k κ).toMonoidHom du := Units.ext hd.symm
  have hbpow : (β ^ vt) ^ n =
      Units.map (algebraMap k κ).toMonoidHom (a ^ vt) := by
    rw [← pow_mul, Nat.mul_comm vt n, pow_mul, hβ, map_pow]
  have hspow : (rs ^ v) ^ n =
      Units.map (algebraMap k κ).toMonoidHom (f ^ v) := by
    rw [← pow_mul, Nat.mul_comm v n, pow_mul, hs, map_pow]
  have hpow : Units.map (algebraMap k κ).toMonoidHom (g / (a ^ vt * f ^ v)) =
      Units.map (algebraMap k κ).toMonoidHom (du ^ n) := by
    calc
      _ = t ^ n := by
        change _ = (rt / (β ^ vt * rs ^ v)) ^ n
        rw [div_pow, mul_pow, ht, hbpow, hspow, map_div, map_mul]
      _ = _ := by rw [hdu, map_pow]
  have hbase : g / (a ^ vt * f ^ v) = du ^ n := by
    apply Units.ext
    apply (algebraMap k κ).injective
    exact congrArg Units.val hpow
  refine ⟨du, ?_⟩
  exact (div_eq_iff_eq_mul.mp hbase).trans (mul_comm _ _)

/-- Dividing at two cusps cancels the original scalar with its same fixed
coefficient exponent. No new scalar is selected for the second cusp. -/
theorem cusp_class_ratio_cancel_same_scalar
    (n v vt : ℕ) (a f₀ f₁ g₀ g₁ d₀ d₁ : kˣ)
    (h₀ : g₀ = a ^ vt * f₀ ^ v * d₀ ^ n)
    (h₁ : g₁ = a ^ vt * f₁ ^ v * d₁ ^ n) :
    g₁ / g₀ = (f₁ / f₀) ^ v * (d₁ / d₀) ^ n := by
  rw [h₁, h₀, mul_assoc, mul_assoc, mul_div_mul_left_eq_div, mul_div_mul_comm,
    ← div_pow, ← div_pow]

end KummerTheory
