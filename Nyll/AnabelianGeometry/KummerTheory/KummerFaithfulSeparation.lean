/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.AnabelianGeometry.KummerTheory.NumberFieldPowerSeparation
import Nyll.GaloisCohomology.Kummer.Concrete.RootCharacters
import Nyll.Yamaguchi26AbfaithfulGalois.Theorem6Dot7FieldSlimExamples
import Mathlib.FieldTheory.Galois.Infinite
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure

/-! # Kummer separation over torally Kummer-faithful fields

Finite-level Kummer cocycles are compared modulo roots-of-unity
coboundaries, without assuming that roots of unity are rational. A fixed
quotient of actual radicals descends to the base field. Consequently the
Kummer classes at all positive levels distinguish units over every finite
extension of a torally Kummer-faithful characteristic-zero field.

This is the multiplicative-group part of Kummer-faithfulness. No assertion
about all semiabelian varieties, or about reconstruction of an entire curve,
is made here.
-/

noncomputable section

open _root_.KummerTheory Yamaguchi26AbfaithfulGalois

namespace AnabelianGeometry.KummerTheory

universe u v

/-- Matching finite Kummer cocycles modulo a roots-of-unity coboundary gives
an actual power relation in the original field. The root of unity need not
be fixed by Galois. -/
theorem exists_power_of_rootCocycles_cohomologous
    {K : Type u} {Ω : Type v} [Field K] [Field Ω] [Algebra K Ω] [IsGalois K Ω]
    (n : ℕ) (a b : Kˣ) (r s ζ : Ωˣ)
    (hr : r ^ n = Units.map (algebraMap K Ω).toMonoidHom a)
    (hs : s ^ n = Units.map (algebraMap K Ω).toMonoidHom b)
    (hζ : ζ ^ n = 1)
    (h : ∀ σ : Gal(Ω/K), rootQuotient r σ / rootQuotient s σ = rootQuotient ζ σ) :
    ∃ y : Kˣ, y ^ n = a / b := by
  let q := r / s / ζ
  have hfixed : ∀ σ : Gal(Ω/K), σ • q = q := by
    intro σ
    apply (rootQuotient_eq_one_iff q σ).mp
    rw [rootQuotient_div, rootQuotient_div, h σ, div_self']
  obtain ⟨d, hd⟩ :=
    (InfiniteGalois.mem_range_algebraMap_iff_fixed (k := K) (K := Ω) (q : Ω)).mpr
      (fun σ => congrArg Units.val (hfixed σ))
  have hd0 : d ≠ 0 := by
    intro hz
    apply q.ne_zero
    rw [← hd, hz, map_zero]
  let y : Kˣ := Units.mk0 d hd0
  have hy : Units.map (algebraMap K Ω).toMonoidHom y = q := Units.ext hd
  have hpow : q ^ n = Units.map (algebraMap K Ω).toMonoidHom (a / b) := by
    change (r / s / ζ) ^ n = _
    rw [div_pow, div_pow, hr, hs, hζ, div_one, map_div]
  refine ⟨y, ?_⟩
  apply Units.ext
  apply (algebraMap K Ω).injective
  exact congrArg Units.val (by
    rw [map_pow, hy, hpow] :
      Units.map (algebraMap K Ω).toMonoidHom (y ^ n) =
        Units.map (algebraMap K Ω).toMonoidHom (a / b))

/-- Over each finite extension of a torally Kummer-faithful field, two units
are equal exactly when their Kummer cocycles at every positive level are
cohomologous. The radicals and coboundaries are actual elements of the
algebraic closure, and their existence is not a separate input. -/
theorem eq_iff_all_kummerRootCocycles_cohomologous
    (K L : Type u) [Field K] [CharZero K] [Field L] [Algebra K L]
    [FiniteDimensional K L] (hK : IsTorallyKummerFaithful K) (a b : Lˣ) :
    a = b ↔ ∀ n : ℕ+, ∃ r s ζ : (AlgebraicClosure L)ˣ,
      r ^ (n : ℕ) = Units.map (algebraMap L (AlgebraicClosure L)).toMonoidHom a ∧
      s ^ (n : ℕ) = Units.map (algebraMap L (AlgebraicClosure L)).toMonoidHom b ∧
      ζ ^ (n : ℕ) = 1 ∧
      ∀ σ : Gal(AlgebraicClosure L/L),
        rootQuotient r σ / rootQuotient s σ = rootQuotient ζ σ := by
  have : CharZero L := charZero_of_injective_algebraMap (algebraMap K L).injective
  constructor
  · rintro rfl n
    obtain ⟨x, hx⟩ := IsAlgClosed.exists_pow_nat_eq
      (algebraMap L (AlgebraicClosure L) (a : L)) n.pos
    have hx0 : x ≠ 0 := by
      intro hz
      have hz' := hx
      rw [hz, zero_pow n.ne_zero] at hz'
      exact ((map_ne_zero (algebraMap L (AlgebraicClosure L))).mpr a.ne_zero) hz'.symm
    let r : (AlgebraicClosure L)ˣ := Units.mk0 x hx0
    have hr : r ^ (n : ℕ) =
        Units.map (algebraMap L (AlgebraicClosure L)).toMonoidHom a := Units.ext hx
    refine ⟨r, r, 1, hr, hr, one_pow _, ?_⟩
    intro σ
    rw [div_self']
    change 1 = σ • (1 : (AlgebraicClosure L)ˣ) / 1
    rw [smul_one, one_div, inv_one]
  · intro h
    apply div_eq_one.mp
    apply hK L (a / b)
    intro n hn
    obtain ⟨r, s, ζ, hr, hs, hζ, hc⟩ := h ⟨n, hn⟩
    exact exists_power_of_rootCocycles_cohomologous n a b r s ζ hr hs hζ hc

/-- Number fields satisfy the toral Kummer-faithfulness condition, including
its quantification over all finite extensions. Root saturation of one
finitely generated S-unit group supplies the arithmetic input. -/
theorem numberField_isTorallyKummerFaithful
    (K : Type u) [Field K] [NumberField K] : IsTorallyKummerFaithful K := by
  intro L _ _ _ z hz
  have : NumberField L := NumberField.of_module_finite K L
  obtain ⟨T, hzT⟩ := exists_sUnitGroup_mem z
  let S : Subgroup Lˣ := SUnitGroup (K := L) T
  have : Group.FG S := GroupFG.iff_add_fg.mpr
    (Module.Finite.iff_addGroup_fg.mp (SUnitGroup.moduleFinite (K := L) T))
  have heq : (⟨z, hzT⟩ : S) = 1 := by
    apply eq_one_of_forall_exists_pow
    intro n
    obtain ⟨y, hy⟩ := hz n n.pos
    have hyT : y ∈ S := mem_sUnitGroup_of_pow_mem T n y (hy.symm ▸ hzT)
    exact ⟨⟨y, hyT⟩, Subtype.ext hy⟩
  exact congrArg Subtype.val heq

end AnabelianGeometry.KummerTheory
