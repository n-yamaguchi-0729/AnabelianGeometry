/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.AnabelianGeometry.KummerTheory.KummerFaithfulSeparation
public import Mathlib.FieldTheory.Finite.Basic
public import Mathlib.Algebra.Torsor.Basic
public import Mathlib.Tactic.LinearCombination
public import Nyll.AlgebraicCurves.FunctionFields.Rational.ProjectiveRatFuncPairEvaluation

/-!
# Finite-field point separation at one Kummer level

For a finite field K, the single level |Kˣ| separates its multiplicative points.
This level is invertible in K. The comparison uses actual radicals and their
original Galois cocycles, including nontrivial roots-of-unity coboundaries.
There is no characteristic-zero or Kummer-faithfulness assumption.
-/

@[expose] public section

namespace AnabelianGeometry.KummerTheory

open _root_.KummerTheory

universe u v

/-- The order of the multiplicative group is a valid tame Kummer degree. -/
theorem finiteField_unitsCard_isUnit (K : Type u) [Field K] [Finite K] :
    IsUnit (Nat.card Kˣ : K) := by
  classical
  let _ : Fintype K := Fintype.ofFinite K
  have hcard : (Nat.card Kˣ : K) = -1 := by
    rw [Nat.card_eq_fintype_card, Fintype.card_units,
      Nat.cast_sub (Nat.one_le_iff_ne_zero.mpr Fintype.card_ne_zero),
      Nat.cast_card_eq_zero, Nat.cast_one, zero_sub]
  rw [hcard]
  exact isUnit_one.neg

/-- Over a finite field, cohomologous actual Kummer cocycles at the single
level |Kˣ| already force the two original multiplicative points to coincide. -/
theorem finiteField_eq_of_kummerRootCocycles_cohomologous
    {K : Type u} {Ω : Type v} [Field K] [Finite K]
    [Field Ω] [Algebra K Ω] [IsGalois K Ω]
    (a b : Kˣ) (r s ζ : Ωˣ)
    (hr : r ^ Nat.card Kˣ = Units.map (algebraMap K Ω).toMonoidHom a)
    (hs : s ^ Nat.card Kˣ = Units.map (algebraMap K Ω).toMonoidHom b)
    (hζ : ζ ^ Nat.card Kˣ = 1)
    (h : ∀ σ : Gal(Ω/K), rootQuotient r σ / rootQuotient s σ = rootQuotient ζ σ) :
    a = b := by
  obtain ⟨y, hy⟩ := exists_power_of_rootCocycles_cohomologous
    (Nat.card Kˣ) a b r s ζ hr hs hζ h
  apply div_eq_one.mp
  exact hy.symm.trans (pow_card_eq_one' (x := y))


/-- Two root coordinates of the same original torsor, equivariant for the
same surjective arithmetic action, evaluate to the same finite-field unit.
The comparison uses the given action and both given coordinates throughout. -/
theorem finiteField_eq_of_common_rootTorsor
    {k κ P X : Type*} [Field k] [Finite k] [Field κ]
    [Algebra k κ] [IsGalois k κ] [Group P]
    [Torsor (rootsOfUnity (Nat.card kˣ) κ) X] [MulAction P X]
    (q : P →* Gal(κ/k)) (hq : Function.Surjective q)
    (a b : kˣ) (S T : X → κˣ)
    (hSn : ∀ x, S x ^ Nat.card kˣ = Units.map (algebraMap k κ).toMonoidHom a)
    (hTn : ∀ x, T x ^ Nat.card kˣ = Units.map (algebraMap k κ).toMonoidHom b)
    (hSμ : ∀ (ζ : rootsOfUnity (Nat.card kˣ) κ) x, S (ζ • x) = ζ.val * S x)
    (hTμ : ∀ (ζ : rootsOfUnity (Nat.card kˣ) κ) x, T (ζ • x) = ζ.val * T x)
    (hSP : ∀ p x, S (p • x) = q p • S x)
    (hTP : ∀ p x, T (p • x) = q p • T x) (x : X) : a = b := by
  apply finiteField_eq_of_kummerRootCocycles_cohomologous
    a b (S x) (T x) 1 (hSn x) (hTn x) (one_pow _)
  intro σ
  obtain ⟨p, hp⟩ := hq σ
  let ζ : rootsOfUnity (Nat.card kˣ) κ := (p • x) /ₛ x
  have hz : ζ • x = p • x := sdiv_smul _ _
  have hS : σ • S x = ζ.val * S x := by
    rw [← hp, ← hSP, ← hz, hSμ]
  have hT : σ • T x = ζ.val * T x := by
    rw [← hp, ← hTP, ← hz, hTμ]
  rw [rootQuotient, rootQuotient, hS, hT, mul_div_cancel_right,
    mul_div_cancel_right, div_self']
  change 1 = σ • (1 : κˣ) / 1
  rw [smul_one, div_self']

end AnabelianGeometry.KummerTheory

namespace AnabelianGeometry.ProjectiveLine

attribute [local instance] Classical.propDecidable

open AlgebraicCurve

universe u

variable {k : Type u} [Field k]

/-- Evaluation of the original pair function distinguishes projective points
away from its zero and pole, in every characteristic. -/
theorem eq_of_pairFunction_evalAt_eq
    (a b x y : Projectivization k (k × k))
    (hba : b ≠ a) (hxa : x ≠ a) (hxb : x ≠ b) (hyb : y ≠ b)
    (f : RatFunc k) (hf : f ≠ 0)
    (hord : ∀ V : Place k (RatFunc k),
      V.ord f = (if V = projectiveRatFuncPlace a then 1 else 0) -
        (if V = projectiveRatFuncPlace b then 1 else 0))
    (heval : (projectiveRatFuncPlace x).evalAt f = (projectiveRatFuncPlace y).evalAt f) :
    x = y := by
  apply eq_of_crossRatio_eq_of_ne a b x x y hba hxa hxb hxb hyb
  rw [← ratFunc_pair_evalAt_ratio_eq_crossRatio a b x x hxb hxb f hf hord,
    ← ratFunc_pair_evalAt_ratio_eq_crossRatio a b x y hxb hyb f hf hord, heval]

/-- The actual nonzero value of the explicit pair function, as a unit. -/
noncomputable def pairValueUnit (a b x : Projectivization k (k × k))
    (hxa : x ≠ a) (hxb : x ≠ b) : kˣ :=
  Units.mk0 ((projectiveRatFuncPlace x).evalAt (pairRatFunc a b)) (by
    rw [pairRatFunc_evalAt a b x hxb]
    exact div_ne_zero (fun h => hxa ((bracket_rep_eq_zero_iff x a).mp h))
      (fun h => hxb ((bracket_rep_eq_zero_iff x b).mp h)))

/-- A single prime-to-characteristic Kummer level of the actual pair function
separates the original projective points over a finite field. -/
theorem finiteField_eq_of_pairKummerCocycles
    [Finite k] {Ω : Type u} [Field Ω] [Algebra k Ω] [IsGalois k Ω]
    (a b x y : Projectivization k (k × k)) (hba : b ≠ a)
    (hxa : x ≠ a) (hxb : x ≠ b) (hya : y ≠ a) (hyb : y ≠ b)
    (r s ζ : Ωˣ)
    (hr : r ^ Nat.card kˣ = Units.map (algebraMap k Ω).toMonoidHom
      (pairValueUnit a b x hxa hxb))
    (hs : s ^ Nat.card kˣ = Units.map (algebraMap k Ω).toMonoidHom
      (pairValueUnit a b y hya hyb))
    (hζ : ζ ^ Nat.card kˣ = 1)
    (h : ∀ σ : Gal(Ω/k),
      _root_.KummerTheory.rootQuotient r σ / _root_.KummerTheory.rootQuotient s σ =
        _root_.KummerTheory.rootQuotient ζ σ) : x = y := by
  have heq := KummerTheory.finiteField_eq_of_kummerRootCocycles_cohomologous
    (pairValueUnit a b x hxa hxb) (pairValueUnit a b y hya hyb) r s ζ hr hs hζ h
  apply eq_of_pairFunction_evalAt_eq a b x y hba hxa hxb hyb (pairRatFunc a b)
    (div_ne_zero (pairLinearRatFunc_ne_zero a.rep a.rep_nonzero)
      (pairLinearRatFunc_ne_zero b.rep b.rep_nonzero)) (pairRatFunc_orders a b)
  exact congrArg Units.val heq

/-- The three-puncture Abel image contains no translate of a nontrivial
subgroup of the ambient torus. Three powers already force triviality,
including in characteristic two. -/
theorem subgroup_eq_bot_of_coset_mem_threePunctureAbelImage
    (a b : kˣ) (H : Subgroup (kˣ × kˣ))
    (h : ∀ z ∈ H, (a : k) * (z.1 : k) + (b : k) * (z.2 : k) = 1) :
    H = ⊥ := by
  apply le_antisymm ?_ bot_le
  intro z hz
  have h₀ : (a : k) + (b : k) = 1 := by
    simpa only [Prod.fst_one, Prod.snd_one, Units.val_one, mul_one] using h 1 H.one_mem
  have h₁ := h z hz
  have h₂ : (a : k) * (z.1 : k) ^ 2 + (b : k) * (z.2 : k) ^ 2 = 1 := by
    simpa only [Prod.fst_mul, Prod.snd_mul, Units.val_mul, pow_two] using
      h (z * z) (H.mul_mem hz hz)
  have hp : ((z.1 : k) - 1) * ((z.2 : k) - 1) = 0 := by
    linear_combination -h₂ + ((z.1 : k) + (z.2 : k)) * h₁ -
      ((z.1 : k) * (z.2 : k)) * h₀
  have hfirst : (z.1 : k) = 1 := by
    rcases mul_eq_zero.mp hp with hx | hy
    · exact sub_eq_zero.mp hx
    · have hy' := sub_eq_zero.mp hy
      have hx : (a : k) * ((z.1 : k) - 1) = 0 := by
        rw [hy', mul_one] at h₁
        linear_combination h₁ - h₀
      exact sub_eq_zero.mp ((mul_eq_zero.mp hx).resolve_left a.ne_zero)
  have hsecond : (z.2 : k) = 1 := by
    have hy : (b : k) * ((z.2 : k) - 1) = 0 := by
      rw [hfirst, mul_one] at h₁
      linear_combination h₁ - h₀
    exact sub_eq_zero.mp ((mul_eq_zero.mp hy).resolve_left b.ne_zero)
  exact Subgroup.mem_bot.mpr (Prod.ext (Units.ext hfirst) (Units.ext hsecond))

/-- The four-puncture Abel image also contains no nontrivial subgroup coset.
The first two coordinates force triviality there; the third is then fixed
by the original equation with `lam`. -/
theorem subgroup_eq_bot_of_coset_mem_fourPunctureAbelImage
    (a b c : kˣ) (lam : k) (H : Subgroup (kˣ × kˣ × kˣ))
    (h : ∀ z ∈ H,
      (a : k) * (z.1 : k) - (b : k) * (z.2.1 : k) = 1 ∧
      (a : k) * (z.1 : k) - (c : k) * (z.2.2 : k) = lam) : H = ⊥ := by
  let π : (kˣ × kˣ × kˣ) →* (kˣ × kˣ) :=
    { toFun := fun z => (z.1, z.2.1)
      map_one' := rfl
      map_mul' := fun _ _ => rfl }
  have hπ : H.map π = ⊥ := by
    apply subgroup_eq_bot_of_coset_mem_threePunctureAbelImage a (-b)
    rintro _ ⟨z, hz, rfl⟩
    simpa only [π, MonoidHom.coe_mk, OneHom.coe_mk, Units.val_neg,
      neg_mul, sub_eq_add_neg] using (h z hz).1
  apply le_antisymm ?_ bot_le
  intro z hz
  have hp : π z = 1 := by
    have hm : π z ∈ H.map π := ⟨z, hz, rfl⟩
    rw [hπ] at hm
    exact Subgroup.mem_bot.mp hm
  have hx : z.1 = 1 := congrArg Prod.fst hp
  have hy : z.2.1 = 1 := congrArg Prod.snd hp
  have h₀ : (a : k) - (c : k) = lam := by
    simpa only [Prod.fst_one, Prod.snd_one, Units.val_one, mul_one] using (h 1 H.one_mem).2
  have h₁ := (h z hz).2
  rw [hx, Units.val_one, mul_one] at h₁
  have hc : (c : k) * ((z.2.2 : k) - 1) = 0 := by
    linear_combination h₀ - h₁
  have hz₃ : z.2.2 = 1 :=
    Units.ext (sub_eq_zero.mp ((mul_eq_zero.mp hc).resolve_left c.ne_zero))
  exact Subgroup.mem_bot.mpr (Prod.ext hx (Prod.ext hy hz₃))

end AnabelianGeometry.ProjectiveLine
