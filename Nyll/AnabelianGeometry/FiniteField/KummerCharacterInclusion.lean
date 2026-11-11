/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.AnabelianGeometry.WeightFiltration.KummerTransitions
import Nyll.SchemeTheory.LocalGeometry.SmoothStalks

/-!
# Coefficient inclusion in the original proper Kummer characters

The inclusion of m-torsion divisor classes into mn-torsion corresponds to
the literal inclusion of roots of unity. A Kummer function is raised to n;
the same chosen root then computes both monodromy characters.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.PreGaloisCategory AlgebraicCurve

namespace AnabelianGeometry.FiniteField

private theorem mul_index_zsmul_eq_zero
    {A : Type*} [AddCommGroup A] (m k : ℕ) (a : A)
    (h : (m : ℤ) • a = 0) : ((m * k : ℕ) : ℤ) • a = 0 := by
  rw [Nat.cast_mul, mul_comm, mul_smul, h, smul_zero]

private theorem properPicardTorsion_le_multiple
    {K F : Type*} [Field K] [Field F] [Algebra K F] (m k : ℕ+) :
    Pic0.torsion K F (m : ℕ) ≤ Pic0.torsion K F ((m * k : ℕ+) : ℕ) := by
  intro x hx
  exact Pic0.mem_torsion.mpr (mul_index_zsmul_eq_zero (m : ℕ) (k : ℕ) x
    (Pic0.mem_torsion.mp hx))

private theorem addSubgroup_inclusion_eq_of_val_eq
    {A : Type*} [AddGroup A] {H J : AddSubgroup A} (h : H ≤ J)
    (x : H) (y : J) (hxy : (x : A) = (y : A)) :
    AddSubgroup.inclusion h x = y :=
  Subtype.ext hxy

/-- Inclusion of the original torsion subgroup at a multiple of its index. -/
def properPicardTorsionInclusion
    {K F : Type*} [Field K] [Field F] [Algebra K F] (m k : ℕ+) :
    Pic0.torsion K F (m : ℕ) →+ Pic0.torsion K F ((m * k : ℕ+) : ℕ) :=
  AddSubgroup.inclusion (properPicardTorsion_le_multiple m k)

/-- Raising a Kummer function supplies its representative at the larger index. -/
def properKummerUnitsInflate
    {K F : Type*} [Field K] [Field F] [Algebra K F] (m k : ℕ+) :
    Pic0.kummerUnits K F m →* Pic0.kummerUnits K F (m * k) where
  toFun u := ⟨u.val ^ (k : ℕ), by
    intro v
    obtain ⟨d, hd⟩ := u.property v
    refine ⟨d, ?_⟩
    change v.ord ((u.val : F) ^ (k : ℕ)) = ((m * k : ℕ+) : ℤ) * d
    rw [← zpow_natCast, v.ord_zpow, hd, PNat.mul_coe, Nat.cast_mul]
    ring⟩
  map_one' := Subtype.ext (one_pow (k : ℕ))
  map_mul' u v := Subtype.ext (mul_pow u.val v.val (k : ℕ))

/-- The larger-exponent Kummer representative has the same original divisor class. -/
theorem properPicardTorsionInclusion_kummerClass
    {K F : Type*} [Field K] [Field F] [Algebra K F] [HasPrincipalDivisors K F]
    (m k : ℕ+) (u : Pic0.kummerUnits K F m) :
    properPicardTorsionInclusion m k (Multiplicative.toAdd (Pic0.kummerClass m u)) =
      Multiplicative.toAdd
        (Pic0.kummerClass (m * k) (properKummerUnitsInflate m k u)) := by
  obtain ⟨D, hD⟩ := Divisor.exists_degZero_ord_eq_mul_of_dvd_ord
    m.ne_zero (Units.ne_zero u.val) u.property
  have hDmk (v : Place K F) :
      v.ord ((properKummerUnitsInflate m k u).val : F) =
        ((m * k : ℕ+) : ℤ) * (D : Divisor K F) v := by
    change v.ord ((u.val : F) ^ (k : ℕ)) = _
    rw [← zpow_natCast, v.ord_zpow, hD, PNat.mul_coe, Nat.cast_mul]
    ring
  exact addSubgroup_inclusion_eq_of_val_eq (properPicardTorsion_le_multiple m k)
    (Multiplicative.toAdd (Pic0.kummerClass m u))
    (Multiplicative.toAdd (Pic0.kummerClass (m * k) (properKummerUnitsInflate m k u)))
    ((Pic0.kummerClass_eq m u D hD).trans
      (Pic0.kummerClass_eq (m * k) (properKummerUnitsInflate m k u) D hDmk).symm)

/-- At the original generic geometric point, torsion inclusion preserves
the literal value in the coefficient field of every Kummer character. -/
theorem properKummerTorsionCharacter_generic_inclusion
    {K F : Type} [Field K] [IsAlgClosed K] [Field F] [Algebra K F]
    [Algebra.EssFiniteType K F] [IsCurveOver K F]
    (M : CurveModel K F) (m k : ℕ+)
    (hm : IsUnit ((m : ℕ) : K)) (hmk : IsUnit (((m * k : ℕ+) : ℕ) : K))
    {Ω : Type} [Field Ω] [Algebra M.C.functionField Ω]
    [IsSepClosed Ω] [IsSepClosure M.C.functionField Ω]
    (x : Pic0.torsion K F (m : ℕ)) :
    let η := Spec.map (CommRingCat.ofHom (algebraMap M.C.functionField Ω))
    let ξ := η ≫ M.C.fromSpecStalk (genericPoint M.C)
    let : TopologicalSpace (rootsOfUnity (m : ℕ) K) := ⊥
    let : DiscreteTopology (rootsOfUnity (m : ℕ) K) := ⟨rfl⟩
    let : TopologicalSpace (rootsOfUnity ((m * k : ℕ+) : ℕ) K) := ⊥
    let : DiscreteTopology (rootsOfUnity ((m * k : ℕ+) : ℕ) K) := ⟨rfl⟩
    ∀ a : Aut (FiniteEtale.fiber ξ),
      ((M.kummerTorsionCharacter (m * k) hmk ξ
        (Multiplicative.ofAdd (properPicardTorsionInclusion m k x)) a : Kˣ) : K) =
      ((M.kummerTorsionCharacter m hm ξ (Multiplicative.ofAdd x) a : Kˣ) : K) := by
  intro η ξ topm discm topmk discmk a
  have : Smooth M.toBase := SmoothOfRelativeDimension.smooth 1 M.toBase
  have : IsIntegrallyClosed Γ(Spec (.of K), ⊤) :=
    IsIntegrallyClosed.of_equiv (Scheme.ΓSpecIso (.of K)).symm.commRingCatIsoToRingEquiv
  have : IsNormalIntegral M.C := IsNormalIntegral.of_stalks M.C
    (fun z => (Smooth.isDomain_and_isIntegrallyClosed_stalk M.toBase z).2)
  obtain ⟨σ, rfl⟩ := FiniteEtale.genericFieldAction_surjective M.C Ω a
  obtain ⟨u, hu⟩ := Pic0.kummerClass_surjective m (Multiplicative.ofAdd x)
  have hx : x = Multiplicative.toAdd (Pic0.kummerClass m u) :=
    (congrArg Multiplicative.toAdd hu).symm
  rw [hx, properPicardTorsionInclusion_kummerClass]
  let aσ := FiniteEtale.fundamentalGroupHom (M.C.fromSpecStalk (genericPoint M.C)) η
    (toAut (FiniteEtale.fiber η) (Ω ≃ₐ[M.C.functionField] Ω) σ)
  change ((M.kummerTorsionCharacter (m * k) hmk ξ
      (Pic0.kummerClass (m * k) (properKummerUnitsInflate m k u))
      aσ : Kˣ) : K) =
    ((M.kummerTorsionCharacter m hm ξ (Pic0.kummerClass m u)
      aσ : Kˣ) : K)
  rw [M.kummerTorsionCharacter_kummerClass, M.kummerTorsionCharacter_kummerClass]
  let ι : K →+* Ω := (algebraMap M.C.functionField Ω).comp (baseToFunctionField M.toBase)
  have hmΩ : IsUnit ((m : ℕ) : Ω) := by
    simpa only [map_natCast] using hm.map ι
  have : NeZero ((m : ℕ) : Ω) := ⟨hmΩ.ne_zero⟩
  obtain ⟨β, hβ⟩ := IsSepClosed.exists_pow_nat_eq
    (algebraMap M.C.functionField Ω (M.ffEquiv (u.val : F))) (m : ℕ)
  have hβ0 : β ≠ 0 := by
    intro hz
    have h := hβ
    rw [hz, zero_pow m.ne_zero] at h
    exact (map_ne_zero (algebraMap M.C.functionField Ω)).mpr
      ((map_ne_zero M.ffEquiv).mpr (Units.ne_zero u.val)) h.symm
  have hβmk : β ^ ((m * k : ℕ+) : ℕ) = algebraMap M.C.functionField Ω
      (M.ffEquiv ((properKummerUnitsInflate m k u).val : F)) := by
    change β ^ ((m : ℕ) * (k : ℕ)) =
      algebraMap M.C.functionField Ω (M.ffEquiv ((u.val : F) ^ (k : ℕ)))
    rw [pow_mul, hβ, map_pow, map_pow]
  have hsmall := M.kummerMonodromyCharacter_generic_mul_root m u β hβ hm σ
  have hlarge := M.kummerMonodromyCharacter_generic_mul_root (m * k)
    (properKummerUnitsInflate m k u) β hβmk hmk σ
  apply ι.injective
  exact mul_right_cancel₀ hβ0 (hlarge.trans hsmall.symm)

end AnabelianGeometry.FiniteField
