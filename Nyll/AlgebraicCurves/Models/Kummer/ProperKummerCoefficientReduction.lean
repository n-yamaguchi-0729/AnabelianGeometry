/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.AlgebraicCurves.Divisors.ClassGroup.ClassGroup
public import Nyll.AlgebraicCurves.Divisors.ClassGroup.KummerClasses
public import Nyll.AlgebraicCurves.Divisors.Degree.DegZeroOrdEqMulDvdOrd
public import Nyll.AlgebraicCurves.Models.Kummer.CurveCoverCharacter
public import Nyll.AlgebraicCurves.Models.Kummer.CurveCoverCharacterProduct
public import Nyll.AlgebraicCurves.Models.Kummer.CurveCoverGenericCharacter
public import Nyll.AlgebraicCurves.Models.Kummer.DivisorClassCohomologyInjection
public import Nyll.EtaleFundamentalGroups.Cohomology.FiniteH1Comparison
public import Nyll.EtaleFundamentalGroups.Cohomology.GenericPointCharacterDetection
public import Nyll.EtaleFundamentalGroups.GeometricFiber.BasePoint
public import Nyll.EtaleFundamentalGroups.Inertia.PrimeToRootsInverseSystem
public import Nyll.ProCGroups.Abelian.FullTateModule
public import Nyll.SchemeTheory.FunctionFields.StructureMorphism
public import Nyll.SchemeTheory.LocalGeometry.SmoothStalks
public import Nyll.SchemeTheory.Normalization.Normal
public import Mathlib.FieldTheory.IsSepClosed
public import Mathlib.GroupTheory.QuotientGroup.Defs

/-!
# Exponent reduction for proper Kummer cohomology

The power map on roots of unity carries the actual Kummer class of an
`n*m`-torsion divisor class to that of its multiple by `m`. Both maps are
the original coefficient map on derived H¹ and the original torsion transition.
-/

@[expose] public section

universe u

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.PreGaloisCategory
open EtaleFundamentalGroups.Cohomology EtaleFundamentalGroups.Inertia

namespace AlgebraicCurve.Pic0

variable {K F : Type*} [Field K] [Field F] [Algebra K F]

/-- Divisibility of exponents gives inclusion of the original Kummer-unit subgroups. -/
theorem kummerUnits_le_of_dvd {n N : ℕ+} (h : (n : ℕ) ∣ (N : ℕ)) :
    kummerUnits K F N ≤ kummerUnits K F n := by
  intro u hu v
  exact (by exact_mod_cast h : (n : ℤ) ∣ (N : ℤ)).trans (hu v)

/-- Dividing the same principal divisor by `n` instead of `n*m` multiplies
its actual degree-zero divisor class by `m`. -/
theorem kummerClass_inclusion_mul [HasPrincipalDivisors K F]
    (n m : ℕ+) (u : kummerUnits K F (n * m)) :
    (Multiplicative.toAdd (kummerClass n
      (Subgroup.inclusion (kummerUnits_le_of_dvd (n := n) (N := n * m) ⟨(m : ℕ), rfl⟩) u))).val =
      (m : ℕ) • (Multiplicative.toAdd (kummerClass (n * m) u)).val := by
  obtain ⟨D, hD⟩ := Divisor.exists_degZero_ord_eq_mul_of_dvd_ord
    (n * m).ne_zero (Units.ne_zero u.val) u.property
  let un : kummerUnits K F n := Subgroup.inclusion
    (kummerUnits_le_of_dvd (n := n) (N := n * m) ⟨(m : ℕ), rfl⟩) u
  have hDn (v : Place K F) :
      v.ord (un.val : F) = (n : ℤ) * ((m : ℕ) • D : Divisor K F) v := by
    change v.ord (u.val : F) = (n : ℤ) * ((m : ℕ) • (D : Divisor K F) v)
    rw [hD v, nsmul_eq_mul]
    simp only [PNat.mul_coe, Nat.cast_mul, mul_assoc]
  rw [kummerClass_eq n un ((m : ℕ) • D) hDn,
    kummerClass_eq (n * m) u D hD]
  exact QuotientAddGroup.mk_nsmul _ D (m : ℕ)

end AlgebraicCurve.Pic0

namespace AlgebraicCurve.CurveModel

variable {K F : Type u} [Field K] [IsSepClosed K] [Field F] [Algebra K F]
  (M : CurveModel K F) (n m : ℕ+)
  (hn : IsUnit ((n : ℕ) : K)) (hnm : IsUnit (((n * m : ℕ+) : ℕ) : K))

/-- Exponent reduction of the original proper Kummer character at every
geometric basepoint. Its generic calculation uses the roots `β` and `β^m`. -/
theorem kummerMonodromyCharacter_coefficient_power
    (u : Pic0.kummerUnits K F (n * m))
    {Ω : Type u} [Field Ω] [IsSepClosed Ω] (xi : Spec (.of Ω) ⟶ M.C)
    (g : Aut (FiniteEtale.fiber xi)) :
    let : TopologicalSpace (rootsOfUnity (n : ℕ) K) := ⊥
    let : TopologicalSpace (rootsOfUnity ((n * m : ℕ+) : ℕ) K) := ⊥
    M.kummerMonodromyCharacter n
      (Subgroup.inclusion (Pic0.kummerUnits_le_of_dvd
        (n := n) (N := n * m) ⟨(m : ℕ), rfl⟩) u) hn xi g =
      rootsOfUnityPowerTransition K (m := (n : ℕ))
        (n := ((n * m : ℕ+) : ℕ)) ⟨(m : ℕ), rfl⟩
        (M.kummerMonodromyCharacter (n * m) u hnm xi g) := by
  intro tn tnm
  have : IsIntegral M.C := M.isIntegral
  have : Smooth M.toBase := SmoothOfRelativeDimension.smooth 1 M.toBase
  have : IsIntegrallyClosed Γ(Spec (.of K), ⊤) := IsIntegrallyClosed.of_equiv
    (Scheme.ΓSpecIso (.of K)).symm.commRingCatIsoToRingEquiv
  have : IsNormalIntegral M.C := IsNormalIntegral.of_stalks M.C
    (fun x => (Smooth.isDomain_and_isIntegrallyClosed_stalk M.toBase x).2)
  let Ωg := SeparableClosure M.C.functionField
  have : IsSepClosure M.C.functionField Ωg :=
    separableClosure.isSepClosure M.C.functionField (AlgebraicClosure M.C.functionField)
  let η := Spec.map (CommRingCat.ofHom (algebraMap M.C.functionField Ωg))
  let j := M.C.fromSpecStalk (genericPoint M.C)
  let ξ := η ≫ j
  let t := Classical.choice (FiniteEtale.nonempty_fiber_iso ξ xi)
  let b := FiniteEtale.fundamentalGroupIsoOfFiberIso ξ xi t
  obtain ⟨g₀, rfl⟩ := b.surjective g
  obtain ⟨σ, rfl⟩ := FiniteEtale.genericFieldAction_surjective M.C Ωg g₀
  have hdiv : (n : ℕ) ∣ ((n * m : ℕ+) : ℕ) := ⟨(m : ℕ), rfl⟩
  let un : Pic0.kummerUnits K F n := Subgroup.inclusion (Pic0.kummerUnits_le_of_dvd
    (n := n) (N := n * m) ⟨(m : ℕ), rfl⟩) u
  let γ := FiniteEtale.fundamentalGroupHom j η
    (toAut (FiniteEtale.fiber η) (Ωg ≃ₐ[M.C.functionField] Ωg) σ)
  change M.kummerMonodromyCharacter n un hn xi
      (FiniteEtale.fundamentalGroupIsoOfFiberIso ξ xi t γ) =
    rootsOfUnityPowerTransition K (m := (n : ℕ)) (n := ((n * m : ℕ+) : ℕ)) hdiv
      (M.kummerMonodromyCharacter (n * m) u hnm xi
        (FiniteEtale.fundamentalGroupIsoOfFiberIso ξ xi t γ))
  rw [M.kummerMonodromyCharacter_basePoint_apply n hn un ξ xi t γ,
    M.kummerMonodromyCharacter_basePoint_apply (n * m) hnm u ξ xi t γ]
  let ι : K →+* Ωg := (algebraMap M.C.functionField Ωg).comp
    (baseToFunctionField M.toBase)
  have hunit : IsUnit (((n * m : ℕ+) : ℕ) : Ωg) := by
    simpa only [map_natCast] using hnm.map ι
  have : NeZero (((n * m : ℕ+) : ℕ) : Ωg) := ⟨hunit.ne_zero⟩
  obtain ⟨β, hβ⟩ := IsSepClosed.exists_pow_nat_eq
    (algebraMap M.C.functionField Ωg (M.ffEquiv (u.val : F))) ((n * m : ℕ+) : ℕ)
  have hβ0 : β ≠ 0 := by
    intro hzero
    have hz := hβ
    rw [hzero, zero_pow (n * m).ne_zero] at hz
    exact (map_ne_zero (algebraMap M.C.functionField Ωg)).mpr
      ((map_ne_zero M.ffEquiv).mpr (Units.ne_zero u.val)) hz.symm
  have hβn : (β ^ (m : ℕ)) ^ (n : ℕ) =
      algebraMap M.C.functionField Ωg (M.ffEquiv (un.val : F)) := by
    rw [← pow_mul, Nat.mul_comm (m : ℕ) (n : ℕ)]
    exact hβ
  have hsmall := M.kummerMonodromyCharacter_generic_mul_root n un
    (β ^ (m : ℕ)) hβn hn σ
  have hlarge := M.kummerMonodromyCharacter_generic_mul_root (n * m) u β hβ hnm σ
  apply rootsOfUnity.coe_injective
  apply ι.injective
  apply mul_right_cancel₀ (pow_ne_zero (m : ℕ) hβ0)
  change ι ((M.kummerMonodromyCharacter n un hn ξ γ : Kˣ) : K) * β ^ (m : ℕ) =
    ι (((M.kummerMonodromyCharacter (n * m) u hnm ξ γ : Kˣ) : K) ^
      (((n : ℕ) * (m : ℕ)) / (n : ℕ))) * β ^ (m : ℕ)
  rw [Nat.mul_div_cancel_left (m : ℕ) n.pos]
  change ι ((M.kummerMonodromyCharacter (n * m) u hnm ξ γ : Kˣ) : K) * β = σ β at hlarge
  rw [map_pow, ← mul_pow, hlarge, ← map_pow]
  exact hsmall

/-- The original map of constant coefficient sheaves reduces the actual
proper Kummer covering class, with the representing function unchanged. -/
theorem kummerEtaleClass_coefficient_power
    (u : Pic0.kummerUnits K F (n * m))
    {Ω : Type u} [Field Ω] [IsSepClosed Ω] (xi : Spec (.of Ω) ⟶ M.C) :
    Sheaf.H.map ((constantSheaf M.C.smallEtaleTopology AddCommGrpCat.{u}).map
      (AddCommGrpCat.ofHom (rootsOfUnityPowerTransition K
        (m := (n : ℕ)) (n := ((n * m : ℕ+) : ℕ)) ⟨(m : ℕ), rfl⟩).toAdditive)) 1
      (M.kummerEtaleClass (n * m) u hnm xi) =
        M.kummerEtaleClass n (Subgroup.inclusion (Pic0.kummerUnits_le_of_dvd
          (n := n) (N := n * m) ⟨(m : ℕ), rfl⟩) u) hn xi := by
  have : IsIntegral M.C := M.isIntegral
  have : NeZero (n : ℕ) := ⟨n.ne_zero⟩
  have : NeZero ((n * m : ℕ+) : ℕ) := ⟨(n * m).ne_zero⟩
  let A := AddCommGrpCat.of (Additive (rootsOfUnity ((n * m : ℕ+) : ℕ) K))
  let B := AddCommGrpCat.of (Additive (rootsOfUnity (n : ℕ) K))
  let : TopologicalSpace (Multiplicative A) := ⊥
  let : TopologicalSpace (Multiplicative B) := ⊥
  have : DiscreteTopology (Multiplicative A) := ⟨rfl⟩
  have : DiscreteTopology (Multiplicative B) := ⟨rfl⟩
  have hdiv : (n : ℕ) ∣ ((n * m : ℕ+) : ℕ) := ⟨(m : ℕ), rfl⟩
  let α : A ⟶ B := AddCommGrpCat.ofHom (rootsOfUnityPowerTransition K
    (m := (n : ℕ)) (n := ((n * m : ℕ+) : ℕ)) hdiv).toAdditive
  let un : Pic0.kummerUnits K F n := Subgroup.inclusion
    (Pic0.kummerUnits_le_of_dvd (n := n) (N := n * m) hdiv) u
  change Sheaf.H.map ((constantSheaf M.C.smallEtaleTopology AddCommGrpCat.{u}).map α) 1
    (M.kummerEtaleClass (n * m) u hnm xi) = M.kummerEtaleClass n un hn xi
  have hnat := finiteH1CharacterEquiv_naturality A xi α
    (M.kummerEtaleClass (n * m) u hnm xi)
  have hA : finiteH1CharacterEquiv A xi (M.kummerEtaleClass (n * m) u hnm xi) =
      Additive.ofMul (M.kummerMonodromyCharacter (n * m) u hnm xi) := by
    exact (finiteH1CharacterEquiv A xi).apply_symm_apply
      (Additive.ofMul (M.kummerMonodromyCharacter (n * m) u hnm xi))
  have hB : finiteH1CharacterEquiv B xi (M.kummerEtaleClass n un hn xi) =
      Additive.ofMul (M.kummerMonodromyCharacter n un hn xi) := by
    exact (finiteH1CharacterEquiv B xi).apply_symm_apply
      (Additive.ofMul (M.kummerMonodromyCharacter n un hn xi))
  apply (finiteH1CharacterEquiv B xi).injective
  apply Additive.toMul.injective
  rw [← hnat]
  rw [hA, hB]
  apply ContinuousMonoidHom.ext
  intro g
  exact (M.kummerMonodromyCharacter_coefficient_power n m hn hnm u xi g).symm

variable [IsAlgClosed K] [Algebra.EssFiniteType K F] [IsCurveOver K F]

omit [IsSepClosed K] in
/-- The native Kummer H¹ comparison intertwines the original multiplication
transition on torsion points with the original coefficient-power map. -/
theorem kummerTorsionCohomology_torsionTransition
    {Ω : Type u} [Field Ω] [IsSepClosed Ω] (xi : Spec (.of Ω) ⟶ M.C)
    (x : Pic0.torsion K F ((n * m : ℕ+) : ℕ)) :
    let x' : ProCGroups.torsionLevel (Pic0 K F) (n * m) :=
      ⟨x.val, by
        change ((n * m : ℕ+) : ℕ) • x.val = 0
        simpa only [natCast_zsmul] using (Pic0.mem_torsion.mp x.property)⟩
    let y := ProCGroups.torsionTransition (Pic0 K F) n m x'
    Sheaf.H.map ((constantSheaf M.C.smallEtaleTopology AddCommGrpCat.{u}).map
      (AddCommGrpCat.ofHom (rootsOfUnityPowerTransition K
        (m := (n : ℕ)) (n := ((n * m : ℕ+) : ℕ)) ⟨(m : ℕ), rfl⟩).toAdditive)) 1
      (M.kummerTorsionCohomology (n * m) hnm xi x) =
        M.kummerTorsionCohomology n hn xi
          ⟨y.val, Pic0.mem_torsion.mpr (by rw [natCast_zsmul]; exact y.property)⟩ := by
  intro x' y
  obtain ⟨u, hu⟩ := Pic0.kummerClass_surjective (n * m) (Multiplicative.ofAdd x)
  have hx : Multiplicative.toAdd (Pic0.kummerClass (n * m) u) = x :=
    congrArg Multiplicative.toAdd hu
  let un : Pic0.kummerUnits K F n := Subgroup.inclusion (Pic0.kummerUnits_le_of_dvd
    (n := n) (N := n * m) ⟨(m : ℕ), rfl⟩) u
  have hy : Multiplicative.toAdd (Pic0.kummerClass n un) =
      (⟨y.val, Pic0.mem_torsion.mpr
        (by rw [natCast_zsmul]; exact y.property)⟩ : Pic0.torsion K F (n : ℕ)) := by
    apply Subtype.ext
    change (Multiplicative.toAdd (Pic0.kummerClass n un)).val = (m : ℕ) • x.val
    rw [Pic0.kummerClass_inclusion_mul, hx]
  have hxC : M.kummerTorsionCohomology (n * m) hnm xi x =
      M.kummerEtaleClass (n * m) u hnm xi :=
    (congrArg (M.kummerTorsionCohomology (n * m) hnm xi) hx).symm.trans
      (M.kummerTorsionCohomology_kummerClass (n * m) hnm xi u)
  have hyC : M.kummerTorsionCohomology n hn xi
      (⟨y.val, Pic0.mem_torsion.mpr
        (by rw [natCast_zsmul]; exact y.property)⟩ : Pic0.torsion K F (n : ℕ)) =
        M.kummerEtaleClass n un hn xi :=
    (congrArg (M.kummerTorsionCohomology n hn xi) hy).symm.trans
      (M.kummerTorsionCohomology_kummerClass n hn xi un)
  rw [hxC, hyC]
  exact M.kummerEtaleClass_coefficient_power n m hn hnm u xi

end AlgebraicCurve.CurveModel
