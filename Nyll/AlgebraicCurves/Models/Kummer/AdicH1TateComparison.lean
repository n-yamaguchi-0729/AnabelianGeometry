/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.AbelianVarieties.Tate.PrimePower
public import Nyll.AlgebraicCurves.Divisors.ClassGroup.ClassGroup
public import Nyll.AlgebraicCurves.Models.Kummer.DivisorClassCohomologyComparison
public import Nyll.AlgebraicCurves.Models.Kummer.ProperKummerCoefficientReduction
public import Nyll.EtaleCohomology.Classical.Adic
public import Nyll.EtaleCohomology.Classical.RationalAdic
public import Nyll.EtaleFundamentalGroups.Cohomology.KummerPowerCoefficients
public import Nyll.EtaleFundamentalGroups.Inertia.PrimeToRootsInverseSystem
public import Nyll.ProCGroups.Abelian.FullTateModule
public import Mathlib.Algebra.Category.Grp.Basic
public import Mathlib.Algebra.Module.End
public import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor
public import Mathlib.CategoryTheory.Sites.ConstantSheaf
public import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
public import Mathlib.Data.PNat.Basic
public import Mathlib.LinearAlgebra.TensorProduct.Tower
public import Mathlib.Logic.Function.ULift
public import Mathlib.RingTheory.RootsOfUnity.Basic

/-!
# Proper curve Kummer comparison at the integral and rational adic limits

The original finite Kummer equivalences and compatible roots coordinates
identify the actual prime-power Tate module of the degree-zero divisor class
group with classical integral H¹. The comparison shifts the original Tate
index by one and respects the original p-adic scalar actions.

The choice of primitive roots trivializes the coefficient Tate twist only
as modules. No arithmetic equivariance of this choice is asserted here.
The cohomology is the ordinary inverse limit of finite-level cohomology;
no derived inverse-limit comparison is used.
-/

@[expose] public section

universe u

noncomputable section

open AlgebraicGeometry CategoryTheory EtaleCohomology.Classical
open EtaleFundamentalGroups.Cohomology EtaleFundamentalGroups.Inertia

namespace AlgebraicCurve.CurveModel

variable {K F : Type u} [Field K] [IsAlgClosed K] [Field F] [Algebra K F]
  [Algebra.EssFiniteType K F] [IsCurveOver K F]
  (M : CurveModel K F) {Ω : Type u} [Field Ω] [IsSepClosed Ω]
  (xi : Spec (.of Ω) ⟶ M.C) (ℓ : ℕ) [Fact ℓ.Prime] (hℓ : IsUnit (ℓ : K))

/-- The finite cohomology comparison induced by the chosen roots-of-unity coordinates. -/
def rootsH1Equiv (n : ℕ) :
    finiteLevelCohomology M.C ℓ n 1 ≃+
      Sheaf.H.{u} ((constantSheaf M.C.smallEtaleTopology AddCommGrpCat.{u}).obj
        (AddCommGrpCat.of (Additive (rootsOfUnity (ℓ ^ (n + 1)) K)))) 1 :=
  ((constantSheaf M.C.smallEtaleTopology AddCommGrpCat.{u} ⋙
    Sheaf.functorH M.C.smallEtaleTopology 1).mapIso
      (ellPowerRootsCoefficientEquiv K ℓ hℓ n).toAddCommGrpIso).addCommGroupIsoToAddEquiv

/-- The original proper Kummer comparison, written in the actual finite
cyclic coefficients using a compatible choice of primitive roots. -/
def kummerEllPowerCohomologyEquiv (n : ℕ) :
    Pic0.torsion K F (ℓ ^ (n + 1)) ≃+ finiteLevelCohomology M.C ℓ n 1 :=
  (M.kummerTorsionCohomologyEquiv
    ⟨ℓ ^ (n + 1), pow_pos (Fact.out : ℓ.Prime).pos (n + 1)⟩
    (by
      change IsUnit ((ℓ ^ (n + 1) : ℕ) : K)
      simpa only [Nat.cast_pow] using hℓ.pow (n + 1)) xi).trans
      (rootsH1Equiv M ℓ hℓ n).symm

/-- In roots coordinates, the finite comparison is precisely the original
Kummer map of actual torsion divisor classes. -/
theorem kummerEllPowerCohomologyEquiv_roots (n : ℕ)
    (x : Pic0.torsion K F (ℓ ^ (n + 1))) :
    Sheaf.H.map ((constantSheaf M.C.smallEtaleTopology AddCommGrpCat.{u}).map
      (AddCommGrpCat.ofHom (ellPowerRootsCoefficientEquiv K ℓ hℓ n).toAddMonoidHom)) 1
      (M.kummerEllPowerCohomologyEquiv xi ℓ hℓ n x) =
        M.kummerTorsionCohomology
          ⟨ℓ ^ (n + 1), pow_pos (Fact.out : ℓ.Prime).pos (n + 1)⟩
          (by
            change IsUnit ((ℓ ^ (n + 1) : ℕ) : K)
            simpa only [Nat.cast_pow] using hℓ.pow (n + 1)) xi x :=
  (rootsH1Equiv M ℓ hℓ n).apply_symm_apply _

omit [Algebra.EssFiniteType K F] [IsCurveOver K F] in
private theorem rootsH1Equiv_reduction (n : ℕ)
    (a : finiteLevelCohomology M.C ℓ (n + 1) 1) :
    rootsH1Equiv M ℓ hℓ n (finiteLevelReduction M.C ℓ n 1 a) =
      Sheaf.H.map ((constantSheaf M.C.smallEtaleTopology AddCommGrpCat.{u}).map
        (AddCommGrpCat.ofHom (rootsOfUnityPowerTransition K
          (m := ℓ ^ (n + 1)) (n := ℓ ^ ((n + 1) + 1))
          ⟨ℓ, pow_succ ℓ (n + 1)⟩).toAdditive)) 1
        (rootsH1Equiv M ℓ hℓ (n + 1) a) := by
  let H := constantSheaf M.C.smallEtaleTopology AddCommGrpCat.{u} ⋙
    Sheaf.functorH M.C.smallEtaleTopology 1
  let en : ellPowerCoefficients.{u} ℓ n ≅
      AddCommGrpCat.of (Additive (rootsOfUnity (ℓ ^ (n + 1)) K)) :=
    (ellPowerRootsCoefficientEquiv K ℓ hℓ n).toAddCommGrpIso
  let eN : ellPowerCoefficients.{u} ℓ (n + 1) ≅
      AddCommGrpCat.of (Additive (rootsOfUnity (ℓ ^ ((n + 1) + 1)) K)) :=
    (ellPowerRootsCoefficientEquiv K ℓ hℓ (n + 1)).toAddCommGrpIso
  let r := AddCommGrpCat.ofHom (ellPowerReduction ℓ n)
  let s := AddCommGrpCat.ofHom (rootsOfUnityPowerTransition K
    (m := ℓ ^ (n + 1)) (n := ℓ ^ ((n + 1) + 1))
    ⟨ℓ, pow_succ ℓ (n + 1)⟩).toAdditive
  have he : r ≫ en.hom = eN.hom ≫ s := by
    apply AddCommGrpCat.hom_ext
    apply AddMonoidHom.ext
    intro b
    exact (ellPowerRootsCoefficientEquiv_reduction K ℓ hℓ n b).symm
  change H.map en.hom (H.map r a) = H.map s (H.map eN.hom a)
  change (H.map r ≫ H.map en.hom) a = (H.map eN.hom ≫ H.map s) a
  rw [← H.map_comp, ← H.map_comp, he]

private theorem kummerTorsionCohomology_power_of_mul_eq
    (n m N : ℕ+) (hN : n * m = N)
    (hn : IsUnit ((n : ℕ) : K)) (hunit : IsUnit ((N : ℕ) : K))
    (x : Pic0.torsion K F (N : ℕ)) :
    Sheaf.H.map ((constantSheaf M.C.smallEtaleTopology AddCommGrpCat.{u}).map
      (AddCommGrpCat.ofHom (rootsOfUnityPowerTransition K
        (m := (n : ℕ)) (n := (N : ℕ))
        ⟨(m : ℕ), congrArg PNat.val hN.symm⟩).toAdditive)) 1
      (M.kummerTorsionCohomology N hunit xi x) =
        M.kummerTorsionCohomology n hn xi
          ⟨((m : ℕ) : ℤ) • x.val, Pic0.mem_torsion.mpr (by
            rw [smul_smul, ← Nat.cast_mul]
            change (((n * m : ℕ+) : ℕ) : ℤ) • x.val = 0
            rw [hN]
            exact Pic0.mem_torsion.mp x.property)⟩ := by
  subst N
  exact (M.kummerTorsionCohomology_torsionTransition n m hn hunit xi x).trans
    (congrArg (M.kummerTorsionCohomology n hn xi)
      (Subtype.ext (natCast_zsmul x.val (m : ℕ)).symm))

/-- Native coefficient reduction corresponds to the original multiplication
transition on the prime-power torsion subgroups. -/
theorem kummerEllPowerCohomologyEquiv_reduction (n : ℕ)
    (x : Pic0.torsion K F (ℓ ^ ((n + 1) + 1))) :
    finiteLevelReduction M.C ℓ n 1
      (M.kummerEllPowerCohomologyEquiv xi ℓ hℓ (n + 1) x) =
        M.kummerEllPowerCohomologyEquiv xi ℓ hℓ n
          (TateModule.mulP ℓ (Pic0 K F) (n + 1) x) := by
  have hp : ℓ.Prime := Fact.out
  let p : ℕ+ := ⟨ℓ, hp.pos⟩
  let pn : ℕ+ := ⟨ℓ ^ (n + 1), pow_pos hp.pos (n + 1)⟩
  let pN : ℕ+ := ⟨ℓ ^ ((n + 1) + 1), pow_pos hp.pos ((n + 1) + 1)⟩
  have hpn : pn * p = pN := PNat.eq (pow_succ ℓ (n + 1)).symm
  have hn : IsUnit ((pn : ℕ) : K) := by
    change IsUnit ((ℓ ^ (n + 1) : ℕ) : K)
    simpa only [Nat.cast_pow] using hℓ.pow (n + 1)
  have hN' : IsUnit ((pN : ℕ) : K) := by
    change IsUnit ((ℓ ^ ((n + 1) + 1) : ℕ) : K)
    simpa only [Nat.cast_pow] using hℓ.pow ((n + 1) + 1)
  have ht := kummerTorsionCohomology_power_of_mul_eq M xi pn p pN hpn hn hN' x
  apply (rootsH1Equiv M ℓ hℓ n).injective
  rw [rootsH1Equiv_reduction]
  rw [show rootsH1Equiv M ℓ hℓ (n + 1)
      (M.kummerEllPowerCohomologyEquiv xi ℓ hℓ (n + 1) x) =
        M.kummerTorsionCohomology pN hN' xi x from
      M.kummerEllPowerCohomologyEquiv_roots xi ℓ hℓ (n + 1) x]
  rw [show rootsH1Equiv M ℓ hℓ n
      (M.kummerEllPowerCohomologyEquiv xi ℓ hℓ n
        (TateModule.mulP ℓ (Pic0 K F) (n + 1) x)) =
        M.kummerTorsionCohomology pn hn xi
          (TateModule.mulP ℓ (Pic0 K F) (n + 1) x) from
      M.kummerEllPowerCohomologyEquiv_roots xi ℓ hℓ n _]
  exact ht

/-- Compatible Kummer classes send a Tate-module element to integral adic H¹. -/
def tateToAdicH1 :
    TateModule ℓ (Pic0 K F) →+ ellAdicCohomology M.C ℓ 1 where
  toFun x := ⟨fun n => M.kummerEllPowerCohomologyEquiv xi ℓ hℓ n
    ⟨x.val (n + 1), Pic0.mem_torsion.mpr (TateModule.torsion x (n + 1))⟩,
    fun n => by
      rw [M.kummerEllPowerCohomologyEquiv_reduction xi ℓ hℓ n]
      apply congrArg (M.kummerEllPowerCohomologyEquiv xi ℓ hℓ n)
      exact Subtype.ext (TateModule.compat x (n + 1))⟩
  map_zero' := by
    apply Subtype.ext
    funext n
    change M.kummerEllPowerCohomologyEquiv xi ℓ hℓ n 0 = 0
    exact (M.kummerEllPowerCohomologyEquiv xi ℓ hℓ n).map_zero
  map_add' x y := by
    apply Subtype.ext
    funext n
    let xn : Pic0.torsion K F (ℓ ^ (n + 1)) :=
      ⟨x.val (n + 1), Pic0.mem_torsion.mpr (TateModule.torsion x (n + 1))⟩
    let yn : Pic0.torsion K F (ℓ ^ (n + 1)) :=
      ⟨y.val (n + 1), Pic0.mem_torsion.mpr (TateModule.torsion y (n + 1))⟩
    change M.kummerEllPowerCohomologyEquiv xi ℓ hℓ n (xn + yn) =
      M.kummerEllPowerCohomologyEquiv xi ℓ hℓ n xn +
        M.kummerEllPowerCohomologyEquiv xi ℓ hℓ n yn
    exact (M.kummerEllPowerCohomologyEquiv xi ℓ hℓ n).map_add xn yn

theorem tateToAdicH1_bijective :
    Function.Bijective (tateToAdicH1 M xi ℓ hℓ) := by
  constructor
  · intro x y h
    apply Subtype.ext
    funext n
    cases n with
    | zero => exact (TateModule.apply_zero x).trans (TateModule.apply_zero y).symm
    | succ n =>
      have hn := congrArg (fun a : ellAdicCohomology M.C ℓ 1 => a.val n) h
      exact congrArg Subtype.val ((M.kummerEllPowerCohomologyEquiv xi ℓ hℓ n).injective hn)
  · intro a
    let y (n : ℕ) := (M.kummerEllPowerCohomologyEquiv xi ℓ hℓ n).symm (a.val n)
    have hy (n : ℕ) : TateModule.mulP ℓ (Pic0 K F) (n + 1) (y (n + 1)) = y n := by
      apply (M.kummerEllPowerCohomologyEquiv xi ℓ hℓ n).injective
      rw [← M.kummerEllPowerCohomologyEquiv_reduction xi ℓ hℓ n]
      change finiteLevelReduction M.C ℓ n 1
          ((M.kummerEllPowerCohomologyEquiv xi ℓ hℓ (n + 1))
            ((M.kummerEllPowerCohomologyEquiv xi ℓ hℓ (n + 1)).symm (a.val (n + 1)))) =
        (M.kummerEllPowerCohomologyEquiv xi ℓ hℓ n)
          ((M.kummerEllPowerCohomologyEquiv xi ℓ hℓ n).symm (a.val n))
      rw [AddEquiv.apply_symm_apply, AddEquiv.apply_symm_apply]
      exact a.property n
    let x : TateModule ℓ (Pic0 K F) := ⟨fun k => Nat.casesOn k 0 (fun n => (y n).val), by
      intro k
      cases k with
      | zero =>
        refine ⟨smul_zero _, ?_⟩
        have h := Pic0.mem_torsion.mp (y 0).property
        change (ℓ : ℤ) • (y 0).val = 0
        simpa only [zero_add, pow_one] using h
      | succ n =>
        exact ⟨Pic0.mem_torsion.mp (y n).property, congrArg Subtype.val (hy n)⟩⟩
    refine ⟨x, Subtype.ext (funext fun n => ?_)⟩
    exact (M.kummerEllPowerCohomologyEquiv xi ℓ hℓ n).apply_symm_apply (a.val n)

omit [IsAlgClosed K] [Algebra.EssFiniteType K F] [IsCurveOver K F] in
private theorem finiteLevel_smul_eq_appr (n : ℕ) (c : ℤ_[ℓ])
    (a : finiteLevelCohomology M.C ℓ n 1) :
    c • a = c.appr (n + 1) • a := by
  let : Module ℤ_[ℓ] (ellPowerCoefficients.{u} ℓ n) := ellPowerPadicModule ℓ n
  let H := constantSheaf M.C.smallEtaleTopology AddCommGrpCat.{u} ⋙
    Sheaf.functorH M.C.smallEtaleTopology 1
  have he : AddCommGrpCat.ofHom (smulAddHom ℤ_[ℓ] (ellPowerCoefficients ℓ n) c) =
      c.appr (n + 1) • 𝟙 (ellPowerCoefficients ℓ n) := by
    apply AddCommGrpCat.hom_ext
    apply AddMonoidHom.ext
    intro b
    apply ULift.down_injective
    change PadicInt.toZModPow (n + 1) c * b.down = c.appr (n + 1) • b.down
    rw [TateModule.toZModPow_eq_appr, nsmul_eq_mul]
  change H.map (AddCommGrpCat.ofHom (smulAddHom ℤ_[ℓ] (ellPowerCoefficients ℓ n) c)) a =
    c.appr (n + 1) • a
  rw [he, Functor.map_nsmul, H.map_id]
  rfl

theorem tateToAdicH1_smul (c : ℤ_[ℓ]) (x : TateModule ℓ (Pic0 K F)) :
    tateToAdicH1 M xi ℓ hℓ (c • x) = c • tateToAdicH1 M xi ℓ hℓ x := by
  apply Subtype.ext
  funext n
  change M.kummerEllPowerCohomologyEquiv xi ℓ hℓ n
      ⟨(c • x).val (n + 1), _⟩ =
    c • M.kummerEllPowerCohomologyEquiv xi ℓ hℓ n ⟨x.val (n + 1), _⟩
  rw [finiteLevel_smul_eq_appr]
  rw [← map_nsmul]
  apply congrArg (M.kummerEllPowerCohomologyEquiv xi ℓ hℓ n)
  apply Subtype.ext
  exact (TateModule.smul_apply c x (n + 1)).trans (natCast_zsmul _ _)

/-- Compatible roots coordinates identify the original integral Tate module
of `Pic0` with the original inverse limit defining classical integral H¹.
This is an isomorphism of modules; arithmetic transport retains its twist. -/
def kummerTateEllAdicH1Equiv :
    TateModule ℓ (Pic0 K F) ≃ₗ[ℤ_[ℓ]] ellAdicCohomology M.C ℓ 1 where
  __ := AddEquiv.ofBijective (tateToAdicH1 M xi ℓ hℓ)
    (tateToAdicH1_bijective M xi ℓ hℓ)
  map_smul' := tateToAdicH1_smul M xi ℓ hℓ

/-- Each actual finite-level projection is the original Kummer equivalence
at the shifted Tate coordinate `n+1`. -/
theorem kummerTateEllAdicH1Equiv_projection (x : TateModule ℓ (Pic0 K F)) (n : ℕ) :
    ellAdicProjection M.C ℓ 1 n (M.kummerTateEllAdicH1Equiv xi ℓ hℓ x) =
      M.kummerEllPowerCohomologyEquiv xi ℓ hℓ n
        ⟨x.val (n + 1), Pic0.mem_torsion.mpr (TateModule.torsion x (n + 1))⟩ := rfl

/-- Scalar extension identifies the actual rational Tate module with the
standard classical rational étale H¹ of the proper curve. -/
def kummerTateRationalEllAdicH1Equiv :
    TensorProduct ℤ_[ℓ] ℚ_[ℓ] (TateModule ℓ (Pic0 K F)) ≃ₗ[ℚ_[ℓ]]
      rationalEllAdicCohomology ℓ M.C 1 :=
  (M.kummerTateEllAdicH1Equiv xi ℓ hℓ).baseChange ℤ_[ℓ] ℚ_[ℓ]
    (TateModule ℓ (Pic0 K F)) (ellAdicCohomology M.C ℓ 1)

end AlgebraicCurve.CurveModel
