/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.AnabelianGeometry.WeightFiltration.KummerTransitions
public import Nyll.EtaleFundamentalGroups.Cohomology.KummerCoefficientCoordinates
public import Nyll.EtaleCohomology.Classical.FiniteLevelScalars
public import Nyll.AbelianVarieties.Tate.PrimePower

/-!
# Integral Kummer comparison with the original Picard Tate module

The original finite Kummer comparison and its proved multiplication
transitions identify the actual prime-power Tate sequences with the actual
derived cohomology inverse limit. Compatible cyclic roots coordinates are
constructed from the roots inverse limit. The finite approximation formula
for both original scalar actions then proves linearity over the adic integers.

Only invertibility of the chosen prime in the constants is required. No
rational point on the curve and no characteristic-zero hypothesis is used.
Arithmetic Frobenius equivariance is a separate geometric comparison.

-/

@[expose] public section

universe uGeom uField₁ uField₂

noncomputable section

open AlgebraicGeometry CategoryTheory AlgebraicCurve
open EtaleCohomology.Classical EtaleFundamentalGroups.Cohomology

namespace AnabelianGeometry.FiniteField

/-- Invertibility is preserved by the original positive power exponents. -/
theorem isUnit_powerExponent
    {K : Type uGeom} [Field K] (p : ℕ+) (hp : IsUnit ((p : ℕ) : K)) (n : ℕ) :
    IsUnit (((p ^ (n + 1) : ℕ+) : ℕ) : K) := by
  change IsUnit (((p : ℕ) ^ (n + 1) : ℕ) : K)
  rw [Nat.cast_pow]
  exact hp.pow (n + 1)

variable {K : Type uGeom} {F : Type uField₁} [Field K] [IsAlgClosed K] [Field F] [Algebra K F]
  [Algebra.EssFiniteType K F] [IsCurveOver K F]

/-- The original finite Kummer map, expressed in the constructed cyclic
coordinates at the original geometric generic point. -/
def properKummerFiniteLevelEquiv (M : CurveModel K F)
    (p : ℕ+) (hp : IsUnit ((p : ℕ) : K)) (n : ℕ) :
    Submodule.torsionBy ℤ (Pic0 K F) (((p : ℕ) ^ (n + 1) : ℕ) : ℤ) ≃+
      finiteLevelCohomology M.C (p : ℕ) n 1 :=
  (M.kummerTorsionCohomologyEquiv (p ^ (n + 1))
    (isUnit_powerExponent p hp n)
    (Spec.map (CommRingCat.ofHom
      (algebraMap M.C.functionField (SeparableClosure M.C.functionField))) ≫
        M.C.fromSpecStalk (genericPoint M.C))).trans
    (finiteLevelKummerEquiv K M.C (p : ℕ) hp n 1).symm

/-- The finite comparison retains the original Kummer class, rather than
choosing a new cohomology representative. -/
theorem finiteLevelKummerEquiv_properKummerFiniteLevelEquiv
    (M : CurveModel K F) (p : ℕ+) (hp : IsUnit ((p : ℕ) : K)) (n : ℕ)
    (a : Submodule.torsionBy ℤ (Pic0 K F) (((p : ℕ) ^ (n + 1) : ℕ) : ℤ)) :
    finiteLevelKummerEquiv K M.C (p : ℕ) hp n 1
        (properKummerFiniteLevelEquiv M p hp n a) =
      M.kummerTorsionCohomology (p ^ (n + 1)) (isUnit_powerExponent p hp n)
        (Spec.map (CommRingCat.ofHom
          (algebraMap M.C.functionField (SeparableClosure M.C.functionField))) ≫
            M.C.fromSpecStalk (genericPoint M.C)) a :=
  (finiteLevelKummerEquiv K M.C (p : ℕ) hp n 1).apply_symm_apply _

/-- Original coefficient reduction corresponds to multiplication by the
prime on the original torsion points. -/
theorem properKummerFiniteLevelEquiv_transition
    (M : CurveModel K F) (p : ℕ+) (hp : IsUnit ((p : ℕ) : K)) (n : ℕ)
    (a : Submodule.torsionBy ℤ (Pic0 K F) (((p : ℕ) ^ (n + 1 + 1) : ℕ) : ℤ)) :
    finiteLevelReduction M.C (p : ℕ) n 1
        (properKummerFiniteLevelEquiv M p hp (n + 1) a) =
      properKummerFiniteLevelEquiv M p hp n
        (TateModule.mulP (p : ℕ) (Pic0 K F) (n + 1) a) := by
  apply (finiteLevelKummerEquiv K M.C (p : ℕ) hp n 1).injective
  rw [← finiteLevelKummerEquiv_reduction,
    finiteLevelKummerEquiv_properKummerFiniteLevelEquiv,
    finiteLevelKummerEquiv_properKummerFiniteLevelEquiv]
  have h := properKummerTorsionCohomology_generic_transition
    (Ω := SeparableClosure M.C.functionField) M (p ^ (n + 1)) p
    (isUnit_powerExponent p hp n) (isUnit_powerExponent p hp (n + 1)) a
  have ht : TateModule.mulP (p : ℕ) (Pic0 K F) (n + 1) a =
      properPicardTorsionTransition (p ^ (n + 1)) p a := by
    apply Subtype.ext
    change ((p : ℕ) : ℤ) • (a : Pic0 K F) = (p : ℕ) • (a : Pic0 K F)
    rw [natCast_zsmul]
  rw [ht]
  exact h

/-- Passing from actual finite torsion equivalences to compatible sequences
is purely additive. The zeroth Tate coordinate is forced to be zero. -/
def tateSequentialEquiv (p : ℕ) (B : Type uField₁) [AddCommGroup B]
    (A : ℕ → Type uField₂) [∀ n, AddCommGroup (A n)]
    (r : ∀ n, A (n + 1) →+ A n)
    (e : ∀ n, Submodule.torsionBy ℤ B ((p ^ (n + 1) : ℕ) : ℤ) ≃+ A n)
    (he : ∀ n a, r n (e (n + 1) a) = e n (TateModule.mulP p B (n + 1) a)) :
    TateModule p B ≃+ sequentialLimit A r := by
  refine
    { toFun := fun x => ⟨fun n => e n ⟨x.val (n + 1), TateModule.torsion x (n + 1)⟩,
        fun n => (he n _).trans (congrArg (e n)
          (Subtype.ext (TateModule.compat x (n + 1))))⟩
      invFun := fun a => ⟨fun n => Nat.casesOn n 0 (fun k => ((e k).symm (a.val k)).val), ?_⟩
      left_inv := ?_
      right_inv := ?_
      map_add' := ?_ }
  · intro n
    cases n with
    | zero =>
        constructor
        · exact smul_zero _
        · change (p : ℤ) • (((e 0).symm (a.val 0)).val : B) = 0
          have h := (Submodule.mem_torsionBy_iff _ _).mp
            ((e 0).symm (a.val 0)).property
          simpa only [Nat.zero_add, pow_one] using h
    | succ n =>
        refine ⟨((e n).symm (a.val n)).property, ?_⟩
        have h : TateModule.mulP p B (n + 1) ((e (n + 1)).symm (a.val (n + 1))) =
            (e n).symm (a.val n) := by
          apply (e n).injective
          rw [← he, AddEquiv.apply_symm_apply, AddEquiv.apply_symm_apply]
          exact a.property n
        exact congrArg Subtype.val h
  · intro x
    apply Subtype.ext
    funext n
    cases n with
    | zero => exact (TateModule.apply_zero x).symm
    | succ n => exact congrArg Subtype.val ((e n).symm_apply_apply _)
  · intro a
    apply Subtype.ext
    funext n
    exact (e n).apply_symm_apply (a.val n)
  · intro x y
    apply Subtype.ext
    funext n
    exact (e n).map_add
      ⟨x.val (n + 1), TateModule.torsion x (n + 1)⟩
      ⟨y.val (n + 1), TateModule.torsion y (n + 1)⟩

/-- The actual prime-power Picard Tate module and actual integral étale H¹
are additively equivalent through the original finite Kummer comparisons. -/
def properKummerTateAdicEquiv (M : CurveModel K F)
    (p : ℕ+) [Fact (p : ℕ).Prime] (hp : IsUnit ((p : ℕ) : K)) :
    TateModule (p : ℕ) (Pic0 K F) ≃+ ellAdicCohomology M.C (p : ℕ) 1 :=
  tateSequentialEquiv (p : ℕ) (Pic0 K F)
    (fun n => finiteLevelCohomology M.C (p : ℕ) n 1)
    (fun n => finiteLevelReduction M.C (p : ℕ) n 1)
    (properKummerFiniteLevelEquiv M p hp)
    (properKummerFiniteLevelEquiv_transition M p hp)

/-- Every original projection is preserved by the integral comparison. -/
theorem properKummerTateAdicEquiv_projection
    (M : CurveModel K F) (p : ℕ+) [Fact (p : ℕ).Prime]
    (hp : IsUnit ((p : ℕ) : K)) (x : TateModule (p : ℕ) (Pic0 K F)) (n : ℕ) :
    ellAdicProjection M.C (p : ℕ) 1 n (properKummerTateAdicEquiv M p hp x) =
      properKummerFiniteLevelEquiv M p hp n
        ⟨x.val (n + 1), TateModule.torsion x (n + 1)⟩ := rfl

/-- Linearity follows from the original finite-approximation scalar actions
on both sides of the actual Kummer comparison. -/
def properKummerTateAdicLinearEquiv
    (M : CurveModel K F) (p : ℕ+) [Fact (p : ℕ).Prime]
    (hp : IsUnit ((p : ℕ) : K)) :
    TateModule (p : ℕ) (Pic0 K F) ≃ₗ[ℤ_[p]] ellAdicCohomology M.C (p : ℕ) 1 :=
  { properKummerTateAdicEquiv M p hp with
    map_smul' := fun c x => by
      apply ellAdicCohomology_ext M.C (p : ℕ) 1
      intro n
      change properKummerFiniteLevelEquiv M p hp n
          ⟨(c • x).val (n + 1), TateModule.torsion (c • x) (n + 1)⟩ =
        c • properKummerFiniteLevelEquiv M p hp n
          ⟨x.val (n + 1), TateModule.torsion x (n + 1)⟩
      rw [finiteLevel_smul_eq_appr_nsmul]
      have ht : (⟨(c • x).val (n + 1), TateModule.torsion (c • x) (n + 1)⟩ :
          Submodule.torsionBy ℤ (Pic0 K F) (((p : ℕ) ^ (n + 1) : ℕ) : ℤ)) =
          c.appr (n + 1) • ⟨x.val (n + 1), TateModule.torsion x (n + 1)⟩ := by
        apply Subtype.ext
        change (c.appr (n + 1) : ℤ) • x.val (n + 1) =
          c.appr (n + 1) • x.val (n + 1)
        rw [natCast_zsmul]
      rw [ht]
      exact map_nsmul (properKummerFiniteLevelEquiv M p hp n) _ _ }

end AnabelianGeometry.FiniteField
