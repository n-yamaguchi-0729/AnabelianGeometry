/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.AnabelianGeometry.FiniteField.KummerCharacterInclusion
import Nyll.JacobianVarieties.WeilPairing.FiniteFieldNondegeneracy
import Nyll.JacobianVarieties.Pic0.TorsionBijectiveInjective
import Nyll.JacobianVarieties.WeilPairing.DivisorialPairingPairEqPair
import Nyll.AlgebraicCurves.Models.Kummer.SemilinearGenericCharacter
import Nyll.GaloisCohomology.Kummer.Concrete.SemilinearConjugation

/-!
# Actual Kummer–Weil coordinates of the proper fundamental group

Evaluating the original Kummer characters gives a character on Picard
torsion. The proved finite Weil duality supplies its unique torsion
coordinate. These coordinates satisfy the original multiplication
transitions and the original semilinear generic conjugation formula.

No curve-to-Jacobian fundamental-group comparison is assumed.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.PreGaloisCategory AlgebraicCurve
open ProCGroups

namespace AnabelianGeometry.FiniteField

private theorem properPicardTorsionInclusion_coe
    {K F : Type*} [Field K] [Field F] [Algebra K F] (m n : ℕ+)
    (x : Pic0.torsion K F (m : ℕ)) :
    (properPicardTorsionInclusion m n x : Pic0 K F) = x := by
  exact AddSubgroup.coe_inclusion _ x

private theorem properPicardTorsionTransition_coe
    {K F : Type*} [Field K] [Field F] [Algebra K F] (m n : ℕ+)
    (z : Pic0.torsion K F ((m * n : ℕ+) : ℕ)) :
    (properPicardTorsionTransition m n z : Pic0 K F) = (n : ℕ) • (z : Pic0 K F) := rfl

private theorem properPicardTorsionTransition_pair
    {K F : Type*} [Field K] [Field F] [Algebra K F] [HasPrincipalDivisors K F]
    (m n : ℕ+) (wm : DivisorialWeilPairingData K F (m : ℕ))
    (wmn : DivisorialWeilPairingData K F ((m * n : ℕ+) : ℕ))
    (z : Pic0.torsion K F ((m * n : ℕ+) : ℕ)) (x : Pic0.torsion K F (m : ℕ)) :
    wm.pair (properPicardTorsionTransition m n z) x =
      wmn.pair z (properPicardTorsionInclusion m n x) :=
  (wmn.pair_eq_pair_of_coe_eq_nsmul (m : ℕ) (n : ℕ) wm z x
    (properPicardTorsionInclusion m n x) (properPicardTorsionInclusion_coe m n x)
    (properPicardTorsionTransition m n z)
    ((properPicardTorsionTransition_coe m n z).trans (natCast_zsmul _ _).symm)).symm

variable {K F : Type} [Field K] [IsAlgClosed K] [Field F] [Algebra K F]
  [Algebra.EssFiniteType K F] [IsCurveOver K F]

/-- Evaluation of the actual Kummer characters at an original fundamental-group element. -/
def properKummerEvaluationCharacter
    (M : CurveModel K F) (n : ℕ+) (hn : IsUnit ((n : ℕ) : K))
    {Ω : Type} [Field Ω] [IsSepClosed Ω] (ξ : Spec (.of Ω) ⟶ M.C)
    (a : Aut (FiniteEtale.fiber ξ)) : HomPic0Gm K F (n : ℕ) := by
  let : TopologicalSpace (rootsOfUnity (n : ℕ) K) := ⊥
  let : DiscreteTopology (rootsOfUnity (n : ℕ) K) := ⟨rfl⟩
  exact
    { toFun x := ((M.kummerTorsionCharacter n hn ξ (Multiplicative.ofAdd x) a : Kˣ) : K)
      map_zero_eq_one' := by
        change ((M.kummerTorsionCharacter n hn ξ 1 a : Kˣ) : K) = 1
        rw [map_one]
        rfl
      map_add_eq_mul' x y := by
        change ((M.kummerTorsionCharacter n hn ξ
          (Multiplicative.ofAdd x * Multiplicative.ofAdd y) a : Kˣ) : K) = _
        rw [map_mul]
        rfl }

variable (k : Type) [Field k] [Finite k] [Algebra k K] [Algebra.IsAlgebraic k K]
  (M : CurveModel K F)
  (hfg : ∃ x : F, Transcendental K x ∧
    FiniteDimensional (IntermediateField.adjoin K ({x} : Set F)) F)

/-- The finite Kummer–Weil coordinate, constructed by proved finite duality. -/
def properKummerWeilCoordinate
    (n : ℕ+) (hn : IsUnit ((n : ℕ) : K)) [Finite (Pic0.torsion K F (n : ℕ))]
    {Ω : Type} [Field Ω] [IsSepClosed Ω] (ξ : Spec (.of Ω) ⟶ M.C)
    (w : DivisorialWeilPairingData K F (n : ℕ))
    (a : Aut (FiniteEtale.fiber ξ)) : Pic0.torsion K F (n : ℕ) := by
  have : NeZero ((n : ℕ) : K) := ⟨hn.ne_zero⟩
  exact (AddEquiv.ofBijective w.toHom
    (Pic0.torsion.bijective_of_injective w.toHom
      (w.toHom_injective_finiteField k hfg hn.ne_zero))).symm
        (Additive.ofMul (properKummerEvaluationCharacter M n hn ξ a))

/-- The constructed coordinate represents evaluation of every original Kummer character. -/
theorem properKummerWeilCoordinate_pair
    (n : ℕ+) (hn : IsUnit ((n : ℕ) : K)) [Finite (Pic0.torsion K F (n : ℕ))]
    {Ω : Type} [Field Ω] [IsSepClosed Ω] (ξ : Spec (.of Ω) ⟶ M.C)
    (w : DivisorialWeilPairingData K F (n : ℕ))
    (a : Aut (FiniteEtale.fiber ξ)) (x : Pic0.torsion K F (n : ℕ)) :
    w.pair (properKummerWeilCoordinate k M hfg n hn ξ w a) x =
      properKummerEvaluationCharacter M n hn ξ a x := by
  have : NeZero ((n : ℕ) : K) := ⟨hn.ne_zero⟩
  exact congrArg (fun χ : Additive (HomPic0Gm K F (n : ℕ)) => χ.toMul x)
    ((AddEquiv.ofBijective w.toHom
      (Pic0.torsion.bijective_of_injective w.toHom
        (w.toHom_injective_finiteField k hfg hn.ne_zero))).apply_symm_apply
          (Additive.ofMul (properKummerEvaluationCharacter M n hn ξ a)))

/-- The independently constructed finite coordinates satisfy the actual
multiplication transition, as proved from divisor Weil compatibility and
the literal Kummer coefficient inclusion. -/
theorem properKummerWeilCoordinate_transition
    (m n : ℕ+) (hm : IsUnit ((m : ℕ) : K))
    (hmn : IsUnit (((m * n : ℕ+) : ℕ) : K))
    [Finite (Pic0.torsion K F (m : ℕ))]
    [Finite (Pic0.torsion K F ((m * n : ℕ+) : ℕ))]
    {Ω : Type} [Field Ω] [Algebra M.C.functionField Ω]
    [IsSepClosed Ω] [IsSepClosure M.C.functionField Ω]
    (wm : DivisorialWeilPairingData K F (m : ℕ))
    (wmn : DivisorialWeilPairingData K F ((m * n : ℕ+) : ℕ)) :
    let ξ := Spec.map (CommRingCat.ofHom (algebraMap M.C.functionField Ω)) ≫
      M.C.fromSpecStalk (genericPoint M.C)
    ∀ a : Aut (FiniteEtale.fiber ξ),
      properPicardTorsionTransition m n
        (properKummerWeilCoordinate k M hfg (m * n) hmn ξ wmn a) =
      properKummerWeilCoordinate k M hfg m hm ξ wm a := by
  intro ξ a
  apply wm.toHom_injective_finiteField k hfg hm.ne_zero
  apply Additive.toMul.injective
  ext x
  change wm.pair _ x = wm.pair _ x
  exact (properPicardTorsionTransition_pair m n wm wmn
    (properKummerWeilCoordinate k M hfg (m * n) hmn ξ wmn a) x).trans
    ((properKummerWeilCoordinate_pair k M hfg (m * n) hmn ξ wmn a
      (properPicardTorsionInclusion m n x)).trans
      ((properKummerTorsionCharacter_generic_inclusion M m n hm hmn x a).trans
        (properKummerWeilCoordinate_pair k M hfg m hm ξ wm a x).symm))

/-- The original generic semilinear conjugation transports the actual
Kummer–Weil coordinate by the same semilinear Picard action. -/
theorem properKummerWeilCoordinate_generic_semilinear
    (n : ℕ+) (hn : IsUnit ((n : ℕ) : K)) [Finite (Pic0.torsion K F (n : ℕ))]
    {Ω : Type} [Field Ω] [Algebra M.C.functionField Ω]
    [IsSepClosed Ω] [IsSepClosure M.C.functionField Ω]
    (w : DivisorialWeilPairingData K F (n : ℕ))
    (g : SemilinearAut K F) (τ : M.C.functionField ≃+* M.C.functionField)
    (hτ : ∀ z : F, τ (M.ffEquiv z) = M.ffEquiv (SemilinearAut.toRingAut g z))
    (b : Ω ≃+* Ω)
    (hb : ∀ z : M.C.functionField,
      b (algebraMap M.C.functionField Ω z) = algebraMap M.C.functionField Ω (τ z))
    (ρ : Ω ≃ₐ[M.C.functionField] Ω) :
    let η := Spec.map (CommRingCat.ofHom (algebraMap M.C.functionField Ω))
    let ξ := η ≫ M.C.fromSpecStalk (genericPoint M.C)
    let s := fun σ : Ω ≃ₐ[M.C.functionField] Ω =>
      FiniteEtale.fundamentalGroupHom (M.C.fromSpecStalk (genericPoint M.C)) η
        (toAut (FiniteEtale.fiber η) (Ω ≃ₐ[M.C.functionField] Ω) σ)
    properKummerWeilCoordinate k M hfg n hn ξ w
      (s (KummerTheory.semilinearGaloisConjugate τ b hb ρ)) =
      g • properKummerWeilCoordinate k M hfg n hn ξ w (s ρ) := by
  intro η ξ s
  apply w.toHom_injective_finiteField k hfg hn.ne_zero
  apply Additive.toMul.injective
  ext x
  obtain ⟨y, rfl⟩ := (DistribMulAction.toAddEquiv (Pic0.torsion K F (n : ℕ)) g).surjective x
  change w.pair _ (g • y) = w.pair (g • _) (g • y)
  rw [properKummerWeilCoordinate_pair, w.pair_semilinearSmul,
    properKummerWeilCoordinate_pair]
  exact M.kummerTorsionCharacter_generic_semilinear n hn g τ hτ b hb y ρ

/-- The actual compatible Kummer–Weil coordinates, with multiplication
compatibility supplied by the preceding divisor calculation. -/
def properKummerWeilFamily
    (I : Submonoid ℕ+) (hI : ∀ n : I, IsUnit ((n.1 : ℕ) : K))
    [∀ n : I, Finite (Pic0.torsion K F (n.1 : ℕ))]
    (Ω : Type) [Field Ω] [Algebra M.C.functionField Ω]
    [IsSepClosed Ω] [IsSepClosure M.C.functionField Ω] :
    let ξ := Spec.map (CommRingCat.ofHom (algebraMap M.C.functionField Ω)) ≫
      M.C.fromSpecStalk (genericPoint M.C)
    Aut (FiniteEtale.fiber ξ) → RestrictedTateModule (Pic0 K F) I := by
  intro ξ a
  let W (n : I) : DivisorialWeilPairingData K F (n.1 : ℕ) :=
    Classical.choice (Pic0.nonempty_divisorialWeilPairingData_of_isAlgClosed
      K F hfg (n.1 : ℕ))
  let v (n : I) := properKummerWeilCoordinate k M hfg n.1 (hI n) ξ (W n) a
  refine ⟨fun n => ⟨(v n).val, ?_⟩, ?_⟩
  · exact (natCast_zsmul _ _).symm.trans (Pic0.mem_torsion.mp (v n).property)
  · intro m n
    have : Finite (Pic0.torsion K F ((m.1 * n.1 : ℕ+) : ℕ)) :=
      inferInstanceAs (Finite (Pic0.torsion K F ((m * n : I).1 : ℕ)))
    apply Subtype.ext
    exact congrArg (fun z : Pic0.torsion K F (m.1 : ℕ) => z.val)
      (properKummerWeilCoordinate_transition k M hfg m.1 n.1
        (hI m) (hI (m * n)) (W m) (W (m * n)) a)

/-- Family evaluation is the original finite Kummer–Weil coordinate. -/
theorem properKummerWeilFamily_evaluation
    (I : Submonoid ℕ+) (hI : ∀ n : I, IsUnit ((n.1 : ℕ) : K))
    [∀ n : I, Finite (Pic0.torsion K F (n.1 : ℕ))]
    (Ω : Type) [Field Ω] [Algebra M.C.functionField Ω]
    [IsSepClosed Ω] [IsSepClosure M.C.functionField Ω]
    (n : I) :
    let ξ := Spec.map (CommRingCat.ofHom (algebraMap M.C.functionField Ω)) ≫
      M.C.fromSpecStalk (genericPoint M.C)
    let w := Classical.choice (Pic0.nonempty_divisorialWeilPairingData_of_isAlgClosed
      K F hfg (n.1 : ℕ))
    ∀ a : Aut (FiniteEtale.fiber ξ),
      RestrictedTateModule.evaluation (Pic0 K F) I n
        (properKummerWeilFamily k M hfg I hI Ω a) =
          (properKummerWeilCoordinate k M hfg n.1 (hI n) ξ w a).val := by
  intro ξ w a
  rfl

end AnabelianGeometry.FiniteField
