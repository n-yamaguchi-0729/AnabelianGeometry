/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.AlgebraicCurves.Models.FunctionFields.CurveMultiplicativeGroupVanishing
public import Nyll.EtaleCohomology.Classical.Adic
public import Nyll.EtaleCohomology.Classical.ConstantRootsOfUnityNaturality
public import Nyll.EtaleCohomology.Classical.FiniteLevelKummerKernel
public import Nyll.EtaleCohomology.Classical.FiniteLevelKummerKernelReduction
public import Nyll.EtaleCohomology.Classical.KummerSequence
public import Nyll.EtaleCohomology.Classical.MultiplicativeGroup
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.CategoryTheory.Sites.SheafCohomology.ExactSequences
public import Mathlib.GroupTheory.QuotientGroup.Defs

/-!
# Original finite H² on smooth proper curves

The proved vanishing of native H²(Gm) makes the actual finite-level Kummer
kernel the whole original finite coefficient cohomology group. The native
Kummer boundary therefore identifies this group with H¹(Gm) modulo the
finite exponent. This identification retains the original finite reduction
and the original boundary in the existing coherent primitive-root coordinates.
-/

@[expose] public section

universe u

noncomputable section

open AlgebraicGeometry CategoryTheory
open EtaleCohomology EtaleCohomology.Classical

namespace AlgebraicCurve

variable (K : Type u) [Field K] [IsAlgClosed K]
  {X : Scheme.{u}} [IsIntegral X] (c : X ⟶ Spec (.of K))
  [SmoothOfRelativeDimension 1 c] [IsProper c]
  (ℓ : ℕ) [Fact ℓ.Prime] (hℓ : IsUnit (ℓ : K))

/-- Vanishing of native H²(Gm) identifies the actual finite Kummer kernel
with the whole original finite coefficient group. -/
def smoothProperCurveFiniteLevelKernelEquiv (n : ℕ) :
    (finiteLevelH2ToMultiplicativeGroup c ℓ hℓ n).ker ≃+
      finiteLevelCohomology X ℓ n 2 where
  toFun := Subtype.val
  invFun a := ⟨a, smoothProperCurve_multiplicativeGroup_H2_eq_zero K c
    (finiteLevelH2ToMultiplicativeGroup c ℓ hℓ n a)⟩
  left_inv _ := Subtype.ext rfl
  right_inv _ := rfl
  map_add' _ _ := rfl

/-- Original finite cyclic H² is the quotient of native H¹(Gm) by the
actual coefficient exponent. The curve supplies the vanishing proof. -/
def smoothProperCurveFiniteLevelH2EquivH1Quotient (n : ℕ) :
    finiteLevelCohomology X ℓ n 2 ≃+
      (Sheaf.H.{u} (etaleMultiplicativeGroupSheaf X) 1 ⧸
        (nsmulAddMonoidHom (α := Sheaf.H.{u} (etaleMultiplicativeGroupSheaf X) 1)
          (ℓ ^ (n + 1))).range) :=
  ((finiteLevelKummerH1QuotientEquivH2Kernel c ℓ hℓ n).trans
    (smoothProperCurveFiniteLevelKernelEquiv K c ℓ hℓ n)).symm

/-- The inverse comparison sends an original H¹ class to its actual
Kummer boundary, expressed in the original coherent finite coefficients. -/
theorem smoothProperCurveFiniteLevelH2EquivH1Quotient_symm_mk (n : ℕ)
    (a : Sheaf.H.{u} (etaleMultiplicativeGroupSheaf X) 1) :
    (smoothProperCurveFiniteLevelH2EquivH1Quotient K c ℓ hℓ n).symm
        (QuotientAddGroup.mk a) =
      (finiteLevelKummerCohomologyEquiv c ℓ hℓ n 2).symm
        (Sheaf.H.δ (etaleKummerComplex_shortExact X
          (pow_pos (Fact.out : ℓ.Prime).pos (n + 1))
          (etaleKummerExponentUnit_of_base c
            (by simpa only [Nat.cast_pow] using hℓ.pow (n + 1)))) 1 2 rfl a) :=
  finiteLevelKummerH1QuotientEquivH2Kernel_mk_val c ℓ hℓ n a

/-- The original finite reduction of a boundary class is the boundary
of the original H¹(Gm) quotient reduction. -/
theorem smoothProperCurveFiniteLevelH2EquivH1Quotient_symm_reduction (n : ℕ)
    (a : Sheaf.H.{u} (etaleMultiplicativeGroupSheaf X) 1 ⧸
      (nsmulAddMonoidHom (α := Sheaf.H.{u} (etaleMultiplicativeGroupSheaf X) 1)
        (ℓ ^ ((n + 1) + 1))).range) :
    finiteLevelReduction X ℓ n 2
        ((smoothProperCurveFiniteLevelH2EquivH1Quotient K c ℓ hℓ (n + 1)).symm a) =
      (smoothProperCurveFiniteLevelH2EquivH1Quotient K c ℓ hℓ n).symm
        (ellPowerKummerH1QuotientReduction X ℓ n a) :=
  congrArg Subtype.val
    (finiteLevelKummerH1QuotientEquivH2Kernel_reduction c ℓ hℓ n a)

/-- The finite H² comparisons commute with the actual coefficient
reductions and the canonical native H¹(Gm) quotient reductions. -/
theorem smoothProperCurveFiniteLevelH2EquivH1Quotient_reduction (n : ℕ)
    (a : finiteLevelCohomology X ℓ (n + 1) 2) :
    smoothProperCurveFiniteLevelH2EquivH1Quotient K c ℓ hℓ n
        (finiteLevelReduction X ℓ n 2 a) =
      ellPowerKummerH1QuotientReduction X ℓ n
        (smoothProperCurveFiniteLevelH2EquivH1Quotient K c ℓ hℓ (n + 1) a) := by
  apply (smoothProperCurveFiniteLevelH2EquivH1Quotient K c ℓ hℓ n).symm.injective
  rw [AddEquiv.symm_apply_apply]
  simpa only [AddEquiv.symm_apply_apply] using
    smoothProperCurveFiniteLevelH2EquivH1Quotient_symm_reduction K c ℓ hℓ n
      (smoothProperCurveFiniteLevelH2EquivH1Quotient K c ℓ hℓ (n + 1) a)

include c hℓ in
/-- The original degree-two finite coefficient reductions are surjective
for a smooth proper integral curve over an algebraically closed field. -/
theorem smoothProperCurveFiniteLevelH2_reduction_surjective (n : ℕ) :
    Function.Surjective (finiteLevelReduction X ℓ n 2) := by
  intro a
  obtain ⟨b, hb⟩ := ellPowerKummerH1QuotientReduction_surjective X ℓ n
    (smoothProperCurveFiniteLevelH2EquivH1Quotient K c ℓ hℓ n a)
  refine ⟨(smoothProperCurveFiniteLevelH2EquivH1Quotient K c ℓ hℓ (n + 1)).symm b, ?_⟩
  apply (smoothProperCurveFiniteLevelH2EquivH1Quotient K c ℓ hℓ n).injective
  rw [smoothProperCurveFiniteLevelH2EquivH1Quotient_reduction,
    AddEquiv.apply_symm_apply, hb]

end AlgebraicCurve
