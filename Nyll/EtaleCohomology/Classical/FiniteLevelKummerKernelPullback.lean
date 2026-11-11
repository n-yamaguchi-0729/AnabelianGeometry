/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.EtaleCohomology.Classical.Adic
public import Nyll.EtaleCohomology.Classical.AdicPullback
public import Nyll.EtaleCohomology.Classical.ConstantRootsOfUnityNaturality
public import Nyll.EtaleCohomology.Classical.FiniteLevelKummerKernel
public import Nyll.EtaleCohomology.Classical.FiniteLevelKummerKernelReduction
public import Nyll.EtaleCohomology.Classical.KummerH2Functoriality
public import Nyll.EtaleCohomology.Classical.KummerPullback
public import Nyll.EtaleCohomology.Classical.MultiplicativeGroup
public import Mathlib.GroupTheory.QuotientGroup.Defs

/-!
# Actual scheme pullback on the finite degree-two Kummer kernel

The original finite coefficient pullback preserves the actual kernel of
the map to H²(Gm). Its comparison with native H¹(Gm) modulo the exponent
commutes with the original pullback on units. These maps also commute
with the original finite coefficient reductions.
-/

@[expose] public section

noncomputable section

universe u

open AlgebraicGeometry CategoryTheory
open EtaleCohomology.Classical

namespace EtaleCohomology

variable {K : Type u} [Field K] [IsAlgClosed K]
  {X Y : Scheme.{u}} (f : X ⟶ Y) (c : Y ⟶ Spec (.of K))
  (ℓ : ℕ) [Fact ℓ.Prime] (hℓ : IsUnit (ℓ : K))

/-- The finite coefficient map to native H²(Gm) commutes with the
original pullback on both coefficient sheaves. -/
theorem finiteLevelH2ToMultiplicativeGroup_pullback (n : ℕ)
    (a : finiteLevelCohomology Y ℓ n 2) :
    finiteLevelH2ToMultiplicativeGroup (f ≫ c) ℓ hℓ n
        (finiteLevelCohomologyPullback ℓ f n 2 a) =
      etaleMultiplicativeGroupCohomologyPullback f 2
        (finiteLevelH2ToMultiplicativeGroup c ℓ hℓ n a) := by
  rw [finiteLevelH2ToMultiplicativeGroup_apply,
    finiteLevelKummerCohomologyEquiv_pullback,
    etaleRootsOfUnityH2ToMultiplicativeGroup_pullback,
    finiteLevelH2ToMultiplicativeGroup_apply]

/-- Restriction of the actual finite coefficient pullback to the actual
kernel of the map to native H²(Gm). -/
def finiteLevelKummerH2KernelPullback (n : ℕ) :
    (finiteLevelH2ToMultiplicativeGroup c ℓ hℓ n).ker →+
      (finiteLevelH2ToMultiplicativeGroup (f ≫ c) ℓ hℓ n).ker where
  toFun a := ⟨finiteLevelCohomologyPullback ℓ f n 2 a.val,
    (finiteLevelH2ToMultiplicativeGroup_pullback f c ℓ hℓ n a.val).trans
      ((congrArg (etaleMultiplicativeGroupCohomologyPullback f 2) a.property).trans
        (map_zero (etaleMultiplicativeGroupCohomologyPullback f 2)))⟩
  map_zero' := Subtype.ext (map_zero (finiteLevelCohomologyPullback ℓ f n 2))
  map_add' a b := Subtype.ext
    (map_add (finiteLevelCohomologyPullback ℓ f n 2) a.val b.val)

/-- The restricted map retains the original finite cohomology pullback. -/
theorem finiteLevelKummerH2KernelPullback_val (n : ℕ)
    (a : (finiteLevelH2ToMultiplicativeGroup c ℓ hℓ n).ker) :
    (finiteLevelKummerH2KernelPullback f c ℓ hℓ n a).val =
      finiteLevelCohomologyPullback ℓ f n 2 a.val := rfl

/-- The native Kummer quotient equivalence commutes with the original
finite coefficient pullback and the actual pullback on H¹(Gm). -/
theorem finiteLevelKummerH1QuotientEquivH2Kernel_pullback (n : ℕ)
    (a : Sheaf.H.{u} (etaleMultiplicativeGroupSheaf Y) 1 ⧸
      (nsmulAddMonoidHom (α := Sheaf.H.{u} (etaleMultiplicativeGroupSheaf Y) 1)
        (ℓ ^ (n + 1))).range) :
    finiteLevelKummerH2KernelPullback f c ℓ hℓ n
        (finiteLevelKummerH1QuotientEquivH2Kernel c ℓ hℓ n a) =
      finiteLevelKummerH1QuotientEquivH2Kernel (f ≫ c) ℓ hℓ n
        (etaleKummerH1QuotientPullback f (ℓ ^ (n + 1)) a) := by
  refine Quotient.inductionOn' a ?_
  intro b
  rw [etaleKummerH1QuotientPullback_mk]
  apply Subtype.ext
  rw [finiteLevelKummerH2KernelPullback_val,
    finiteLevelKummerH1QuotientEquivH2Kernel_mk_val,
    finiteLevelKummerH1QuotientEquivH2Kernel_mk_val]
  apply (finiteLevelKummerCohomologyEquiv (f ≫ c) ℓ hℓ n 2).injective
  rw [finiteLevelKummerCohomologyEquiv_pullback,
    AddEquiv.apply_symm_apply, AddEquiv.apply_symm_apply]
  exact etaleKummerBoundary_one_pullback f
    (pow_pos (Fact.out : ℓ.Prime).pos (n + 1))
    (etaleKummerExponentUnit_of_base c
      (by simpa only [Nat.cast_pow] using hℓ.pow (n + 1))) b

/-- The actual pullbacks form a morphism of the original finite Kummer
kernel systems, with their original coefficient reductions. -/
theorem finiteLevelKummerH2KernelPullback_reduction (n : ℕ)
    (a : (finiteLevelH2ToMultiplicativeGroup c ℓ hℓ (n + 1)).ker) :
    finiteLevelKummerH2KernelPullback f c ℓ hℓ n
        (finiteLevelKummerH2KernelReduction c ℓ hℓ n a) =
      finiteLevelKummerH2KernelReduction (f ≫ c) ℓ hℓ n
        (finiteLevelKummerH2KernelPullback f c ℓ hℓ (n + 1) a) := by
  apply Subtype.ext
  rw [finiteLevelKummerH2KernelPullback_val,
    finiteLevelKummerH2KernelReduction_val,
    finiteLevelKummerH2KernelReduction_val,
    finiteLevelKummerH2KernelPullback_val]
  exact finiteLevelCohomologyPullback_reduction ℓ f n 2 a.val

end EtaleCohomology
