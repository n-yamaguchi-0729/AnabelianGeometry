/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.AlgebraicCurves.Models.Divisors.CartierPointSums
public import Nyll.AlgebraicCurves.RelativeDivisors.PointSums.RelEffCartierDivSum
public import Nyll.AlgebraicCurves.Geometry.Schemes.BaseChange.HomPullbackKerPowInvModuleIso
public import Nyll.AlgebraicCurves.Geometry.Sheaves.Pullback.PullbackFoldrTwistIso

/-! # Actual relative point divisors and function-field multiplicities -/

@[expose] public section

noncomputable section

universe u v

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits NeronModelInfra
open AlgebraicCurves.Geometry.Schemes.Proofs
open Scheme_Hom_nonempty_pullback_ker_pow_invModule_iso_of_isIso.AlgebraicGeometry.BCKerGlue
open AlgebraicCurves.Geometry.Sheaves.Proofs
open Scheme_Modules_nonempty_pullback_foldr_twist_iso.AlgebraicGeometry.Scheme.IdealSheafData
open scoped BigOperators

namespace AlgebraicCurve.CurveModel

attribute [local instance] CurveModel.isIntegral CurveModel.isProper CurveModel.smooth

variable {K : Type u} [Field K] [IsAlgClosed K]
  {F : Type v} [Field F] [Algebra K F] (M : CurveModel K F)

omit [IsAlgClosed K] in
/-- Removing the identity fibre product sends the full graph-product ideal to
the product of the original point kernels. -/
theorem prodKerGraph_comap_identity {n : ℕ}
    (p : Fin n → SchemeHomOver (𝟙 (Spec (CommRingCat.of K))) M.toBase) :
    (prodKerGraph M.toBase (fun i => (p i).1) (fun i => (p i).2)).comap
      (inv (pullback.fst M.toBase (𝟙 (Spec (CommRingCat.of K))))) =
        ∏ i, (p i).1.ker := by
  classical
  rw [prodKerGraph_eq_prod]
  rw [comap_finset_prod]
  apply Finset.prod_congr rfl
  intro i hi
  apply ker_comap_eq_ker
  apply (cancel_mono (pullback.fst M.toBase (𝟙 (Spec (CommRingCat.of K))))).mp
  rw [Category.assoc, IsIso.inv_hom_id, Category.comp_id, graphOver_fst]

/-- The divisor coefficients of an actual relative sum of rational points are
exactly the finite sum of the corresponding places, including repetitions. -/
theorem cartierModulus_relativePointSum {n : ℕ}
    (p : Fin n → SchemeHomOver (𝟙 (Spec (CommRingCat.of K))) M.toBase)
    (hI : ((prodKerGraph M.toBase (fun i => (p i).1) (fun i => (p i).2)).comap
      (inv (pullback.fst M.toBase (𝟙 (Spec (CommRingCat.of K)))))).IsInvertible) :
    M.cartierModulus
      ((prodKerGraph M.toBase (fun i => (p i).1) (fun i => (p i).2)).comap
        (inv (pullback.fst M.toBase (𝟙 (Spec (CommRingCat.of K)))))) hI =
      ∑ i, Finsupp.single (M.pointEquivPlace (p i)) 1 := by
  have he := M.prodKerGraph_comap_identity p
  have hp : (∏ i, (p i).1.ker).IsInvertible := he ▸ hI
  have h := congrArg M.cartierIdealEquiv
    (show (⟨_, hI⟩ : {I : M.C.IdealSheafData // I.IsInvertible}) = ⟨_, hp⟩ from
      Subtype.ext he)
  exact h.trans (M.cartierModulus_point_prod Finset.univ p)

end AlgebraicCurve.CurveModel
