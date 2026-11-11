/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.AlgebraicCurves.Divisors.Modulus.Modulus
public import Nyll.AlgebraicCurves.FunctionFields.Transcendence.CurveOver
public import Nyll.AlgebraicCurves.Models.Construction.Basic
public import Nyll.AlgebraicCurves.Models.Construction.CurveIsIntegral
public import Nyll.AlgebraicCurves.Models.Divisors.CartierIdealEquiv
public import Nyll.AlgebraicCurves.Models.Divisors.CartierRelativePointSums
public import Nyll.AlgebraicCurves.RelativeDivisors.PointSums.IEqProdKerGraphAlgClosed
public import Mathlib.AlgebraicGeometry.IdealSheaf.Functorial
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Data.Finsupp.Single

/-!
# Original Cartier multiplicity degree and relative divisor degree

The existing decomposition of a relative divisor over an algebraically
closed field is a product of exactly as many original point ideals as
its relative degree, with repetitions. The original Cartier modulus
comparison retains those repetitions. Its ordinary place degree is
therefore the original relative degree, including nonreduced divisors
and the empty divisor.
-/

@[expose] public section

noncomputable section

universe u v

open AlgebraicGeometry CategoryTheory Limits NeronModelInfra
open scoped BigOperators

namespace AlgebraicCurve.CurveModel

attribute [local instance] CurveModel.isIntegral CurveModel.isProper CurveModel.smooth

variable {K : Type u} [Field K] [IsAlgClosed K]
  {F : Type v} [Field F] [Algebra K F] (M : CurveModel K F)

private theorem apply_congr_of_proof_parameter
    {α : Type*} {β : Type*} {P : α → Prop}
    (f : ∀ a, P a → β) {a b : α} (h : a = b) (ha : P a) (hb : P b) :
    f a ha = f b hb := by
  cases h
  rfl

private theorem pointModulusSum_degree {r : ℕ}
    (p : Fin r → SchemeHomOver (𝟙 (Spec (CommRingCat.of K))) M.toBase) :
    (∑ i, Finsupp.single (M.pointEquivPlace (p i)) 1 : Modulus K F).degree = r := by
  have hCurve : IsCurveOver K F :=
    isCurveOver_of_isIntegral_of_smoothOfRelativeDimension_one
      M.toBase M.ffEquiv M.ffEquiv_algebraMap
  let d : Modulus K F →+ ℤ :=
    { toFun := Modulus.degree
      map_zero' := Modulus.degree_zero
      map_add' := Modulus.degree_add }
  change d (∑ i, Finsupp.single (M.pointEquivPlace (p i)) 1) = (r : ℤ)
  rw [map_sum]
  calc
    ∑ i, d (Finsupp.single (M.pointEquivPlace (p i)) 1) = ∑ _ : Fin r, (1 : ℤ) := by
      apply Finset.sum_congr rfl
      intro i hi
      change Divisor.degree
        (Finsupp.mapRange (fun n : ℕ => (n : ℤ)) (by rfl)
          (Finsupp.single (M.pointEquivPlace (p i)) 1)) = 1
      simp only [Finsupp.mapRange_single, Divisor.degree_single,
        IsCurveOver.deg_eq_one_of_isAlgClosed, Nat.cast_one, mul_one]
    _ = (r : ℤ) := by
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one]

/-- A degree-indexed original relative divisor has that same integer
degree under the original function-field Cartier modulus, whenever its
full ideal is the displayed identity-base-change ideal. -/
theorem cartierModulus_degree_eq_of_relativeDivisor {r : ℕ}
    (D : RelEffCartierDiv M.toBase r (𝟙 (Spec (CommRingCat.of K))))
    (I : M.C.IdealSheafData) (hI : I.IsInvertible)
    (hD : D.I = I.comap (pullback.fst M.toBase (𝟙 (Spec (CommRingCat.of K))))) :
    (M.cartierModulus I hI).degree = r := by
  obtain ⟨a, ha, hDa⟩ := D.exists_I_eq_prodKerGraph_of_isAlgClosed
  let p : Fin r → SchemeHomOver (𝟙 (Spec (CommRingCat.of K))) M.toBase :=
    fun i => ⟨a i, ha i⟩
  let π : pullback M.toBase (𝟙 (Spec (CommRingCat.of K))) ⟶ M.C :=
    pullback.fst M.toBase (𝟙 (Spec (CommRingCat.of K)))
  let J : M.C.IdealSheafData :=
    (prodKerGraph M.toBase (fun i => (p i).1) (fun i => (p i).2)).comap (inv π)
  have hJ : J = I := by
    change (prodKerGraph M.toBase a ha).comap (inv π) = I
    rw [← hDa, hD, ← Scheme.IdealSheafData.comap_comp,
      IsIso.inv_hom_id, Scheme.IdealSheafData.comap_id]
  have hJI : J.IsInvertible := hJ.symm ▸ hI
  have hmod : M.cartierModulus J hJI =
      ∑ i, Finsupp.single (M.pointEquivPlace (p i)) 1 :=
    M.cartierModulus_relativePointSum p hJI
  have hsame : M.cartierModulus I hI = M.cartierModulus J hJI :=
    apply_congr_of_proof_parameter
      (α := M.C.IdealSheafData) (β := Modulus K F)
      (P := fun L => L.IsInvertible)
      (fun L hL => M.cartierModulus L hL) hJ.symm hI hJI
  exact (congrArg (fun A : Modulus K F => A.degree) (hsame.trans hmod)).trans
    (M.pointModulusSum_degree p)

end AlgebraicCurve.CurveModel
