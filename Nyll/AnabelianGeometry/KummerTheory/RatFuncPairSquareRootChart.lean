/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/
import Nyll.AnabelianGeometry.KummerTheory.RatFuncPairSquareRootCoordinate

/-! # The original quadratic root algebra over the actual open-chart field

Change only the coefficient presentation using the actual open function-field
coordinate. The quotient's root and the given pair square map are retained.
-/
noncomputable section
open AlgebraicCurve Polynomial

namespace AnabelianGeometry.KummerTheory

/-- Re-express the same root coordinate over the original open function field. -/
theorem ratFuncPairSquare_exists_rootCoordinate_over_chart
    {k F : Type} [Field k] [Field F]
    (c : RatFunc k ≃+* F) (eF : RatFunc k ≃ₐ[k] RatFunc k)
    (f : RatFunc k) (hf : eF RatFunc.X = f)
    (v : Place k (RatFunc k)) (hv : v.ord f = -1) :
    ∃ e : AdjoinRoot (Polynomial.X ^ 2 - Polynomial.C (c f)) ≃+* RatFunc k,
      e (AdjoinRoot.root (Polynomial.X ^ 2 - Polynomial.C (c f))) = RatFunc.X ∧
      ∀ z : F,
        e (AdjoinRoot.of (Polynomial.X ^ 2 - Polynomial.C (c f)) z) =
          ratFuncPairSquareHom eF (c.symm z) := by
  obtain ⟨eR, hroot, hcoeff⟩ := ratFuncPairSquare_exists_rootCoordinate eF f hf v hv
  have hp : Associated
      ((Polynomial.X ^ 2 - Polynomial.C (c f)).map c.symm)
      (Polynomial.X ^ 2 - Polynomial.C f) := by
    rw [Polynomial.map_sub, Polynomial.map_pow, Polynomial.map_X,
      Polynomial.map_C]
    change Associated (Polynomial.X ^ 2 - Polynomial.C (c.symm (c f)))
      (Polynomial.X ^ 2 - Polynomial.C f)
    rw [c.symm_apply_apply]
  let eC := AdjoinRoot.mapRingEquiv c.symm
    (Polynomial.X ^ 2 - Polynomial.C (c f)) (Polynomial.X ^ 2 - Polynomial.C f) hp
  refine ⟨eC.trans eR.toRingEquiv, ?_, ?_⟩
  · change eR (AdjoinRoot.map (c.symm : F →+* RatFunc k)
        (Polynomial.X ^ 2 - Polynomial.C (c f))
        (Polynomial.X ^ 2 - Polynomial.C f) hp.symm.dvd
        (AdjoinRoot.root (Polynomial.X ^ 2 - Polynomial.C (c f)))) = RatFunc.X
    rw [AdjoinRoot.map_root]
    exact hroot
  · intro z
    change eR (AdjoinRoot.map (c.symm : F →+* RatFunc k)
        (Polynomial.X ^ 2 - Polynomial.C (c f))
        (Polynomial.X ^ 2 - Polynomial.C f) hp.symm.dvd
        (AdjoinRoot.of (Polynomial.X ^ 2 - Polynomial.C (c f)) z)) =
      ratFuncPairSquareHom eF (c.symm z)
    rw [AdjoinRoot.map_of]
    change eR (AdjoinRoot.of (Polynomial.X ^ 2 - Polynomial.C f) (c.symm z)) = _
    exact hcoeff (c.symm z)

end AnabelianGeometry.KummerTheory
