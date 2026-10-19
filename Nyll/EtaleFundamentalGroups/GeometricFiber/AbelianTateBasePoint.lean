/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.EtaleFundamentalGroups.GeometricFiber.AbelianTateComparison

/-!
# Basepoint-independent evaluation of the existing Tate comparison

The commutative Tate target removes the inner conjugation between two fibre
comparisons. Thus the existing comparison can be evaluated using any specified
comparison with the unit basepoint.
-/

noncomputable section

open CategoryTheory CategoryTheory.PreGaloisCategory
open AlgebraicGeometry AlgebraicGeometry.FiniteEtale

namespace GoodReductionJacobian.RelativeGroupLaw

variable {K : Type} [Field K] [IsAlgClosed K] [CharZero K]
  {A : Scheme} {f : A ⟶ Spec (.of K)}
  [IsProper f] [Smooth f] [GeometricallyConnected f]
  (G : RelativeGroupLaw K f) (hc : G.IsCommutative)
  {Ω : Type} [Field Ω] [IsSepClosed Ω] (xi : Spec (.of Ω) ⟶ A)

/-- The existing Tate comparison is independent of its chosen fibre comparison. -/
theorem fundamentalGroupEquivFullTateAt_eq
    (b : fiber xi ≅ fiber (G.one (𝟙 (Spec (.of K)))).1) (γ : π₁ᵉᵗ(xi)) :
    G.fundamentalGroupEquivFullTateAt hc xi γ =
      G.fundamentalGroupEquivFullTate hc (continuousConjAut b γ) := by
  have : ConnectedSpace A := GeometricallyConnected.connectedSpace f f.isOpenMap
  let t : fiber xi ≅ fiber (G.one (𝟙 (Spec (.of K)))).1 :=
    Classical.choice (nonempty_fiber_iso xi (G.one (𝟙 (Spec (.of K)))).1)
  change G.fundamentalGroupEquivFullTate hc (continuousConjAut t γ) = _
  let e := G.fundamentalGroupEquivFullTate hc
  let d : Aut (fiber (G.one (𝟙 (Spec (.of K)))).1) := b.symm ≪≫ t
  let c := continuousConjAut b γ
  have hconj := continuousConjAut_eq_conj b t γ
  have hmap : e (MulAut.conj d c) = e c := by
    change e (d * c * d⁻¹) = e c
    calc
      e (d * c * d⁻¹) = e (d * c) * e (d⁻¹) := e.map_mul _ _
      _ = e d * e c * (e d)⁻¹ :=
        congrArg₂ (fun x y => x * y) (e.map_mul d c) (map_inv e d)
      _ = e d * (e d)⁻¹ * e c := mul_right_comm _ _ _
      _ = e c :=
        (congrArg (fun x => x * e c) (_root_.mul_inv_cancel (e d))).trans (_root_.one_mul _)
  exact (congrArg e hconj).trans hmap

/-- Every finite coordinate is the actual multiplication monodromy, computed
with any specified comparison to the unit basepoint. -/
theorem fundamentalGroupEquivFullTateAt_projection
    (b : fiber xi ≅ fiber (G.one (𝟙 (Spec (.of K)))).1)
    (γ : π₁ᵉᵗ(xi)) (n : ℕ+) :
    ProCGroups.FullTateModule.projection (G.AlgPoints hc K) n
        (Multiplicative.toAdd (G.fundamentalGroupEquivFullTateAt hc xi γ)) =
      G.multiplicationMonodromy hc n (continuousConjAut b γ) := by
  rw [G.fundamentalGroupEquivFullTateAt_eq hc xi b γ,
    G.fundamentalGroupEquivFullTate_projection]

end GoodReductionJacobian.RelativeGroupLaw
