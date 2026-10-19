/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.AnabelianGeometry.ArithmeticIsomorphisms.Basic

/-! # Independence of the lift used for arithmetic normalization

The discrepancy in the quotient is specified, rather than inferred merely
from commutation up to an unspecified inner automorphism.
-/

noncomputable section

namespace AnabelianGeometry.ArithmeticIsomorphisms

universe u v w

variable {G : Type u} {H : Type v} {Γ : Type w}
  [Group G] [Group H] [Group Γ]
  [TopologicalSpace G] [TopologicalSpace H] [IsTopologicalGroup H]
  (p : G →* Γ) (q : H →* Γ)

/-- Correct the specified arithmetic discrepancy by a specified lift. -/
def normalize (e : G ≃ₜ* H) (d : Γ)
    (he : ∀ g : G, q (e g) = d * p g * d⁻¹)
    (c : H) (hc : q c = d⁻¹) : OverQuotientEquiv p q :=
  ⟨ProCGroups.innerCorrectedGroupEquiv e c, fun g => by
    change q (c * e g * c⁻¹) = p g
    rw [map_mul, map_mul, map_inv, hc, he g]
    simp only [inv_inv, mul_assoc, inv_mul_cancel_left, inv_mul_cancel, mul_one]⟩

/-- Two lifts of the same arithmetic correction yield the same geometric outer class. -/
theorem normalize_geometricInnerRelated (e : G ≃ₜ* H) (d : Γ)
    (he : ∀ g : G, q (e g) = d * p g * d⁻¹)
    (c c' : H) (hc : q c = d⁻¹) (hc' : q c' = d⁻¹) :
    GeometricInnerRelated (normalize p q e d he c hc)
      (normalize p q e d he c' hc') := by
  refine ⟨c' * c⁻¹, ?_, ?_⟩
  · rw [map_mul, map_inv, hc, hc', inv_inv, inv_mul_cancel]
  · intro g
    change c' * e g * c'⁻¹ =
      (c' * c⁻¹) * (c * e g * c⁻¹) * (c' * c⁻¹)⁻¹
    simp only [mul_inv_rev, inv_inv, mul_assoc, inv_mul_cancel_left]

/-- A surjective quotient supplies a normalized outer class without choosing a lift in its API. -/
def normalizedOuterEquiv (e : G ≃ₜ* H) (hq : Function.Surjective q) (d : Γ)
    (he : ∀ g : G, q (e g) = d * p g * d⁻¹) : OuterEquiv p q :=
  OuterEquiv.mk (normalize p q e d he (Classical.choose (hq d⁻¹))
    (Classical.choose_spec (hq d⁻¹)))

/-- Every actual lift represents the class constructed by normalization. -/
theorem normalizedOuterEquiv_eq (e : G ≃ₜ* H) (hq : Function.Surjective q) (d : Γ)
    (he : ∀ g : G, q (e g) = d * p g * d⁻¹)
    (c : H) (hc : q c = d⁻¹) :
    normalizedOuterEquiv p q e hq d he =
      OuterEquiv.mk (normalize p q e d he c hc) := by
  apply Quotient.sound
  exact normalize_geometricInnerRelated p q e d he
    (Classical.choose (hq d⁻¹)) c (Classical.choose_spec (hq d⁻¹)) hc

end AnabelianGeometry.ArithmeticIsomorphisms
