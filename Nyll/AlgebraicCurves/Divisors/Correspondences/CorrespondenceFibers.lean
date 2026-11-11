/-
Copyright (c) 2026 Naganori Yamaguchi (local additions and compilation).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
Repository maintainer: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.

The original local additions in the following modules have no established direct
Anthropic source-file match:
- Divisor_correspondence_congr
- Divisor_correspondence_single
- Divisor_correspondence_single_of_forall_restrictAlong_eq
- Divisor_correspondence_single_eq_finrankAlong_smul
Adapted Anthropic FLT sources (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_AlgebraicCurve_Divisor_correspondence_single_one_apply_eq_sum_and_eq_finsum.lean
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_AlgebraicCurve_Divisor_mem_support_correspondence_single_iff_exists_and_iff_mem_support_correspondence_single.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md
-/

module

public import Nyll.AlgebraicCurves.Divisors.Correspondences.Correspondences
public import Nyll.AlgebraicCurves.Places.Ramification.SumRamificationIndexMulInertiaDegAlong
public import Nyll.AlgebraicCurves.Places.Ramification.InertiaDegPosFiniteDimensional

/-!
# Correspondence Fibers
-/

@[expose] public section

section

/-!
# Divisor correspondence congr
-/

section ProofImplementation

namespace AlgebraicCurves.Divisors.Proofs.Divisor_correspondence_congr

open IsDedekindDomain AlgebraicCurve

theorem _root_.AlgebraicCurve.Divisor.correspondence_congr {K F F₁ : Type*} [Field K] [Field F]
  [Field F₁] [Algebra K F] [Algebra K F₁] [HasPrincipalDivisors K F₁] {φ ψ φ' ψ' : F →ₐ[K] F₁}
  (hφeq : φ = φ') (hψeq : ψ = ψ') (hφ : φ.toRingHom.IsIntegral) (hψ : ψ.toRingHom.IsIntegral) (hφ'
  : φ'.toRingHom.IsIntegral) (hψ' : ψ'.toRingHom.IsIntegral) (D : Divisor K F) :
  Divisor.correspondence φ ψ hφ hψ D = Divisor.correspondence φ' ψ' hφ' hψ' D := by
  subst hφeq
  subst hψeq
  rfl
end AlgebraicCurves.Divisors.Proofs.Divisor_correspondence_congr
end ProofImplementation

end

section

/-!
# Divisor correspondence single
-/

section ProofImplementation

namespace AlgebraicCurves.Divisors.Proofs.Divisor_correspondence_single

open AlgebraicCurve AlgebraicCurve.SemilinearAut
open scoped Pointwise

noncomputable section

theorem _root_.AlgebraicCurve.Divisor.correspondence_single {K F F' : Type*} [Field K] [Field F]
  [Field F'] [Algebra K F] [Algebra K F'] [HasPrincipalDivisors K F'] (φ ψ : F →ₐ[K] F') (hφ :
  φ.toRingHom.IsIntegral) (hψ : ψ.toRingHom.IsIntegral) (v : Place K F) (n : ℤ) :
  Divisor.correspondence φ ψ hφ hψ (Finsupp.single v n) = ∑ w ∈ Place.fiberAlong φ hφ v,
  Finsupp.single (w.restrictAlong ψ hψ) (n * (w.ramificationIndexAlong φ : ℤ) * (w.inertiaDegAlong
  ψ hψ : ℤ)) := by
  rw [Divisor.correspondence_apply, Divisor.pullbackAlong_single, map_sum]
  exact Finset.sum_congr rfl fun w _ => Divisor.pushforwardAlong_single ψ hψ w _

end
end AlgebraicCurves.Divisors.Proofs.Divisor_correspondence_single
end ProofImplementation

end

section

/-!
# Divisor correspondence single of forall restrict Along eq
-/

section ProofImplementation

namespace AlgebraicCurves.Divisors.Proofs.Divisor_correspondence_single_of_forall_restrictAlong_eq

open AlgebraicCurve AlgebraicCurve.SemilinearAut
open scoped Pointwise

noncomputable section

theorem _root_.AlgebraicCurve.Divisor.correspondence_single_of_forall_restrictAlong_eq {K F F' :
  Type*} [Field K] [Field F] [Field F'] [Algebra K F] [Algebra K F'] [HasPrincipalDivisors K F'] (φ
  ψ : F →ₐ[K] F') (hφ : φ.toRingHom.IsIntegral) (hψ : ψ.toRingHom.IsIntegral) (v : Place K F)
  (hcoll : ∀ w ∈ Place.fiberAlong φ hφ v, w.restrictAlong ψ hψ = v) (n : ℤ) :
  Divisor.correspondence φ ψ hφ hψ (Finsupp.single v n) = Finsupp.single v (n * ∑ w ∈
  Place.fiberAlong φ hφ v, (w.ramificationIndexAlong φ : ℤ) * (w.inertiaDegAlong ψ hψ : ℤ)) := by
  rw [Divisor.correspondence_single φ ψ hφ hψ v n, Finset.mul_sum, Finsupp.single_finsetSum]
  exact Finset.sum_congr rfl fun w hw => by rw [hcoll w hw, mul_assoc]

end
end AlgebraicCurves.Divisors.Proofs.Divisor_correspondence_single_of_forall_restrictAlong_eq
end ProofImplementation

end

section

/-!
# Divisor correspondence single eq finrank Along smul
-/

section ProofImplementation

namespace AlgebraicCurves.Divisors.Proofs.Divisor_correspondence_single_eq_finrankAlong_smul

open AlgebraicCurve AlgebraicCurve.SemilinearAut
open scoped Pointwise

noncomputable section

theorem _root_.AlgebraicCurve.Divisor.correspondence_single_eq_finrankAlong_smul {K F F' : Type*}
  [Field K] [Field F] [Field F'] [Algebra K F] [Algebra K F'] [HasPrincipalDivisors K F'] (φ ψ : F
  →ₐ[K] F') (hφ : φ.toRingHom.IsIntegral) (hψ : ψ.toRingHom.IsIntegral) (hfin : FiniteAlong K φ)
  (hsep : SeparableAlong K φ) (v : Place K F) (hcoll : ∀ w ∈ Place.fiberAlong φ hφ v,
  w.restrictAlong ψ hψ = v) (hfψ : ∀ w ∈ Place.fiberAlong φ hφ v, w.inertiaDegAlong ψ hψ = 1) (hfφ
  : ∀ w ∈ Place.fiberAlong φ hφ v, w.inertiaDegAlong φ hφ = 1) (n : ℤ) : Divisor.correspondence φ ψ
  hφ hψ (Finsupp.single v n) = (finrankAlong K φ : ℤ) • Finsupp.single v n := by
  rw [Divisor.correspondence_single_of_forall_restrictAlong_eq φ ψ hφ hψ v hcoll n,
    Finsupp.smul_single,
    smul_eq_mul, mul_comm (finrankAlong K φ : ℤ) n]
  congr 1
  rw [← Place.sum_ramificationIndexAlong_mul_inertiaDegAlong φ hφ hfin hsep v]
  congr 1
  exact Finset.sum_congr rfl fun w hw => by rw [hfψ w hw, hfφ w hw]

end
end AlgebraicCurves.Divisors.Proofs.Divisor_correspondence_single_eq_finrankAlong_smul
end ProofImplementation

end

section

/-!
# Divisor correspondence single one apply eq sum and eq finsum
-/

section ProofImplementation

namespace AlgebraicCurves.Divisors.Proofs
namespace Divisor_correspondence_single_one_apply_eq_sum_and_eq_finsum

open AlgebraicCurve

namespace IdentB0

section Generic

variable {K F F' : Type*} [Field K] [Field F] [Field F'] [Algebra K F] [Algebra K F']
variable [HasPrincipalDivisors K F']
variable (φ ψ : F →ₐ[K] F') (hφ : φ.toRingHom.IsIntegral) (hψ : ψ.toRingHom.IsIntegral)

open Classical in
theorem correspondence_single_one_apply (x y : Place K F) :
    Divisor.correspondence φ ψ hφ hψ (Finsupp.single x 1) y =
      ∑ W ∈ Place.fiberAlong φ hφ x,
        if W.restrictAlong ψ hψ = y then
          (W.ramificationIndexAlong φ : ℤ) * (W.inertiaDegAlong ψ hψ : ℤ) else 0 := by
  classical
  rw [Divisor.correspondence_apply, Divisor.pullbackAlong_single, map_sum, Finset.sum_apply']
  refine Finset.sum_congr rfl fun W _ => ?_
  rw [Divisor.pushforwardAlong_single, Finsupp.single_apply, one_mul]

open Classical in
theorem correspondence_single_one_apply_eq_finsum (x y : Place K F) :
    Divisor.correspondence φ ψ hφ hψ (Finsupp.single x 1) y =
      ∑ᶠ W : Place K F',
        if W.restrictAlong φ hφ = x ∧ W.restrictAlong ψ hψ = y then
          (W.ramificationIndexAlong φ : ℤ) * (W.inertiaDegAlong ψ hψ : ℤ) else 0 := by
  classical
  rw [correspondence_single_one_apply]
  symm
  rw [finsum_eq_sum_of_support_subset _ (s := Place.fiberAlong φ hφ x)]
  · refine Finset.sum_congr rfl fun W hW => ?_
    rw [Place.mem_fiberAlong] at hW
    simp only [hW, true_and]
  · intro W hW
    rw [Function.mem_support] at hW
    simp only [Finset.mem_coe, Place.mem_fiberAlong]
    by_contra hx
    exact hW (ite_eq_right fun h => hx h.1)

end Generic

end IdentB0

open Classical in
theorem _root_.AlgebraicCurve.Divisor.correspondence_single_one_apply_eq_sum_and_eq_finsum
    {K F F' : Type*} [Field K] [Field F] [Field F'] [Algebra K F] [Algebra K F']
    [HasPrincipalDivisors K F']
    (φ ψ : F →ₐ[K] F') (hφ : φ.toRingHom.IsIntegral) (hψ : ψ.toRingHom.IsIntegral) (x y : Place K
      F) :
    (Divisor.correspondence φ ψ hφ hψ (Finsupp.single x 1) y =
      ∑ W ∈ Place.fiberAlong φ hφ x,
        if W.restrictAlong ψ hψ = y then (W.ramificationIndexAlong φ : ℤ) * (W.inertiaDegAlong ψ hψ
          : ℤ) else 0) ∧
    (Divisor.correspondence φ ψ hφ hψ (Finsupp.single x 1) y =
      ∑ᶠ W : Place K F',
        if W.restrictAlong φ hφ = x ∧ W.restrictAlong ψ hψ = y then
          (W.ramificationIndexAlong φ : ℤ) * (W.inertiaDegAlong ψ hψ : ℤ) else 0) := by
  exact ⟨IdentB0.correspondence_single_one_apply φ ψ hφ hψ x y,
    IdentB0.correspondence_single_one_apply_eq_finsum φ ψ hφ hψ x y⟩
end AlgebraicCurves.Divisors.Proofs.Divisor_correspondence_single_one_apply_eq_sum_and_eq_finsum
end ProofImplementation

end

section

/-!
# Divisor mem support correspondence single iff exists and iff mem support correspondence
single
-/

section ProofImplementation

namespace AlgebraicCurve.Divisor

open _root_.AlgebraicCurve

theorem mem_support_correspondence_single_iff_exists_and_iff_mem_support_correspondence_single
    {K F F' : Type*} [Field K] [Field F] [Field F'] [Algebra K F] [Algebra K F']
      [HasPrincipalDivisors K F']
    (φ ψ : F →ₐ[K] F') (hφ : φ.toRingHom.IsIntegral) (hψ : ψ.toRingHom.IsIntegral)
    (hfφ : FiniteAlong K φ) (hfψ : FiniteAlong K ψ) (P Q : Place K F) :
    (Q ∈ (Divisor.correspondence φ ψ hφ hψ (Finsupp.single P 1)).support ↔
        ∃ R : Place K F', R.restrictAlong φ hφ = P ∧ R.restrictAlong ψ hψ = Q) ∧
    (Q ∈ (Divisor.correspondence φ ψ hφ hψ (Finsupp.single P 1)).support ↔
        P ∈ (Divisor.correspondence ψ φ hψ hφ (Finsupp.single Q 1)).support) := by
  have key : ∀ (φ ψ : F →ₐ[K] F') (hφ : φ.toRingHom.IsIntegral) (hψ : ψ.toRingHom.IsIntegral)
      (hfψ : FiniteAlong K ψ) (P Q : Place K F),
      Q ∈ (Divisor.correspondence φ ψ hφ hψ (Finsupp.single P 1)).support ↔
        ∃ R : Place K F', R.restrictAlong φ hφ = P ∧ R.restrictAlong ψ hψ = Q := by
    intro φ ψ hφ hψ hfψ P Q
    classical
    have he : ∀ R : Place K F', 0 < R.ramificationIndexAlong φ := fun R => by
      let := algebraAlong φ
      have := isIntegral_along φ hφ
      exact R.ramificationIndex_pos
    have hf : ∀ R : Place K F', 0 < R.inertiaDegAlong ψ hψ := fun R => by
      let := algebraAlong ψ
      have := isScalarTower_along ψ
      have : Module.Finite F F' := hfψ
      exact AlgebraicCurve.Place.inertiaDeg_pos_of_finiteDimensional R
    rw [Finsupp.mem_support_iff, AlgebraicCurve.Divisor.correspondence_single,
      Finsupp.coe_finsetSum, Finset.sum_apply]
    simp only [Finsupp.single_apply, one_mul]
    rw [Finset.sum_ite, Finset.sum_const_zero, add_zero]
    constructor
    · intro h
      obtain ⟨R, hR, -⟩ := Finset.exists_ne_zero_of_sum_ne_zero h
      rw [Finset.mem_filter, Place.mem_fiberAlong] at hR
      exact ⟨R, hR.1, hR.2⟩
    · rintro ⟨R, hRφ, hRψ⟩
      apply ne_of_gt
      apply Finset.sum_pos'
      · intro i _
        positivity
      · refine ⟨R, ?_, ?_⟩
        · rw [Finset.mem_filter, Place.mem_fiberAlong]; exact ⟨hRφ, hRψ⟩
        · exact mul_pos (Int.natCast_pos.mpr (he R)) (Int.natCast_pos.mpr (hf R))
  refine ⟨key φ ψ hφ hψ hfψ P Q, ?_⟩
  rw [key φ ψ hφ hψ hfψ P Q, key ψ φ hψ hφ hfφ Q P]
  exact ⟨fun ⟨R, h1, h2⟩ => ⟨R, h2, h1⟩, fun ⟨R, h1, h2⟩ => ⟨R, h2, h1⟩⟩
end AlgebraicCurve.Divisor
end ProofImplementation

end
