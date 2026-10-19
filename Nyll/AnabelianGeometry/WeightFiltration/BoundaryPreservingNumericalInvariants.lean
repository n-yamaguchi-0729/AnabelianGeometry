/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.AnabelianGeometry.WeightFiltration.ResidueAbelianCharacters
import Nyll.AnabelianGeometry.WeightFiltration.CharacterAnnihilatorTransport
import Nyll.AnabelianGeometry.WeightFiltration.ResidueNumericalInvariants
import Nyll.AlgebraicCurves.Models.Points.RationalPointExistence

/-!
# Numerical invariants under boundary-preserving abelian equivalences

The actual compactification kernel determines the genus, and, when the
boundary is nonempty on both sides, its cardinality. Individual inertia
subgroups need not be matched for this argument.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory AlgebraicCurve NeronModelInfra
open EtaleFundamentalGroups.Cohomology ProCGroups.Abelian

namespace AnabelianGeometry.WeightFiltration

variable {K F₁ F₂ : Type}
  [Field K] [IsAlgClosed K] [CharZero K]
  [Field F₁] [Field F₂] [Algebra K F₁] [Algebra K F₂]
  [Algebra.EssFiniteType K F₁] [Algebra.EssFiniteType K F₂]
  [IsCurveOver K F₁] [IsCurveOver K F₂]
  (M₁ : CurveModel K F₁) (M₂ : CurveModel K F₂)
  {X₁ X₂ : Scheme}
  [IsIntegral X₁] [CompactSpace X₁]
  [IsIntegral X₂] [CompactSpace X₂]
  (j₁ : X₁ ⟶ M₁.C) [IsOpenImmersion j₁] (hj₁ : DenseRange j₁)
  (j₂ : X₂ ⟶ M₂.C) [IsOpenImmersion j₂] (hj₂ : DenseRange j₂)
  {Ω₁ Ω₂ : Type} [Field Ω₁] [Field Ω₂]
  [IsSepClosed Ω₁] [IsSepClosed Ω₂]
  (xi₁ : Spec (.of Ω₁) ⟶ X₁)
  (xi₂ : Spec (.of Ω₂) ⟶ X₂)
  (e :
    TopologicalAbelianization (Aut (FiniteEtale.fiber xi₁)) ≃ₜ*
    TopologicalAbelianization (Aut (FiniteEtale.fiber xi₂)))
  (hW :
    ((compactificationAbelianizationMap j₁ xi₁).toMonoidHom.ker).map
        e.toMulEquiv.toMonoidHom =
      (compactificationAbelianizationMap j₂ xi₂).toMonoidHom.ker)

include hW in
theorem finiteResidue_card_eq_of_abelianization_equiv
    (n : ℕ+) (hn : IsUnit ((n : ℕ) : K)) :
    Nat.card (finiteResidue M₁ n j₁ hj₁ hn xi₁).ker =
        Nat.card (finiteResidue M₂ n j₂ hj₂ hn xi₂).ker ∧
      Nat.card (finiteResidue M₁ n j₁ hj₁ hn xi₁).range =
        Nat.card (finiteResidue M₂ n j₂ hj₂ hn xi₂).range := by
  let : NeZero (n : ℕ) := ⟨n.ne_zero⟩
  let C := AddCommGrpCat.of (Additive (rootsOfUnity (n : ℕ) K))
  let : TopologicalSpace (Multiplicative C) := ⊥
  let : DiscreteTopology (Multiplicative C) := ⟨rfl⟩
  let r₁ := finiteResidue M₁ n j₁ hj₁ hn xi₁
  let r₂ := finiteResidue M₂ n j₂ hj₂ hn xi₂
  let E₁ := finiteH1AbelianCharacterEquiv C xi₁
  let E₂ := finiteH1AbelianCharacterEquiv C xi₂
  let P := characterPullback (T := Multiplicative C) e
  let EH : FiniteKummerH1 K X₂ n ≃+ FiniteKummerH1 K X₁ n :=
    (E₂.trans P).trans E₁.symm
  have hχ (x : FiniteKummerH1 K X₂ n) :
      h1AbelianCharacter C xi₁ (EH x) =
        (h1AbelianCharacter C xi₂ x).comp
          (ContinuousMonoidHom.toContinuousMonoidHom e) := by
    change (E₁ (E₁.symm (P (E₂ x)))).toMul = _
    rw [E₁.apply_symm_apply]
    rfl
  have hzero (x : FiniteKummerH1 K X₂ n) :
      r₁ (EH x) = 0 ↔ r₂ x = 0 := by
    have hz₁ :
        r₁ (EH x) = 0 ↔
          (compactificationAbelianizationMap j₁ xi₁).toMonoidHom.ker ≤
            (h1AbelianCharacter C xi₁ (EH x)).toMonoidHom.ker :=
      finiteResidue_eq_zero_iff_abelianCharacter_ker_le
        M₁ n j₁ hj₁ hn xi₁ (EH x)
    have hz₂ :
        r₂ x = 0 ↔
          (compactificationAbelianizationMap j₂ xi₂).toMonoidHom.ker ≤
            (h1AbelianCharacter C xi₂ x).toMonoidHom.ker :=
      finiteResidue_eq_zero_iff_abelianCharacter_ker_le
        M₂ n j₂ hj₂ hn xi₂ x
    rw [hz₁, hz₂, hχ, ← hW]
    constructor
    · intro h b hb
      obtain ⟨a, ha, rfl⟩ := hb
      exact h ha
    · intro h a ha
      exact h ⟨a, ha, rfl⟩
  have hker : r₂.ker.map EH.toAddMonoidHom = r₁.ker := by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact (hzero y).mpr hy
    · intro hx
      refine ⟨EH.symm x, ?_, EH.apply_symm_apply x⟩
      apply (hzero (EH.symm x)).mp
      change r₁ x = 0 at hx
      simpa only [EH.apply_symm_apply] using hx
  let EK : r₂.ker ≃+ r₁.ker :=
    (EH.addSubgroupMap r₂.ker).trans (AddEquiv.addSubgroupCongr hker)
  let ER : r₂.range ≃+ r₁.range :=
    (QuotientAddGroup.quotientKerEquivRange r₂).symm.trans
      ((QuotientAddGroup.congr r₂.ker r₁.ker EH hker).trans
        (QuotientAddGroup.quotientKerEquivRange r₁))
  exact ⟨(Nat.card_congr EK.toEquiv).symm, (Nat.card_congr ER.toEquiv).symm⟩

include hW hj₁ hj₂ in
theorem genus_eq_of_boundary_preserving_abelianization_equiv :
    genusFF K F₁ = genusFF K F₂ := by
  obtain ⟨ε₁⟩ := M₁.nonempty_rationalPoint
  obtain ⟨ε₂⟩ := M₂.nonempty_rationalPoint
  let n : ℕ+ := ⟨2, by decide⟩
  have hn₁ : 1 < (n : ℕ) := by decide
  have hn : IsUnit ((n : ℕ) : K) :=
    isUnit_iff_ne_zero.mpr (Nat.cast_ne_zero.mpr n.ne_zero)
  have hcard := (finiteResidue_card_eq_of_abelianization_equiv
    M₁ M₂ j₁ hj₁ j₂ hj₂ xi₁ xi₂ e hW n hn).1
  rw [genus_eq_log_card_finiteResidue_ker M₁ ε₁ n j₁ hj₁ hn xi₁ hn₁,
    genus_eq_log_card_finiteResidue_ker M₂ ε₂ n j₂ hj₂ hn xi₂ hn₁]
  exact congrArg (fun c : ℕ => Nat.log (n : ℕ) c / 2) hcard

include hW hj₁ hj₂ in
theorem boundaryCard_eq_of_boundary_preserving_abelianization_equiv
    [Fintype (M₁.openBoundaryPlaces j₁)]
    [Fintype (M₂.openBoundaryPlaces j₂)]
    (v₁ : M₁.openBoundaryPlaces j₁) (v₂ : M₂.openBoundaryPlaces j₂) :
    Fintype.card (M₁.openBoundaryPlaces j₁) =
      Fintype.card (M₂.openBoundaryPlaces j₂) := by
  obtain ⟨ε₁⟩ := M₁.nonempty_rationalPoint
  obtain ⟨ε₂⟩ := M₂.nonempty_rationalPoint
  let n : ℕ+ := ⟨2, by decide⟩
  have hn₁ : 1 < (n : ℕ) := by decide
  have hn : IsUnit ((n : ℕ) : K) :=
    isUnit_iff_ne_zero.mpr (Nat.cast_ne_zero.mpr n.ne_zero)
  have hcard := (finiteResidue_card_eq_of_abelianization_equiv
    M₁ M₂ j₁ hj₁ j₂ hj₂ xi₁ xi₂ e hW n hn).2
  rw [boundaryCard_eq_log_card_finiteResidue_range M₁ ε₁ n j₁ hj₁ hn xi₁ v₁ hn₁,
    boundaryCard_eq_log_card_finiteResidue_range M₂ ε₂ n j₂ hj₂ hn xi₂ v₂ hn₁]
  exact congrArg (fun c : ℕ => Nat.log (n : ℕ) c + 1) hcard

end AnabelianGeometry.WeightFiltration
