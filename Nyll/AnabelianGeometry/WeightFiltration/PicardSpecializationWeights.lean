/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.AnabelianGeometry.WeightFiltration.TorsionSpecializationWeights
import Nyll.JacobianVarieties.WeilPairing.TransportedDivisorialPairing
import Nyll.JacobianVarieties.Picard.Torsion.TorsionAlgebraicPoints

/-!
# Actual Picard pairing and specialization weight separation

The finite-level nondegeneracy and pairing multiplier are supplied by the
proved divisorial Weil pairing and the same semilinear coefficient action.
The caller supplies the actual Picard-to-point identification and good model,
not an abstract perfect pairing or a vanishing assertion.
-/

noncomputable section

open CategoryTheory AlgebraicGeometry AlgebraicCurve ProCGroups

namespace GoodReductionJacobian.RelativeGroupLaw

/-- A generic Picard identification compatible with the actual arithmetic
action supplies the pairings needed for scalar weight separation. -/
theorem restrictedTate_eq_zero_of_picard_specialization
    {H : Type} [CommRing H] [IsLocalRing H]
    {A : Scheme} {f : A ⟶ Spec (.of H)} [IsProper f] [Smooth f] [CompactSpace A]
    (G : RelativeGroupLaw H f) (hc : G.IsCommutative)
    (R L F : Type) [CommRing R] [HenselianLocalRing R] [IsIntegrallyClosed R]
    [Field L] [IsAlgClosed L] [CharZero L] [Algebra H R] [Algebra R L]
    [IsFractionRing R L] [Algebra H L] [IsScalarTower H R L]
    [Field F] [Algebra L F] [IsCurveOver L F]
    (hfg : ∃ z : F, Transcendental L z ∧
      FiniteDimensional (IntermediateField.adjoin L ({z} : Set F)) F)
    (I : Submonoid ℕ+) (hI : ∀ n : I, IsUnit ((n.1 : ℕ) : H))
    (τ : R ≃ₐ[H] R) (σ : L ≃ₐ[H] L)
    [Finite {z : IsLocalRing.ResidueField R // SchemeTheory.residueAlgEquiv H R τ z = z}]
    (hσ : ∀ r : R, σ (algebraMap R L r) = algebraMap R L (τ r))
    (e : Pic0 L F ≃+ G.AlgPoints hc L) (g : SemilinearAut L F)
    (hg : SemilinearAut.baseAut g = σ.toRingEquiv)
    (he : ∀ z : Pic0 L F, e (g • z) = AlgPoints.map σ.toAlgHom (e z))
    (q : ℕ) (hq : ∀ n : I, Nat.Coprime q (n.1 : ℕ))
    (hroot : ∀ n : I, ∀ z : L, z ^ (n.1 : ℕ) = 1 → σ z = z ^ q)
    (x : RestrictedTateModule (G.AlgPoints hc L) I)
    (hx : ∀ n, G.torsionCoefficientMap hc σ.toAlgHom n.1
      (RestrictedTateModule.projection (G.AlgPoints hc L) I n x) =
      q • RestrictedTateModule.projection (G.AlgPoints hc L) I n x) : x = 0 := by
  let E (n : I) := JacobianVarieties.Picard.torsionEquivOfAddEquiv e n.1
  let W (n : I) : DivisorialWeilPairingData L F (n.1 : ℕ) := by
    have : NeZero (n.1 : ℕ) := ⟨n.1.ne_zero⟩
    exact Classical.choice (Pic0.nonempty_divisorialWeilPairingData_of_isAlgClosed
      L F hfg (n.1 : ℕ))
  have hE (n : I) (z : Pic0.torsion L F (n.1 : ℕ)) :
      E n (g • z) = G.torsionCoefficientMap hc σ.toAlgHom n.1 (E n z) := by
    apply Subtype.ext
    exact he z.val
  let P (n : I) : torsionLevel (G.AlgPoints hc L) n.1 →+
      Additive (AddChar (torsionLevel (G.AlgPoints hc L) n.1) L) := by
    have : NeZero (n.1 : ℕ) := ⟨n.1.ne_zero⟩
    exact (W n).pairingOn (E n)
  apply G.restrictedTate_eq_zero_of_specialization_pairing hc R L I hI τ σ hσ
    P (fun n => ?_) q hq (fun n a b => ?_) x hx
  · have : NeZero (n.1 : ℕ) := ⟨n.1.ne_zero⟩
    exact (W n).pairingOn_injective_charZero (E n) hfg
  · have : NeZero (n.1 : ℕ) := ⟨n.1.ne_zero⟩
    exact (W n).pairingOn_multiplier (E n) g
      (G.torsionCoefficientMap hc σ.toAlgHom n.1) (hE n) q
      (fun z hz => by rw [hg]; exact hroot n z hz) a b

end GoodReductionJacobian.RelativeGroupLaw
