/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.AnabelianGeometry.WeightFiltration.TorsionTateSpecialization
import Nyll.ProCGroups.Abelian.RestrictedTatePairingWeights
import Nyll.AnabelianGeometry.WeightFiltration.FiniteTorsionCoefficients

/-!
# Pairing weights from actual equivariant specialization

The common finite target for all fixed torsion subgroups is constructed from
the actual residue coefficient action. The remaining pairing inputs are on
the generic fibre; no residue-field perfect pairing is postulated.
-/

noncomputable section

open CategoryTheory AlgebraicGeometry ProCGroups

namespace GoodReductionJacobian.RelativeGroupLaw

variable {H : Type} [CommRing H] {A : Scheme} {f : A ⟶ Spec (.of H)}
  (G : RelativeGroupLaw H f) (hc : G.IsCommutative)
  [IsLocalRing H] [IsProper f] [Smooth f]
  (R L : Type) [CommRing R] [HenselianLocalRing R] [IsIntegrallyClosed R]
  [Field L] [Algebra H R] [Algebra R L] [IsFractionRing R L]
  [Algebra H L] [IsScalarTower H R L]

/-- An actual good model with compatible coefficient actions and generic-fibre
pairings has no nonzero multiplier eigenvector in its restricted Tate module. -/
theorem restrictedTate_eq_zero_of_specialization_pairing
    [CompactSpace A] {C : Type*} [CommMonoid C] (I : Submonoid ℕ+)
    (hI : ∀ n : I, IsUnit ((n.1 : ℕ) : H))
    (τ : R ≃ₐ[H] R) (σ : L ≃ₐ[H] L)
    [Finite {z : IsLocalRing.ResidueField R // SchemeTheory.residueAlgEquiv H R τ z = z}]
    (hσ : ∀ r : R, σ (algebraMap R L r) = algebraMap R L (τ r))
    (P : ∀ n : I, torsionLevel (G.AlgPoints hc L) n.1 →+
      Additive (AddChar (torsionLevel (G.AlgPoints hc L) n.1) C))
    (hP : ∀ n, Function.Injective (P n))
    (q : ℕ) (hq : ∀ n : I, Nat.Coprime q (n.1 : ℕ))
    (hpair : ∀ n a b,
      Additive.toMul (P n (G.torsionCoefficientMap hc σ.toAlgHom n.1 a))
        (G.torsionCoefficientMap hc σ.toAlgHom n.1 b) =
      (Additive.toMul (P n a) b) ^ q)
    (x : RestrictedTateModule (G.AlgPoints hc L) I)
    (hx : ∀ n, G.torsionCoefficientMap hc σ.toAlgHom n.1
      (RestrictedTateModule.projection (G.AlgPoints hc L) I n x) =
      q • RestrictedTateModule.projection (G.AlgPoints hc L) I n x) : x = 0 := by
  have : ∀ n : I, Finite (torsionLevel (G.AlgPoints hc L) n.1) :=
    fun n => G.finite_torsionLevel_of_isUnit hc L n.1 (hI n)
  let ρ := SchemeTheory.residueAlgEquiv H R τ
  let F := AlgPoints.map (L := G) (hc := hc) ρ.toAlgHom
  let S := F.eqLocus (AddMonoidHom.id (G.AlgPoints hc (IsLocalRing.ResidueField R)))
  have : Finite S := AnabelianGeometry.WeightFiltration.finite_fixed_algebraicPoints
    H (IsLocalRing.ResidueField R) A f G hc ρ
  let e (n : I) := G.torsionSpecializationAddEquiv hc R L n.1 (hI n)
  let Fn (n : I) := G.torsionCoefficientMap hc σ.toAlgHom n.1
  have he (n : I) (a : torsionLevel (G.AlgPoints hc L) n.1) :
      F (e n a).val = (e n (Fn n a)).val := by
    exact (congrArg Subtype.val
      (G.torsionSpecializationAddEquiv_equivariant hc R L τ σ hσ n.1 (hI n) a)).symm
  let j (n : I) : (Fn n - AddMonoidHom.id (torsionLevel (G.AlgPoints hc L) n.1)).ker →+ S :=
    { toFun := fun a => ⟨(e n a.val).val, by
        change F (e n a.val).val = (e n a.val).val
        rw [he]
        have ha : Fn n a.val = a.val := sub_eq_zero.mp a.property
        rw [ha]⟩
      map_zero' := by
        apply Subtype.ext
        exact congrArg (fun z : torsionLevel
          (G.AlgPoints hc (IsLocalRing.ResidueField R)) n.1 => z.val)
          (map_zero (e n))
      map_add' := by
        intro a b
        apply Subtype.ext
        exact congrArg (fun z : torsionLevel
          (G.AlgPoints hc (IsLocalRing.ResidueField R)) n.1 => z.val)
          (map_add (e n) a.val b.val) }
  have hj (n : I) : Function.Injective (j n) := by
    intro a b hab
    apply Subtype.ext
    apply (e n).injective
    apply Subtype.ext
    exact congrArg (fun z : S => z.val) hab
  exact RestrictedTateModule.eq_zero_of_scalar_pairing Fn j hj P hP q hq hpair x hx

end GoodReductionJacobian.RelativeGroupLaw
