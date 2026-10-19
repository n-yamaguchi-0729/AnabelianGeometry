/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.JacobianVarieties.Kummer.OpenDivisorResidues

/-!
# Reduction of divisorial Kummer classes and boundary residues

When one exponent divides another, the same function defines a class for the
smaller exponent. These transition maps compose and reduce boundary orders
by the usual map between the coefficient rings.
-/

noncomputable section

open AlgebraicCurve

namespace AnabelianGeometry.WeightFiltration

variable {K F : Type*} [Field K] [Field F] [Algebra K F]
  (S : Set (Place K F)) {m n : ℕ+}

/-- Forget divisibility down to a divisor of the original exponent. -/
def openKummerUnitsReduce (h : (m : ℕ) ∣ (n : ℕ)) :
    Pic0.openKummerUnits K F S n →* Pic0.openKummerUnits K F S m where
  toFun u := ⟨u.val, fun v hv => (by exact_mod_cast h : (m : ℤ) ∣ (n : ℤ)).trans
    (u.property v hv)⟩
  map_one' := rfl
  map_mul' _ _ := rfl

/-- An actual power for the larger exponent remains a power for the smaller one. -/
theorem openKummerUnitsReduce_mem_powers (h : (m : ℕ) ∣ (n : ℕ))
    {u : Pic0.openKummerUnits K F S n} (hu : u ∈ Pic0.openKummerPowers K F S n) :
    openKummerUnitsReduce S h u ∈ Pic0.openKummerPowers K F S m := by
  change ∃ w : Fˣ, w ^ (n : ℕ) = u.val at hu
  change ∃ w : Fˣ, w ^ (m : ℕ) = u.val
  obtain ⟨w, hw⟩ := hu
  obtain ⟨k, hk⟩ := h
  refine ⟨w ^ k, ?_⟩
  rw [← pow_mul, Nat.mul_comm k (m : ℕ), ← hk]
  exact hw

/-- Reduction of actual divisorial Kummer classes to a dividing exponent. -/
def openKummerQuotientReduce (h : (m : ℕ) ∣ (n : ℕ)) :
    Pic0.openKummerUnits K F S n ⧸ Pic0.openKummerPowers K F S n →*
      Pic0.openKummerUnits K F S m ⧸ Pic0.openKummerPowers K F S m :=
  QuotientGroup.map (Pic0.openKummerPowers K F S n) (Pic0.openKummerPowers K F S m)
    (openKummerUnitsReduce S h) (fun _ hu => openKummerUnitsReduce_mem_powers S h hu)

/-- Exponent reduction preserves the representing function. -/
theorem openKummerQuotientReduce_mk (h : (m : ℕ) ∣ (n : ℕ))
    (u : Pic0.openKummerUnits K F S n) :
    openKummerQuotientReduce S h (QuotientGroup.mk u) =
      QuotientGroup.mk (openKummerUnitsReduce S h u) := rfl

/-- Reducing twice agrees with reducing directly. -/
theorem openKummerQuotientReduce_trans {k : ℕ+}
    (hkm : (k : ℕ) ∣ (m : ℕ)) (hmn : (m : ℕ) ∣ (n : ℕ))
    (q : Pic0.openKummerUnits K F S n ⧸ Pic0.openKummerPowers K F S n) :
    openKummerQuotientReduce S hkm (openKummerQuotientReduce S hmn q) =
      openKummerQuotientReduce S (hkm.trans hmn) q := by
  obtain ⟨u, rfl⟩ := QuotientGroup.mk_surjective q
  rfl

/-- Reduction to the same exponent is the identity. -/
theorem openKummerQuotientReduce_refl
    (q : Pic0.openKummerUnits K F S n ⧸ Pic0.openKummerPowers K F S n) :
    openKummerQuotientReduce S (dvd_refl (n : ℕ)) q = q := by
  obtain ⟨u, rfl⟩ := QuotientGroup.mk_surjective q
  rfl

/-- Boundary residues commute with exponent reduction. -/
theorem openKummerResidueQuotient_reduce (h : (m : ℕ) ∣ (n : ℕ))
    (q : Pic0.openKummerUnits K F S n ⧸ Pic0.openKummerPowers K F S n) (v : S) :
    (Pic0.openKummerResidueQuotient S m (openKummerQuotientReduce S h q)).toAdd v =
      ZMod.castHom h (ZMod (m : ℕ)) ((Pic0.openKummerResidueQuotient S n q).toAdd v) := by
  obtain ⟨u, rfl⟩ := QuotientGroup.mk_surjective q
  change (v.val.ord (u.val : F) : ZMod (m : ℕ)) =
    ZMod.castHom h (ZMod (m : ℕ)) (v.val.ord (u.val : F) : ZMod (n : ℕ))
  exact (map_intCast (ZMod.castHom h (ZMod (m : ℕ))) _).symm

end AnabelianGeometry.WeightFiltration
