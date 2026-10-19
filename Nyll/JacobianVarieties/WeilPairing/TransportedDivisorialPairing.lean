/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.JacobianVarieties.WeilPairing.CharZeroNondegeneracy
import Nyll.JacobianVarieties.WeilPairing.DivisorialPairingPairSemilinearSmul

/-!
# The divisorial pairing on an identified finite torsion group

Transport the proved characteristic-zero Weil pairing along the actual
Picard-to-point comparison. Nondegeneracy is derived from the divisorial
theorem, and the scalar multiplier follows from the same semilinear action
and its action on roots of unity.
-/

noncomputable section

namespace AlgebraicCurve.DivisorialWeilPairingData

variable {K F B : Type*} [Field K] [Field F] [Algebra K F]
  [HasPrincipalDivisors K F] {n : ℕ} [NeZero n] [AddCommGroup B]
  (w : DivisorialWeilPairingData K F n) (e : Pic0.torsion K F n ≃+ B)

/-- The same divisorial pairing expressed on the identified torsion group. -/
def pairingOn : B →+ Additive (AddChar B K) :=
  AddMonoidHom.mk'
    (fun a => Additive.ofMul ((w.toChar (e.symm a)).compAddMonoidHom e.symm.toAddMonoidHom))
    (by
      intro a b
      apply Additive.toMul.injective
      ext c
      change w.pair (e.symm (a + b)) (e.symm c) =
        w.pair (e.symm a) (e.symm c) * w.pair (e.symm b) (e.symm c)
      rw [map_add, w.pair_add_left])

@[simp] theorem pairingOn_apply (a b : B) :
    Additive.toMul (w.pairingOn e a) b = w.pair (e.symm a) (e.symm b) := rfl

/-- The transported actual pairing is nondegenerate in characteristic zero. -/
theorem pairingOn_injective_charZero [IsAlgClosed K] [CharZero K]
    (hfg : ∃ x : F, Transcendental K x ∧
      FiniteDimensional (IntermediateField.adjoin K ({x} : Set F)) F) :
    Function.Injective (w.pairingOn e) := by
  intro a b hab
  apply e.symm.injective
  apply w.toHom_injective_charZero hfg
  apply Additive.toMul.injective
  ext z
  have h := congrArg (fun χ : Additive (AddChar B K) => Additive.toMul χ (e z)) hab
  simpa only [pairingOn_apply, e.symm_apply_apply, toHom_apply_apply] using h

/-- Actual equivariance transports without replacing the given action. -/
theorem pairingOn_semilinear (g : SemilinearAut K F) (T : B →+ B)
    (he : ∀ z, e (g • z) = T (e z)) (a b : B) :
    Additive.toMul (w.pairingOn e (T a)) (T b) =
      SemilinearAut.baseAut g (Additive.toMul (w.pairingOn e a) b) := by
  have hi (z : B) : e.symm (T z) = g • e.symm z := by
    apply e.injective
    rw [e.apply_symm_apply, he, e.apply_symm_apply]
  simp only [pairingOn_apply, hi]
  exact w.pair_semilinearSmul g (e.symm a) (e.symm b)

/-- Root-of-unity arithmetic of the same semilinear action supplies the
pairing multiplier; no weight assertion is assumed. -/
theorem pairingOn_multiplier (g : SemilinearAut K F) (T : B →+ B)
    (he : ∀ z, e (g • z) = T (e z))
    (q : ℕ) (hroot : ∀ z : K, z ^ n = 1 → SemilinearAut.baseAut g z = z ^ q)
    (a b : B) :
    Additive.toMul (w.pairingOn e (T a)) (T b) =
      (Additive.toMul (w.pairingOn e a) b) ^ q := by
  rw [w.pairingOn_semilinear e g T he]
  apply hroot
  have hb : n • e.symm b = 0 := by
    apply Subtype.ext
    change n • (e.symm b).val = 0
    simpa only [natCast_zsmul] using (Pic0.mem_torsion.mp (e.symm b).property)
  change w.toChar (e.symm a) (e.symm b) ^ n = 1
  rw [← AddChar.map_nsmul_eq_pow, hb, AddChar.map_zero_eq_one]

end AlgebraicCurve.DivisorialWeilPairingData
