/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/
import Nyll.JacobianVarieties.Kummer.PlaceOrdZeroKummerCover

/-! # The actual value of the same powered arithmetic unit -/

noncomputable section
namespace AlgebraicCurve.Place

/-- The literal local coefficient of the named power cover reduces to the
same power of the original value. Both order-zero proofs may be the ones
already supplied by the chosen-cusp specialization. -/
theorem ordZeroValue_pow
    {k F : Type} [Field k] [Field F] [Algebra k F]
    (v : Place k F) (hv : v.IsRational) (u : Fˣ) (r : ℕ)
    (hu : v.ord (u : F) = 0) (hr : v.ord ((u ^ r : Fˣ) : F) = 0) :
    ordZeroValue v hv (u ^ r) hr = ordZeroValue v hv u hu ^ r := by
  apply Units.ext
  apply (algebraMap k v.ResidueField).injective
  change algebraMap k v.ResidueField (ordZeroValue v hv (u ^ r) hr : k) =
    algebraMap k v.ResidueField ((ordZeroValue v hv u hu : k) ^ r)
  rw [map_pow, ← ordZeroUnit_residue v hv (u ^ r) hr,
    ← ordZeroUnit_residue v hv u hu, ← map_pow]
  rfl

end AlgebraicCurve.Place
