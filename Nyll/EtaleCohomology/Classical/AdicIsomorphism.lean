/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.EtaleCohomology.Classical.Adic
public import Nyll.EtaleCohomology.Classical.AdicPullback
public import Nyll.EtaleCohomology.Classical.ExternalCupPullbackComposition
public import Nyll.EtaleCohomology.Classical.RationalAdic
public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.LinearAlgebra.TensorProduct.Basic

/-!
# Actual adic pullback equivalences for scheme isomorphisms

The original pullbacks along a scheme isomorphism and its inverse are
mutual inverses in every degree. This gives compatible linear
equivalences at the original finite levels, on the original integral
inverse limits, and on their original rational scalar extensions.
No comparison with a fundamental group or a replacement cohomology
object is needed for this transport.
-/

@[expose] public section

noncomputable section

universe u

open AlgebraicGeometry CategoryTheory
open scoped TensorProduct

namespace EtaleCohomology.Classical

variable (ℓ : ℕ) [Fact ℓ.Prime] {X Y : Scheme.{u}} (e : X ≅ Y)

/-- The original finite-level pullbacks along an actual scheme
isomorphism are inverse linear maps in every degree. -/
def finiteLevelCohomologyIso (n i : ℕ) :
    finiteLevelCohomology Y ℓ n i ≃ₗ[ℤ_[ℓ]] finiteLevelCohomology X ℓ n i where
  __ := finiteLevelCohomologyPullback ℓ e.hom n i
  invFun := finiteLevelCohomologyPullback ℓ e.inv n i
  left_inv a := by
    calc
      _ = finiteLevelCohomologyPullback ℓ (e.inv ≫ e.hom) n i a :=
        (LinearMap.congr_fun
          (finiteLevelCohomologyPullback_comp e.inv e.hom ℓ n i) a).symm
      _ = finiteLevelCohomologyPullback ℓ (𝟙 Y) n i a :=
        congrArg (fun f : Y ⟶ Y => finiteLevelCohomologyPullback ℓ f n i a) e.inv_hom_id
      _ = a := LinearMap.congr_fun (finiteLevelCohomologyPullback_id ℓ Y n i) a
  right_inv a := by
    calc
      _ = finiteLevelCohomologyPullback ℓ (e.hom ≫ e.inv) n i a :=
        (LinearMap.congr_fun
          (finiteLevelCohomologyPullback_comp e.hom e.inv ℓ n i) a).symm
      _ = finiteLevelCohomologyPullback ℓ (𝟙 X) n i a :=
        congrArg (fun f : X ⟶ X => finiteLevelCohomologyPullback ℓ f n i a) e.hom_inv_id
      _ = a := LinearMap.congr_fun (finiteLevelCohomologyPullback_id ℓ X n i) a

/-- The finite equivalence retains pullback by the original morphism. -/
theorem finiteLevelCohomologyIso_apply (n i : ℕ)
    (a : finiteLevelCohomology Y ℓ n i) :
    finiteLevelCohomologyIso ℓ e n i a =
      finiteLevelCohomologyPullback ℓ e.hom n i a := rfl

/-- Its inverse retains pullback by the original inverse morphism. -/
theorem finiteLevelCohomologyIso_symm_apply (n i : ℕ)
    (a : finiteLevelCohomology X ℓ n i) :
    (finiteLevelCohomologyIso ℓ e n i).symm a =
      finiteLevelCohomologyPullback ℓ e.inv n i a := rfl

/-- These actual isomorphism comparisons commute with the original
finite coefficient reductions. -/
theorem finiteLevelCohomologyIso_reduction (n i : ℕ)
    (a : finiteLevelCohomology Y ℓ (n + 1) i) :
    finiteLevelCohomologyIso ℓ e n i (finiteLevelReduction Y ℓ n i a) =
      finiteLevelReduction X ℓ n i (finiteLevelCohomologyIso ℓ e (n + 1) i a) :=
  finiteLevelCohomologyPullback_reduction ℓ e.hom n i a

/-- The original integral pullbacks are inverse linear maps on the
same compatible families in every degree. -/
def ellAdicCohomologyIso (i : ℕ) :
    ellAdicCohomology Y ℓ i ≃ₗ[ℤ_[ℓ]] ellAdicCohomology X ℓ i where
  __ := ellAdicCohomologyPullback ℓ e.hom i
  invFun := ellAdicCohomologyPullback ℓ e.inv i
  left_inv a := ellAdicCohomology_ext Y ℓ i (fun n =>
    (finiteLevelCohomologyIso ℓ e n i).left_inv (a.val n))
  right_inv a := ellAdicCohomology_ext X ℓ i (fun n =>
    (finiteLevelCohomologyIso ℓ e n i).right_inv (a.val n))

/-- Every projection keeps the same original finite pullback. -/
theorem ellAdicCohomologyIso_projection (i n : ℕ)
    (a : ellAdicCohomology Y ℓ i) :
    ellAdicProjection X ℓ i n (ellAdicCohomologyIso ℓ e i a) =
      finiteLevelCohomologyIso ℓ e n i (ellAdicProjection Y ℓ i n a) := rfl

/-- The original rational pullbacks are inverse linear maps on the
existing rational scalar extensions, in every degree. -/
def rationalEllAdicCohomologyIso (i : ℕ) :
    rationalEllAdicCohomology ℓ Y i ≃ₗ[ℚ_[ℓ]] rationalEllAdicCohomology ℓ X i where
  __ := rationalEllAdicCohomologyPullback ℓ e.hom i
  invFun := rationalEllAdicCohomologyPullback ℓ e.inv i
  left_inv a := by
    calc
      _ = rationalEllAdicCohomologyPullback ℓ (e.inv ≫ e.hom) i a :=
        (LinearMap.congr_fun
          (rationalEllAdicCohomologyPullback_comp e.inv e.hom ℓ i) a).symm
      _ = rationalEllAdicCohomologyPullback ℓ (𝟙 Y) i a :=
        congrArg (fun f : Y ⟶ Y => rationalEllAdicCohomologyPullback ℓ f i a) e.inv_hom_id
      _ = a := LinearMap.congr_fun (rationalEllAdicCohomologyPullback_id ℓ Y i) a
  right_inv a := by
    calc
      _ = rationalEllAdicCohomologyPullback ℓ (e.hom ≫ e.inv) i a :=
        (LinearMap.congr_fun
          (rationalEllAdicCohomologyPullback_comp e.hom e.inv ℓ i) a).symm
      _ = rationalEllAdicCohomologyPullback ℓ (𝟙 X) i a :=
        congrArg (fun f : X ⟶ X => rationalEllAdicCohomologyPullback ℓ f i a) e.hom_inv_id
      _ = a := LinearMap.congr_fun (rationalEllAdicCohomologyPullback_id ℓ X i) a

/-- Rational isomorphism pullback is the scalar extension of the same
integral isomorphism pullback on every pure tensor. -/
theorem rationalEllAdicCohomologyIso_tmul (i : ℕ) (q : ℚ_[ℓ])
    (a : ellAdicCohomology Y ℓ i) :
    rationalEllAdicCohomologyIso ℓ e i (q ⊗ₜ[ℤ_[ℓ]] a) =
      q ⊗ₜ[ℤ_[ℓ]] ellAdicCohomologyIso ℓ e i a := rfl

end EtaleCohomology.Classical
