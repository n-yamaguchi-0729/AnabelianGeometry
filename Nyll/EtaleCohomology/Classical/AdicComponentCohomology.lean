/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.EtaleCohomology.Classical.FiniteComponentCohomology
public import Mathlib.LinearAlgebra.TensorProduct.Pi
public import Mathlib.LinearAlgebra.TensorProduct.Tower

/-!
# The original adic groups on the actual finite components

The proved finite coefficient decomposition commutes with the original
reductions. Applying it to compatible families gives an equivalence of
the original integral inverse limits. Its inverse is constructed at
each finite level, so no exactness assertion about inverse limits is
needed. Scalar extension then commutes with the actual finite product.
-/

@[expose] public section

noncomputable section

universe u

open AlgebraicGeometry TopologicalSpace
open EtaleCohomology.Classical
open scoped TensorProduct

namespace EtaleCohomology

variable (X : Scheme.{u}) [IsNoetherian X]
  (hdom : ∀ x : X, IsDomain (X.presheaf.stalk x))
  (ℓ : ℕ) [Fact ℓ.Prime] (i : ℕ)

local notation "U" => reducedIrreducibleComponentEtale X hdom

/-- Apply the original finite coefficient comparison to the same
compatible family at every level and on every actual component. -/
def ellAdicComponentCohomologyMap :
    ellAdicCohomology X ℓ i →ₗ[ℤ_[ℓ]]
      ∀ Z : irreducibleComponents X, ellAdicCohomology (U Z).left ℓ i where
  toFun a Z := ⟨fun n => finiteLevelComponentCohomologyEquiv X hdom ℓ n i (a.val n) Z,
    fun n =>
      (finiteLevelComponentCohomologyEquiv_reduction X hdom ℓ n i (a.val (n + 1)) Z).symm.trans
        (congrArg (fun v => finiteLevelComponentCohomologyEquiv X hdom ℓ n i v Z)
          (a.property n))⟩
  map_add' a b := funext fun Z => Subtype.ext (funext fun n =>
    congrFun ((finiteLevelComponentCohomologyEquiv X hdom ℓ n i).map_add
      (a.val n) (b.val n)) Z)
  map_smul' r a := funext fun Z => Subtype.ext (funext fun n =>
    finiteLevelComponentCohomologyEquiv_smul X hdom ℓ n i r (a.val n) Z)

/-- The inverse is obtained from the same finite coefficient
equivalences; their original reduction compatibility proves that
these inverse images form an actual compatible family. -/
theorem ellAdicComponentCohomologyMap_bijective :
    Function.Bijective (ellAdicComponentCohomologyMap X hdom ℓ i) := by
  constructor
  · intro a b h
    apply ellAdicCohomology_ext X ℓ i
    intro n
    apply (finiteLevelComponentCohomologyEquiv X hdom ℓ n i).injective
    funext Z
    exact congrArg (fun v => (v Z).val n) h
  · intro b
    let a : ellAdicCohomology X ℓ i := ⟨fun n =>
      (finiteLevelComponentCohomologyEquiv X hdom ℓ n i).symm (fun Z => (b Z).val n), by
      intro n
      let e₀ := finiteLevelComponentCohomologyEquiv X hdom ℓ n i
      let e₁ := finiteLevelComponentCohomologyEquiv X hdom ℓ (n + 1) i
      let v₀ := fun Z : irreducibleComponents X => (b Z).val n
      let v₁ := fun Z : irreducibleComponents X => (b Z).val (n + 1)
      apply e₀.injective
      funext Z
      change e₀ (finiteLevelReduction X ℓ n i (e₁.symm v₁)) Z = e₀ (e₀.symm v₀) Z
      calc
        _ = finiteLevelReduction (U Z).left ℓ n i (e₁ (e₁.symm v₁) Z) :=
          finiteLevelComponentCohomologyEquiv_reduction X hdom ℓ n i (e₁.symm v₁) Z
        _ = finiteLevelReduction (U Z).left ℓ n i ((b Z).val (n + 1)) :=
          congrArg (finiteLevelReduction (U Z).left ℓ n i)
            (congrFun (e₁.apply_symm_apply v₁) Z)
        _ = (b Z).val n := (b Z).property n
        _ = e₀ (e₀.symm v₀) Z := (congrFun (e₀.apply_symm_apply v₀) Z).symm⟩
    refine ⟨a, ?_⟩
    funext Z
    apply Subtype.ext
    funext n
    exact congrFun ((finiteLevelComponentCohomologyEquiv X hdom ℓ n i).apply_symm_apply
      (fun W => (b W).val n)) Z

/-- The original integral adic cohomology decomposes into the same
original integral groups on the actual finite components. -/
def ellAdicComponentCohomologyEquiv :
    ellAdicCohomology X ℓ i ≃ₗ[ℤ_[ℓ]]
      ∀ Z : irreducibleComponents X, ellAdicCohomology (U Z).left ℓ i :=
  LinearEquiv.ofBijective (ellAdicComponentCohomologyMap X hdom ℓ i)
    (ellAdicComponentCohomologyMap_bijective X hdom ℓ i)

/-- Every actual finite coefficient projection is retained by the
integral component comparison. -/
theorem ellAdicComponentCohomologyEquiv_projection
    (a : ellAdicCohomology X ℓ i) (Z : irreducibleComponents X) (n : ℕ) :
    ellAdicProjection (U Z).left ℓ i n (ellAdicComponentCohomologyEquiv X hdom ℓ i a Z) =
      finiteLevelComponentCohomologyEquiv X hdom ℓ n i (ellAdicProjection X ℓ i n a) Z := rfl

/-- The inverse component comparison retains the original inverse
finite coefficient maps at every level. -/
theorem ellAdicComponentCohomologyEquiv_symm_projection
    (b : ∀ Z : irreducibleComponents X, ellAdicCohomology (U Z).left ℓ i) (n : ℕ) :
    ellAdicProjection X ℓ i n ((ellAdicComponentCohomologyEquiv X hdom ℓ i).symm b) =
      (finiteLevelComponentCohomologyEquiv X hdom ℓ n i).symm
        (fun Z => ellAdicProjection (U Z).left ℓ i n (b Z)) := by
  apply (finiteLevelComponentCohomologyEquiv X hdom ℓ n i).injective
  rw [AddEquiv.apply_symm_apply]
  funext Z
  rw [← ellAdicComponentCohomologyEquiv_projection, LinearEquiv.apply_symm_apply]

/-- Scalar extension of the original integral comparison gives the
original rational cohomology on the actual finite components. -/
def rationalEllAdicComponentCohomologyEquiv :
    rationalEllAdicCohomology ℓ X i ≃ₗ[ℚ_[ℓ]]
      ∀ Z : irreducibleComponents X, rationalEllAdicCohomology ℓ (U Z).left i := by
  let : Fintype (irreducibleComponents X) := X.irreducibleComponentsFintype
  let : DecidableEq (irreducibleComponents X) := _root_.Classical.decEq _
  exact ((ellAdicComponentCohomologyEquiv X hdom ℓ i).baseChange ℤ_[ℓ] ℚ_[ℓ]
    (ellAdicCohomology X ℓ i)
    (∀ Z : irreducibleComponents X, ellAdicCohomology (U Z).left ℓ i)).trans
      (TensorProduct.piRight ℤ_[ℓ] ℚ_[ℓ] ℚ_[ℓ]
        (fun Z : irreducibleComponents X => ellAdicCohomology (U Z).left ℓ i))

/-- Rational decomposition on a pure tensor is exactly the actual
integral decomposition on its second factor. -/
theorem rationalEllAdicComponentCohomologyEquiv_tmul
    (q : ℚ_[ℓ]) (a : ellAdicCohomology X ℓ i) (Z : irreducibleComponents X) :
    rationalEllAdicComponentCohomologyEquiv X hdom ℓ i (q ⊗ₜ[ℤ_[ℓ]] a) Z =
      q ⊗ₜ[ℤ_[ℓ]] ellAdicComponentCohomologyEquiv X hdom ℓ i a Z := rfl

end EtaleCohomology
