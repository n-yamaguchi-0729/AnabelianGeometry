/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.EtaleCohomology.Classical.Adic
public import Nyll.EtaleCohomology.Classical.AdditiveCoefficientAction
public import Mathlib.FieldTheory.Finite.Basic
public import Mathlib.RingTheory.RootsOfUnity.Basic

/-!
# Frobenius on the original roots coefficients

Every arithmetic Frobenius power acts on roots-of-unity coefficients by the
corresponding cardinality multiple. These coefficients are finite when `n > 0`;
for `n = 0` they are all of `Kˣ` and can be infinite. Additivity of the actual derived functor
retains that scalar on cohomology in every degree. This is coefficient action;
it is kept distinct from pullback by the geometric scheme Frobenius.
-/

@[expose] public section

noncomputable section

open AlgebraicGeometry CategoryTheory

namespace EtaleCohomology.Classical

universe u

variable (k K : Type u) [Field k] [Fintype k] [Field K]
  [Algebra k K] [Algebra.IsAlgebraic k K]

/-- The actual arithmetic Frobenius action on roots of unity is the
cardinality scalar, for every power and every `n`, without an invertibility assumption. -/
theorem finiteRoots_frobeniusPower_coefficient (n r : ℕ) :
    AddCommGrpCat.ofHom
        (restrictRootsOfUnity (FiniteField.frobeniusAlgEquivOfAlgebraic k K ^ r).toRingHom
          n).toAdditive =
      Fintype.card k ^ r • 𝟙 (AddCommGrpCat.of (Additive (rootsOfUnity n K))) := by
  apply AddCommGrpCat.hom_ext
  apply AddMonoidHom.ext
  intro z
  apply Subtype.ext
  apply Units.ext
  change (FiniteField.frobeniusAlgEquivOfAlgebraic k K ^ r) (z.toMul.val : K) =
    (z.toMul.val : K) ^ (Fintype.card k ^ r)
  rw [AlgEquiv.coe_pow, FiniteField.coe_frobeniusAlgEquivOfAlgebraic_iterate]

/-- Applying the original coefficient Frobenius to actual derived
cohomology is the same cardinality multiple, in every degree. -/
theorem rootsCohomology_frobeniusPower_coefficient
    (X : Scheme.{u}) (n r i : ℕ)
    (x : Sheaf.H.{u} ((constantSheaf X.smallEtaleTopology AddCommGrpCat.{u}).obj
      (AddCommGrpCat.of (Additive (rootsOfUnity n K)))) i) :
    Sheaf.H.map ((constantSheaf X.smallEtaleTopology AddCommGrpCat.{u}).map
      (AddCommGrpCat.ofHom
        (restrictRootsOfUnity (FiniteField.frobeniusAlgEquivOfAlgebraic k K ^ r).toRingHom
          n).toAdditive)) i x = Fintype.card k ^ r • x := by
  let A := AddCommGrpCat.of (Additive (rootsOfUnity n K))
  let F := constantSheaf X.smallEtaleTopology AddCommGrpCat.{u} ⋙
    Sheaf.functorH X.smallEtaleTopology i
  change F.map (AddCommGrpCat.ofHom
    (restrictRootsOfUnity (FiniteField.frobeniusAlgEquivOfAlgebraic k K ^ r).toRingHom
      n).toAdditive) x = Fintype.card k ^ r • x
  rw [finiteRoots_frobeniusPower_coefficient, F.map_nsmul, F.map_id]
  rfl

end EtaleCohomology.Classical
