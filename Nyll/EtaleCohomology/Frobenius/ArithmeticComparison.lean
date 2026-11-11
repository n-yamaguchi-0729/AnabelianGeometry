/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.EtaleCohomology.Classical.PullbackSiteComparison
public import Nyll.SchemeTheory.Etale.Frobenius
public import Nyll.SchemeTheory.Morphisms.FiniteFieldConstantAction
public import Nyll.SchemeTheory.Morphisms.FrobeniusBaseChange
public import Mathlib.CategoryTheory.MorphismProperty.OverAdjunction

/-!
# Geometric and arithmetic Frobenius on constant étale cohomology

After extending the constants of a scheme over a finite field, its original
q-power Frobenius acts on the small étale site like the inverse arithmetic
q-power automorphism of the constants. The comparison is constructed from
relative Frobenius and the actual factorization of scheme morphisms.

The resulting equality concerns the canonical pullback maps on abelian
constant-coefficient cohomology in every degree. No composition law for
cohomology or comparison with a separately supplied Galois action is assumed.
-/

@[expose] public section

noncomputable section

universe u

open AlgebraicGeometry CategoryTheory Limits

namespace EtaleCohomology

variable (k Ω : Type u) [Field k] [Fintype k] [Field Ω] [Algebra k Ω]
  [Algebra.IsAlgebraic k Ω] (X : Scheme.{u}) [X.Over (Spec (.of k))]

local notation "b" => Spec.map (CommRingCat.ofHom (algebraMap k Ω))
local notation "f" => (X ↘ Spec (CommRingCat.of k))
local notation "Y" => pullback f b

attribute [local instance] Scheme.constantPullbackOver

/-- The actual étale base-change functors for geometric Frobenius and
inverse arithmetic Frobenius on the constants are naturally isomorphic. -/
def finiteFieldGeometricArithmeticSiteIso :
    etaleBaseChange (Scheme.constantBaseChangeFrobenius k Ω X) ≅
      etaleBaseChange (Scheme.constantFieldTwist k Ω X
        (FiniteField.frobeniusAlgEquivOfAlgebraic k Ω).symm) := by
  let a : Y ⟶ Y := (Y).finiteFieldFrobenius k
  let c : Y ⟶ Y := Scheme.constantFieldTwist k Ω X
    (FiniteField.frobeniusAlgEquivOfAlgebraic k Ω).symm
  let r : Y ⟶ Y := Scheme.constantBaseChangeFrobenius k Ω X
  have h : r = a ≫ c :=
    Scheme.baseChangeFrobenius_eq_absolute_comp_inverseConstantTwist k Ω X
  let e : etaleBaseChange r ≅ etaleBaseChange c ⋙ etaleBaseChange a :=
    MorphismProperty.Over.pullbackComp
      (P := show MorphismProperty Scheme.{u} from @AlgebraicGeometry.Etale)
      (Q := ⊤) a c r h
  let t : etaleBaseChange a ≅ 𝟭 (Y).Etale :=
    (Scheme.Etale.finiteFieldFrobeniusPullbackIso k Y).symm
  exact e ≪≫ Functor.isoWhiskerLeft (etaleBaseChange c) t ≪≫
    Functor.rightUnitor (etaleBaseChange c)

/-- On actual constant abelian étale cohomology, the base change of the
original q-power Frobenius has the action of inverse arithmetic Frobenius. -/
theorem geometricFrobenius_eq_inverseArithmetic_on_constantCohomology
    (A : AddCommGrpCat.{u}) (n : ℕ)
    (x : Sheaf.H.{u} ((constantSheaf (Y).smallEtaleTopology AddCommGrpCat.{u}).obj A) n) :
    Sheaf.H.map
        ((etaleAbelianPullbackConstantIso
          (Scheme.constantBaseChangeFrobenius k Ω X)).hom.app A) n
        (etaleAbelianCohomologyPullbackMap (Scheme.constantBaseChangeFrobenius k Ω X)
          ((constantSheaf (Y).smallEtaleTopology AddCommGrpCat.{u}).obj A) n x) =
      Sheaf.H.map
        ((etaleAbelianPullbackConstantIso (Scheme.constantFieldTwist k Ω X
          (FiniteField.frobeniusAlgEquivOfAlgebraic k Ω).symm)).hom.app A) n
        (etaleAbelianCohomologyPullbackMap (Scheme.constantFieldTwist k Ω X
          (FiniteField.frobeniusAlgEquivOfAlgebraic k Ω).symm)
          ((constantSheaf (Y).smallEtaleTopology AddCommGrpCat.{u}).obj A) n x) :=
  etaleAbelianConstantCohomologyPullbackMap_siteIso
    (finiteFieldGeometricArithmeticSiteIso k Ω X) A n x

end EtaleCohomology
