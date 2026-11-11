/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.EtaleCohomology.Classical.FreeModuleSheafAugmentation
public import Nyll.EtaleCohomology.Classical.FreeModuleSheafCoalgebra
public import Nyll.EtaleCohomology.Classical.FreeModuleSheafCochains
public import Nyll.EtaleCohomology.Classical.FreeModuleYoneda
public import Mathlib.Algebra.Category.ModuleCat.Adjunctions
public import Mathlib.CategoryTheory.Adjunction.Additive
public import Mathlib.CategoryTheory.Limits.Shapes.ZeroMorphisms
public import Mathlib.CategoryTheory.Monoidal.Preadditive
public import Mathlib.CategoryTheory.Preadditive.Basic
public import Mathlib.CategoryTheory.Sites.ConstantSheaf
public import Mathlib.CategoryTheory.Sites.Sheafification
public import Mathlib.CategoryTheory.Yoneda

/-!
# Actual coefficient action on individual cochain sections

The original free-sheaf action by an integer multiple of the actual
counit is that same integer multiple of the original cochain. Evaluation
on an arbitrary generator is reduced to its actual Yoneda map. Thus an
edge coefficient whose value is a specified integer multiple of the
constant section one acts by that integer on the other actual section.

The section criterion is local to the specified generator. In particular
no connectedness or global constancy of an overlap is required.
-/

@[expose] public section

noncomputable section

universe u

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory Opposite
open scoped EtaleCohomology.ModuleTensor

namespace EtaleCohomology

variable (X : Scheme.{u}) (R : Type u) [CommRing R]

variable {P : X.Etaleᵒᵖ ⥤ Type u}
  {F : Sheaf X.smallEtaleTopology (ModuleCat.{u} R)}

/-- The actual left coefficient action preserves zero. -/
theorem freeModuleSheafAction_zero_left
    (b : (freeModuleSheafFunctor X R).obj P ⟶ F) :
    freeModuleSheafAction X R 0 b = 0 := by
  unfold freeModuleSheafAction freeModuleSheafPairing
  rw [MonoidalPreadditive.zero_tensor, comp_zero, zero_comp]

/-- Additivity in the actual coefficient, with the original free source. -/
def freeModuleSheafActionAddHomLeft
    (b : (freeModuleSheafFunctor X R).obj P ⟶ F) :
    ((freeModuleSheafFunctor X R).obj P ⟶ (constantSheaf X.smallEtaleTopology (ModuleCat.{u} R)).obj
      (ModuleCat.of R R)) →+
      ((freeModuleSheafFunctor X R).obj P ⟶ F) where
  toFun a := freeModuleSheafAction X R a b
  map_zero' := freeModuleSheafAction_zero_left X R b
  map_add' a a' := freeModuleSheafAction_add_left X R a a' b

/-- A literal natural multiple of the actual counit acts by the
same natural multiple on the original cochain. -/
theorem freeModuleSheafAction_nsmul_counit
    (m : ℕ) (b : (freeModuleSheafFunctor X R).obj P ⟶ F) :
    freeModuleSheafAction X R (m • freeModuleSheafCounit X R P) b = m • b := by
  let ε : (freeModuleSheafFunctor X R).obj P ⟶
      (constantSheaf X.smallEtaleTopology (ModuleCat.{u} R)).obj (ModuleCat.of R R) :=
    freeModuleSheafCounit X R P
  exact (map_nsmul (freeModuleSheafActionAddHomLeft X R b) m ε).trans
    (congrArg (fun a => m • a) (freeModuleSheafAction_counit_left X R b))

/-- The same calculation retains signed integer coefficients. -/
theorem freeModuleSheafAction_zsmul_counit
    (m : ℤ) (b : (freeModuleSheafFunctor X R).obj P ⟶ F) :
    freeModuleSheafAction X R (m • freeModuleSheafCounit X R P) b = m • b := by
  let ε : (freeModuleSheafFunctor X R).obj P ⟶
      (constantSheaf X.smallEtaleTopology (ModuleCat.{u} R)).obj (ModuleCat.of R R) :=
    freeModuleSheafCounit X R P
  exact (map_zsmul (freeModuleSheafActionAddHomLeft X R b) m ε).trans
    (congrArg (fun a => m • a) (freeModuleSheafAction_counit_left X R b))

/-- The existing actual Yoneda section equivalence preserves addition. -/
def freeModuleSheafYonedaHomAddEquiv (V : X.Etale)
    (F : Sheaf X.smallEtaleTopology (ModuleCat.{u} R)) :
    ((freeModuleSheafYoneda X.smallEtaleTopology R).obj V ⟶ F) ≃+
      F.obj.obj (op V) where
  toEquiv := freeModuleSheafYonedaHomEquiv X.smallEtaleTopology R V F
  map_add' a b := by
    change (((sheafificationAdjunction X.smallEtaleTopology (ModuleCat.{u} R)).homEquiv
      (yoneda.obj V ⋙ ModuleCat.free R) F (a + b)).app (op V))
        (ModuleCat.freeMk (𝟙 V)) =
      (((sheafificationAdjunction X.smallEtaleTopology (ModuleCat.{u} R)).homEquiv
        (yoneda.obj V ⋙ ModuleCat.free R) F a).app (op V))
          (ModuleCat.freeMk (𝟙 V)) +
      (((sheafificationAdjunction X.smallEtaleTopology (ModuleCat.{u} R)).homEquiv
        (yoneda.obj V ⋙ ModuleCat.free R) F b).app (op V))
          (ModuleCat.freeMk (𝟙 V))
    rw [Adjunction.homAddEquiv_add]
    rfl

/-- A specified original presheaf generator is evaluated by its
actual Yoneda map, before any coefficient is identified with a scalar. -/
theorem freeModuleSheafYonedaHomEquiv_generator (V : X.Etale) (x : P.obj (op V))
    (a : (freeModuleSheafFunctor X R).obj P ⟶ F) :
    freeModuleSheafYonedaHomEquiv X.smallEtaleTopology R V F
        ((freeModuleSheafFunctor X R).map (yonedaEquiv.symm x) ≫ a) =
      (freeModuleSheafHomEquiv X R P F a).app (op V) x := by
  change (freeModuleSheafHomEquiv X R (yoneda.obj V) F
    ((freeModuleSheafFunctor X R).map (yonedaEquiv.symm x) ≫ a)).app (op V) (𝟙 V) = _
  rw [freeModuleSheafHomEquiv_precomp]
  exact congrArg ((freeModuleSheafHomEquiv X R P F a).app (op V))
    (yonedaEquiv.apply_symm_apply x)

/-- At any specified generator, a coefficient with the given actual
constant value acts by its integer exponent on the original section. -/
theorem freeModuleSheafAction_generator_of_zsmul
    (a : (freeModuleSheafFunctor X R).obj P ⟶
      (constantSheaf X.smallEtaleTopology (ModuleCat.{u} R)).obj (ModuleCat.of R R))
    (b : (freeModuleSheafFunctor X R).obj P ⟶ F)
    (V : X.Etale) (x : P.obj (op V)) (m : ℤ)
    (ha : (freeModuleSheafHomEquiv X R P
      ((constantSheaf X.smallEtaleTopology (ModuleCat.{u} R)).obj (ModuleCat.of R R)) a).app (op V)
      x =
      m • (toSheafify X.smallEtaleTopology
        ((Functor.const X.Etaleᵒᵖ).obj (ModuleCat.of R R))).app (op V) (1 : R)) :
    (freeModuleSheafHomEquiv X R P F (freeModuleSheafAction X R a b)).app (op V) x =
      m • (freeModuleSheafHomEquiv X R P F b).app (op V) x := by
  let η : yoneda.obj V ⟶ P := yonedaEquiv.symm x
  let C : Sheaf X.smallEtaleTopology (ModuleCat.{u} R) :=
    (constantSheaf X.smallEtaleTopology (ModuleCat.{u} R)).obj (ModuleCat.of R R)
  let a' : (freeModuleSheafYoneda X.smallEtaleTopology R).obj V ⟶ C :=
    (freeModuleSheafFunctor X R).map η ≫ a
  let b' := (freeModuleSheafFunctor X R).map η ≫ b
  let ε : (freeModuleSheafYoneda X.smallEtaleTopology R).obj V ⟶ C :=
    freeModuleSheafCounit X R (yoneda.obj V)
  let e := freeModuleSheafYonedaHomAddEquiv X R V C
  have ha' : a' = m • ε := by
    apply e.injective
    exact (freeModuleSheafYonedaHomEquiv_generator X R V x a).trans
      (ha.trans
        ((congrArg (fun s => m • s)
          (freeModuleSheafCounit_yoneda_sections X R V).symm).trans
            (map_zsmul e m ε).symm))
  calc
    _ = freeModuleSheafYonedaHomEquiv X.smallEtaleTopology R V F
        ((freeModuleSheafFunctor X R).map η ≫ freeModuleSheafAction X R a b) :=
      (freeModuleSheafYonedaHomEquiv_generator X R V x _).symm
    _ = freeModuleSheafYonedaHomEquiv X.smallEtaleTopology R V F
        (freeModuleSheafAction X R (m • ε) b') :=
      congrArg (freeModuleSheafYonedaHomEquiv X.smallEtaleTopology R V F)
        ((freeModuleSheafAction_precomp X R η a b).trans
          (congrArg
            (fun z : (freeModuleSheafYoneda X.smallEtaleTopology R).obj V ⟶ C =>
              freeModuleSheafAction X R z b') ha'))
    _ = freeModuleSheafYonedaHomEquiv X.smallEtaleTopology R V F (m • b') :=
      congrArg (freeModuleSheafYonedaHomEquiv X.smallEtaleTopology R V F)
        (freeModuleSheafAction_zsmul_counit X R m b')
    _ = m • freeModuleSheafYonedaHomEquiv X.smallEtaleTopology R V F b' :=
      map_zsmul (freeModuleSheafYonedaHomAddEquiv X R V F) m b'
    _ = _ := congrArg (fun s => m • s)
      (freeModuleSheafYonedaHomEquiv_generator X R V x b)

end EtaleCohomology
