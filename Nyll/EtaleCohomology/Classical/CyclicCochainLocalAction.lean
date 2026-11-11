/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.EtaleCohomology.Classical.FreeModuleSheafActionSections
public import Nyll.EtaleCohomology.Classical.FreeModuleSheafCoalgebra
public import Nyll.EtaleCohomology.Classical.FreeModuleSheafCochains
public import Nyll.EtaleCohomology.Sites.ConstantModuleLocalSections
public import Mathlib.Algebra.Ring.ULift
public import Mathlib.CategoryTheory.Sites.LocallySurjective
public import Mathlib.CategoryTheory.Sites.Sheafification
public import Mathlib.Data.ZMod.Basic

/-!
# Actual local integer exponents for cyclic cup coefficients

Every section of the original cyclic coefficient sheaf has integer
representatives on an actual covering sieve. Combining that proved
cover with the original action on free-sheaf generators computes the
actual cup cochain locally as an integer multiple of its second factor.
The same cover retains both original cochains and their restrictions.
-/

@[expose] public section

noncomputable section

universe u

open AlgebraicGeometry CategoryTheory Opposite
open scoped EtaleCohomology.ModuleTensor

namespace EtaleCohomology

variable (X : Scheme.{u}) (N : ℕ)

local notation "R" => ULift (ZMod N)
local notation "C" =>
  CategoryTheory.Functor.obj (constantSheaf X.smallEtaleTopology (ModuleCat R)) (ModuleCat.of R R)
local notation "η" =>
  toSheafify X.smallEtaleTopology
    (CategoryTheory.Functor.obj (CategoryTheory.Functor.const X.Etaleᵒᵖ) (ModuleCat.of R R))

/-- Actual local preimages in the original cyclic module give
literal integer multiples of the original constant section one. -/
theorem constantCyclicModuleSection_exists_local_integer (V : X.Etale)
    (s : (C).obj.obj (op V)) :
    ∃ S : Sieve V, S ∈ X.smallEtaleTopology V ∧
      ∀ (W : X.Etale) (k : W ⟶ V), S k →
        ∃ m : ℤ, (C).obj.map k.op s = m • (η).app (op W) (1 : R) := by
  have : Presheaf.IsLocallySurjective X.smallEtaleTopology η :=
    etaleConstantModule_toSheafify_isLocallySurjective X R (ModuleCat.of R R)
  refine ⟨Presheaf.imageSieve η s,
    Presheaf.imageSieve_mem X.smallEtaleTopology η s, ?_⟩
  intro W k hk
  obtain ⟨r, hr⟩ := hk
  obtain ⟨m, hm⟩ := ZMod.intCast_surjective r.down
  have hmr : (m : R) = r := by
    apply ULift.ext
    exact hm
  have hη : (η).app (op W) (m : R) = m • (η).app (op W) (1 : R) := by
    simpa only [zsmul_one] using (map_zsmul ((η).app (op W)).hom m (1 : R))
  exact ⟨m, hr.symm.trans ((congrArg ((η).app (op W)) hmr.symm).trans hη)⟩

/-- On an actual cover of each original generator, its first
cyclic coefficient and its actual action use the same integer exponent. -/
theorem freeModuleSheafAction_exists_local_integer
    {P : X.Etaleᵒᵖ ⥤ Type u}
    {F : Sheaf X.smallEtaleTopology (ModuleCat.{u} R)}
    (a : (freeModuleSheafFunctor X R).obj P ⟶ C)
    (b : (freeModuleSheafFunctor X R).obj P ⟶ F)
    (V : X.Etale) (x : P.obj (op V)) :
    ∃ S : Sieve V, S ∈ X.smallEtaleTopology V ∧
      ∀ (W : X.Etale) (k : W ⟶ V), S k →
        ∃ m : ℤ,
          (freeModuleSheafHomEquiv X R P C a).app (op W) (P.map k.op x) =
              m • (η).app (op W) (1 : R) ∧
          (freeModuleSheafHomEquiv X R P F (freeModuleSheafAction X R a b)).app
              (op W) (P.map k.op x) =
            m • (freeModuleSheafHomEquiv X R P F b).app (op W) (P.map k.op x) := by
  obtain ⟨S, hS, hrep⟩ := constantCyclicModuleSection_exists_local_integer X N V
    ((freeModuleSheafHomEquiv X R P C a).app (op V) x)
  refine ⟨S, hS, ?_⟩
  intro W k hk
  obtain ⟨m, hm⟩ := hrep W k hk
  have ha : (freeModuleSheafHomEquiv X R P C a).app (op W) (P.map k.op x) =
      m • (η).app (op W) (1 : R) :=
    (ConcreteCategory.congr_hom
      ((freeModuleSheafHomEquiv X R P C a).naturality k.op) x).trans hm
  exact ⟨m, ha,
    freeModuleSheafAction_generator_of_zsmul X R a b W (P.map k.op x) m ha⟩

end EtaleCohomology
