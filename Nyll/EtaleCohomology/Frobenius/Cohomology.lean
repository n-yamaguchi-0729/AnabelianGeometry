/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.EtaleCohomology.Classical.Etale
public import Nyll.EtaleCohomology.Classical.ModuleCohomology
public import Nyll.EtaleCohomology.Classical.PullbackCohomology
public import Nyll.EtaleCohomology.Sites.ConstantPullback
public import Nyll.SchemeTheory.Morphisms.FrobeniusBaseChange

/-!
# Scheme Frobenius on classical étale cohomology

Constant coefficients are pulled back by the actual exact inverse-image functor.
Applying this construction to the existing finite-field scheme Frobenius after
extending constants gives a coefficient-linear endomorphism of classical
étale cohomology in every degree.

The geometric morphism used here is the base change of the q-power Frobenius
of the original scheme. Identifying its cohomological action with inverse
arithmetic Galois Frobenius requires the separate étale Frobenius comparison.
No such comparison is assumed in these definitions.
-/

@[expose] public section

noncomputable section

universe u

open AlgebraicGeometry CategoryTheory Limits

namespace EtaleCohomology

variable {X Y : Scheme.{u}} (f : X ⟶ Y) (R : Type u) [CommRing R]

/-- The actual pullback on classical cohomology with a constant module as
coefficients, using the canonical inverse-image comparison of constant sheaves. -/
def etaleConstantCohomologyPullbackMap (M : ModuleCat.{u} R) (n : ℕ) :
    etaleCohomology Y R ((constantSheaf Y.smallEtaleTopology (ModuleCat.{u} R)).obj M) n
      →ₗ[R]
    etaleCohomology X R ((constantSheaf X.smallEtaleTopology (ModuleCat.{u} R)).obj M) n :=
  (Classical.cohomologyMap.{u + 1, u, u, u, u} ((etalePullbackConstantIso f R).hom.app M) n).comp
    (etaleCohomologyPullbackMap f R
      ((constantSheaf Y.smallEtaleTopology (ModuleCat.{u} R)).obj M) n)

/-- Pullback with constant coefficients is natural in the coefficient module. -/
theorem etaleConstantCohomologyPullbackMap_naturality
    {M N : ModuleCat.{u} R} (φ : M ⟶ N) (n : ℕ)
    (x : etaleCohomology Y R
      ((constantSheaf Y.smallEtaleTopology (ModuleCat.{u} R)).obj M) n) :
    etaleConstantCohomologyPullbackMap f R N n
        (Classical.cohomologyMap
          ((constantSheaf Y.smallEtaleTopology (ModuleCat.{u} R)).map φ) n x) =
      Classical.cohomologyMap
        ((constantSheaf X.smallEtaleTopology (ModuleCat.{u} R)).map φ) n
          (etaleConstantCohomologyPullbackMap f R M n x) := by
  let FM := (constantSheaf Y.smallEtaleTopology (ModuleCat.{u} R)).obj M
  let FN := (constantSheaf Y.smallEtaleTopology (ModuleCat.{u} R)).obj N
  let φY : FM ⟶ FN := (constantSheaf Y.smallEtaleTopology (ModuleCat.{u} R)).map φ
  let φX := (constantSheaf X.smallEtaleTopology (ModuleCat.{u} R)).map φ
  let eM : (etalePullback f R).obj FM ⟶
      (constantSheaf X.smallEtaleTopology (ModuleCat.{u} R)).obj M :=
    (etalePullbackConstantIso f R).hom.app M
  let eN : (etalePullback f R).obj FN ⟶
      (constantSheaf X.smallEtaleTopology (ModuleCat.{u} R)).obj N :=
    (etalePullbackConstantIso f R).hom.app N
  let y : Sheaf.H.{u} (Classical.forgetCoefficients.{u + 1, u, u, u}.obj
      ((etalePullback f R).obj FM)) n := etaleCohomologyPullbackMap f R FM n x
  have h := etaleCohomologyPullbackMap_naturality f R φY n x
  have he : (etalePullback f R).map φY ≫ eN = eM ≫ φX :=
    (etalePullbackConstantIso f R).hom.naturality φ
  have hy :
      Sheaf.H.map (Classical.forgetCoefficients.{u + 1, u, u, u}.map eN) n
        (Sheaf.H.map (Classical.forgetCoefficients.{u + 1, u, u, u}.map
          ((etalePullback f R).map φY)) n y) =
      Sheaf.H.map (Classical.forgetCoefficients.{u + 1, u, u, u}.map φX) n
        (Sheaf.H.map (Classical.forgetCoefficients.{u + 1, u, u, u}.map eM) n y) := by
    rw [← Sheaf.H.map_comp_apply, ← Sheaf.H.map_comp_apply,
      ← Functor.map_comp, ← Functor.map_comp, he]
  exact (congrArg (fun z : etaleCohomology X R ((etalePullback f R).obj FN) n =>
    Classical.cohomologyMap.{u + 1, u, u, u, u} eN n z) h).trans hy

variable (k Ω : Type u) [Field k] [Fintype k] [Field Ω] [Algebra k Ω]
  [Algebra.IsAlgebraic k Ω] (X : Scheme.{u}) [X.Over (Spec (CommRingCat.of k))]

local notation "XΩ" => pullback (X ↘ Spec (CommRingCat.of k))
  (Spec.map (CommRingCat.ofHom (algebraMap k Ω)))

/-- The q-power scheme Frobenius acts on actual classical étale cohomology
after extension of constants, with an arbitrary constant coefficient module. -/
def finiteFieldFrobeniusCohomology (M : ModuleCat.{u} R) (n : ℕ) :
    Module.End R
      (etaleCohomology XΩ R
        ((constantSheaf (XΩ).smallEtaleTopology (ModuleCat.{u} R)).obj M) n) :=
  etaleConstantCohomologyPullbackMap
    (Scheme.constantBaseChangeFrobenius k Ω X) R M n

end EtaleCohomology
