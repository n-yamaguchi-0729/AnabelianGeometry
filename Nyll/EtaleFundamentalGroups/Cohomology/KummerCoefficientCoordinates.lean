/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.EtaleFundamentalGroups.Inertia.PrimeToRootsCoordinates
public import Nyll.EtaleCohomology.Classical.Adic
public import Nyll.EtaleFundamentalGroups.Cohomology.SchemePullback

/-!
# Actual finite cohomology in compatible Kummer coordinates

The coordinates are supplied by the original roots inverse limit. Applying
the constant-sheaf and derived cohomology functors gives equivalences with
the original finite cyclic cohomology in every degree. Their transition and
scheme-pullback squares retain the actual coefficient maps.

-/

@[expose] public section

noncomputable section

open AlgebraicGeometry CategoryTheory EtaleCohomology.Classical
open EtaleFundamentalGroups.Inertia

universe u

namespace EtaleFundamentalGroups.Cohomology

/-- The original derived cohomology with constant roots-of-unity
coefficients, bundled with its existing additive group. -/
def rootsCohomology (K : Type u) [CommMonoid K] (X : Scheme.{u}) (n i : ℕ) :
    AddCommGrpCat.{u} :=
  AddCommGrpCat.of (Sheaf.H.{u} ((constantSheaf X.smallEtaleTopology AddCommGrpCat.{u}).obj
    (AddCommGrpCat.of (Additive (rootsOfUnity n K)))) i)

/-- The cohomology map induced by the original roots power map. -/
def rootsCohomologyReduce (K : Type u) [CommMonoid K] (X : Scheme.{u})
    {m n : ℕ} (h : m ∣ n) (i : ℕ) :
    rootsCohomology K X n i →+ rootsCohomology K X m i :=
  Sheaf.H.map ((constantSheaf X.smallEtaleTopology AddCommGrpCat.{u}).map
    (AddCommGrpCat.ofHom (rootsOfUnityPowerTransition K h).toAdditive)) i

/-- Compatible roots coordinates identify the actual lifted cyclic
coefficient group with the original finite roots group. -/
def cyclicRootsCoefficientIso (K : Type u) [Field K] [IsAlgClosed K]
    (n : InvertibleExponent K) :
    AddCommGrpCat.of (ULift.{u} (ZMod n.val)) ≅
      AddCommGrpCat.of (Additive (rootsOfUnity n.val K)) :=
  ((AddEquiv.ulift : ULift.{u} (ZMod n.val) ≃+ ZMod n.val).trans
    (primeToRootsCoordinate K n)).toAddCommGrpIso

/-- The prime-power exponent with its supplied invertibility in the coefficient field. -/
def invertiblePowerExponent (K : Type u) [Field K]
    (ℓ : ℕ) (hℓ : IsUnit (ℓ : K)) (n : ℕ) : InvertibleExponent K :=
  ⟨ℓ ^ (n + 1), by rw [Nat.cast_pow]; exact hℓ.pow (n + 1)⟩

/-- The actual cyclic coefficients at level `n` in roots coordinates. -/
def ellPowerRootsCoefficientIso (K : Type u) [Field K] [IsAlgClosed K]
    (ℓ : ℕ) (hℓ : IsUnit (ℓ : K)) (n : ℕ) :
    ellPowerCoefficients.{u} ℓ n ≅
      AddCommGrpCat.of (Additive (rootsOfUnity (ℓ ^ (n + 1)) K)) :=
  cyclicRootsCoefficientIso K (invertiblePowerExponent K ℓ hℓ n)

/-- Consecutive cyclic coefficient reductions are the original roots power
maps under the constructed, compatible coordinates. -/
theorem ellPowerRootsCoefficientIso_reduction
    (K : Type u) [Field K] [IsAlgClosed K]
    (ℓ : ℕ) (hℓ : IsUnit (ℓ : K)) (n : ℕ) :
    (ellPowerRootsCoefficientIso K ℓ hℓ (n + 1)).hom ≫
        AddCommGrpCat.ofHom
          (rootsOfUnityPowerTransition K (pow_dvd_pow ℓ (Nat.le_succ (n + 1)))).toAdditive =
      AddCommGrpCat.ofHom (ellPowerReduction ℓ n) ≫
        (ellPowerRootsCoefficientIso K ℓ hℓ n).hom := by
  apply AddCommGrpCat.hom_ext
  apply AddMonoidHom.ext
  intro a
  exact primeToRootsCoordinate_reduction K
    (m := invertiblePowerExponent K ℓ hℓ n)
    (n := invertiblePowerExponent K ℓ hℓ (n + 1))
    (pow_dvd_pow ℓ (Nat.le_succ (n + 1))) a.down

/-- Actual finite cyclic cohomology and actual constant-roots cohomology,
in every degree, through the constructed coefficient isomorphism. -/
def finiteLevelKummerEquiv
    (K : Type u) [Field K] [IsAlgClosed K] (X : Scheme.{u})
    (ℓ : ℕ) (hℓ : IsUnit (ℓ : K)) (n i : ℕ) :
    finiteLevelCohomology X ℓ n i ≃+ rootsCohomology K X (ℓ ^ (n + 1)) i :=
  (((constantSheaf X.smallEtaleTopology AddCommGrpCat.{u} ⋙
    Sheaf.functorH X.smallEtaleTopology i).mapIso
      (ellPowerRootsCoefficientIso K ℓ hℓ n))).addCommGroupIsoToAddEquiv

private theorem cohomology_coefficientSquare
    (X : Scheme.{u}) {A B C D : AddCommGrpCat.{u}}
    (f : A ⟶ B) (g : B ⟶ D) (h : A ⟶ C) (k : C ⟶ D)
    (hsq : f ≫ g = h ≫ k) (i : ℕ)
    (a : Sheaf.H.{u} ((constantSheaf X.smallEtaleTopology AddCommGrpCat.{u}).obj A) i) :
    Sheaf.H.map ((constantSheaf X.smallEtaleTopology AddCommGrpCat.{u}).map g) i
        (Sheaf.H.map ((constantSheaf X.smallEtaleTopology AddCommGrpCat.{u}).map f) i a) =
      Sheaf.H.map ((constantSheaf X.smallEtaleTopology AddCommGrpCat.{u}).map k) i
        (Sheaf.H.map ((constantSheaf X.smallEtaleTopology AddCommGrpCat.{u}).map h) i a) := by
  rw [← Sheaf.H.map_comp_apply, ← Sheaf.H.map_comp_apply,
    ← Functor.map_comp, ← Functor.map_comp, hsq]

/-- The finite derived equivalences commute with the original transition
maps, without replacing either cohomology group by a character model. -/
theorem finiteLevelKummerEquiv_reduction
    (K : Type u) [Field K] [IsAlgClosed K] (X : Scheme.{u})
    (ℓ : ℕ) (hℓ : IsUnit (ℓ : K)) (n i : ℕ)
    (a : finiteLevelCohomology X ℓ (n + 1) i) :
    rootsCohomologyReduce K X (pow_dvd_pow ℓ (Nat.le_succ (n + 1))) i
        (finiteLevelKummerEquiv K X ℓ hℓ (n + 1) i a) =
      finiteLevelKummerEquiv K X ℓ hℓ n i (finiteLevelReduction X ℓ n i a) :=
  cohomology_coefficientSquare X (ellPowerRootsCoefficientIso K ℓ hℓ (n + 1)).hom
    (AddCommGrpCat.ofHom
      (rootsOfUnityPowerTransition K (pow_dvd_pow ℓ (Nat.le_succ (n + 1)))).toAdditive)
    (AddCommGrpCat.ofHom (ellPowerReduction ℓ n)) (ellPowerRootsCoefficientIso K ℓ hℓ n).hom
    (ellPowerRootsCoefficientIso_reduction K ℓ hℓ n) i a

/-- The same coefficient coordinates commute with pullback along the
original scheme morphism, in every cohomological degree. -/
theorem finiteLevelKummerEquiv_pullback
    (K : Type u) [Field K] [IsAlgClosed K] {X Y : Scheme.{u}} (f : X ⟶ Y)
    (ℓ : ℕ) (hℓ : IsUnit (ℓ : K)) (n i : ℕ)
    (a : finiteLevelCohomology Y ℓ n i) :
    finiteLevelKummerEquiv K X ℓ hℓ n i
        (constantCohomologyPullback f (ellPowerCoefficients ℓ n) i a) =
      constantCohomologyPullback f
        (AddCommGrpCat.of (Additive (rootsOfUnity (ℓ ^ (n + 1)) K))) i
        (finiteLevelKummerEquiv K Y ℓ hℓ n i a) :=
  constantCohomologyPullback_naturality f (ellPowerCoefficients ℓ n)
    (AddCommGrpCat.of (Additive (rootsOfUnity (ℓ ^ (n + 1)) K)))
    (ellPowerRootsCoefficientIso K ℓ hℓ n).hom i a

end EtaleFundamentalGroups.Cohomology
