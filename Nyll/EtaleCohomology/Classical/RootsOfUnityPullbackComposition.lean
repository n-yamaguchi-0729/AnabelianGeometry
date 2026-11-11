/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.EtaleCohomology.Classical.AlgebraicallyClosedCohomology
public import Nyll.EtaleCohomology.Classical.ConstantRootsOfUnity
public import Nyll.EtaleCohomology.Classical.ConstantRootsOfUnityNaturality
public import Nyll.EtaleCohomology.Classical.ExternalCupPullbackComposition
public import Nyll.EtaleCohomology.Classical.KummerPullback
public import Nyll.EtaleCohomology.Classical.KummerSequence
public import Nyll.EtaleCohomology.Classical.PullbackIdentity
public import Nyll.EtaleFundamentalGroups.Cohomology.SchemePullback
public import Mathlib.Algebra.Category.Grp.Basic
public import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic

/-!
# Composition of the original Kummer-coefficient pullbacks

The actual structural constant-root comparison identifies the original
Kummer pullback with the original constant-coefficient pullback. Its
bijectivity transfers composition and identity to the native maps.
Positive-degree pullback through an algebraically closed point vanishes
by the original cohomology of that point.
-/

@[expose] public section

noncomputable section

universe u

open AlgebraicGeometry CategoryTheory
open EtaleFundamentalGroups.Cohomology

namespace EtaleCohomology

variable {K : Type u} [Field K] [IsAlgClosed K]
  {X Y Z : Scheme.{u}} {n : ℕ}

/-- The original roots-of-unity cohomology maps compose in the
contravariant order, with the same structural roots comparison. -/
theorem etaleRootsOfUnityCohomologyPullback_comp
    (f : X ⟶ Y) (g : Y ⟶ Z) (c : Z ⟶ Spec (.of K))
    (hn : 0 < n) (hnK : IsUnit (n : K)) (i : ℕ)
    (a : Sheaf.H.{u} (etaleRootsOfUnitySheaf Z n) i) :
    etaleRootsOfUnityCohomologyPullback (f ≫ g) n i a =
      etaleRootsOfUnityCohomologyPullback f n i
        (etaleRootsOfUnityCohomologyPullback g n i a) := by
  let A := AddCommGrpCat.of (Additive (rootsOfUnity n K))
  let e := (Sheaf.functorH Z.smallEtaleTopology i).mapIso
    (constantRootsOfUnityKummerKernelIso c hn hnK)
  obtain ⟨x, hx⟩ := e.addCommGroupIsoToAddEquiv.surjective a
  change Sheaf.H.map (constantRootsOfUnityToKummerKernel c n) i x = a at hx
  rw [← hx,
    ← constantRootsOfUnityToKummerKernel_cohomologyPullback (f ≫ g) c hn hnK i x,
    ← constantRootsOfUnityToKummerKernel_cohomologyPullback g c hn hnK i x,
    ← constantRootsOfUnityToKummerKernel_cohomologyPullback f (g ≫ c) hn hnK,
    etaleAbelianConstantCohomologyPullbackMap_comp f g A i x, Category.assoc]

/-- The actual identity scheme morphism induces the identity on native
roots-of-unity cohomology in every degree. -/
theorem etaleRootsOfUnityCohomologyPullback_id
    (c : X ⟶ Spec (.of K)) (hn : 0 < n) (hnK : IsUnit (n : K)) (i : ℕ)
    (a : Sheaf.H.{u} (etaleRootsOfUnitySheaf X n) i) :
    etaleRootsOfUnityCohomologyPullback (𝟙 X) n i a = a := by
  let A := AddCommGrpCat.of (Additive (rootsOfUnity n K))
  let e := (Sheaf.functorH X.smallEtaleTopology i).mapIso
    (constantRootsOfUnityKummerKernelIso c hn hnK)
  obtain ⟨x, hx⟩ := e.addCommGroupIsoToAddEquiv.surjective a
  change Sheaf.H.map (constantRootsOfUnityToKummerKernel c n) i x = a at hx
  rw [← hx,
    ← constantRootsOfUnityToKummerKernel_cohomologyPullback (𝟙 X) c hn hnK i x,
    Category.id_comp]
  exact congrArg (Sheaf.H.map (constantRootsOfUnityToKummerKernel c n) i)
    (etaleAbelianConstantCohomologyPullbackMap_id X A i x)

/-- A section of a scheme morphism gives a left inverse to its original
Kummer pullback, so that this pullback detects zero classes. -/
theorem etaleRootsOfUnityCohomologyPullback_injective_of_retraction
    (p : X ⟶ Y) (s : Y ⟶ X) (hs : s ≫ p = 𝟙 Y)
    (c : Y ⟶ Spec (.of K)) (hn : 0 < n) (hnK : IsUnit (n : K)) (i : ℕ) :
    Function.Injective (etaleRootsOfUnityCohomologyPullback p n i) := by
  have hleft : Function.LeftInverse (etaleRootsOfUnityCohomologyPullback s n i)
      (etaleRootsOfUnityCohomologyPullback p n i) := by
    intro a
    rw [← etaleRootsOfUnityCohomologyPullback_comp s p c hn hnK,
      hs, etaleRootsOfUnityCohomologyPullback_id c hn hnK]
  exact hleft.injective

/-- Original positive-degree Kummer cohomology pullback through an
algebraically closed field is zero, for the actual composite morphism. -/
theorem etaleRootsOfUnityCohomologyPullback_through_field_eq_zero
    (f : X ⟶ Spec (.of K)) (p : Spec (.of K) ⟶ Y)
    (c : Y ⟶ Spec (.of K)) (hn : 0 < n) (hnK : IsUnit (n : K))
    (i : ℕ) (a : Sheaf.H.{u} (etaleRootsOfUnitySheaf Y n) (i + 1)) :
    etaleRootsOfUnityCohomologyPullback (f ≫ p) n (i + 1) a = 0 := by
  rw [etaleRootsOfUnityCohomologyPullback_comp f p c hn hnK]
  have hp : etaleRootsOfUnityCohomologyPullback p n (i + 1) a = 0 :=
    fieldSheafCohomology_eq_zero_of_isAlgClosed K
      (etaleRootsOfUnitySheaf (Spec (.of K)) n) i _
  rw [hp, map_zero]

end EtaleCohomology
