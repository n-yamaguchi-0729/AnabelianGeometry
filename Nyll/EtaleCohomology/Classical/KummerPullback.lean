/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.EtaleCohomology.Classical.AbelianSheafFunctors
public import Nyll.EtaleCohomology.Classical.KummerSequence
public import Nyll.EtaleCohomology.Classical.MultiplicativeGroup
public import Nyll.EtaleCohomology.Classical.MultiplicativeGroupPushforward
public import Nyll.EtaleCohomology.Classical.PullbackCohomology
public import Mathlib.Algebra.Category.Grp.Basic
public import Mathlib.Algebra.Homology.DerivedCategory.Ext.Basic
public import Mathlib.Algebra.Homology.DerivedCategory.Ext.ExtClass
public import Mathlib.Algebra.Homology.DerivedCategory.Ext.Map
public import Mathlib.Algebra.Homology.ShortComplex.Basic
public import Mathlib.Algebra.Homology.ShortComplex.ShortExact
public import Mathlib.AlgebraicGeometry.Sites.AffineEtale
public import Mathlib.AlgebraicGeometry.Sites.Small
public import Mathlib.CategoryTheory.Adjunction.Basic
public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.HasExt
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Zero
public import Mathlib.CategoryTheory.Limits.Shapes.Kernels
public import Mathlib.CategoryTheory.Sites.ConstantSheaf
public import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
public import Mathlib.CategoryTheory.Sites.SheafCohomology.ExactSequences

/-!
# Scheme pullback and the original Kummer boundary

The original map of units to direct image supplies its adjoint inverse-image
map. The actual power square then induces a map on the original roots-of-unity
kernels and a morphism of the original Kummer complexes. Exact inverse image
and naturality of their extension classes identify the resulting map in H²
with pullback of the original H¹ Kummer boundary.
-/

@[expose] public section

noncomputable section

universe u

open AlgebraicGeometry CategoryTheory CategoryTheory.Abelian Limits

namespace EtaleCohomology

variable {X Y : Scheme.{u}} (f : X ⟶ Y)

/-- The inverse-image map on units is the adjoint of the original
restriction-of-units map to direct image. -/
def etaleMultiplicativeGroupPullback :
    (etaleAbelianPullback f).obj (etaleMultiplicativeGroupSheaf Y) ⟶
      etaleMultiplicativeGroupSheaf X :=
  ((etaleAbelianPullbackPushforwardAdjunction f).homEquiv
    (etaleMultiplicativeGroupSheaf Y) (etaleMultiplicativeGroupSheaf X)).symm
      (etaleMultiplicativeGroupToPushforward f)

/-- The comparison retains the original direct-image map, including its
structural map on unit sections. -/
theorem etaleMultiplicativeGroupPullback_adjunct :
    (etaleAbelianPullbackPushforwardAdjunction f).homEquiv
      (etaleMultiplicativeGroupSheaf Y) (etaleMultiplicativeGroupSheaf X)
        (etaleMultiplicativeGroupPullback f) =
      etaleMultiplicativeGroupToPushforward f :=
  ((etaleAbelianPullbackPushforwardAdjunction f).homEquiv
    (etaleMultiplicativeGroupSheaf Y) (etaleMultiplicativeGroupSheaf X)).apply_symm_apply _

/-- The actual inverse-image unit map commutes with the original power maps. -/
theorem etaleMultiplicativeGroupPullback_power (n : ℕ) :
    (etaleAbelianPullback f).map (etaleMultiplicativeGroupPower Y n) ≫
        etaleMultiplicativeGroupPullback f =
      etaleMultiplicativeGroupPullback f ≫ etaleMultiplicativeGroupPower X n :=
  (etaleAbelianPullbackPushforwardAdjunction f).homEquiv_naturality_right_square
    (etaleMultiplicativeGroupPower Y n) (etaleMultiplicativeGroupToPushforward f)
    (etaleMultiplicativeGroupToPushforward f) (etaleMultiplicativeGroupPower X n)
    (etaleMultiplicativeGroupToPushforward_power f n)

/-- The pulled-back root inclusion is killed by the original power morphism. -/
theorem rootsPullback_zero (n : ℕ) :
    ((etaleAbelianPullback f).map (kernel.ι (etaleMultiplicativeGroupPower Y n)) ≫
      etaleMultiplicativeGroupPullback f) ≫ etaleMultiplicativeGroupPower X n = 0 := by
  rw [Category.assoc, ← etaleMultiplicativeGroupPullback_power,
    ← Category.assoc, ← Functor.map_comp, kernel.condition, Functor.map_zero, zero_comp]

/-- The original power square induces pullback on the actual Kummer kernels. -/
def etaleRootsOfUnityPullback (n : ℕ) :
    (etaleAbelianPullback f).obj (etaleRootsOfUnitySheaf Y n) ⟶
      etaleRootsOfUnitySheaf X n :=
  kernel.lift (etaleMultiplicativeGroupPower X n)
    ((etaleAbelianPullback f).map (kernel.ι (etaleMultiplicativeGroupPower Y n)) ≫
      etaleMultiplicativeGroupPullback f) (rootsPullback_zero f n)

/-- The kernel map retains the original inclusion in the unit sheaf. -/
theorem etaleRootsOfUnityPullback_ι (n : ℕ) :
    etaleRootsOfUnityPullback f n ≫ kernel.ι (etaleMultiplicativeGroupPower X n) =
      (etaleAbelianPullback f).map (kernel.ι (etaleMultiplicativeGroupPower Y n)) ≫
        etaleMultiplicativeGroupPullback f :=
  kernel.lift_ι _ _ _

/-- Pullback of the original Kummer complex maps to the original Kummer
complex on the source, with the actual unit map in both unit positions. -/
def etaleKummerPullbackComplex (n : ℕ) :
    (etaleKummerComplex Y n).map (etaleAbelianPullback f) ⟶ etaleKummerComplex X n where
  τ₁ := etaleRootsOfUnityPullback f n
  τ₂ := etaleMultiplicativeGroupPullback f
  τ₃ := etaleMultiplicativeGroupPullback f
  comm₁₂ := etaleRootsOfUnityPullback_ι f n
  comm₂₃ := (etaleMultiplicativeGroupPullback_power f n).symm

/-- Scheme pullback on the original cohomology of the unit sheaf. -/
def etaleMultiplicativeGroupCohomologyPullback (i : ℕ) :
    Sheaf.H.{u} (etaleMultiplicativeGroupSheaf Y) i →+
      Sheaf.H.{u} (etaleMultiplicativeGroupSheaf X) i :=
  (Sheaf.H.map (etaleMultiplicativeGroupPullback f) i).comp
    (etaleAbelianCohomologyPullbackMap f (etaleMultiplicativeGroupSheaf Y) i)

/-- Scheme pullback on the original cohomology of the Kummer kernel. -/
def etaleRootsOfUnityCohomologyPullback (n i : ℕ) :
    Sheaf.H.{u} (etaleRootsOfUnitySheaf Y n) i →+
      Sheaf.H.{u} (etaleRootsOfUnitySheaf X n) i :=
  (Sheaf.H.map (etaleRootsOfUnityPullback f n) i).comp
    (etaleAbelianCohomologyPullbackMap f (etaleRootsOfUnitySheaf Y n) i)

private theorem kummerBoundary_one_exactPullback
    {n : ℕ} (hn : 0 < n) (hnY : IsUnit (n : Γ(Y, ⊤)))
    (a : Sheaf.H.{u} (etaleMultiplicativeGroupSheaf Y) 1) :
    etaleAbelianCohomologyPullbackMap f (etaleRootsOfUnitySheaf Y n) 2
        (Sheaf.H.δ (etaleKummerComplex_shortExact Y hn hnY) 1 2 rfl a) =
      Sheaf.H.δ ((etaleKummerComplex_shortExact Y hn hnY).map_of_exact
        (etaleAbelianPullback f)) 1 2 rfl
          (etaleAbelianCohomologyPullbackMap f (etaleMultiplicativeGroupSheaf Y) 1 a) := by
  let L := etaleAbelianPullback f
  let hS := etaleKummerComplex_shortExact Y hn hnY
  let u := ((etaleAbelianPullbackConstantIso f).app
    (AddCommGrpCat.of (ULift.{u} ℤ))).inv
  change (Ext.mk₀ u).comp ((a.comp hS.extClass rfl).mapExactFunctor L) (zero_add 2) =
    ((Ext.mk₀ u).comp (a.mapExactFunctor L) (zero_add 1)).comp
      (hS.map_of_exact L).extClass rfl
  rw [Ext.mapExactFunctor_comp, Ext.mapExactFunctor_extClass]
  exact (Ext.comp_assoc (Ext.mk₀ u) (a.mapExactFunctor L)
    (hS.map_of_exact L).extClass (zero_add 1) rfl rfl).symm

/-- Pullback by the original scheme morphism commutes with the original
H¹(Gm) → H²(μn) Kummer boundary. Invertibility on the source is supplied by
the actual global-section map of the scheme morphism. -/
theorem etaleKummerBoundary_one_pullback
    {n : ℕ} (hn : 0 < n) (hnY : IsUnit (n : Γ(Y, ⊤)))
    (a : Sheaf.H.{u} (etaleMultiplicativeGroupSheaf Y) 1) :
    etaleRootsOfUnityCohomologyPullback f n 2
        (Sheaf.H.δ (etaleKummerComplex_shortExact Y hn hnY) 1 2 rfl a) =
      Sheaf.H.δ (etaleKummerComplex_shortExact X hn
        (by simpa only [map_natCast] using hnY.map f.appTop.hom)) 1 2 rfl
          (etaleMultiplicativeGroupCohomologyPullback f 1 a) := by
  have hnX : IsUnit (n : Γ(X, ⊤)) := by
    simpa only [map_natCast] using hnY.map f.appTop.hom
  let hY := etaleKummerComplex_shortExact Y hn hnY
  let hX := etaleKummerComplex_shortExact X hn hnX
  let b := etaleAbelianCohomologyPullbackMap f (etaleMultiplicativeGroupSheaf Y) 1 a
  have hδ := Sheaf.H.δ_naturality 1 2 rfl
    (hY.map_of_exact (etaleAbelianPullback f)) hX
    (etaleKummerPullbackComplex f n) b
  change Sheaf.H.δ hX 1 2 rfl
      (Sheaf.H.map (etaleMultiplicativeGroupPullback f) 1 b) =
    Sheaf.H.map (etaleRootsOfUnityPullback f n) 2
      (Sheaf.H.δ (hY.map_of_exact (etaleAbelianPullback f)) 1 2 rfl b) at hδ
  exact (congrArg (Sheaf.H.map (etaleRootsOfUnityPullback f n) 2)
    (kummerBoundary_one_exactPullback f hn hnY a)).trans hδ.symm

end EtaleCohomology
