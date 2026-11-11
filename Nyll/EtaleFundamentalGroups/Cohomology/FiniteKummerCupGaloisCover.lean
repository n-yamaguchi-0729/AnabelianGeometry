/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.EtaleCohomology.Classical.GenericUnitCohomology
public import Nyll.EtaleCohomology.Sites.GaloisSections
public import Nyll.EtaleFundamentalGroups.Cohomology.FiniteKummerCupCover
public import Nyll.EtaleFundamentalGroups.FiniteEtale.Connected
public import Nyll.EtaleFundamentalGroups.Pi1.FiniteEtale.GaloisCategory
public import Nyll.SchemeTheory.Pi1.FiniteEtale.Basic
public import Nyll.SchemeTheory.Pi1.FiniteEtale.Geometry
public import Mathlib.AlgebraicGeometry.Sites.Etale
public import Mathlib.AlgebraicGeometry.Sites.Small
public import Mathlib.CategoryTheory.Galois.Decomposition

/-!
# A genuine Galois refinement of the original two-root cover

The original common Kummer cover is finite and nonempty. Its fiber
therefore admits an actual map from a finite Galois object. This gives
a genuine covering refinement, retaining the map to the original
common cover and hence both original universal roots. The refinement
map need not cover every connected component of the common cover.
-/

@[expose] public section

noncomputable section

universe u

open AlgebraicGeometry CategoryTheory Limits TopologicalSpace
open CategoryTheory.PreGaloisCategory
open EtaleCohomology

namespace EtaleFundamentalGroups.Cohomology

variable {K : Type u} [Field K] [IsAlgClosed K]
  {X : Scheme.{u}} [IsIntegral X] (c : X ⟶ Spec (.of K))
  (ℓ : ℕ) [Fact ℓ.Prime] (hℓ : IsUnit (ℓ : K)) (n : ℕ)
  (d : Bool → Sheaf.H.{u} (etaleGenericUnitQuotient X) 0)
  (b : Bool → Sheaf.H.{u} (etaleGenericUnitShortComplex X).X₂ 0)
  (hb : ∀ i, Sheaf.H.map (etaleGenericUnitShortComplex X).g 0 (b i) =
    ℓ ^ (n + 1) • d i)
  {T : X.Etale} (hT : IsTerminal T)

/-- An actual finite Galois object refines the original common root
cover and still covers the original terminal representative. -/
theorem finiteKummerCupCommonCover_exists_galois_refinement :
    ∃ (Y : FiniteEtale X) (_ : IsGalois Y)
      (g : (finiteEtaleInclusion X).obj Y ⟶
        finiteKummerCupCommonCover c ℓ hℓ n d b hb hT),
      Surjective Y.hom ∧
        Sieve.generate (Presieve.singleton
          (g ≫ hT.from (finiteKummerCupCommonCover c ℓ hℓ n d b hb hT))) ∈
            X.smallEtaleTopology T := by
  let V := finiteKummerCupCommonCover c ℓ hℓ n d b hb hT
  let f := hT.from V
  have hcover : Sieve.ofArrows (fun _ : PUnit.{u + 1} => V) (fun _ => f) ∈
      X.smallEtaleTopology T := by
    simpa only [Sieve.ofArrows, Presieve.ofArrows_pUnit] using
      finiteKummerCupCommonCover_covering c ℓ hℓ n d b hb hT
  have hfs : Function.Surjective f.left := Set.range_eq_univ.mp (by
    simpa only [Set.iUnion_const] using
      (Scheme.ofArrows_mem_smallEtaleTopology_iff (fun _ : PUnit.{u + 1} => f)).mp hcover)
  obtain ⟨v, _⟩ := hfs ((hT.from (Scheme.Etale.mk (𝟙 X))).left (genericPoint X))
  have : IsFinite V.hom := finiteKummerCupCommonCover_finite c ℓ hℓ n d b hb hT
  have : IsFiniteEtale V.hom := IsFiniteEtale.mk
  let V' : FiniteEtale X := FiniteEtale.mk V.hom
  have : Nonempty V'.left := by
    change Nonempty V.left
    exact ⟨v⟩
  let F := CategoryTheory.GaloisCategory.getFiberFunctor (FiniteEtale X)
  have hnonempty : Nonempty (F.obj V') :=
    (not_initial_iff_fiber_nonempty F V').mp (FiniteEtale.notInitial_of_nonempty_left V')
  obtain ⟨Y, g₀, hY⟩ := exists_hom_from_galois_of_fiber_nonempty F V' hnonempty
  have : IsGalois Y := hY
  have : ConnectedSpace Y.left := FiniteEtale.connectedSpace_left_of_isConnected Y
  have hYsurj : Surjective Y.hom :=
    IsFiniteEtale.surjective (X := Y.left) (Y := X) Y.hom
  let g : (finiteEtaleInclusion X).obj Y ⟶ V := (finiteEtaleInclusion X).map g₀
  have : IsIso T.hom := etaleTerminal_hom_isIso X hT
  have hw : (g ≫ f).left ≫ T.hom = Y.hom :=
    MorphismProperty.Over.w
      (P := show MorphismProperty Scheme.{u} from @Etale) (Q := ⊤) (g ≫ f)
  have hbase : (g ≫ f).left = Y.hom ≫ inv T.hom :=
    (IsIso.eq_comp_inv T.hom).mpr hw
  have hcomp : Surjective (Y.hom ≫ inv T.hom) :=
    ⟨(show Function.Surjective (inv T.hom : X ⟶ T.left) from
      (inv T.hom).homeomorph.surjective).comp
      (show Function.Surjective (Y.hom : Y.left ⟶ X) from hYsurj.surj)⟩
  have : Surjective (g ≫ f).left := by
    rw [hbase]
    exact hcomp
  refine ⟨Y, hY, g, inferInstance, ?_⟩
  have hgf : Sieve.ofArrows (fun _ : PUnit.{u + 1} => (finiteEtaleInclusion X).obj Y)
      (fun _ => g ≫ f) ∈ X.smallEtaleTopology T := by
    rw [Scheme.ofArrows_mem_smallEtaleTopology_iff, Set.iUnion_const]
    exact Set.range_eq_univ.mpr (g ≫ f).left.surjective
  simpa only [Sieve.ofArrows, Presieve.ofArrows_pUnit] using hgf

end EtaleFundamentalGroups.Cohomology
