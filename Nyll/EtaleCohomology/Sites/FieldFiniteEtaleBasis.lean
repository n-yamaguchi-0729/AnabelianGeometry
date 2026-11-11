/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.EtaleCohomology.Sites.GaloisSections
public import Nyll.SchemeTheory.Etale.OverField.Decomposition
public import Mathlib.RingTheory.Etale.Field
public import Mathlib.CategoryTheory.Sites.DenseSubsite.InducedTopology
public import Mathlib.CategoryTheory.Sites.DenseSubsite.OneHypercoverDense
public import Nyll.SchemeTheory.Pi1.FiniteEtale.Basic

/-!
# The finite etale basis of a field

Actual spectra of finite separable extensions cover every object of the
small etale site of a field. Thus the existing inclusion of finite etale
objects is cover dense, in every characteristic. This is the geometric
input for passing between field sheaves and their finite-cover values.
-/

@[expose] public section

noncomputable section
universe u v w
open AlgebraicGeometry CategoryTheory Limits Opposite

namespace EtaleCohomology

/-- Every small etale object over a field has a small covering family of
actual finite etale objects. -/
theorem exists_small_finiteEtale_cover_of_field
    (K : Type u) [Field K] (V : (Spec (.of K)).Etale) :
    ∃ (ι : Type u) (A : ι → FiniteEtale (Spec (.of K)))
      (l : ∀ i, (finiteEtaleInclusion (Spec (.of K))).obj (A i) ⟶ V),
      Sieve.ofArrows _ l ∈ (Spec (.of K)).smallEtaleTopology V := by
  obtain ⟨L, a, e, hfield, hsep, he⟩ := Scheme.Etale.exists_iso_sigmaSpec K V
  have hfinite (x : V.left) : IsFiniteEtale (Spec.map (a x)) := by
    let : Field (L x) := (hfield x).toField
    let : Algebra K (L x) := (a x).hom.toAlgebra
    have : Module.Finite K (L x) := (hsep x).1
    have : Algebra.IsSeparable K (L x) := (hsep x).2
    have : Algebra.FormallyEtale K (L x) :=
      Algebra.FormallyEtale.of_isSeparable K (L x)
    have : Algebra.Etale K (L x) :=
      ⟨inferInstance, Algebra.FinitePresentation.of_finiteType.mp inferInstance⟩
    rw [IsFiniteEtale.SpecMap_iff]
    change (algebraMap K (L x)).FiniteEtale
    rw [RingHom.finiteEtale_algebraMap_iff, Algebra.finiteEtale_iff]
    exact ⟨inferInstance, inferInstance⟩
  let A (x : V.left) : FiniteEtale (Spec (.of K)) :=
    MorphismProperty.Over.mk ⊤ (Spec.map (a x)) (hfinite x)
  let I := finiteEtaleInclusion (Spec (.of K))
  let l (x : V.left) : I.obj (A x) ⟶ V :=
    MorphismProperty.Over.homMk
      (P := show MorphismProperty Scheme.{u} from @AlgebraicGeometry.Etale)
      (Q := ⊤) (Sigma.ι (fun y => Spec (L y)) x ≫ e.hom) (by
        change (Sigma.ι (fun y => Spec (L y)) x ≫ e.hom) ≫ V.hom =
          Spec.map (a x)
        rw [Category.assoc, he, Sigma.ι_comp_desc])
  have hc : Sieve.ofArrows (fun x => I.obj (A x)) l ∈
      (Spec (.of K)).smallEtaleTopology V := by
    apply (Scheme.ofArrows_mem_smallEtaleTopology_iff l).mpr
    apply Set.eq_univ_of_forall
    intro v
    obtain ⟨z, hz⟩ := e.hom.homeomorph.surjective v
    obtain ⟨⟨x, t⟩, ht⟩ := (sigmaMk (fun y => Spec (L y))).surjective z
    refine Set.mem_iUnion.mpr ⟨x, t, ?_⟩
    change e.hom (Sigma.ι (fun y => Spec (L y)) x t) = v
    rw [← sigmaMk_mk, ht]
    exact hz
  exact ⟨V.left, A, l, hc⟩

/-- Finite etale objects form a cover-dense subsite of the actual small
etale site of a field, by decomposition into finite separable fields. -/
theorem finiteEtaleInclusion_isCoverDense_of_field
    (K : Type u) [Field K] :
    (finiteEtaleInclusion (Spec (.of K))).IsCoverDense
      (Spec (.of K)).smallEtaleTopology where
  is_cover V := by
    obtain ⟨ι, A, l, hc⟩ := exists_small_finiteEtale_cover_of_field K V
    apply (Spec (.of K)).smallEtaleTopology.superset_covering (R := _) ?_ hc
    intro W g hg
    obtain ⟨x, k, rfl⟩ := (Sieve.mem_ofArrows_iff
      (fun i => (finiteEtaleInclusion (Spec (.of K))).obj (A i)) l g).mp hg
    exact ⟨⟨A x, k, l x, rfl⟩⟩

/-- The topology on actual finite etale objects induced by the small
etale topology of the field. -/
def fieldFiniteEtaleTopology (K : Type u) [Field K] :
    GrothendieckTopology (FiniteEtale (Spec (.of K))) :=
  (finiteEtaleInclusion (Spec (.of K))).restrictedTopology
    (Spec (.of K)).smallEtaleTopology

instance finiteEtaleInclusion_full (Z : Scheme.{u}) :
    (finiteEtaleInclusion Z).Full where
  map_surjective {A B} g := by
    refine ⟨MorphismProperty.Over.homMk
      (P := show MorphismProperty Scheme.{u} from @IsFiniteEtale)
      (Q := ⊤) g.left g.w, ?_⟩
    apply MorphismProperty.Over.Hom.ext
    rfl

instance finiteEtaleInclusion_faithful (Z : Scheme.{u}) :
    (finiteEtaleInclusion Z).Faithful where
  map_injective {A B} g h e := by
    apply MorphismProperty.Over.Hom.ext
    exact congrArg (fun k => k.left) e

instance fieldFiniteEtale_denseSubsite (K : Type u) [Field K] :
    (finiteEtaleInclusion (Spec (.of K))).IsDenseSubsite
      (fieldFiniteEtaleTopology K) (Spec (.of K)).smallEtaleTopology := by
  have := finiteEtaleInclusion_isCoverDense_of_field K
  dsimp only [fieldFiniteEtaleTopology]
  infer_instance

instance fieldFiniteEtale_oneHypercoverDense (K : Type u) [Field K] :
    (finiteEtaleInclusion (Spec (.of K))).IsOneHypercoverDense.{u}
      (fieldFiniteEtaleTopology K) (Spec (.of K)).smallEtaleTopology :=
  Functor.IsOneHypercoverDense.of_hasPullbacks
    (exists_small_finiteEtale_cover_of_field K)

/-- Restriction to actual finite etale objects is an equivalence for
sheaves with coefficients admitting small limits. In particular this
applies to the original small abelian sheaves, without a universe lift. -/
def fieldFiniteEtaleSheafEquivalence
    (K : Type u) [Field K] (A : Type v) [Category.{w} A]
    [HasLimitsOfSize.{u, u} A] :
    Sheaf (fieldFiniteEtaleTopology K) A ≌
      Sheaf (Spec (.of K)).smallEtaleTopology A := by
  have : ((finiteEtaleInclusion (Spec (.of K))).sheafPushforwardContinuous A
      (fieldFiniteEtaleTopology K) (Spec (.of K)).smallEtaleTopology).IsEquivalence :=
    Functor.isEquivalence_of_isOneHypercoverDense
      (finiteEtaleInclusion (Spec (.of K))) (fieldFiniteEtaleTopology K)
      (Spec (.of K)).smallEtaleTopology A
  exact Functor.IsDenseSubsite.sheafEquiv (fieldFiniteEtaleTopology K)
    (Spec (.of K)).smallEtaleTopology (finiteEtaleInclusion (Spec (.of K))) A

end EtaleCohomology
