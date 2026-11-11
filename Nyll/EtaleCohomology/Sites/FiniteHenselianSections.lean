/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.EtaleCohomology.Sites.EmptySections
public import Nyll.EtaleCohomology.Sites.FiniteAffineSectionLifts
public import Nyll.SchemeTheory.Etale.FiniteStrictLocalSection
public import Mathlib.Algebra.Category.Grp.ForgetCorepresentable
public import Mathlib.Algebra.Category.Grp.Zero
public import Mathlib.AlgebraicGeometry.Cover.Open
public import Mathlib.AlgebraicGeometry.Limits
public import Mathlib.AlgebraicGeometry.Morphisms.Basic
public import Mathlib.AlgebraicGeometry.Morphisms.RingHomProperties
public import Mathlib.AlgebraicGeometry.Morphisms.UnderlyingMap
public import Mathlib.AlgebraicGeometry.Sites.AffineEtale
public import Mathlib.AlgebraicGeometry.Sites.Etale
public import Mathlib.CategoryTheory.Sites.EpiMono
public import Mathlib.CategoryTheory.Sites.IsSheafFor
public import Mathlib.CategoryTheory.Sites.LocallySurjective
public import Mathlib.CategoryTheory.Sites.Whiskering

/-!
# Exact global sections on finite schemes over a strictly local base

Local preimages along a sheaf epimorphism glue on a finite disjoint union
of affine étale neighborhoods. The actual étale cover therefore carries
one global preimage. Over a finite algebra of a strictly Henselian ring,
the geometric section of that cover pulls this preimage back to the base.

This supplies the strictly local exactness step in Stacks Project 59.55.2.
It does not identify a direct-image stalk with a geometric-fiber product.
-/

@[expose] public section

noncomputable section

universe u

open AlgebraicGeometry CategoryTheory Limits Opposite

namespace EtaleCohomology

/-- A section of an abelian sheaf lifts along an epimorphism after one
actual affine surjective étale cover of its quasi-compact domain. The
cover is a finite disjoint union of affine local lift domains. -/
theorem exists_affine_etale_cover_section_lift
    {X : Scheme.{u}}
    {F G : Sheaf X.smallEtaleTopology AddCommGrpCat.{u}}
    (η : F ⟶ G) [Epi η]
    (U : X.Etale) [QuasiCompact (terminal.from U.left)]
    (a : G.obj.obj (op U)) :
    ∃ (W : X.Etale) (g : W ⟶ U),
      IsAffine W.left ∧ Surjective g.left ∧
      ∃ b : F.obj.obj (op W), η.hom.app (op W) b = G.obj.map g.op a := by
  classical
  have : Sheaf.IsLocallySurjective η :=
    (Sheaf.isLocallySurjective_iff_epi'
      (J := X.smallEtaleTopology) AddCommGrpCat.{u} η).mpr inferInstance
  obtain ⟨K, V, f, hAffine, hCover, hlift⟩ :=
    exists_finite_affine_cover_section_lifts η.hom (U := U) a
      (Presheaf.imageSieve_mem X.smallEtaleTopology η.hom a)
  choose b hb using hlift
  let Z : Scheme.{u} := ∐ fun i : K => (V i).left
  let q : Z ⟶ U.left := Sigma.desc fun i : K => (f i).left
  have : Etale q := IsZariskiLocalAtSource.sigmaDesc
    (P := show MorphismProperty Scheme.{u} from @Etale) (fun i => inferInstance)
  have : Surjective q := Surjective.sigmaDesc_of_union_range_eq_univ
    ((Scheme.ofArrows_mem_smallEtaleTopology_iff f).mp hCover)
  let W : X.Etale := Scheme.Etale.mk (q ≫ U.hom)
  let g : W ⟶ U := MorphismProperty.Over.homMk q rfl
  let j (i : K) : V i ⟶ W := MorphismProperty.Over.homMk
    (Sigma.ι (fun i : K => (V i).left) i) (by
      change Sigma.ι (fun i : K => (V i).left) i ≫ (q ≫ U.hom) = (V i).hom
      rw [← Category.assoc, Sigma.ι_comp_desc]
      exact (f i).w)
  have hjg (i : K) : j i ≫ g = f i :=
    MorphismProperty.Over.Hom.ext (Sigma.ι_comp_desc _ i)
  have hSigmaCover : Sieve.ofArrows V j ∈ X.smallEtaleTopology W := by
    apply (Scheme.ofArrows_mem_smallEtaleTopology_iff j).mpr
    apply Set.eq_univ_of_forall
    intro x
    obtain ⟨i, v, hv⟩ := (sigmaOpenCover (fun i : K => (V i).left)).exists_eq x
    exact Set.mem_iUnion.mpr ⟨i, v, hv⟩
  let P : X.Etaleᵒᵖ ⥤ Type u := F.obj ⋙ forget AddCommGrpCat.{u}
  have hCompat : Presieve.Arrows.Compatible P j b := by
    intro i i' T k k' h
    by_cases hii' : i = i'
    · subst i'
      have hkk' : k = k' := by
        apply MorphismProperty.Over.Hom.ext
        apply (cancel_mono (Sigma.ι (fun i : K => (V i).left) i)).mp
        exact congrArg (fun l : T ⟶ W => l.left) h
      rw [hkk']
    · have : IsEmpty T.left := isEmpty_of_commSq_sigmaι_of_ne
        (g := fun i : K => (V i).left) (a := k.left) (b := k'.left)
        (show CommSq k.left k'.left
          (Sigma.ι (fun i : K => (V i).left) i)
          (Sigma.ι (fun i : K => (V i).left) i') from
            ⟨congrArg (fun l : T ⟶ W => l.left) h⟩) hii'
      have : Subsingleton (F.obj.obj (op T)) :=
        AddCommGrpCat.subsingleton_of_isZero (etaleSections_isZero_of_isEmpty T F)
      change F.obj.map k.op (b i) = F.obj.map k'.op (b i')
      exact Subsingleton.elim _ _
  have hSheaf : Presieve.IsSheafFor P (Presieve.ofArrows V j) := by
    apply (Presieve.isSheafFor_iff_generate _).mpr
    exact (isSheaf_iff_isSheaf_of_type _ _).mp
      ((sheafCompose X.smallEtaleTopology (forget AddCommGrpCat.{u})).obj F).property
        _ hSigmaCover
  obtain ⟨s, hs, _⟩ := (Presieve.isSheafFor_arrows_iff P j).mp hSheaf b hCompat
  have hs' (i : K) : F.obj.map (j i).op s = b i := hs i
  have hηs : η.hom.app (op W) s = G.obj.map g.op a := by
    apply G.isSeparated W (Sieve.ofArrows V j) hSigmaCover
    intro T m hm
    obtain ⟨i, k, rfl⟩ := (Sieve.mem_ofArrows_iff V j m).mp hm
    have hi : G.obj.map (j i).op (η.hom.app (op W) s) =
        G.obj.map (j i).op (G.obj.map g.op a) := by
      rw [← NatTrans.naturality_apply, hs' i, hb i,
        ← G.obj.map_comp_apply, ← op_comp, hjg]
    rw [op_comp, G.obj.map_comp_apply, G.obj.map_comp_apply, hi]
  have (i : K) : IsAffine (V i).left := hAffine i
  exact ⟨W, g, inferInstanceAs (IsAffine Z), inferInstanceAs (Surjective q), s, hηs⟩

/-- Abelian sheaf epimorphisms are surjective on actual global sections
over every finite algebra of a strictly Henselian local ring. -/
theorem sheaf_epi_globalSections_surjective_of_finite_over_strictlyHenselian
    (R B : Type u) [CommRing R] [HenselianLocalRing R]
    [IsSepClosed (IsLocalRing.ResidueField R)]
    [CommRing B] [Algebra R B] [Module.Finite R B]
    {F G : Sheaf (Spec (.of B)).smallEtaleTopology AddCommGrpCat.{u}}
    (η : F ⟶ G) [Epi η] :
    Function.Surjective (η.hom.app (op (Scheme.Etale.mk (𝟙 (Spec (.of B)))))) := by
  intro a
  let X₀ : (Spec (.of B)).Etale := Scheme.Etale.mk (𝟙 (Spec (.of B)))
  have : QuasiCompact (terminal.from X₀.left) :=
    inferInstanceAs (QuasiCompact (terminal.from (Spec (.of B))))
  obtain ⟨W, g, _, hsurj, b, hb⟩ := exists_affine_etale_cover_section_lift η X₀ a
  have hg : g.left = W.hom := (Category.comp_id g.left).symm.trans g.w
  have : Surjective W.hom := hg ▸ hsurj
  obtain ⟨s, hs⟩ := Etale.exists_section_of_finite_over_strictlyHenselian R B W.hom
  let r : X₀ ⟶ W := MorphismProperty.Over.homMk s hs
  have hrg : r ≫ g = 𝟙 X₀ := by
    apply MorphismProperty.Over.Hom.ext
    exact (congrArg (fun k => s ≫ k) hg).trans hs
  refine ⟨F.obj.map r.op b, ?_⟩
  rw [NatTrans.naturality_apply, hb, ← G.obj.map_comp_apply, ← op_comp, hrg,
    op_id, G.obj.map_id, ConcreteCategory.id_apply]

end EtaleCohomology
