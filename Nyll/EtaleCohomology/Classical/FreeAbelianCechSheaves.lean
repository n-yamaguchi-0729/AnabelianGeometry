/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.EtaleCohomology.Classical.FreeAbelianCechRelations
public import Mathlib.Algebra.Category.Grp.Adjunctions
public import Mathlib.Algebra.Homology.ShortComplex.Ab
public import Mathlib.CategoryTheory.Abelian.FunctorCategory
public import Mathlib.CategoryTheory.Sites.Abelian

/-!
# Exact free abelian Cech relations as sheaves

The pointwise contraction of free abelian edge cycles gives an exact
complex of presheaves. Exact sheafification preserves this complex.
Consequently Cech cocycles with values in an injective abelian sheaf
have primitives, with no assumption about Galois-cohomology comparison.
-/

@[expose] public section

noncomputable section

universe v u w
open CategoryTheory Limits Opposite

namespace EtaleCohomology

variable {C : Type u} [Category.{v} C]
variable {P Q : C ⥤ Type w} (η : P ⟶ Q)

/-- The presheaf of pairs with equal image under a presheaf morphism. -/
def cechEdgeFunctor : C ⥤ Type w where
  obj V := CechEdge (η.app V)
  map {V W} g := ↾fun p =>
    ⟨P.map g p.first, P.map g p.second, by
      exact (ConcreteCategory.congr_hom (η.naturality g) p.first).trans
        ((congrArg (Q.map g) p.same).trans
          (ConcreteCategory.congr_hom (η.naturality g) p.second).symm)⟩
  map_id V := by
    ext p
    · exact ConcreteCategory.congr_hom (P.map_id V) p.first
    · exact ConcreteCategory.congr_hom (P.map_id V) p.second
  map_comp g h := by
    ext p
    · exact ConcreteCategory.congr_hom (P.map_comp g h) p.first
    · exact ConcreteCategory.congr_hom (P.map_comp g h) p.second

/-- The presheaf of triples lying in a single fiber. -/
def cechTriangleFunctor : C ⥤ Type w where
  obj V := CechTriangle (η.app V)
  map {V W} g := ↾fun t =>
    ⟨P.map g t.first, P.map g t.second, P.map g t.third, by
      exact (ConcreteCategory.congr_hom (η.naturality g) t.first).trans
        ((congrArg (Q.map g) t.same₁).trans
          (ConcreteCategory.congr_hom (η.naturality g) t.second).symm), by
      exact (ConcreteCategory.congr_hom (η.naturality g) t.second).trans
        ((congrArg (Q.map g) t.same₂).trans
          (ConcreteCategory.congr_hom (η.naturality g) t.third).symm)⟩
  map_id V := by
    ext t
    · exact ConcreteCategory.congr_hom (P.map_id V) t.first
    · exact ConcreteCategory.congr_hom (P.map_id V) t.second
    · exact ConcreteCategory.congr_hom (P.map_id V) t.third
  map_comp g h := by
    ext t
    · exact ConcreteCategory.congr_hom (P.map_comp g h) t.first
    · exact ConcreteCategory.congr_hom (P.map_comp g h) t.second
    · exact ConcreteCategory.congr_hom (P.map_comp g h) t.third

/-- The natural edge boundary on free abelian presheaves. -/
def freeCechEdgeBoundaryNat :
    cechEdgeFunctor η ⋙ AddCommGrpCat.free ⟶ P ⋙ AddCommGrpCat.free where
  app V := AddCommGrpCat.ofHom (freeCechEdgeBoundary (η.app V))
  naturality {V W} g := by
    apply AddCommGrpCat.hom_ext
    apply FreeAbelianGroup.lift_ext
    intro p
    change freeCechEdgeBoundary (η.app W)
        (FreeAbelianGroup.map ((cechEdgeFunctor η).map g) (FreeAbelianGroup.of p)) =
      FreeAbelianGroup.map (P.map g)
        (freeCechEdgeBoundary (η.app V) (FreeAbelianGroup.of p))
    simp only [FreeAbelianGroup.map_of_apply, freeCechEdgeBoundary]
    rfl

/-- The natural triangle boundary on free abelian presheaves. -/
def freeCechTriangleBoundaryNat :
    cechTriangleFunctor η ⋙ AddCommGrpCat.free ⟶
      cechEdgeFunctor η ⋙ AddCommGrpCat.free where
  app V := AddCommGrpCat.ofHom (freeCechTriangleBoundary (η.app V))
  naturality {V W} g := by
    apply AddCommGrpCat.hom_ext
    apply FreeAbelianGroup.lift_ext
    intro t
    change freeCechTriangleBoundary (η.app W)
        (FreeAbelianGroup.map ((cechTriangleFunctor η).map g) (FreeAbelianGroup.of t)) =
      FreeAbelianGroup.map ((cechEdgeFunctor η).map g)
        (freeCechTriangleBoundary (η.app V) (FreeAbelianGroup.of t))
    simp only [FreeAbelianGroup.map_of_apply, freeCechTriangleBoundary]
    rfl

/-- The actual first positive-degree free abelian Cech complex. -/
def freeCechRelationComplex : ShortComplex (C ⥤ AddCommGrpCat.{w}) :=
  ShortComplex.mk (freeCechTriangleBoundaryNat η) (freeCechEdgeBoundaryNat η) (by
    ext V c
    exact freeCechEdgeBoundary_triangle (η.app V) c)

/-- Pointwise exactness of the free relation complex, before sheafification. -/
theorem freeCechRelationComplex_exact : (freeCechRelationComplex η).Exact := by
  let S : ShortComplex (C ⥤ AddCommGrpCat.{w}) := freeCechRelationComplex η
  have hV (V : C) : (S.map ((evaluation C AddCommGrpCat.{w}).obj V)).Exact := by
    rw [ShortComplex.ab_exact_iff]
    intro c hc
    exact exists_freeCechTriangle_primitive (η.app V) c hc
  rw [S.exact_iff_iCycles_pOpcycles_zero]
  apply NatTrans.ext
  funext V
  exact (hV V).comp_eq_zero
    (congrArg (fun k => k.app V) S.iCycles_g)
    (congrArg (fun k => k.app V) S.f_pOpcycles)

/-- The actual augmentation from free vertices to free images. -/
def freeCechAugmentationComplex : ShortComplex (C ⥤ AddCommGrpCat.{w}) :=
  ShortComplex.mk (freeCechEdgeBoundaryNat η)
    (Functor.whiskerRight η AddCommGrpCat.free) (by
      ext V c
      exact freeCechEdgeBoundary_augmentation (η.app V) c)

/-- The kernel of the free augmentation is generated by edge boundaries,
objectwise and naturally in the presheaf variable. -/
theorem freeCechAugmentationComplex_exact :
    (freeCechAugmentationComplex η).Exact := by
  let S := freeCechAugmentationComplex η
  have hV (V : C) : (S.map ((evaluation C AddCommGrpCat.{w}).obj V)).Exact := by
    rw [ShortComplex.ab_exact_iff]
    intro c hc
    exact exists_freeCechEdge_primitive (η.app V) c hc
  rw [S.exact_iff_iCycles_pOpcycles_zero]
  apply NatTrans.ext
  funext V
  exact (hV V).comp_eq_zero
    (congrArg (fun k => k.app V) S.iCycles_g)
    (congrArg (fun k => k.app V) S.f_pOpcycles)

variable {D : Type u} [Category.{v} D] (J : GrothendieckTopology D)
  [HasSheafify J AddCommGrpCat.{w}]
  {R T : Dᵒᵖ ⥤ Type w} (ρ : R ⟶ T)

/-- Exactness survives actual abelian sheafification. -/
theorem freeCechRelationComplex_sheaf_exact :
    ((freeCechRelationComplex ρ).map (presheafToSheaf J AddCommGrpCat.{w})).Exact :=
  (freeCechRelationComplex_exact ρ).map _

/-- Every cocycle on the actual free Cech relations with injective
coefficients has a primitive. This uses proved exactness, not a
comparison theorem included as an assumption. -/
theorem exists_injective_freeCech_primitive
    (I : Sheaf J AddCommGrpCat.{w}) [Injective I]
    (z : (presheafToSheaf J AddCommGrpCat.{w}).obj
      (cechEdgeFunctor ρ ⋙ AddCommGrpCat.free) ⟶ I)
    (hz : (presheafToSheaf J AddCommGrpCat.{w}).map
      (freeCechTriangleBoundaryNat ρ) ≫ z = 0) :
    ∃ b : (presheafToSheaf J AddCommGrpCat.{w}).obj
        (R ⋙ AddCommGrpCat.free) ⟶ I,
      (presheafToSheaf J AddCommGrpCat.{w}).map
        (freeCechEdgeBoundaryNat ρ) ≫ b = z :=
  ⟨(freeCechRelationComplex_sheaf_exact J ρ).descToInjective z hz,
    (freeCechRelationComplex_sheaf_exact J ρ).comp_descToInjective z hz⟩

/-- The actual sheafified augmentation is exact at its vertex term. -/
theorem freeCechAugmentationComplex_sheaf_exact :
    ((freeCechAugmentationComplex ρ).map
      (presheafToSheaf J AddCommGrpCat.{w})).Exact :=
  (freeCechAugmentationComplex_exact ρ).map _

end EtaleCohomology

