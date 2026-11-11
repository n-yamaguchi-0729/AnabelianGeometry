/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.EtaleCohomology.Classical.FreeAbelianCechSheaves
public import Nyll.EtaleCohomology.Classical.FreeAbelianYoneda
public import Nyll.EtaleCohomology.Sites.FiniteHenselianSections
public import Nyll.SchemeTheory.HomologicalAlgebra.CocycleCorrection
public import Mathlib.AlgebraicGeometry.Sites.AffineEtale
public import Mathlib.CategoryTheory.Abelian.Injective.Resolution
public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.HasExt
public import Mathlib.CategoryTheory.Sites.SheafCohomology.ExactSequences

/-!
# First sheaf cohomology from actual Čech primitives

The existing exact free Čech augmentation and cocycle-correction theorem
turn a primitive for the difference of a local lift into an actual global
lift. An injective presentation and the original cohomology connecting
map then kill native first cohomology. For a quasi-compact scheme the
existing affine étale section-lifting theorem supplies the cover.

The input is a primitive for an actual free Čech cocycle on affine
surjective covers. No cohomology vanishing or comparison is an input.
This file proves only the degree-one criterion.
-/

@[expose] public section

noncomputable section

universe u v

open AlgebraicGeometry CategoryTheory Limits Opposite

namespace EtaleCohomology

section Cover

variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
  [HasSheafify J AddCommGrpCat.{v}]

/-- Correcting the actual free Čech difference of a local section lift
produces a global section lift along the original coefficient map. -/
theorem exists_section_lift_of_freeCech_primitives
    (S : ShortComplex (Sheaf J AddCommGrpCat.{v})) (hS : S.ShortExact)
    {V W : C} (f : V ⟶ W) [HasPullback f f]
    (hf : Sieve.generate (Presieve.singleton f) ∈ J W)
    (hprimitive : ∀ z : (presheafToSheaf J AddCommGrpCat.{v}).obj
        (cechEdgeFunctor (yoneda.map f) ⋙ AddCommGrpCat.free) ⟶ S.X₁,
      (presheafToSheaf J AddCommGrpCat.{v}).map
          (freeCechTriangleBoundaryNat (yoneda.map f)) ≫ z = 0 →
        ∃ b : (freeAbelianSheafYoneda J).obj V ⟶ S.X₁,
          (presheafToSheaf J AddCommGrpCat.{v}).map
            (freeCechEdgeBoundaryNat (yoneda.map f)) ≫ b = z)
    (a : S.X₃.obj.obj (op W)) (b : S.X₂.obj.obj (op V))
    (hb : S.g.hom.app (op V) b = S.X₃.obj.map f.op a) :
    ∃ t : S.X₂.obj.obj (op W), S.g.hom.app (op W) t = a := by
  let Q := presheafToSheaf J AddCommGrpCat.{v}
  let K := (freeCechAugmentationComplex (yoneda.map f)).map Q
  let d := Q.map (freeCechTriangleBoundaryNat (yoneda.map f))
  have hK : K.Exact := freeCechAugmentationComplex_sheaf_exact J (yoneda.map f)
  have : Epi K.g := freeAbelianSheafYoneda_map_epi_of_cover J f hf
  have hd : d ≫ K.f = 0 :=
    ((freeCechRelationComplex (yoneda.map f)).map Q).zero
  let a' := (freeAbelianSheafYonedaHomEquiv J W S.X₃).symm a
  let b' := (freeAbelianSheafYonedaHomEquiv J V S.X₂).symm b
  have hb' : b' ≫ S.g = K.g ≫ a' := by
    apply (freeAbelianSheafYonedaHomEquiv J V S.X₃).injective
    change freeAbelianSheafYonedaHomEquiv J V S.X₃ (b' ≫ S.g) =
      freeAbelianSheafYonedaHomEquiv J V S.X₃
        ((freeAbelianSheafYoneda J).map f ≫ a')
    rw [freeAbelianSheafYonedaHomEquiv_postcomp,
      freeAbelianSheafYonedaHomEquiv_precomp]
    change S.g.hom.app (op V)
        (freeAbelianSheafYonedaHomEquiv J V S.X₂
          ((freeAbelianSheafYonedaHomEquiv J V S.X₂).symm b)) =
      S.X₃.obj.map f.op
        (freeAbelianSheafYonedaHomEquiv J W S.X₃
          ((freeAbelianSheafYonedaHomEquiv J W S.X₃).symm a))
    rw [Equiv.apply_symm_apply, Equiv.apply_symm_apply]
    exact hb
  obtain ⟨t, ht⟩ := ShortComplex.exists_lift_of_cocycle_primitives
    K S hK hS d hd hprimitive a' b' hb'
  let t' : (freeAbelianSheafYoneda J).obj W ⟶ S.X₂ := t
  have ht' : t' ≫ S.g = a' := ht
  refine ⟨freeAbelianSheafYonedaHomEquiv J W S.X₂ t', ?_⟩
  exact (freeAbelianSheafYonedaHomEquiv_postcomp J W t' S.g).symm.trans
    ((congrArg (freeAbelianSheafYonedaHomEquiv J W S.X₃) ht').trans
      ((freeAbelianSheafYonedaHomEquiv J W S.X₃).apply_symm_apply a))

end Cover

/-- Actual first étale sheaf cohomology on a quasi-compact scheme vanishes
when the actual free Čech cocycles on affine surjective covers have primitives.
The local lift and the injective presentation are constructed, not assumed. -/
theorem etaleSheafH1_eq_zero_of_affine_freeCech_primitives
    (X : Scheme.{u}) [CompactSpace X]
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u})
    (hprimitive : ∀ (V : X.Etale) (f : V ⟶ Scheme.Etale.mk (𝟙 X)),
      IsAffine V.left → Surjective f.left →
      ∀ z : (presheafToSheaf X.smallEtaleTopology AddCommGrpCat.{u}).obj
          (cechEdgeFunctor (yoneda.map f) ⋙ AddCommGrpCat.free) ⟶ F,
        (presheafToSheaf X.smallEtaleTopology AddCommGrpCat.{u}).map
            (freeCechTriangleBoundaryNat (yoneda.map f)) ≫ z = 0 →
          ∃ b : (freeAbelianSheafYoneda X.smallEtaleTopology).obj V ⟶ F,
            (presheafToSheaf X.smallEtaleTopology AddCommGrpCat.{u}).map
              (freeCechEdgeBoundaryNat (yoneda.map f)) ≫ b = z)
    (c : Sheaf.H.{u} F 1) : c = 0 := by
  let I : InjectivePresentation F := Classical.arbitrary _
  let S := I.shortComplex
  have hS : S.ShortExact := I.shortExact_shortComplex
  have : Injective S.X₂ := I.injective
  have : Epi S.g := hS.epi_g
  let U : X.Etale := Scheme.Etale.mk (𝟙 X)
  let hU : IsTerminal U := MorphismProperty.Over.mkIdTerminal
    (show MorphismProperty Scheme.{u} from @Etale) X
  have : QuasiCompact (terminal.from U.left) :=
    (AlgebraicGeometry.compactSpace_iff_quasiCompact X).mp inferInstance
  obtain ⟨a, ha⟩ := Sheaf.H.longSequence_exact₁ hS c
    (Subsingleton.elim _ _) (n₀ := 0) rfl
  let a₀ := Sheaf.H.equiv₀ S.X₃ hU a
  obtain ⟨V, f, hV, hsurj, b, hb⟩ :=
    exists_affine_etale_cover_section_lift S.g U a₀
  have hf : Sieve.generate (Presieve.singleton f) ∈ X.smallEtaleTopology U := by
    have hcover : Sieve.ofArrows (fun _ : PUnit.{u + 1} => V) (fun _ => f) ∈
        X.smallEtaleTopology U := by
      apply (Scheme.ofArrows_mem_smallEtaleTopology_iff
        (fun _ : PUnit.{u + 1} => f)).mpr
      apply Set.eq_univ_of_forall
      intro x
      obtain ⟨y, hy⟩ := hsurj.surj x
      exact Set.mem_iUnion.mpr ⟨PUnit.unit, y, hy⟩
    change Sieve.generate
      (Presieve.ofArrows (fun _ : PUnit.{u + 1} => V) (fun _ => f)) ∈
      X.smallEtaleTopology U at hcover
    simpa only [Presieve.ofArrows_pUnit] using hcover
  obtain ⟨t, ht⟩ := exists_section_lift_of_freeCech_primitives
    X.smallEtaleTopology S hS f hf (hprimitive V f hV hsurj) a₀ b hb
  let t₀ := (Sheaf.H.equiv₀ S.X₂ hU).symm t
  have hmap : Sheaf.H.map S.g 0 t₀ = a := by
    apply (Sheaf.H.equiv₀ S.X₃ hU).injective
    rw [← Sheaf.H.equiv₀_naturality]
    change S.g.hom.app (op U)
      (Sheaf.H.equiv₀ S.X₂ hU ((Sheaf.H.equiv₀ S.X₂ hU).symm t)) = _
    rw [AddEquiv.apply_symm_apply]
    exact ht
  have hz : AddCommGrpCat.ofHom (Sheaf.H.map S.g 0) ≫
      AddCommGrpCat.ofHom (Sheaf.H.δ hS 0 1 rfl) = 0 :=
    (Sheaf.H.longSequence_exact hS 0 1 rfl).zero 1
  have hzero := ConcreteCategory.congr_hom hz t₀
  change Sheaf.H.δ hS 0 1 rfl (Sheaf.H.map S.g 0 t₀) = 0 at hzero
  rw [hmap, ha] at hzero
  exact hzero

end EtaleCohomology
