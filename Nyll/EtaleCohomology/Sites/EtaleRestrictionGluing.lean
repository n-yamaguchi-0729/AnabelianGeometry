/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.EtaleCohomology.Sites.EtaleRestriction
public import Nyll.EtaleCohomology.Sites.EtaleSlice
public import Mathlib.AlgebraicGeometry.Sites.Etale
public import Mathlib.CategoryTheory.Equivalence
public import Mathlib.CategoryTheory.Functor.FullyFaithful
public import Mathlib.CategoryTheory.Sites.CoversTop.Basic
public import Mathlib.CategoryTheory.Sites.LocalProperties
public import Mathlib.CategoryTheory.Sites.SheafHom
public import Mathlib.CategoryTheory.Whiskering

/-!
# Gluing morphisms of actual small étale sheaves

Restriction to an étale scheme is transported to the slice of the original
site through its existing equivalence. Compatible morphisms on a covering
family then glue using the ordinary sheaf of morphisms. The restriction
calculation retains the original local morphisms, and local isomorphisms
give a global isomorphism.
-/

@[expose] public section

noncomputable section

universe u v w

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite

namespace EtaleCohomology

private theorem inverseWhisker_unitConjugate
    {C : Type*} [Category C] {D : Type*} [Category D]
    {B : Type*} [Category B] (E : C ≌ D) (P Q : Cᵒᵖ ⥤ B)
    (f : E.inverse.op ⋙ P ⟶ E.inverse.op ⋙ Q) :
    Functor.whiskerLeft E.inverse.op
        (Functor.whiskerRight (NatTrans.op E.unitIso.inv) P ≫
          Functor.whiskerLeft E.functor.op f ≫
            Functor.whiskerRight (NatTrans.op E.unitIso.hom) Q) = f := by
  ext Y
  let d := E.counitIso.app Y.unop
  let P' := E.inverse.op ⋙ P
  let Q' := E.inverse.op ⋙ Q
  change P.map (E.unitIso.inv.app (E.inverse.obj Y.unop)).op ≫
      f.app (op (E.functor.obj (E.inverse.obj Y.unop))) ≫
        Q.map (E.unitIso.hom.app (E.inverse.obj Y.unop)).op = f.app Y
  rw [E.unitInv_app_inverse, E.unit_app_inverse]
  change P'.map d.hom.op ≫ f.app (op (E.functor.obj (E.inverse.obj Y.unop))) ≫
      Q'.map d.inv.op = f.app Y
  have hn := f.naturality d.hom.op
  calc
    _ = (P'.map d.hom.op ≫
        f.app (op (E.functor.obj (E.inverse.obj Y.unop)))) ≫ Q'.map d.inv.op :=
      (Category.assoc _ _ _).symm
    _ = (f.app Y ≫ Q'.map d.hom.op) ≫ Q'.map d.inv.op :=
      congrArg (fun k => k ≫ Q'.map d.inv.op) hn
    _ = f.app Y := by
      rw [Category.assoc, ← Q'.map_comp, ← op_comp, Iso.inv_hom_id,
        op_id]
      exact (congrArg (fun z : Q'.obj Y ⟶ Q'.obj Y => f.app Y ≫ z)
        (Q'.map_id Y)).trans (Category.comp_id (f.app Y))

variable {X : Scheme.{u}} {A : Type v} [Category.{w} A]
  {F G : Sheaf X.smallEtaleTopology A}

/-- A morphism between actual restrictions, regarded as a section of the
presheaf of morphisms on the slice of the original small étale site. -/
def etaleRestrictionHomToSlice (U : X.Etale)
    (f : (etaleRestriction U.hom A).obj F ⟶
      (etaleRestriction U.hom A).obj G) :
    (presheafHom F.obj G.obj).obj (op U) := by
  let E := etaleSliceEquiv U
  let P : (Over U)ᵒᵖ ⥤ A := (Over.forget U).op ⋙ F.obj
  let Q : (Over U)ᵒᵖ ⥤ A := (Over.forget U).op ⋙ G.obj
  exact Functor.whiskerRight (NatTrans.op E.unitIso.inv) P ≫
    Functor.whiskerLeft E.functor.op f.hom ≫
      Functor.whiskerRight (NatTrans.op E.unitIso.hom) Q

/-- Returning to the actual small site recovers the original local
morphism. The equivalence is used before any section calculation. -/
theorem etaleRestrictionHomToSlice_whisker (U : X.Etale)
    (f : (etaleRestriction U.hom A).obj F ⟶
      (etaleRestriction U.hom A).obj G) :
    Functor.whiskerLeft (etaleSliceEquiv U).inverse.op
      (etaleRestrictionHomToSlice U f) = f.hom := by
  let E := etaleSliceEquiv U
  let P : (Over U)ᵒᵖ ⥤ A := (Over.forget U).op ⋙ F.obj
  let Q : (Over U)ᵒᵖ ⥤ A := (Over.forget U).op ⋙ G.obj
  exact inverseWhisker_unitConjugate E P Q f.hom

/-- The slice component is the original restriction component transported
by the actual identity-on-source isomorphism in the slice equivalence. -/
theorem etaleRestrictionHomToSlice_app (U : X.Etale)
    (f : (etaleRestriction U.hom A).obj F ⟶
      (etaleRestriction U.hom A).obj G) (T : Over U) :
    (etaleRestrictionHomToSlice U f).app (op T) =
      F.obj.map ((etaleSliceEquiv U).unitIso.app T).inv.left.op ≫
        f.hom.app (op ((etaleSliceEquiv U).functor.obj T)) ≫
          G.obj.map ((etaleSliceEquiv U).unitIso.app T).hom.left.op := by
  rfl

/-- The passage to the slice does not identify distinct local morphisms. -/
theorem etaleRestrictionHomToSlice_injective (U : X.Etale) :
    Function.Injective (etaleRestrictionHomToSlice (F := F) (G := G) U) := by
  intro f g h
  apply (sheafToPresheaf U.left.smallEtaleTopology A).map_injective
  have hw := congrArg
    (Functor.whiskerLeft (etaleSliceEquiv U).inverse.op) h
  exact (etaleRestrictionHomToSlice_whisker U f).symm.trans
    (hw.trans (etaleRestrictionHomToSlice_whisker U g))

/-- Restricting a global morphism and then passing to the slice is ordinary
restriction of that same global natural transformation. -/
theorem etaleRestrictionHomToSlice_map (U : X.Etale) (f : F ⟶ G) :
    etaleRestrictionHomToSlice U ((etaleRestriction U.hom A).map f) =
      Functor.whiskerLeft (Over.forget U).op f.hom := by
  let W : ((Over U)ᵒᵖ ⥤ A) ⥤ (U.left.Etale)ᵒᵖ ⥤ A :=
    (Functor.whiskeringLeft (U.left.Etale)ᵒᵖ (Over U)ᵒᵖ A).obj
      (etaleSliceEquiv U).inverse.op
  apply W.map_injective
  exact etaleRestrictionHomToSlice_whisker U
    ((etaleRestriction U.hom A).map f)

/-- A local isomorphism remains an isomorphism on the slice of the
original small étale site. -/
theorem etaleRestrictionHomToSlice_isIso (U : X.Etale)
    (f : (etaleRestriction U.hom A).obj F ⟶
      (etaleRestriction U.hom A).obj G) [IsIso f] :
    IsIso (etaleRestrictionHomToSlice U f) := by
  let W : ((Over U)ᵒᵖ ⥤ A) ⥤ (U.left.Etale)ᵒᵖ ⥤ A :=
    (Functor.whiskeringLeft (U.left.Etale)ᵒᵖ (Over U)ᵒᵖ A).obj
      (etaleSliceEquiv U).inverse.op
  have hw : IsIso (W.map (etaleRestrictionHomToSlice U f)) := by
    change IsIso (Functor.whiskerLeft (etaleSliceEquiv U).inverse.op
      (etaleRestrictionHomToSlice U f))
    rw [etaleRestrictionHomToSlice_whisker]
    change IsIso ((sheafToPresheaf U.left.smallEtaleTopology A).map f)
    infer_instance
  exact isIso_of_fully_faithful W (etaleRestrictionHomToSlice U f)

/-- A jointly surjective family of actual étale schemes covers the
terminal object of the original small site. -/
theorem smallEtale_coversTop_of_jointly_surjective
    {ι : Type*} (U : ι → X.Etale)
    (hU : ∀ x : X, ∃ (i : ι) (y : (U i).left), (U i).hom y = x) :
    X.smallEtaleTopology.CoversTop U := by
  let T : X.Etale := Scheme.Etale.mk (𝟙 X)
  let hT : IsTerminal T := MorphismProperty.Over.mkIdTerminal
    (show MorphismProperty Scheme.{u} from @Etale) X
  let l : ∀ i, U i ⟶ T := fun i =>
    MorphismProperty.Over.homMk (U i).hom (Category.comp_id _)
  apply (X.smallEtaleTopology.coversTop_iff_of_isTerminal T hT (Y := U)).mpr
  have hc : Sieve.ofArrows U l ∈ X.smallEtaleTopology T := by
    rw [Scheme.ofArrows_mem_smallEtaleTopology_iff]
    ext x
    simp only [Set.mem_iUnion, Set.mem_range, Set.mem_univ, iff_true]
    exact hU x
  apply X.smallEtaleTopology.superset_covering (R := _) ?_ hc
  intro V f hf
  obtain ⟨i, g, rfl⟩ := (Sieve.mem_ofArrows_iff U l f).mp hf
  exact ⟨i, ⟨g⟩⟩

section Gluing

variable {ι : Type*} (U : ι → X.Etale)
  (hU : X.smallEtaleTopology.CoversTop U)
  (f : ∀ i, (etaleRestriction (U i).hom A).obj F ⟶
    (etaleRestriction (U i).hom A).obj G)

/-- The family of local morphisms, in the original site's sheaf of
morphisms. Its compatibility is an equality of the actual restrictions. -/
def etaleRestrictionHomFamily :
    Presheaf.FamilyOfElementsOnObjects (presheafHom F.obj G.obj) U :=
  fun i => etaleRestrictionHomToSlice (U i) (f i)

variable (hf : (etaleRestrictionHomFamily U f).IsCompatible)

/-- Glue compatible actual local sheaf morphisms. -/
def etaleGlueHom : F ⟶ G :=
  ⟨presheafHomSectionsEquiv F.obj G.obj
    (hf.section_ hU (G.property.hom F.obj))⟩

/-- On each original slice, the glued morphism has the prescribed local
value. This is the calculation supplied by the ordinary sheaf gluing. -/
theorem etaleGlueHom_slice (i : ι) :
    Functor.whiskerLeft (Over.forget (U i)).op
      (etaleGlueHom U hU f hf).hom =
        etaleRestrictionHomToSlice (U i) (f i) := by
  let s := hf.section_ hU (G.property.hom F.obj)
  have hs := congrArg
    (fun t : (presheafHom F.obj G.obj).sections => t.1 (op (U i)))
    ((presheafHomSectionsEquiv F.obj G.obj).symm_apply_apply s)
  exact hs.trans (hf.section_apply hU (G.property.hom F.obj) i)

/-- Restricting the glued morphism on the actual small site gives back
the specified morphism, with no change of source or target sheaf. -/
theorem etaleGlueHom_restrict (i : ι) :
    (etaleRestriction (U i).hom A).map (etaleGlueHom U hU f hf) = f i := by
  apply etaleRestrictionHomToSlice_injective (U i)
  rw [etaleRestrictionHomToSlice_map]
  exact etaleGlueHom_slice U hU f hf i

/-- A global morphism with these actual restrictions is the glued
morphism. -/
theorem etaleGlueHom_unique (g : F ⟶ G)
    (hg : ∀ i, (etaleRestriction (U i).hom A).map g = f i) :
    g = etaleGlueHom U hU f hf := by
  apply (sheafToPresheaf X.smallEtaleTopology A).map_injective
  apply (presheafHomSectionsEquiv F.obj G.obj).symm.injective
  apply hU.sections_ext ⟨presheafHom F.obj G.obj, G.property.hom F.obj⟩
  intro i
  change Functor.whiskerLeft (Over.forget (U i)).op g.hom =
    Functor.whiskerLeft (Over.forget (U i)).op
      (etaleGlueHom U hU f hf).hom
  have hmap : Functor.whiskerLeft (Over.forget (U i)).op g.hom =
      etaleRestrictionHomToSlice (U i)
        ((etaleRestriction (U i).hom A).map g) :=
    (etaleRestrictionHomToSlice_map (U i) g).symm
  have hlocal : etaleRestrictionHomToSlice (U i)
      ((etaleRestriction (U i).hom A).map g) =
        etaleRestrictionHomToSlice (U i) (f i) :=
    congrArg (etaleRestrictionHomToSlice (F := F) (G := G) (U i)) (hg i)
  exact hmap.trans (hlocal.trans (etaleGlueHom_slice U hU f hf i).symm)

end Gluing

/-- Compatible local isomorphisms on a covering family give an actual
global isomorphism. Local invertibility is checked on the original slices. -/
def etaleGlueIso {ι : Type*} (U : ι → X.Etale)
    (hU : X.smallEtaleTopology.CoversTop U)
    (e : ∀ i, (etaleRestriction (U i).hom A).obj F ≅
      (etaleRestriction (U i).hom A).obj G)
    (he : (etaleRestrictionHomFamily U (fun i => (e i).hom)).IsCompatible) :
    F ≅ G := by
  let f := etaleGlueHom U hU (fun i => (e i).hom) he
  have hf : IsIso f := by
    apply Sheaf.isIso_of_coversTop hU
    intro i
    rw [← ObjectProperty.isIso_hom_iff]
    change IsIso (Functor.whiskerLeft (Over.forget (U i)).op f.hom)
    rw [etaleGlueHom_slice U hU (fun j => (e j).hom) he i]
    exact etaleRestrictionHomToSlice_isIso (U i) (e i).hom
  exact asIso f

/-- The global isomorphism restricts to the prescribed original local
isomorphism on every chart. -/
theorem etaleGlueIso_hom_restrict {ι : Type*} (U : ι → X.Etale)
    (hU : X.smallEtaleTopology.CoversTop U)
    (e : ∀ i, (etaleRestriction (U i).hom A).obj F ≅
      (etaleRestriction (U i).hom A).obj G)
    (he : (etaleRestrictionHomFamily U (fun i => (e i).hom)).IsCompatible)
    (i : ι) :
    (etaleRestriction (U i).hom A).map (etaleGlueIso U hU e he).hom =
      (e i).hom :=
  etaleGlueHom_restrict U hU (fun j => (e j).hom) he i

end EtaleCohomology
