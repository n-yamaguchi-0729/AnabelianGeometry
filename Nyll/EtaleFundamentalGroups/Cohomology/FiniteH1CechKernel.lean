/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.EtaleCohomology.Classical.CupAbelianCechResolution
public import Nyll.EtaleCohomology.Classical.CupTwoStepExtension
public import Nyll.EtaleCohomology.Classical.FreeAbelianCechOverlap
public import Nyll.EtaleCohomology.Classical.FreeAbelianYoneda
public import Nyll.EtaleCohomology.Constructible.FiniteEtaleSheaf
public import Nyll.EtaleFundamentalGroups.Cohomology.ExtensionFiberCechLift
public import Nyll.EtaleFundamentalGroups.Cohomology.ExtensionFiberSectionDifference
public import Nyll.EtaleFundamentalGroups.Cohomology.FiniteH1CechDifference
public import Nyll.EtaleFundamentalGroups.Cohomology.FiniteH1CechLift
public import Nyll.EtaleFundamentalGroups.Cohomology.H1Character
public import Nyll.EtaleFundamentalGroups.Cohomology.H1FiniteCover
public import Mathlib.Algebra.Category.Grp.EpiMono
public import Mathlib.CategoryTheory.Sites.EpiMono

/-!
# Original H¹ on the first kernel of a specified finite cover

The actual extension section on a cover defines a morphism from the
original augmentation kernel. Its connecting class is the original H¹
class. On every connected finite overlap its value is the original
character, computed on the same two geometric covering points.
-/

@[expose] public section

noncomputable section

universe u

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian
open CategoryTheory.PreGaloisCategory EtaleCohomology Opposite
open scoped FintypeCatDiscrete

namespace EtaleFundamentalGroups.Cohomology

/-- The original character supplies a genuine first-kernel representative
on the specified cover, including its exact coefficients on all connected
finite overlaps. -/
theorem exists_h1_cechKernel_of_stabilizer
    {X : Scheme.{u}} [ConnectedSpace X]
    (A : AddCommGrpCat.{u}) [Finite A]
    {Ω : Type u} [Field Ω] [IsSepClosed Ω] (ξ : Spec (.of Ω) ⟶ X)
    (V : FiniteEtale X) [IsConnected V] (z : (FiniteEtale.fiber ξ).obj V)
    {T : X.Etale} (hT : IsTerminal T)
    (q : (finiteEtaleToEtale X).obj V ⟶ T)
    (hq : Sieve.generate (Presieve.singleton q) ∈ X.smallEtaleTopology T)
    (a : Sheaf.H.{u} ((constantSheaf X.smallEtaleTopology AddCommGrpCat.{u}).obj A) 1) :
    let : TopologicalSpace (Multiplicative A) := ⊥
    (∀ g : Aut (FiniteEtale.fiber ξ), g • z = z → h1Character A ξ a g = 1) →
    let J := X.smallEtaleTopology
    let C := (constantSheaf J AddCommGrpCat.{u}).obj A
    let S := abelianCechAugmentationSequence J hT q
    let hS := abelianCechAugmentationSequence_shortExact J hT q hq
    ∃ d : S.X₁ ⟶ C,
      hS.extClass.comp (Ext.mk₀ d) (add_zero 1) = a ∧
      ∀ (W : FiniteEtale X) [IsConnected W] (m₀ m₁ : W ⟶ V)
        (w : (FiniteEtale.fiber ξ).obj W) (g : Aut (FiniteEtale.fiber ξ)),
        (FiniteEtale.fiber ξ).map m₁ w = g • (FiniteEtale.fiber ξ).map m₀ w →
        let x := (finiteEtaleToEtale X).map m₀
        let y := (finiteEtaleToEtale X).map m₁
        let l := pullback.lift x y (hT.hom_ext (x ≫ q) (y ≫ q))
        let edge := (freeAbelianSheafYoneda J).map l ≫
          (freeCechEdgeSheafIso J q).inv ≫ abelianCechFirstRelationMap J hT q
        freeAbelianSheafYonedaHomEquiv J ((finiteEtaleToEtale X).obj W) C (edge ≫ d) =
          (toSheafify J ((Functor.const X.Etaleᵒᵖ).obj A)).app _
            (h1Character A ξ a g).toAdd := by
  intro coefficientTopology hstab J C S hS
  obtain ⟨E, i, p, hip, hs, f, ha⟩ :=
    exists_h1_extensionFiber_map_of_stabilizer A ξ V z a hstab
  let Q := ShortComplex.mk i p hip
  let s := f.hom.app (op ((finiteEtaleToEtale X).obj V)) (𝟙 _)
  let b := (freeAbelianSheafYonedaHomEquiv J ((finiteEtaleToEtale X).obj V) E).symm s.val
  have hb : b ≫ p = S.g := by
    apply (freeAbelianSheafYonedaHomEquiv J ((finiteEtaleToEtale X).obj V) _).injective
    rw [freeAbelianSheafYonedaHomEquiv_postcomp]
    change p.hom.app _
      (freeAbelianSheafYonedaHomEquiv J ((finiteEtaleToEtale X).obj V) E b) = _
    rw [Equiv.apply_symm_apply, abelianCechUnitAugmentation_section]
    exact s.property
  let d := CupTwoStepExtension.difference S Q hs (𝟙 _) b
    (hb.trans (Category.comp_id S.g).symm)
  have hd : d ≫ i = S.f ≫ b :=
    CupTwoStepExtension.difference_comp S Q hs (𝟙 _) b _
  refine ⟨d, ?_, ?_⟩
  · exact (show hS.extClass.comp (Ext.mk₀ d) (add_zero 1) = hs.extClass by
      simpa only [Ext.mk₀_id_comp] using
        CupTwoStepExtension.extClass_difference S Q hS hs (𝟙 _) b
          (hb.trans (Category.comp_id S.g).symm)).trans ha
  · intro W hW m₀ m₁ w g hg x y l edge
    have hboundary : edge ≫ S.f =
        (freeAbelianSheafYoneda J).map y - (freeAbelianSheafYoneda J).map x := by
      change ((freeAbelianSheafYoneda J).map l ≫
        (freeCechEdgeSheafIso J q).inv ≫ abelianCechFirstRelationMap J hT q) ≫
          kernel.ι (abelianCechUnitAugmentation J hT q) = _
      rw [Category.assoc, Category.assoc, abelianCechFirstRelationMap_comp,
        freeCechEdgeSheafIso_boundary, Preadditive.comp_sub,
        ← Functor.map_comp, ← Functor.map_comp, pullback.lift_snd, pullback.lift_fst]
    have hsection (m : W ⟶ V) :
        E.obj.map ((finiteEtaleToEtale X).map m).op s.val =
          (f.hom.app (op ((finiteEtaleToEtale X).obj W))
            ((finiteEtaleToEtale X).map m)).val := by
      have hn := CategoryTheory.types_congr_hom
        (f.hom.naturality ((finiteEtaleToEtale X).map m).op)
        (𝟙 ((finiteEtaleToEtale X).obj V))
      exact congrArg Subtype.val (by
        simpa only [Category.comp_id] using hn.symm)
    have hdiff := extensionFiberSectionDifference_eq_h1Character
      A ξ i p hip hs f m₀ m₁ w g hg
    rw [ha] at hdiff
    have hincl := extensionFiberSectionDifference_inclusion Q
      (integerUnitSection X) hs (op ((finiteEtaleToEtale X).obj W))
      (f.hom.app _ x) (f.hom.app _ y)
    rw [hdiff] at hincl
    have : Mono i := hs.mono_f
    apply (AddCommGrpCat.mono_iff_injective (i.hom.app _)).mp inferInstance
    rw [← freeAbelianSheafYonedaHomEquiv_postcomp, Category.assoc, hd,
      ← Category.assoc, hboundary, Preadditive.sub_comp]
    change freeAbelianSheafYonedaHomAddEquiv J ((finiteEtaleToEtale X).obj W) E
      ((freeAbelianSheafYoneda J).map y ≫ b -
        (freeAbelianSheafYoneda J).map x ≫ b) = _
    rw [map_sub]
    change freeAbelianSheafYonedaHomEquiv J ((finiteEtaleToEtale X).obj W) E
        ((freeAbelianSheafYoneda J).map y ≫ b) -
      freeAbelianSheafYonedaHomEquiv J ((finiteEtaleToEtale X).obj W) E
        ((freeAbelianSheafYoneda J).map x ≫ b) = _
    rw [freeAbelianSheafYonedaHomEquiv_precomp,
      freeAbelianSheafYonedaHomEquiv_precomp, Equiv.apply_symm_apply,
      hsection m₁, hsection m₀]
    exact hincl.symm

end EtaleFundamentalGroups.Cohomology
