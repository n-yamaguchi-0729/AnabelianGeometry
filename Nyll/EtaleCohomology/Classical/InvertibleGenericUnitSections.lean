/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.AlgebraicCurves.Geometry.Sheaves.Invertible.InvertibleRationalFrames
public import Nyll.EtaleCohomology.Classical.InvertibleGenericUnitLocalSections
public import Nyll.EtaleCohomology.Classical.MultiplicativeGroupPushforward
public import Nyll.EtaleCohomology.Sites.ZariskiGlobalSections
public import Nyll.EtaleCohomology.Sites.ZariskiRestriction
public import Nyll.SchemeTheory.Modules.Frames.Frames
public import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
public import Mathlib.Topology.Sheaves.SheafCondition.UniqueGluing

/-!
# Native generic-unit sections of actual invertible modules

The actual local-frame sections glue in the original generic-unit
quotient. Their native H⁰ class is characterized by every genuine
local frame. The chosen rational realization is retained in H⁰;
the subsequent original boundary removes its global rational ambiguity.
-/

@[expose] public section

noncomputable section

universe u

open AlgebraicGeometry CategoryTheory Limits Opposite TopologicalSpace
open Scheme.Modules

namespace EtaleCohomology

variable {X : Scheme.{u}} [IsIntegral X] {M : X.Modules}
  (hM : Scheme.Modules.IsInvertible M)

/-- A chosen local frame chart containing the given point. -/
def invertibleFrameChart (x : X) :
    Σ U : X.Opens, {s : Γ(M, U) // x ∈ U ∧ IsFrameOn s U} := by
  let U := Classical.choose (hM.exists_frameSection x)
  have hU : ∃ s : Γ(M, U), x ∈ U ∧ IsFrameOn s U :=
    Classical.choose_spec (hM.exists_frameSection x)
  exact ⟨U, Classical.choose hU, Classical.choose_spec hU⟩

/-- The generic-unit quotient section of the chosen local frame chart. -/
def invertibleFrameChartSection (x : X) :
    (etaleGenericUnitQuotient X).obj.obj
      (op ((zariskiToEtale X).obj (invertibleFrameChart hM x).1)) := by
  let e := invertibleFrameChart hM x
  have : Nonempty e.1 := ⟨⟨x, e.2.property.1⟩⟩
  exact invertibleFrameGenericUnitQuotient hM e.1 e.2.val e.2.property.2

/-- The chosen frame sections agree on their pairwise overlaps. -/
theorem invertibleFrameChartSections_compatible :
    TopCat.Presheaf.IsCompatible
      ((etaleZariskiRestriction X AddCommGrpCat.{u}).obj
        (etaleGenericUnitQuotient X)).obj
      (fun x : X => (invertibleFrameChart hM x).1)
      (invertibleFrameChartSection hM) := by
  intro x y
  let e := invertibleFrameChart hM x
  let d := invertibleFrameChart hM y
  have : Nonempty e.1 := ⟨⟨x, e.2.property.1⟩⟩
  have : Nonempty d.1 := ⟨⟨y, d.2.property.1⟩⟩
  exact invertibleFrames_genericUnit_overlap hM e.1 d.1
    e.2.val d.2.val e.2.property.2 d.2.property.2

/-- The glued quotient section with its restrictions to the chosen frames. -/
def invertibleModuleGenericUnitGluing :
    {s : ((etaleZariskiRestriction X AddCommGrpCat.{u}).obj
        (etaleGenericUnitQuotient X)).obj.obj (op (⊤ : X.Opens)) //
      ∀ x : X, ((etaleZariskiRestriction X AddCommGrpCat.{u}).obj
        (etaleGenericUnitQuotient X)).obj.map
          (homOfLE (show (invertibleFrameChart hM x).1 ≤ ⊤ from le_top)).op s =
            invertibleFrameChartSection hM x} := by
  let F : TopCat.Sheaf AddCommGrpCat.{u} X :=
    (etaleZariskiRestriction X AddCommGrpCat.{u}).obj (etaleGenericUnitQuotient X)
  let U : X → X.Opens := fun x => (invertibleFrameChart hM x).1
  have hcover : (⊤ : X.Opens) ≤ iSup U := by
    intro x hx
    exact Opens.mem_iSup.mpr ⟨x, (invertibleFrameChart hM x).2.property.1⟩
  let h := F.existsUnique_gluing' U ⊤ (fun _ => homOfLE le_top) hcover
    (invertibleFrameChartSection hM) (invertibleFrameChartSections_compatible hM)
  exact ⟨Classical.choose h, (Classical.choose_spec h).1⟩

/-- The actual global quotient section of the original rational
realization of an invertible module. -/
def invertibleModuleGenericUnitZariskiSection :
    ((etaleZariskiRestriction X AddCommGrpCat.{u}).obj
      (etaleGenericUnitQuotient X)).obj.obj (op (⊤ : X.Opens)) :=
  (invertibleModuleGenericUnitGluing hM).val

/-- Every actual local frame computes the original glued section,
independently of the trivializing cover chosen for the construction. -/
theorem invertibleModuleGenericUnitZariskiSection_restrict
    (U : X.Opens) [Nonempty U] (s : Γ(M, U)) (hs : IsFrameOn s U) :
    ((etaleZariskiRestriction X AddCommGrpCat.{u}).obj
      (etaleGenericUnitQuotient X)).obj.map (homOfLE (show U ≤ ⊤ from le_top)).op
        (invertibleModuleGenericUnitZariskiSection hM) =
      invertibleFrameGenericUnitQuotient hM U s hs := by
  let F : TopCat.Sheaf AddCommGrpCat.{u} X :=
    (etaleZariskiRestriction X AddCommGrpCat.{u}).obj (etaleGenericUnitQuotient X)
  apply TopCat.Presheaf.IsSheaf.section_ext F.property
  intro x hx
  let e := invertibleFrameChart hM x
  have : Nonempty e.1 := ⟨⟨x, e.2.property.1⟩⟩
  refine ⟨U ⊓ e.1, inf_le_left, ⟨hx, e.2.property.1⟩, ?_⟩
  have he : F.obj.map (homOfLE (show e.1 ≤ ⊤ from le_top)).op
      (invertibleModuleGenericUnitZariskiSection hM) =
        invertibleFrameGenericUnitQuotient hM e.1 e.2.val e.2.property.2 :=
    (invertibleModuleGenericUnitGluing hM).property x
  have hover := invertibleFrames_genericUnit_overlap hM U e.1
    s e.2.val hs e.2.property.2
  calc
    F.obj.map (homOfLE (show U ⊓ e.1 ≤ U from inf_le_left)).op
        (F.obj.map (homOfLE (show U ≤ ⊤ from le_top)).op
          (invertibleModuleGenericUnitZariskiSection hM)) =
      F.obj.map (Opens.infLERight U e.1).op
        (F.obj.map (homOfLE (show e.1 ≤ ⊤ from le_top)).op
          (invertibleModuleGenericUnitZariskiSection hM)) := by
            have hthin :
                (homOfLE (show U ≤ ⊤ from le_top)).op ≫
                    (homOfLE (show U ⊓ e.1 ≤ U from inf_le_left)).op =
                  (homOfLE (show e.1 ≤ ⊤ from le_top)).op ≫
                    (Opens.infLERight U e.1).op := Subsingleton.elim _ _
            simpa only [Functor.map_comp, ConcreteCategory.comp_apply] using
              ConcreteCategory.congr_hom (congrArg F.obj.map hthin)
                (invertibleModuleGenericUnitZariskiSection hM)
    _ = F.obj.map (Opens.infLERight U e.1).op
        (invertibleFrameGenericUnitQuotient hM e.1 e.2.val e.2.property.2) :=
      congrArg (F.obj.map (Opens.infLERight U e.1).op) he
    _ = F.obj.map (homOfLE (show U ⊓ e.1 ≤ U from inf_le_left)).op
        (invertibleFrameGenericUnitQuotient hM U s hs) := hover.symm

/-- The same glued section on the original small étale site's actual
terminal object. -/
def invertibleModuleGenericUnitSection :
    (etaleGenericUnitQuotient X).obj.obj (op (Scheme.Etale.mk (𝟙 X))) :=
  (etaleZariskiGlobalSectionsIso X AddCommGrpCat.{u}
    (etaleGenericUnitQuotient X)).hom (invertibleModuleGenericUnitZariskiSection hM)

/-- The native H⁰ class in the original generic-unit quotient. -/
def invertibleModuleGenericUnitH0 : Sheaf.H.{u} (etaleGenericUnitQuotient X) 0 :=
  (Sheaf.H.equiv₀.{u} (etaleGenericUnitQuotient X)
    (MorphismProperty.Over.mkIdTerminal
      (show MorphismProperty Scheme.{u} from @Etale) X)).symm
        (invertibleModuleGenericUnitSection hM)

/-- The actual H⁰ representative restricts to the literal rational
value of every actual local frame. -/
theorem invertibleModuleGenericUnitH0_section
    (U : X.Opens) [Nonempty U] (s : Γ(M, U)) (hs : IsFrameOn s U) :
    let hT := MorphismProperty.Over.mkIdTerminal
      (show MorphismProperty Scheme.{u} from @Etale) X
    (etaleGenericUnitQuotient X).obj.map
      (hT.from ((zariskiToEtale X).obj U)).op
        (Sheaf.H.equiv₀.{u} (etaleGenericUnitQuotient X) hT
          (invertibleModuleGenericUnitH0 hM)) =
      invertibleFrameGenericUnitQuotient hM U s hs := by
  intro hT
  rw [invertibleModuleGenericUnitH0, AddEquiv.apply_symm_apply]
  let e := etaleZariskiGlobalSectionsIso X AddCommGrpCat.{u} (etaleGenericUnitQuotient X)
  let a := invertibleModuleGenericUnitZariskiSection hM
  let j : (zariskiToEtale X).obj U ⟶ Scheme.Etale.mk (𝟙 X) :=
    MorphismProperty.Over.homMk
      (P := show MorphismProperty Scheme.{u} from @Etale) (Q := ⊤)
      U.ι (Category.comp_id U.ι)
  have ht : hT.from ((zariskiToEtale X).obj U) = j := hT.hom_ext _ _
  have hr := ConcreteCategory.congr_hom
    (etaleZariskiGlobalSectionsIso_inv_restrict X AddCommGrpCat.{u}
      (etaleGenericUnitQuotient X) U) (e.hom a)
  change ((etaleZariskiRestriction X AddCommGrpCat.{u}).obj
      (etaleGenericUnitQuotient X)).obj.map (homOfLE (show U ≤ ⊤ from le_top)).op
      (e.inv (e.hom a)) = (etaleGenericUnitQuotient X).obj.map j.op (e.hom a) at hr
  have hc : e.inv (e.hom a) = a := ConcreteCategory.congr_hom e.hom_inv_id a
  rw [hc] at hr
  rw [ht]
  exact hr.symm.trans (invertibleModuleGenericUnitZariskiSection_restrict hM U s hs)

end EtaleCohomology
