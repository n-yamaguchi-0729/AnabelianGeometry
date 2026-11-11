/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.EtaleCohomology.Sites.ZariskiGlobalSections
public import Nyll.EtaleCohomology.Sites.ZariskiRestriction
public import Mathlib.Algebra.Category.Grp.AB
public import Mathlib.AlgebraicGeometry.Sites.AffineEtale
public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.HasExt
public import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
public import Mathlib.Topology.Sheaves.Sheaf

/-!
# Local equality of original étale H⁰ classes

The actual terminal-section equivalence and the actual top-open
isomorphism identify Zariski-local equality with equality in native H⁰.
This applies to the original unit quotients without changing their
cohomology groups or their maps.
-/

@[expose] public section

noncomputable section

universe u

open AlgebraicGeometry CategoryTheory Limits Opposite

namespace EtaleCohomology

/-- Restriction of the actual global-section isomorphism agrees with
the unique map to the original terminal object. -/
theorem etaleAbelianZariskiGlobalSection_restrict
    (X : Scheme.{u}) (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u})
    (U : X.Opens) (s : F.obj.obj (op (Scheme.Etale.mk (𝟙 X)))) :
    let hT := MorphismProperty.Over.mkIdTerminal
      (show MorphismProperty Scheme.{u} from @Etale) X
    ((etaleZariskiRestriction X AddCommGrpCat.{u}).obj F).obj.map
        (homOfLE (show U ≤ ⊤ from le_top)).op
          ((etaleZariskiGlobalSectionsIso X AddCommGrpCat.{u} F).inv s) =
      F.obj.map (hT.from ((zariskiToEtale X).obj U)).op s := by
  intro hT
  let j : (zariskiToEtale X).obj U ⟶ Scheme.Etale.mk (𝟙 X) :=
    MorphismProperty.Over.homMk
      (P := show MorphismProperty Scheme.{u} from @Etale) (Q := ⊤)
      U.ι (Category.comp_id U.ι)
  have ht : hT.from ((zariskiToEtale X).obj U) = j := hT.hom_ext _ _
  rw [ht]
  exact ConcreteCategory.congr_hom
    (etaleZariskiGlobalSectionsIso_inv_restrict X AddCommGrpCat.{u} F U) s

/-- Two actual H⁰ classes agree if their actual terminal sections agree
on an open neighborhood of every point. -/
theorem etaleAbelianH0_ext_zariski
    (X : Scheme.{u}) (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u})
    (a b : Sheaf.H.{u} F 0)
    (h : ∀ x : X, ∃ U : X.Opens, x ∈ U ∧
      let hT := MorphismProperty.Over.mkIdTerminal
        (show MorphismProperty Scheme.{u} from @Etale) X
      F.obj.map (hT.from ((zariskiToEtale X).obj U)).op
          (Sheaf.H.equiv₀.{u} F hT a) =
        F.obj.map (hT.from ((zariskiToEtale X).obj U)).op
          (Sheaf.H.equiv₀.{u} F hT b)) : a = b := by
  let hT := MorphismProperty.Over.mkIdTerminal
    (show MorphismProperty Scheme.{u} from @Etale) X
  let e := etaleZariskiGlobalSectionsIso X AddCommGrpCat.{u} F
  let ZF : TopCat.Sheaf AddCommGrpCat.{u} X :=
    (etaleZariskiRestriction X AddCommGrpCat.{u}).obj F
  let sa := Sheaf.H.equiv₀.{u} F hT a
  let sb := Sheaf.H.equiv₀.{u} F hT b
  have hz : e.inv sa = e.inv sb := by
    apply TopCat.Presheaf.IsSheaf.section_ext ZF.property
    intro x hx
    obtain ⟨U, hxU, hU⟩ := h x
    refine ⟨U, le_top, hxU, ?_⟩
    exact (etaleAbelianZariskiGlobalSection_restrict X F U sa).trans
      (hU.trans (etaleAbelianZariskiGlobalSection_restrict X F U sb).symm)
  apply (Sheaf.H.equiv₀.{u} F hT).injective
  have ha : e.hom (e.inv sa) = sa := ConcreteCategory.congr_hom e.inv_hom_id sa
  have hb : e.hom (e.inv sb) = sb := ConcreteCategory.congr_hom e.inv_hom_id sb
  exact ha.symm.trans ((congrArg e.hom hz).trans hb)

end EtaleCohomology
