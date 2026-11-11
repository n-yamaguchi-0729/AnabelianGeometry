/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.EtaleCohomology.Constructible.FiniteEtaleSheaf
public import Nyll.EtaleCohomology.Constructible.FiniteLocallyConstantEquivalence
public import Mathlib.CategoryTheory.Yoneda

/-!
# The original universal section of a finite étale local system

The actual finite étale representability equivalence supplies a cover
and its universal section. Naturality of its original counit relates
restriction along the actual representing cover map to the original
map of local systems. No new representability data are assumed.
-/

@[expose] public section

noncomputable section

universe u

open AlgebraicGeometry CategoryTheory Opposite
open EtaleCohomology

namespace EtaleFundamentalGroups.Cohomology

variable {X : Scheme.{u}}

/-- The actual finite étale cover supplied by the original proved
representability equivalence. -/
abbrev finiteLocalSystemRepresenter (F : EtaleFiniteLocallyConstantSetSheaf X) :
    FiniteEtale X :=
  (finiteEtaleEquivFiniteLocallyConstantSetSheaf X).inverse.obj F

/-- The image of the literal identity section under the original
representability counit. -/
def finiteLocalSystemUniversalSection (F : EtaleFiniteLocallyConstantSetSheaf X) :
    F.obj.obj.obj (op ((finiteEtaleToEtale X).obj (finiteLocalSystemRepresenter F))) :=
  ((finiteEtaleEquivFiniteLocallyConstantSetSheaf X).counitIso.hom.app F).hom.hom.app
    (op ((finiteEtaleToEtale X).obj (finiteLocalSystemRepresenter F))) (𝟙 _)

/-- Restricting the original universal section evaluates the original
counit on that same actual morphism to the representing cover. -/
theorem finiteLocalSystemUniversalSection_restrict
    (F : EtaleFiniteLocallyConstantSetSheaf X) {U : X.Etale}
    (f : U ⟶ (finiteEtaleToEtale X).obj (finiteLocalSystemRepresenter F)) :
    F.obj.obj.map f.op (finiteLocalSystemUniversalSection F) =
      ((finiteEtaleEquivFiniteLocallyConstantSetSheaf X).counitIso.hom.app F).hom.hom.app
        (op U) f := by
  let V := (finiteEtaleToEtale X).obj (finiteLocalSystemRepresenter F)
  let e := (finiteEtaleEquivFiniteLocallyConstantSetSheaf X).counitIso.hom.app F
  have h := ConcreteCategory.congr_hom (e.hom.hom.naturality f.op) (𝟙 V)
  change e.hom.hom.app (op U) (f ≫ 𝟙 V) =
    F.obj.obj.map f.op (finiteLocalSystemUniversalSection F) at h
  exact h.symm.trans
    (congrArg (fun q : U ⟶ V => e.hom.hom.app (op U) q) (Category.comp_id f))

/-- A map of original local systems carries the original universal
section to the restriction of the target's original universal section
along the actual map of their original representing covers. -/
theorem finiteLocalSystemUniversalSection_naturality
    {F G : EtaleFiniteLocallyConstantSetSheaf X} (f : F ⟶ G) :
    G.obj.obj.map
        ((finiteEtaleToEtale X).map
          ((finiteEtaleEquivFiniteLocallyConstantSetSheaf X).inverse.map f)).op
        (finiteLocalSystemUniversalSection G) =
      f.hom.hom.app
        (op ((finiteEtaleToEtale X).obj (finiteLocalSystemRepresenter F)))
          (finiteLocalSystemUniversalSection F) := by
  let E := finiteEtaleEquivFiniteLocallyConstantSetSheaf X
  let V := (finiteEtaleToEtale X).obj (finiteLocalSystemRepresenter F)
  let k := (finiteEtaleToEtale X).map (E.inverse.map f)
  have h := ConcreteCategory.congr_hom
    (congrArg (fun t : E.functor.obj (E.inverse.obj F) ⟶ G =>
      t.hom.hom.app (op V)) (E.counitIso.hom.naturality f)) (𝟙 V)
  change (E.counitIso.hom.app G).hom.hom.app (op V) ((𝟙 V) ≫ k) =
    f.hom.hom.app (op V) (finiteLocalSystemUniversalSection F) at h
  exact (finiteLocalSystemUniversalSection_restrict G k).trans
    (by simpa only [Category.id_comp] using h)

end EtaleFundamentalGroups.Cohomology
