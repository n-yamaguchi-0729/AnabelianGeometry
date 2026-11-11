/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.EtaleFundamentalGroups.Cohomology.ExtensionFibers
public import Nyll.EtaleFundamentalGroups.Cohomology.FiniteLocalSystemUniversalSection
public import Nyll.EtaleFundamentalGroups.Cohomology.LocalTrivialization
public import Mathlib.CategoryTheory.Sites.Grothendieck
public import Mathlib.CategoryTheory.Sites.Sieves.Basic
public import Mathlib.CategoryTheory.Sites.Sieves.Presieve

/-!
# The actual covering morphism representing an extension fiber

The original finite étale representability equivalence supplies the
universal lift of a quotient section. Exactness makes the representing
morphism a cover: every local lift obtained from the original epimorphism
factors through that same representer by the original counit isomorphism.
No separate surjectivity or covering hypothesis is needed.
-/

@[expose] public section

noncomputable section

universe u

open AlgebraicGeometry CategoryTheory Limits Opposite EtaleCohomology

namespace EtaleFundamentalGroups.Cohomology

variable {X : Scheme.{u}}
  (S : ShortComplex (Sheaf X.smallEtaleTopology AddCommGrpCat.{u}))
  (t : (Functor.const X.Etaleᵒᵖ).obj PUnit ⟶ S.X₃.obj ⋙ forget AddCommGrpCat.{u})
  (hS : S.ShortExact)
  (hF : IsEtaleFiniteLocallyConstantSet
    ((sheafCompose X.smallEtaleTopology (forget AddCommGrpCat.{u})).obj S.X₁))

/-- The actual original extension fiber, with local constancy supplied
by its original short exact sequence. -/
def extensionFiberLocalSystem : EtaleFiniteLocallyConstantSetSheaf X :=
  ⟨extensionFiber S t, extensionFiber_isFiniteLocallyConstant S t hS hF⟩

/-- The finite étale scheme representing the original extension fiber. -/
abbrev extensionFiberFiniteCover : FiniteEtale X :=
  finiteLocalSystemRepresenter (extensionFiberLocalSystem S t hS hF)

/-- The original counit evaluated at the identity is an actual lift of
the specified original quotient section on the representing scheme. -/
def extensionFiberUniversalSection :
    (extensionFiber S t).obj.obj
      (op ((finiteEtaleToEtale X).obj (extensionFiberFiniteCover S t hS hF))) :=
  finiteLocalSystemUniversalSection (extensionFiberLocalSystem S t hS hF)

/-- The original representing morphism is a cover of any terminal
étale object. The covering sieve is supplied by the original epimorphism. -/
theorem extensionFiberFiniteCover_covering {T : X.Etale} (hT : IsTerminal T) :
    Sieve.generate (Presieve.singleton
      (hT.from ((finiteEtaleToEtale X).obj (extensionFiberFiniteCover S t hS hF)))) ∈
      X.smallEtaleTopology T := by
  let F := extensionFiberLocalSystem S t hS hF
  let V := (finiteEtaleToEtale X).obj (extensionFiberFiniteCover S t hS hF)
  let E := finiteEtaleEquivFiniteLocallyConstantSetSheaf X
  have hle : Presheaf.imageSieve S.g.hom (t.app (op T) PUnit.unit) ≤
      Sieve.generate (Presieve.singleton (hT.from V)) := by
    intro W f hf
    obtain ⟨a, ha⟩ := hf
    have hn := ConcreteCategory.congr_hom (t.naturality f.op) PUnit.unit
    let s : (extensionFiber S t).obj.obj (op W) := ⟨a, ha.trans hn.symm⟩
    let k : W ⟶ V := (E.counitIso.inv.app F).hom.hom.app (op W) s
    exact ⟨V, k, hT.from V, Presieve.singleton_self _, hT.hom_ext _ _⟩
  exact X.smallEtaleTopology.superset_covering hle
    (extensionFiber_locally_nonempty S t hS (op T))

end EtaleFundamentalGroups.Cohomology
