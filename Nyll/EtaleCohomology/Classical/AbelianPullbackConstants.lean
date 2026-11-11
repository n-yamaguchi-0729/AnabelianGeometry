/-
Copyright (c) 2026 Naganori Yamaguchi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
https://github.com/n-yamaguchi-0729
-/

module

public import Nyll.EtaleCohomology.Classical.AbelianSheafFunctors
public import Nyll.EtaleCohomology.Sites.ConstantPullback
public import Nyll.EtaleCohomology.Sites.ConstantPullbackSections
public import Mathlib.CategoryTheory.Adjunction.Unique
public import Mathlib.CategoryTheory.Sites.ConstantSheaf
public import Mathlib.CategoryTheory.Sites.Sheafification

/-!
# Constant sections under actual abelian inverse image

The constant-sheaf inverse-image comparison is defined by uniqueness of left
adjoints. Its adjoint sends each original constant section to the same section
on the base-changed etale scheme. In particular it preserves the integer section
one used to represent degree-one cohomology classes by extension fibers.
-/

@[expose] public section

noncomputable section

universe u

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite

namespace EtaleCohomology

/-- The adjoint of the canonical constant comparison preserves the original
constant section for every left adjoint to actual direct image. -/
theorem constantSheafCompLeftAdjointIso_hom_section
    {X Y : Scheme.{u}} (f : X ⟶ Y)
    (L : Sheaf Y.smallEtaleTopology AddCommGrpCat.{u} ⥤
      Sheaf X.smallEtaleTopology AddCommGrpCat.{u})
    (adj : L ⊣ etaleAbelianPushforward f) (A : AddCommGrpCat.{u}) (U : Y.Etale) :
    (toSheafify Y.smallEtaleTopology ((Functor.const Y.Etaleᵒᵖ).obj A)).app (op U) ≫
        (adj.homEquiv _ _
          ((Sites.constantSheafCompLeftAdjointIso (etaleBaseChange f) AddCommGrpCat.{u}
            terminalIsTerminal
              (terminalIsTerminal.isTerminalObj (etaleBaseChange f) (⊤_ Y.Etale))
                L adj).hom.app A)).hom.app (op U) =
      (toSheafify X.smallEtaleTopology ((Functor.const X.Etaleᵒᵖ).obj A)).app
        (op ((etaleBaseChange f).obj U)) :=
  Sites.constantSheafCompLeftAdjointIso_hom_section f L adj A U

/-- The adjoint of the actual constant inverse-image comparison sends a constant
coefficient to the same coefficient on each base-changed etale scheme. -/
theorem etaleAbelianPullbackConstantIso_hom_section
    {X Y : Scheme.{u}} (f : X ⟶ Y) (A : AddCommGrpCat.{u}) (U : Y.Etale) :
    (toSheafify Y.smallEtaleTopology ((Functor.const Y.Etaleᵒᵖ).obj A)).app (op U) ≫
        ((etaleAbelianPullbackPushforwardAdjunction f).homEquiv _ _
          ((etaleAbelianPullbackConstantIso f).hom.app A)).hom.app (op U) =
      (toSheafify X.smallEtaleTopology ((Functor.const X.Etaleᵒᵖ).obj A)).app
        (op ((etaleBaseChange f).obj U)) :=
  constantSheafCompLeftAdjointIso_hom_section f (etaleAbelianPullback f)
    (etaleAbelianPullbackPushforwardAdjunction f) A U

end EtaleCohomology
