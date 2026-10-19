/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/
import Nyll.EtaleFundamentalGroups.GeometricFiber.FundamentalGroup

/-! # Actual section points are fixed by every fibre-functor comparison

The diagonal section of a pulled-back constant cover is a special case. Its
point is preserved by the independently chosen comparison of geometric fibre
functors; no preservation hypothesis is needed.
-/
noncomputable section
open CategoryTheory

namespace AlgebraicGeometry.FiniteEtale

universe u

variable {S : Scheme.{u}}

local instance sectionPointIdentity_isFiniteEtale : IsFiniteEtale (𝟙 S) := by
  constructor

/-- The unique fibre point of the identity covering, displayed as a literal lift. -/
def identityCoverFiberPoint
    {Ω : Type u} [Field Ω] [IsSepClosed Ω] (xi : Spec (.of Ω) ⟶ S) :
    (fiber xi).obj (FiniteEtale.mk (𝟙 S)) :=
  (fiberObjEquivHom xi (FiniteEtale.mk (𝟙 S))).symm
    (Over.homMk xi (Category.comp_id xi))

theorem identityCoverFiber_subsingleton
    {Ω : Type u} [Field Ω] [IsSepClosed Ω] (xi : Spec (.of Ω) ⟶ S) :
    Subsingleton ((fiber xi).obj (FiniteEtale.mk (𝟙 S))) := by
  constructor
  intro a b
  apply (fiberObjEquivHom xi (FiniteEtale.mk (𝟙 S))).injective
  apply Over.OverMorphism.ext
  have ha := (fiberObjEquivHom xi (FiniteEtale.mk (𝟙 S)) a).w
  have hb := (fiberObjEquivHom xi (FiniteEtale.mk (𝟙 S)) b).w
  change (fiberObjEquivHom xi (FiniteEtale.mk (𝟙 S)) a).left ≫ 𝟙 S = xi at ha
  change (fiberObjEquivHom xi (FiniteEtale.mk (𝟙 S)) b).left ≫ 𝟙 S = xi at hb
  have ha' : (fiberObjEquivHom xi (FiniteEtale.mk (𝟙 S)) a).left = xi :=
    (Category.comp_id _).symm.trans ha
  have hb' : (fiberObjEquivHom xi (FiniteEtale.mk (𝟙 S)) b).left = xi :=
    (Category.comp_id _).symm.trans hb
  exact ha'.trans hb'.symm

/-- The actual fibre point defined by a section of the specified cover. -/
def sectionCoverFiberPoint
    {Ω : Type u} [Field Ω] [IsSepClosed Ω] (xi : Spec (.of Ω) ⟶ S)
    (A : FiniteEtale S) (s : S ⟶ A.left) (hs : s ≫ A.hom = 𝟙 S) :
    (fiber xi).obj A :=
  (fiber xi).map (MorphismProperty.Over.homMk s hs) (identityCoverFiberPoint xi)

/-- Its represented point is the original geometric point followed by the section. -/
theorem sectionCoverFiberPoint_lift
    {Ω : Type u} [Field Ω] [IsSepClosed Ω] (xi : Spec (.of Ω) ⟶ S)
    (A : FiniteEtale S) (s : S ⟶ A.left) (hs : s ≫ A.hom = 𝟙 S) :
    (fiberObjEquivHom xi A (sectionCoverFiberPoint xi A s hs)).left = xi ≫ s := by
  have h := (fiberObjEquivHom_naturality xi
    (show FiniteEtale.mk (𝟙 S) ⟶ A from MorphismProperty.Over.homMk s hs)
    (identityCoverFiberPoint xi)).symm
  have hh := congrArg (fun z : Over.mk xi ⟶ A.toComma => z.left) h
  change (fiberObjEquivHom xi A (sectionCoverFiberPoint xi A s hs)).left =
    (fiberObjEquivHom xi (FiniteEtale.mk (𝟙 S)) (identityCoverFiberPoint xi)).left ≫ s at hh
  rw [identityCoverFiberPoint, Equiv.apply_symm_apply] at hh
  exact hh

/-- Naturality forces preservation of every actual section point. -/
theorem fiberComparison_sectionCoverFiberPoint
    {Ω Ω' : Type u} [Field Ω] [Field Ω'] [IsSepClosed Ω] [IsSepClosed Ω']
    (xi : Spec (.of Ω) ⟶ S) (xi' : Spec (.of Ω') ⟶ S)
    (t : fiber xi ≅ fiber xi')
    (A : FiniteEtale S) (s : S ⟶ A.left) (hs : s ≫ A.hom = 𝟙 S) :
    t.hom.app A (sectionCoverFiberPoint xi A s hs) =
      sectionCoverFiberPoint xi' A s hs := by
  let q : FiniteEtale.mk (𝟙 S) ⟶ A := MorphismProperty.Over.homMk s hs
  have hn := ConcreteCategory.congr_hom (t.hom.naturality q) (identityCoverFiberPoint xi)
  change t.hom.app A ((fiber xi).map q (identityCoverFiberPoint xi)) =
    (fiber xi').map q (t.hom.app _ (identityCoverFiberPoint xi)) at hn
  change t.hom.app A ((fiber xi).map q (identityCoverFiberPoint xi)) =
    (fiber xi').map q (identityCoverFiberPoint xi')
  rw [hn]
  exact congrArg ((fiber xi').map q)
    ((identityCoverFiber_subsingleton xi').elim _ _)

end AlgebraicGeometry.FiniteEtale
