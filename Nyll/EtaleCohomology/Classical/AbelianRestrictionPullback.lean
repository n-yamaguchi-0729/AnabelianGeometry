/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.EtaleCohomology.Classical.AbelianSheafFunctors
public import Nyll.EtaleCohomology.Classical.EtaleRestriction
public import Nyll.EtaleCohomology.Classical.KummerPullback
public import Nyll.EtaleCohomology.Classical.MultiplicativeGroup
public import Nyll.EtaleCohomology.Classical.MultiplicativeGroupPushforward
public import Nyll.EtaleCohomology.Classical.PullbackCohomology
public import Nyll.EtaleCohomology.Classical.PullbackCohomologySections
public import Nyll.EtaleCohomology.Sites.BaseChange
public import Nyll.EtaleCohomology.Sites.EtaleRestriction
public import Nyll.EtaleCohomology.Sites.EtaleRestrictionSectionMaps
public import Nyll.EtaleCohomology.Sites.PullbackSections
public import Mathlib.CategoryTheory.Adjunction.Unique
public import Mathlib.CategoryTheory.Limits.MorphismProperty
public import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic

/-!
# The original abelian pullback is actual étale restriction

The two left adjoints of the same original direct image are canonically
isomorphic. This comparison retains the original adjunction unit, the
original unit-sheaf pullback, and the original degree-zero section map.
-/

@[expose] public section

noncomputable section

universe u

open AlgebraicGeometry CategoryTheory Limits Opposite

namespace EtaleCohomology

variable {U X : Scheme.{u}} (f : U ⟶ X) [Etale f]

/-- The original abelian inverse image agrees with restriction along
an étale morphism through uniqueness of its original adjunction. -/
def etaleAbelianPullbackRestrictionIso :
    etaleAbelianPullback f ≅ etaleRestriction f AddCommGrpCat.{u} :=
  (etaleAbelianPullbackPushforwardAdjunction f).leftAdjointUniq
    (etaleRestrictionPushforwardAdjunction f AddCommGrpCat.{u})

/-- The comparison preserves the original inverse-image unit. -/
theorem etaleAbelianPullbackRestrictionIso_unit
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u}) :
    (etaleAbelianPullbackPushforwardAdjunction f).unit.app F ≫
        (etaleAbelianPushforward f).map
          ((etaleAbelianPullbackRestrictionIso f).hom.app F) =
      (etaleRestrictionPushforwardAdjunction f AddCommGrpCat.{u}).unit.app F :=
  Adjunction.unit_leftAdjointUniq_hom_app
    (etaleAbelianPullbackPushforwardAdjunction f)
    (etaleRestrictionPushforwardAdjunction f AddCommGrpCat.{u}) F

/-- On the unit sheaf the comparison is the original adjoint of
restriction of actual unit sections. -/
theorem etaleMultiplicativeGroupPullback_restriction :
    (etaleAbelianPullbackRestrictionIso f).hom.app
        (etaleMultiplicativeGroupSheaf X) ≫
      (etaleRestrictionMultiplicativeGroupIso f).hom =
        etaleMultiplicativeGroupPullback f := by
  apply ((etaleAbelianPullbackPushforwardAdjunction f).homEquiv
    (etaleMultiplicativeGroupSheaf X)
    (etaleMultiplicativeGroupSheaf U)).injective
  have hr :
      (etaleRestrictionPushforwardAdjunction f AddCommGrpCat.{u}).unit.app
          (etaleMultiplicativeGroupSheaf X) ≫
        (etaleAbelianPushforward f).map (etaleRestrictionMultiplicativeGroupIso f).hom =
      etaleMultiplicativeGroupToPushforward f := by
    apply Sheaf.hom_ext
    apply NatTrans.ext
    funext V
    change
      ((etaleRestrictionPushforwardAdjunction f AddCommGrpCat.{u}).unit.app
        (etaleMultiplicativeGroupSheaf X)).hom.app V ≫ 𝟙 _ =
          (etaleMultiplicativeGroupToPushforward f).hom.app V
    exact (Category.comp_id _).trans
      ((etaleRestrictionUnit_app f (etaleMultiplicativeGroupSheaf X) V.unop).trans rfl)
  calc
    (etaleAbelianPullbackPushforwardAdjunction f).homEquiv _ _
        ((etaleAbelianPullbackRestrictionIso f).hom.app
          (etaleMultiplicativeGroupSheaf X) ≫
            (etaleRestrictionMultiplicativeGroupIso f).hom) =
      (etaleAbelianPullbackPushforwardAdjunction f).unit.app
          (etaleMultiplicativeGroupSheaf X) ≫
        (etaleAbelianPushforward f).map
          ((etaleAbelianPullbackRestrictionIso f).hom.app
            (etaleMultiplicativeGroupSheaf X) ≫
              (etaleRestrictionMultiplicativeGroupIso f).hom) := by
      rw [Adjunction.homEquiv_unit]
    _ = (etaleRestrictionPushforwardAdjunction f AddCommGrpCat.{u}).unit.app
          (etaleMultiplicativeGroupSheaf X) ≫
        (etaleAbelianPushforward f).map (etaleRestrictionMultiplicativeGroupIso f).hom := by
      rw [Functor.map_comp, ← Category.assoc, etaleAbelianPullbackRestrictionIso_unit]
      rfl
    _ = etaleMultiplicativeGroupToPushforward f := hr
    _ = (etaleAbelianPullbackPushforwardAdjunction f).homEquiv _ _
        (etaleMultiplicativeGroupPullback f) :=
      (etaleMultiplicativeGroupPullback_adjunct f).symm

/-- The original section pullback followed by the restriction comparison
is restriction along the original local factor. -/
theorem etaleAbelianPullbackRestrictionIso_section
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u})
    {V : X.Etale} {W : U.Etale}
    (l : W.left ⟶ V.left) (hl : l ≫ V.hom = W.hom ≫ f) :
    ((etaleAbelianPullbackPushforwardAdjunction f).unit.app F).hom.app (op V) ≫
      ((etaleAbelianPullback f).obj F).obj.map (etaleBaseChangeLift f l hl).op ≫
        ((etaleAbelianPullbackRestrictionIso f).hom.app F).hom.app (op W) =
      F.obj.map (MorphismProperty.Over.homMk
        (P := show MorphismProperty Scheme.{u} from @Etale) (Q := ⊤)
        (A := (etalePostcompose f).obj W) (B := V) l hl).op := by
  let A : Sheaf U.smallEtaleTopology AddCommGrpCat.{u} := (etaleAbelianPullback f).obj F
  let B : Sheaf U.smallEtaleTopology AddCommGrpCat.{u} :=
    (etaleRestriction f AddCommGrpCat.{u}).obj F
  let I : A ⟶ B := (etaleAbelianPullbackRestrictionIso f).hom.app F
  let η : F ⟶ (etaleAbelianPushforward f).obj A :=
    (etaleAbelianPullbackPushforwardAdjunction f).unit.app F
  let m : W ⟶ (etaleBaseChange f).obj V := etaleBaseChangeLift f l hl
  have hu :
      η.hom.app (op V) ≫ I.hom.app (op ((etaleBaseChange f).obj V)) =
        F.obj.map ((etalePostcomposeBaseChangeAdjunction f).counit.app V).op :=
    (congrArg (fun a => a.hom.app (op V))
      (etaleAbelianPullbackRestrictionIso_unit f F)).trans
        (etaleRestrictionUnit_app f F V)
  have hn := I.hom.naturality m.op
  change ((etaleAbelianPullback f).obj F).obj.map m.op ≫ I.hom.app (op W) =
    I.hom.app (op ((etaleBaseChange f).obj V)) ≫
      F.obj.map ((etalePostcompose f).map m).op at hn
  let uV : F.obj.obj (op V) ⟶ A.obj.obj (op ((etaleBaseChange f).obj V)) :=
    η.hom.app (op V)
  let a : A.obj.obj (op ((etaleBaseChange f).obj V)) ⟶ A.obj.obj (op W) :=
    A.obj.map m.op
  let e : A.obj.obj (op W) ⟶ B.obj.obj (op W) := I.hom.app (op W)
  let eV : A.obj.obj (op ((etaleBaseChange f).obj V)) ⟶
      B.obj.obj (op ((etaleBaseChange f).obj V)) :=
    I.hom.app (op ((etaleBaseChange f).obj V))
  let r : B.obj.obj (op ((etaleBaseChange f).obj V)) ⟶ B.obj.obj (op W) :=
    F.obj.map ((etalePostcompose f).map m).op
  let c : F.obj.obj (op V) ⟶ B.obj.obj (op ((etaleBaseChange f).obj V)) :=
    F.obj.map ((etalePostcomposeBaseChangeAdjunction f).counit.app V).op
  let k : F.obj.obj (op V) ⟶ B.obj.obj (op W) :=
    F.obj.map (MorphismProperty.Over.homMk
      (P := show MorphismProperty Scheme.{u} from @Etale) (Q := ⊤)
      (A := (etalePostcompose f).obj W) (B := V) l hl).op
  change uV ≫ eV = c at hu
  change a ≫ e = eV ≫ r at hn
  have hmap : c ≫ r = k :=
    (F.obj.map_comp _ _).symm.trans
      (congrArg (fun h : (etalePostcompose f).obj W ⟶ V => F.obj.map h.op)
        (etalePostcomposeBaseChangeLift_counit f l hl))
  have hnatural : uV ≫ (a ≫ e) = uV ≫ (eV ≫ r) :=
    congrArg (fun h : A.obj.obj (op ((etaleBaseChange f).obj V)) ⟶
      B.obj.obj (op W) => uV ≫ h) hn
  have hunit : (uV ≫ eV) ≫ r = c ≫ r :=
    congrArg (fun h : F.obj.obj (op V) ⟶
      B.obj.obj (op ((etaleBaseChange f).obj V)) => h ≫ r) hu
  change uV ≫ a ≫ e = k
  exact hnatural.trans ((Category.assoc uV eV r).symm.trans (hunit.trans hmap))

/-- The original cohomological pullback, expressed in the actual
restricted coefficient sheaf. -/
def etaleAbelianRestrictionCohomologyPullback
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u}) (i : ℕ) :
    Sheaf.H.{u} F i →+
      Sheaf.H.{u} ((etaleRestriction f AddCommGrpCat.{u}).obj F) i :=
  (Sheaf.H.map ((etaleAbelianPullbackRestrictionIso f).hom.app F) i).comp
    (etaleAbelianCohomologyPullbackMap f F i)

/-- The original pullback in restricted coefficients is natural in
the original coefficient sheaf. -/
theorem etaleAbelianRestrictionCohomologyPullback_naturality
    {F G : Sheaf X.smallEtaleTopology AddCommGrpCat.{u}} (φ : F ⟶ G)
    (i : ℕ) (a : Sheaf.H.{u} F i) :
    etaleAbelianRestrictionCohomologyPullback f G i (Sheaf.H.map φ i a) =
      Sheaf.H.map ((etaleRestriction f AddCommGrpCat.{u}).map φ) i
        (etaleAbelianRestrictionCohomologyPullback f F i a) := by
  change Sheaf.H.map ((etaleAbelianPullbackRestrictionIso f).hom.app G) i
      (etaleAbelianCohomologyPullbackMap f G i (Sheaf.H.map φ i a)) =
    Sheaf.H.map ((etaleRestriction f AddCommGrpCat.{u}).map φ) i
      (Sheaf.H.map ((etaleAbelianPullbackRestrictionIso f).hom.app F) i
        (etaleAbelianCohomologyPullbackMap f F i a))
  rw [etaleAbelianCohomologyPullbackMap_naturality,
    ← Sheaf.H.map_comp_apply, ← Sheaf.H.map_comp_apply]
  exact congrArg (fun m => Sheaf.H.map m i (etaleAbelianCohomologyPullbackMap f F i a))
    ((etaleAbelianPullbackRestrictionIso f).hom.naturality φ)

/-- The original cohomological unit-sheaf pullback is actual restriction
followed by the unchanged unit-sheaf identification. -/
theorem etaleMultiplicativeGroupCohomologyPullback_restriction
    (i : ℕ) (a : Sheaf.H.{u} (etaleMultiplicativeGroupSheaf X) i) :
    etaleMultiplicativeGroupCohomologyPullback f i a =
      Sheaf.H.map (etaleRestrictionMultiplicativeGroupIso f).hom i
        (etaleAbelianRestrictionCohomologyPullback f
          (etaleMultiplicativeGroupSheaf X) i a) := by
  change Sheaf.H.map (etaleMultiplicativeGroupPullback f) i
      (etaleAbelianCohomologyPullbackMap f (etaleMultiplicativeGroupSheaf X) i a) =
    Sheaf.H.map (etaleRestrictionMultiplicativeGroupIso f).hom i
      (Sheaf.H.map ((etaleAbelianPullbackRestrictionIso f).hom.app
        (etaleMultiplicativeGroupSheaf X)) i
          (etaleAbelianCohomologyPullbackMap f (etaleMultiplicativeGroupSheaf X) i a))
  rw [← etaleMultiplicativeGroupPullback_restriction, Sheaf.H.map_comp_apply]

/-- Degree zero retains the actual restriction of the original section,
including its original terminal-object representatives. -/
theorem etaleAbelianRestrictionCohomologyPullback_zero_sections
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u})
    {V : X.Etale} (hV : IsTerminal V) {W : U.Etale} (hW : IsTerminal W)
    (l : W.left ⟶ V.left) (hl : l ≫ V.hom = W.hom ≫ f)
    (a : Sheaf.H.{u} F 0) :
    Sheaf.H.equiv₀ ((etaleRestriction f AddCommGrpCat.{u}).obj F) hW
        (etaleAbelianRestrictionCohomologyPullback f F 0 a) =
      F.obj.map (MorphismProperty.Over.homMk
        (P := show MorphismProperty Scheme.{u} from @Etale) (Q := ⊤)
        (A := (etalePostcompose f).obj W) (B := V) l hl).op
          (Sheaf.H.equiv₀ F hV a) := by
  change Sheaf.H.equiv₀ ((etaleRestriction f AddCommGrpCat.{u}).obj F) hW
    (Sheaf.H.map ((etaleAbelianPullbackRestrictionIso f).hom.app F) 0
      (etaleAbelianCohomologyPullbackMap f F 0 a)) = _
  rw [← Sheaf.H.equiv₀_naturality,
    etaleAbelianCohomologyPullbackMap_zero_sections f F hV hW
      (etaleBaseChangeLift f l hl)]
  exact ConcreteCategory.congr_hom
    (etaleAbelianPullbackRestrictionIso_section f F l hl) (Sheaf.H.equiv₀ F hV a)

end EtaleCohomology
