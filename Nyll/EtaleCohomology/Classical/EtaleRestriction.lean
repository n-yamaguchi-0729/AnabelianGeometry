/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.EtaleCohomology.Sites.EtaleRestriction
public import Nyll.EtaleCohomology.Classical.MultiplicativeGroup
public import Nyll.EtaleCohomology.Sites.EtaleSlice
public import Nyll.EtaleCohomology.Classical.FreeAbelianYoneda
public import Mathlib.Algebra.Homology.ShortComplex.ExactFunctor
public import Mathlib.Algebra.Homology.DerivedCategory.Ext.MapAdjunction
public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.HasExt
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Terminal
public import Mathlib.CategoryTheory.Preadditive.Injective.Preserves
public import Mathlib.CategoryTheory.Sites.Limits
public import Mathlib.AlgebraicGeometry.Sites.AffineEtale
public import Mathlib.Algebra.Category.Grp.AB

/-!
# Exact etale restriction of abelian coefficients

Actual etale restriction is exact: limits are computed on the underlying
presheaves, and its proved adjunction supplies colimit preservation.
Restriction of the actual unit sheaf is the actual unit sheaf.
-/

@[expose] public section

noncomputable section
universe u
open CategoryTheory Limits AlgebraicGeometry

namespace EtaleCohomology

variable {U X : Scheme.{u}} (f : U ⟶ X) [Etale f]

instance etaleAbelianRestriction_additive :
    (etaleRestriction f AddCommGrpCat.{u}).Additive where
  map_add {A B} a b := by
    apply Sheaf.hom_ext
    apply NatTrans.ext
    funext W
    rfl

/-- Actual abelian etale restriction preserves finite limits. -/
instance etaleAbelianRestriction_preservesFiniteLimits :
    PreservesFiniteLimits (etaleRestriction f AddCommGrpCat.{u}) := by
  constructor
  intro K _ _
  have : PreservesLimitsOfShape K
      (etaleRestriction f AddCommGrpCat.{u} ⋙
        sheafToPresheaf U.smallEtaleTopology AddCommGrpCat.{u}) := by
    change PreservesLimitsOfShape K
      (sheafToPresheaf X.smallEtaleTopology AddCommGrpCat.{u} ⋙
        (Functor.whiskeringLeft U.Etaleᵒᵖ X.Etaleᵒᵖ AddCommGrpCat.{u}).obj
          (etalePostcompose f).op)
    infer_instance
  exact preservesLimitsOfShape_of_reflects_of_preserves
    (etaleRestriction f AddCommGrpCat.{u})
    (sheafToPresheaf U.smallEtaleTopology AddCommGrpCat.{u})

/-- Its existing geometric adjunction makes actual abelian etale
restriction preserve finite colimits as well. -/
instance etaleAbelianRestriction_preservesFiniteColimits :
    PreservesFiniteColimits (etaleRestriction f AddCommGrpCat.{u}) := by
  have : (etaleRestriction f AddCommGrpCat.{u}).IsLeftAdjoint :=
    ⟨_, ⟨etaleRestrictionPushforwardAdjunction f AddCommGrpCat.{u}⟩⟩
  infer_instance

/-- Restriction of the actual small-etale unit sheaf does not change the
units or their pullback maps. -/
def etaleRestrictionMultiplicativeGroupIso :
    (etaleRestriction f AddCommGrpCat.{u}).obj (etaleMultiplicativeGroupSheaf X) ≅
      etaleMultiplicativeGroupSheaf U :=
  (fullyFaithfulSheafToPresheaf U.smallEtaleTopology AddCommGrpCat.{u}).preimageIso
    (Iso.refl _)

/-- The actual abelian restriction of a short exact sequence is short exact. -/
theorem etaleRestriction_shortExact
    (S : ShortComplex (Sheaf X.smallEtaleTopology AddCommGrpCat.{u}))
    (hS : S.ShortExact) :
    (S.map (etaleRestriction f AddCommGrpCat.{u})).ShortExact :=
  hS.map_of_exact _

section SliceCohomology

variable {Y : Scheme.{u}} (V : Y.Etale)

instance etaleOverAbelianHasSheafify :
    HasSheafify (Y.smallEtaleTopology.over V) AddCommGrpCat.{u} :=
  (etaleSliceEquiv V).hasSheafify (Y.smallEtaleTopology.over V)
    V.left.smallEtaleTopology AddCommGrpCat.{u}

instance etaleOverAbelianGrothendieck :
    IsGrothendieckAbelian.{u}
      (Sheaf (Y.smallEtaleTopology.over V) AddCommGrpCat.{u}) :=
  IsGrothendieckAbelian.of_equivalence
    (etaleSliceAbelianSheafEquivalence V).symm

instance etaleSliceAbelianFunctor_additive :
    (etaleSliceAbelianSheafEquivalence V).functor.Additive where
  map_add {A B} f g := by
    apply Sheaf.hom_ext
    apply NatTrans.ext
    funext W
    rfl

instance etaleSliceAbelianInverse_additive :
    (etaleSliceAbelianSheafEquivalence V).inverse.Additive where
  map_add {A B} f g := by
    apply Sheaf.hom_ext
    apply NatTrans.ext
    funext W
    rfl

/-- Actual étale restriction preserves injectives through its exact extension
adjoint and the proved equivalence with the localized site. -/
instance etaleAbelianRestriction_preservesInjectiveObjects :
    (etaleRestriction V.hom AddCommGrpCat.{u}).PreservesInjectiveObjects := by
  change (Y.smallEtaleTopology.overPullback AddCommGrpCat.{u} V ⋙
    (etaleSliceAbelianSheafEquivalence V).functor).PreservesInjectiveObjects
  infer_instance

/-- The actual slice equivalence respects constant abelian sheaves. -/
def etaleSliceAbelianConstantIso :
    constantSheaf (Y.smallEtaleTopology.over V) AddCommGrpCat.{u} ⋙
        (etaleSliceAbelianSheafEquivalence V).functor ≅
      constantSheaf V.left.smallEtaleTopology AddCommGrpCat.{u} :=
  ((constantSheafAdj (Y.smallEtaleTopology.over V) AddCommGrpCat.{u}
      (Over.mkIdTerminal (X := V))).comp
        (etaleSliceAbelianSheafEquivalence V).toAdjunction).leftAdjointUniq
    (constantSheafAdj V.left.smallEtaleTopology AddCommGrpCat.{u}
      ((Over.mkIdTerminal (X := V)).isTerminalObj
        (etaleSliceEquiv V).functor (Over.mk (𝟙 V))))

/-- Actual derived cohomology is unchanged by the equivalence of the localized
site with the small étale site of its structural scheme. -/
def etaleSliceAbelianCohomologyEquiv
    (F : Sheaf (Y.smallEtaleTopology.over V) AddCommGrpCat.{u}) (n : ℕ) :
    Sheaf.H.{u} F n ≃+
      Sheaf.H.{u} ((etaleSliceAbelianSheafEquivalence V).functor.obj F) n := by
  let E := etaleSliceAbelianSheafEquivalence V
  let Z := (constantSheaf (Y.smallEtaleTopology.over V) AddCommGrpCat.{u}).obj
    (AddCommGrpCat.of (ULift.{u} ℤ))
  let eUnit := ((Abelian.extFunctor n).obj (Opposite.op Z)).mapIso (E.unitIso.app F)
  let eConst := (etaleSliceAbelianConstantIso V).app
    (AddCommGrpCat.of (ULift.{u} ℤ))
  let eExt := ((Abelian.extFunctor n).mapIso eConst.symm.op).app (E.functor.obj F)
  exact eUnit.addCommGroupIsoToAddEquiv.trans
    (E.toAdjunction.extEquiv.symm.trans eExt.addCommGroupIsoToAddEquiv)

/-- Evaluation of the actual cohomology presheaf at an étale object is the
actual derived cohomology on that scheme, with the restricted sheaf. -/
def etaleCohomologyPresheafRestrictionEquiv
    (F : Sheaf Y.smallEtaleTopology AddCommGrpCat.{u}) (n : ℕ) :
    Sheaf.H'.{u} F n V ≃+
      Sheaf.H.{u} ((etaleRestriction V.hom AddCommGrpCat.{u}).obj F) n :=
  (sheafCohomologyOverEquiv Y.smallEtaleTopology V F n).trans
    (etaleSliceAbelianCohomologyEquiv V (F.over V) n)

end SliceCohomology

end EtaleCohomology
