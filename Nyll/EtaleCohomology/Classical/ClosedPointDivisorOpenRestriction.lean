/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.EtaleCohomology.Classical.ClosedPointDivisorSheaf
public import Nyll.EtaleCohomology.Sites.EtaleRestriction
public import Mathlib.Algebra.Category.Grp.Basic
public import Mathlib.CategoryTheory.Adjunction.Limits
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Products
public import Mathlib.CategoryTheory.Limits.Shapes.ZeroMorphisms
public import Mathlib.CategoryTheory.Sites.Limits
public import Mathlib.Algebra.Group.Equiv.Basic
public import Mathlib.Topology.JacobsonSpace

/-!
# Restriction of the actual closed-point divisor sheaf to an open subscheme

The original closed-point summands are compared using their existing
section equivalences on residue fibers. Summands outside the open vanish.
The restriction adjunction preserves their coproduct, and the actual
closed points of the open give its surviving indices on a Jacobson scheme.
-/

@[expose] public section

noncomputable section

universe u v w

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace

namespace EtaleCohomology

/-- Removing zero summands identifies a coproduct with the coproduct on its support. -/
def coproductSupportedIso
    {C : Type v} [Category.{w} C] {I : Type u}
    (F : I → C) (P : I → Prop)
    [HasCoproduct F] [HasCoproduct (fun i : {i // P i} => F i.1)]
    (hzero : ∀ i, ¬ P i → IsZero (F i)) :
    (∐ F) ≅ ∐ (fun i : {i // P i} => F i.1) := by
  classical
  let G := fun i : {i // P i} => F i.1
  refine
    { hom := Sigma.desc (fun i => if hi : P i then Sigma.ι G ⟨i, hi⟩
        else (hzero i hi).to_ (∐ G))
      inv := Sigma.desc (fun i : {i // P i} => Sigma.ι F i.1)
      hom_inv_id := ?_
      inv_hom_id := ?_ }
  · apply Sigma.hom_ext
    intro i
    by_cases hi : P i
    · simp only [Sigma.ι_comp_desc_assoc, dite_eq_left hi, Sigma.ι_comp_desc,
        Category.comp_id]
    · exact (hzero i hi).eq_of_src _ _
  · apply Sigma.hom_ext
    intro i
    simp only [Sigma.ι_comp_desc_assoc, Sigma.ι_comp_desc, dite_eq_left i.2,
      Category.comp_id]
    rfl

private theorem coproductSupportedIso_ι
    {C : Type v} [Category.{w} C] {I : Type u}
    (F : I → C) (P : I → Prop)
    [HasCoproduct F] [HasCoproduct (fun i : {i // P i} => F i.1)]
    (hzero : ∀ i, ¬ P i → IsZero (F i)) (i : {i // P i}) :
    Sigma.ι F i.1 ≫ (coproductSupportedIso F P hzero).hom =
      Sigma.ι (fun i : {i // P i} => F i.1) i := by
  classical
  simp only [coproductSupportedIso, Sigma.ι_comp_desc, dite_eq_left i.2]

variable {X : Scheme.{u}} (U : X.Opens)

/-- A closed point that belongs to an open remains closed on that open. -/
def closedPointInOpen (x : closedPoints X) (hx : x.1 ∈ U) :
    closedPoints (U : Scheme) :=
  ⟨⟨x.1, hx⟩,
    preimage_closedPoints_subset U.ι.isOpenEmbedding.injective
      U.ι.isOpenEmbedding.continuous x.2⟩

/-- Passing to an open subscheme preserves the residue fiber over a point in that open. -/
def closedPointOpenResidueFiberEquiv
    (x : closedPoints X) (hx : x.1 ∈ U) (V : (U : Scheme).Etale) :
    closedPointResidueFiber X x ((etalePostcompose U.ι).obj V) ≃
      closedPointResidueFiber (U : Scheme) (closedPointInOpen U x hx) V where
  toFun z := ⟨z.1, Subtype.ext z.2⟩
  invFun z := ⟨z.1, congrArg Subtype.val z.2⟩
  left_inv _ := Subtype.ext rfl
  right_inv _ := Subtype.ext rfl

/-- Restriction to an open preserves sections of a closed-point summand supported there. -/
def closedPointDivisorSummandOpenSectionsEquiv
    (x : closedPoints X) (hx : x.1 ∈ U) (V : (U : Scheme).Etale) :
    ((etaleRestriction U.ι AddCommGrpCat.{u}).obj
      (closedPointDivisorSummand X x)).obj.obj (op V) ≃+
        (closedPointDivisorSummand (U : Scheme)
          (closedPointInOpen U x hx)).obj.obj (op V) :=
  (closedPointDivisorSummandSectionsAddEquiv X x
      ((etalePostcompose U.ι).obj V)).trans
    ((AddEquiv.arrowCongr (closedPointOpenResidueFiberEquiv U x hx V)
        (AddEquiv.refl (ULift.{u} ℤ))).trans
      (closedPointDivisorSummandSectionsAddEquiv (U : Scheme)
        (closedPointInOpen U x hx) V).symm)

private theorem closedPointDivisorSummandOpenSectionsEquiv_coefficient
    (x : closedPoints X) (hx : x.1 ∈ U) (V : (U : Scheme).Etale)
    (s : ((etaleRestriction U.ι AddCommGrpCat.{u}).obj
      (closedPointDivisorSummand X x)).obj.obj (op V))
    (z : closedPointResidueFiber (U : Scheme) (closedPointInOpen U x hx) V) :
    closedPointDivisorSummandSectionsAddEquiv (U : Scheme)
        (closedPointInOpen U x hx) V
        (closedPointDivisorSummandOpenSectionsEquiv U x hx V s) z =
      closedPointDivisorSummandSectionsAddEquiv X x
        ((etalePostcompose U.ι).obj V) s
        ((closedPointOpenResidueFiberEquiv U x hx V).symm z) := by
  change ((closedPointDivisorSummandSectionsAddEquiv (U : Scheme)
    (closedPointInOpen U x hx) V)
      ((closedPointDivisorSummandSectionsAddEquiv (U : Scheme)
        (closedPointInOpen U x hx) V).symm _)) z = _
  rw [AddEquiv.apply_symm_apply]
  rfl

/-- The summand section comparison commutes with restrictions between étale objects. -/
theorem closedPointDivisorSummandOpenSectionsEquiv_naturality
    (x : closedPoints X) (hx : x.1 ∈ U)
    (V W : (U : Scheme).Etale) (m : V ⟶ W)
    (s : ((etaleRestriction U.ι AddCommGrpCat.{u}).obj
      (closedPointDivisorSummand X x)).obj.obj (op W)) :
    closedPointDivisorSummandOpenSectionsEquiv U x hx V
        ((((etaleRestriction U.ι AddCommGrpCat.{u}).obj
          (closedPointDivisorSummand X x)).obj.map m.op).hom s) =
      ((closedPointDivisorSummand (U : Scheme)
        (closedPointInOpen U x hx)).obj.map m.op).hom
        (closedPointDivisorSummandOpenSectionsEquiv U x hx W s) := by
  apply (closedPointDivisorSummandSectionsAddEquiv (U : Scheme)
    (closedPointInOpen U x hx) V).injective
  funext z
  let zW : closedPointResidueFiber (U : Scheme) (closedPointInOpen U x hx) W :=
    ⟨m.left z.1, by
      have hm := congrArg (fun k => k z.1)
        (MorphismProperty.Over.w
          (P := show MorphismProperty Scheme.{u} from @Etale) (Q := ⊤) m)
      exact hm.trans z.2⟩
  rw [closedPointDivisorSummandOpenSectionsEquiv_coefficient]
  calc
    _ = closedPointDivisorSummandSectionsAddEquiv X x
        ((etalePostcompose U.ι).obj W) s
        ((closedPointOpenResidueFiberEquiv U x hx W).symm zW) :=
      closedPointDivisorSummandSectionsAddEquiv_naturality X x
        ((etalePostcompose U.ι).obj V) ((etalePostcompose U.ι).obj W)
        ((etalePostcompose U.ι).map m) s
        ((closedPointOpenResidueFiberEquiv U x hx V).symm z)
    _ = closedPointDivisorSummandSectionsAddEquiv (U : Scheme)
        (closedPointInOpen U x hx) W
        (closedPointDivisorSummandOpenSectionsEquiv U x hx W s) zW :=
      (closedPointDivisorSummandOpenSectionsEquiv_coefficient U x hx W s zW).symm
    _ = _ := (closedPointDivisorSummandSectionsAddEquiv_naturality (U : Scheme)
      (closedPointInOpen U x hx) V W m
      (closedPointDivisorSummandOpenSectionsEquiv U x hx W s) z).symm

/-- Restriction preserves the actual summand at a closed point in the open,
with the original integer coefficient on every residue fiber. -/
def closedPointDivisorSummandOpenRestrictionIso
    (x : closedPoints X) (hx : x.1 ∈ U) :
    (etaleRestriction U.ι AddCommGrpCat.{u}).obj
        (closedPointDivisorSummand X x) ≅
      closedPointDivisorSummand (U : Scheme) (closedPointInOpen U x hx) :=
  (fullyFaithfulSheafToPresheaf (U : Scheme).smallEtaleTopology
    AddCommGrpCat.{u}).preimageIso
      (NatIso.ofComponents
        (fun V => AddEquiv.toAddCommGrpIso
          (closedPointDivisorSummandOpenSectionsEquiv U x hx V.unop))
        (fun {V W} m => by
          ext s
          exact closedPointDivisorSummandOpenSectionsEquiv_naturality
            U x hx W.unop V.unop m.unop s))

/-- The restriction isomorphism preserves the original integer attached
to each point in the residue fiber. -/
theorem closedPointDivisorSummandOpenRestrictionIso_coefficient
    (x : closedPoints X) (hx : x.1 ∈ U) (V : (U : Scheme).Etale)
    (s : ((etaleRestriction U.ι AddCommGrpCat.{u}).obj
      (closedPointDivisorSummand X x)).obj.obj (op V))
    (z : closedPointResidueFiber (U : Scheme) (closedPointInOpen U x hx) V) :
    closedPointDivisorSummandSectionsAddEquiv (U : Scheme)
        (closedPointInOpen U x hx) V
        (((closedPointDivisorSummandOpenRestrictionIso U x hx).hom.hom.app
          (op V)).hom s) z =
      closedPointDivisorSummandSectionsAddEquiv X x
        ((etalePostcompose U.ι).obj V) s
        ⟨z.1, congrArg Subtype.val z.2⟩ :=
  closedPointDivisorSummandOpenSectionsEquiv_coefficient U x hx V s z

/-- A closed-point summand whose support misses the open restricts to zero. -/
theorem closedPointDivisorSummandOpenRestriction_isZero
    (x : closedPoints X) (hx : x.1 ∉ U) :
    IsZero ((etaleRestriction U.ι AddCommGrpCat.{u}).obj
      (closedPointDivisorSummand X x)) := by
  apply (IsZero.iff_id_eq_zero _).mpr
  apply Sheaf.hom_ext
  apply NatTrans.ext
  funext V
  ext s
  apply (closedPointDivisorSummandSectionsAddEquiv X x
    ((etalePostcompose U.ι).obj V.unop)).injective
  funext z
  have hz : U.ι (V.unop.hom z.1) = x.1 := z.2
  have ht : U.ι (V.unop.hom z.1) ∈ U := (V.unop.hom z.1).2
  exact False.elim (hx (hz ▸ ht))

/-- On a Jacobson scheme, the closed points of an open are precisely the
original closed points lying in the open. -/
def closedPointsOpenEquiv [JacobsonSpace X] :
    closedPoints (U : Scheme) ≃ {x : closedPoints X // x.1 ∈ U} where
  toFun y := ⟨⟨y.1.1, by
    change y.1 ∈ U.ι ⁻¹' closedPoints X
    rw [U.ι.isOpenEmbedding.preimage_closedPoints]
    exact y.2⟩, y.1.2⟩
  invFun x := closedPointInOpen U x.1 x.2
  left_inv y := Subtype.ext (Subtype.ext rfl)
  right_inv x := Subtype.ext (Subtype.ext rfl)

/-- Abelian sheaves on the small étale site have small coproducts. -/
theorem etaleAbelianHasSmallCoproducts (Y : Scheme.{u}) :
    HasCoproducts.{u} (Sheaf Y.smallEtaleTopology AddCommGrpCat.{u}) := by
  intro I
  exact @CategoryTheory.Sheaf.instHasColimitsOfShape
    Y.Etale _ Y.smallEtaleTopology AddCommGrpCat.{u} _
    (Discrete I) _ inferInstance inferInstance

/-- The actual closed-point divisor coproduct restricts to the divisor
coproduct of an open subscheme of a Jacobson scheme. -/
def closedPointDivisorOpenRestrictionIso [JacobsonSpace X] :
    (etaleRestriction U.ι AddCommGrpCat.{u}).obj (closedPointDivisorSheaf X) ≅
      closedPointDivisorSheaf (U : Scheme) := by
  let R := etaleRestriction U.ι AddCommGrpCat.{u}
  have : R.IsLeftAdjoint :=
    ⟨_, ⟨etaleRestrictionPushforwardAdjunction U.ι AddCommGrpCat.{u}⟩⟩
  have : HasCoproducts.{u} (Sheaf X.smallEtaleTopology AddCommGrpCat.{u}) :=
    etaleAbelianHasSmallCoproducts X
  have : HasCoproducts.{u} (Sheaf (U : Scheme).smallEtaleTopology AddCommGrpCat.{u}) :=
    etaleAbelianHasSmallCoproducts (U : Scheme)
  let A := fun x : closedPoints X => R.obj (closedPointDivisorSummand X x)
  let P := fun x : closedPoints X => x.1 ∈ U
  let B := fun x : {x // P x} => A x.1
  let e := closedPointsOpenEquiv U
  let hzero : ∀ x, ¬ P x → IsZero (A x) :=
    fun x hx => closedPointDivisorSummandOpenRestriction_isZero U x hx
  let d : Discrete.functor (B ∘ e) ≅
      Discrete.functor (closedPointDivisorSummand (U : Scheme)) :=
    Discrete.natIso (fun y => closedPointDivisorSummandOpenRestrictionIso
      U (e y.as).1 (e y.as).2)
  change R.obj (∐ (closedPointDivisorSummand X)) ≅
    ∐ (closedPointDivisorSummand (U : Scheme))
  exact PreservesCoproduct.iso R (closedPointDivisorSummand X) ≪≫
    coproductSupportedIso A P hzero ≪≫
    (Sigma.reindex e B).symm ≪≫ HasColimit.isoOfNatIso d

/-- The whole divisor restriction comparison preserves each original
closed-point inclusion, through its residue-fiber comparison. -/
theorem closedPointDivisorOpenRestrictionIso_injection [JacobsonSpace X]
    (y : closedPoints (U : Scheme)) :
    (etaleRestriction U.ι AddCommGrpCat.{u}).map
        (closedPointDivisorSheafInjection X ((closedPointsOpenEquiv U) y).1) ≫
        (closedPointDivisorOpenRestrictionIso U).hom =
      (closedPointDivisorSummandOpenRestrictionIso U
        ((closedPointsOpenEquiv U) y).1 ((closedPointsOpenEquiv U) y).2).hom ≫
        closedPointDivisorSheafInjection (U : Scheme) y := by
  let R := etaleRestriction U.ι AddCommGrpCat.{u}
  have : R.IsLeftAdjoint :=
    ⟨_, ⟨etaleRestrictionPushforwardAdjunction U.ι AddCommGrpCat.{u}⟩⟩
  have : HasCoproducts.{u} (Sheaf X.smallEtaleTopology AddCommGrpCat.{u}) :=
    etaleAbelianHasSmallCoproducts X
  have : HasCoproducts.{u} (Sheaf (U : Scheme).smallEtaleTopology AddCommGrpCat.{u}) :=
    etaleAbelianHasSmallCoproducts (U : Scheme)
  let F := closedPointDivisorSummand X
  let A := fun x : closedPoints X => R.obj (F x)
  let P := fun x : closedPoints X => x.1 ∈ U
  let B := fun x : {x // P x} => A x.1
  let e := closedPointsOpenEquiv U
  let hzero : ∀ x, ¬ P x → IsZero (A x) :=
    fun x hx => closedPointDivisorSummandOpenRestriction_isZero U x hx
  let d : Discrete.functor (B ∘ e) ≅
      Discrete.functor (closedPointDivisorSummand (U : Scheme)) :=
    Discrete.natIso (fun z => closedPointDivisorSummandOpenRestrictionIso
      U (e z.as).1 (e z.as).2)
  have hpres : R.map (Sigma.ι F (e y).1) ≫
      (PreservesCoproduct.iso R F).hom = Sigma.ι A (e y).1 := by
    rw [← cancel_mono (PreservesCoproduct.iso R F).inv,
      Category.assoc, Iso.hom_inv_id, Category.comp_id,
      PreservesCoproduct.inv_hom, ι_comp_sigmaComparison]
  change R.map (Sigma.ι F (e y).1) ≫
      (PreservesCoproduct.iso R F ≪≫ coproductSupportedIso A P hzero ≪≫
        (Sigma.reindex e B).symm ≪≫ HasColimit.isoOfNatIso d).hom = _
  simp only [Iso.trans_hom, Iso.symm_hom, ← Category.assoc]
  rw [hpres, coproductSupportedIso_ι A P hzero (e y),
    Sigma.ι_reindex_inv e B y]
  exact HasColimit.ι_isoOfNatIso_hom d ⟨y⟩

end EtaleCohomology
