/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.EtaleFundamentalGroups.GeometricFiber.LangFirstQuotient
public import Nyll.EtaleFundamentalGroups.GeometricFiber.AffineFieldSource
public import Nyll.AnabelianGeometry.FiniteField.LangCoverPointEvaluation
public import Nyll.SchemeTheory.CategoryTheory.SchemeHomOver

/-!
# Native fibers and Frobenius evaluation of the original Lang cover

The finite-étale fiber functor of the original Lang pullback is identified
with the previously constructed actual geometric solution fiber. The
original field-source Galois map acts by its literal coefficient action on
the original group-scheme coordinate. Thus the native arithmetic Frobenius
displacement is the value of the original morphism defining the pullback.
-/

@[expose] public section

universe u

noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.PreGaloisCategory
open AlgebraicGeometry AlgebraicGeometry.FiniteEtale NeronModelInfra
open GoodReductionJacobian GoodReductionJacobian.RelativeGroupLaw
open ProCGroups.Abelian

namespace AnabelianGeometry.FiniteField


variable (k : Type u) [Field k] [Fintype k]
  (A : Scheme.{u}) [A.Over (Spec (.of k))]
  (G : RelativeGroupLaw k (A ↘ Spec (.of k))) (hc : G.IsCommutative)
  (hA : AbelianSchemePropertyBundle k (A ↘ Spec (.of k)))
  {C : Scheme.{u}} (c : C ⟶ Spec (.of k))
  (a : SchemeHomOver c (A ↘ Spec (.of k)))
  (Ω : Type u) [Field Ω] [Algebra k Ω] [IsSepClosed Ω]

local notation "b" => Spec.map (CommRingCat.ofHom (algebraMap k Ω))
local notation "langMap" => Subtype.val (originalFiniteFieldLangMap k A G hc)
local notation "V" =>
  Functor.obj (FiniteEtale.pullback (Subtype.val a)) (originalLangCover k A G hc hA)

/-- Native finite-étale fiber points are precisely the actual lifts to the
same original Lang pullback, with their original projection retained. -/
def langNativeFiberEquiv (y : SchemeHomOver b c) :
    (fiber y.val).obj V ≃ LangCoverFiber k A G hc c a Ω y :=
  (fiberObjEquivHom y.val V).trans
    { toFun := fun w => ⟨w.left, Over.w w⟩
      invFun := fun w => Over.homMk w.val w.property
      left_inv := fun _ => Over.OverMorphism.ext rfl
      right_inv := fun _ => Subtype.ext rfl }

/-- The original group-scheme coordinate of the native arithmetic fiber. -/
def langNativeCoordinate (y : SchemeHomOver b c) (z : (fiber y.val).obj V) :
    G.AlgPoints hc Ω :=
  langCoverFiberCoordinate k A G hc c a Ω y
    (langNativeFiberEquiv k A G hc hA c a Ω y z)

/-- Native coordinates distinguish the points of the actual covering fiber. -/
theorem langNativeCoordinate_injective (y : SchemeHomOver b c) :
    Function.Injective (langNativeCoordinate k A G hc hA c a Ω y) := by
  intro z w h
  apply (fiberObjEquivHom y.val V).injective
  apply Over.OverMorphism.ext
  apply pullback.hom_ext
  · exact congrArg (fun p : G.AlgPoints hc Ω => (AlgPoints.toPoint p).val) h
  · exact (Over.w (fiberObjEquivHom y.val V z)).trans
      (Over.w (fiberObjEquivHom y.val V w)).symm

/-- Pullbacks of the same original Lang cover over the same group-scheme
point have the same actual coordinates. The new covering point is the
literal pullback lift of the old coordinate and the new base point. -/
theorem exists_langNativeCoordinate_eq_of_image_eq
    {D : Scheme.{u}} (d : D ⟶ Spec (.of k))
    (aD : SchemeHomOver d (A ↘ Spec (.of k)))
    (y : SchemeHomOver b c) (yD : SchemeHomOver b d)
    (himage : y.val ≫ a.val = yD.val ≫ aD.val)
    (z : (fiber y.val).obj V) :
    ∃ w : (fiber yD.val).obj
        ((FiniteEtale.pullback aD.val).obj (originalLangCover k A G hc hA)),
      langNativeCoordinate k A G hc hA d aD Ω yD w =
        langNativeCoordinate k A G hc hA c a Ω y z := by
  let z' := langNativeFiberEquiv k A G hc hA c a Ω y z
  have hz : (z'.val ≫ pullback.fst langMap a.val) ≫ langMap = yD.val ≫ aD.val := by
    rw [Category.assoc, pullback.condition, ← Category.assoc]
    exact (congrArg (· ≫ a.val) z'.property).trans himage
  let w : LangCoverFiber k A G hc d aD Ω yD :=
    ⟨pullback.lift (z'.val ≫ pullback.fst langMap a.val) yD.val hz,
      pullback.lift_snd _ _ _⟩
  refine ⟨(langNativeFiberEquiv k A G hc hA d aD Ω yD).symm w, ?_⟩
  change langCoverFiberCoordinate k A G hc d aD Ω yD
      ((langNativeFiberEquiv k A G hc hA d aD Ω yD)
        ((langNativeFiberEquiv k A G hc hA d aD Ω yD).symm w)) =
    langCoverFiberCoordinate k A G hc c a Ω y z'
  rw [Equiv.apply_symm_apply]
  apply AlgPoints.toPoint_injective
  exact Subtype.ext (pullback.lift_fst _ _ _)

/-- The original Lang cover has a point in every native geometric fiber,
also over a geometric function field. The pullback cover may be disconnected. -/
theorem langNativeFiber_nonempty (y : SchemeHomOver b c) :
    Nonempty ((fiber y.val).obj V) := by
  have : Smooth (A ↘ Spec (.of k)) := hA.smooth
  have : GeometricallyIntegral (A ↘ Spec (.of k)) := hA.geometricallyIntegral
  have : GeometricallyConnected (A ↘ Spec (.of k)) :=
    GeometricallyIrreducible.geometricallyConnected _
  have : ConnectedSpace A := GeometricallyConnected.connectedSpace
    (A ↘ Spec (.of k)) (A ↘ Spec (.of k)).isOpenMap
  have : Nonempty (originalLangCover k A G hc hA).left := inferInstanceAs (Nonempty A)
  have hnon : Nonempty ((fiber (y.val ≫ a.val)).obj (originalLangCover k A G hc hA)) :=
    (not_initial_iff_fiber_nonempty _ _).mp
      (FiniteEtale.notInitial_of_nonempty_left (originalLangCover k A G hc hA))
  exact ⟨((pullbackFiberIso a.val y.val).app (originalLangCover k A G hc hA)).inv
    (Classical.choice hnon)⟩

/-- At any supplied field source, including the geometric generic point,
the original pointed fundamental-group map acts on the same Lang coordinate
by the literal coefficient automorphism. -/
theorem langNativeCoordinate_pointedFieldSource
    {F : Type u} [Field F] [Algebra k F] [Algebra F Ω]
    [IsScalarTower k F Ω] [IsSepClosure F Ω]
    (j : Spec (.of F) ⟶ C) (y : SchemeHomOver b c)
    (hy : ξ F Ω ≫ j = y.val) (σ : Gal(Ω/F)) (z : (fiber y.val).obj V) :
    langNativeCoordinate k A G hc hA c a Ω y
        (pointedFundamentalGroupHom j (ξ F Ω) y.val hy
          (suppliedGaloisEquivFundamentalGroup F Ω σ) • z) =
      σ.restrictScalars k • langNativeCoordinate k A G hc hA c a Ω y z := by
  have hl := pointed_field_fiberLift j y.val hy V σ z
  apply AlgPoints.toPoint_injective
  apply Subtype.ext
  change
    (fiberObjEquivHom y.val V
      (pointedFundamentalGroupHom j (ξ F Ω) y.val hy
        (suppliedGaloisEquivFundamentalGroup F Ω σ) • z)).left ≫ pullback.fst langMap a.val =
      Spec.map (CommRingCat.ofHom σ.toRingHom) ≫
        ((fiberObjEquivHom y.val V z).left ≫ pullback.fst langMap a.val)
  rw [mulAction_def (fiber y.val)]
  exact (congrArg (fun t : Spec (.of Ω) ⟶ (V).left =>
    t ≫ pullback.fst langMap a.val) hl).trans (Category.assoc _ _ _)

/-- Equality in the first arithmetic quotient of one original source
gives equality of the native Lang actions on another source with the same
group-scheme image. The comparison is proved on the literal coordinate,
using the two original field-source actions. -/
theorem langNativeFieldSource_smul_eq_of_firstMk_eq_at_common_image
    (κ : Type u) [Field κ] [Algebra k κ] [Algebra κ Ω]
    [IsScalarTower k κ Ω] [IsSepClosure k κ]
    {F : Type u} [Field F] [Algebra k F] [Algebra F Ω]
    [IsScalarTower k F Ω] [IsSepClosure F Ω]
    {D : Scheme.{u}} (d : D ⟶ Spec (.of k))
    (aD : SchemeHomOver d (A ↘ Spec (.of k)))
    (j : Spec (.of F) ⟶ C) (y : SchemeHomOver b c)
    (hy : ξ F Ω ≫ j = y.val)
    (jD : Spec (.of F) ⟶ D) (yD : SchemeHomOver b d)
    (hyD : ξ F Ω ≫ jD = yD.val)
    (himage : y.val ≫ a.val = yD.val ≫ aD.val)
    (σ τ : Gal(Ω/F))
    (heq : arithmeticFirstMk
        (arithmeticFundamentalGroupHom k κ c y.val).toMonoidHom.ker
        (pointedFieldSourceHom j y.val hy σ) =
      arithmeticFirstMk
        (arithmeticFundamentalGroupHom k κ c y.val).toMonoidHom.ker
        (pointedFieldSourceHom j y.val hy τ))
    (z : (fiber yD.val).obj
      ((FiniteEtale.pullback aD.val).obj (originalLangCover k A G hc hA))) :
    pointedFieldSourceHom jD yD.val hyD σ • z =
      pointedFieldSourceHom jD yD.val hyD τ • z := by
  obtain ⟨w, hw⟩ := exists_langNativeCoordinate_eq_of_image_eq
    k A G hc hA d aD Ω c a yD y himage.symm z
  have hwAction := originalLangPullback_smul_eq_of_firstMk_eq k A G hc hA κ Ω
    c a y (pointedFieldSourceHom j y.val hy σ)
      (pointedFieldSourceHom j y.val hy τ) heq w
  have hcoord := congrArg (langNativeCoordinate k A G hc hA c a Ω y) hwAction
  change langNativeCoordinate k A G hc hA c a Ω y
      (pointedFundamentalGroupHom j (ξ F Ω) y.val hy
        (suppliedGaloisEquivFundamentalGroup F Ω σ) • w) =
    langNativeCoordinate k A G hc hA c a Ω y
      (pointedFundamentalGroupHom j (ξ F Ω) y.val hy
        (suppliedGaloisEquivFundamentalGroup F Ω τ) • w) at hcoord
  rw [langNativeCoordinate_pointedFieldSource,
    langNativeCoordinate_pointedFieldSource, hw] at hcoord
  apply langNativeCoordinate_injective k A G hc hA d aD Ω yD
  change langNativeCoordinate k A G hc hA d aD Ω yD
      (pointedFundamentalGroupHom jD (ξ F Ω) yD.val hyD
        (suppliedGaloisEquivFundamentalGroup F Ω σ) • z) =
    langNativeCoordinate k A G hc hA d aD Ω yD
      (pointedFundamentalGroupHom jD (ξ F Ω) yD.val hyD
        (suppliedGaloisEquivFundamentalGroup F Ω τ) • z)
  rw [langNativeCoordinate_pointedFieldSource,
    langNativeCoordinate_pointedFieldSource]
  exact hcoord

variable [Algebra.IsAlgebraic k Ω]

/-- The Lang equation is evaluated on the same native covering point. -/
theorem langNativeCoordinate_displacement (y : SchemeHomOver b c)
    (z : (fiber y.val).obj V) :
    FiniteField.frobeniusAlgEquivOfAlgebraic k Ω •
        langNativeCoordinate k A G hc hA c a Ω y z -
      langNativeCoordinate k A G hc hA c a Ω y z =
        AlgPoints.ofPoint (L := G) (hc := hc) (NeronModelInfra.schemeHomOverComp y a) :=
  langCoverFiberCoordinate_displacement k A G hc c a Ω y
    (langNativeFiberEquiv k A G hc hA c a Ω y z)

variable [IsSepClosure k Ω] [IsIntegral C]

omit [Algebra.IsAlgebraic k Ω] in
/-- On the native Lang fiber at an original rational point, the actual
field-source homomorphism acts by the original coefficient automorphism. -/
theorem langNativeCoordinate_fieldSource
    (y : SchemeHomOver (𝟙 (Spec (.of k))) c) (σ : Gal(Ω/k))
    (z : (fiber (langCoverRationalPoint k c Ω y).val).obj V) :
    langNativeCoordinate k A G hc hA c a Ω (langCoverRationalPoint k c Ω y)
        (fieldSourceAbsoluteGaloisHom k Ω y.val σ • z) =
      σ • langNativeCoordinate k A G hc hA c a Ω (langCoverRationalPoint k c Ω y) z := by
  have hl :
      (fiberObjEquivHom (langCoverRationalPoint k c Ω y).val V
        (fieldSourceAbsoluteGaloisHom k Ω y.val σ • z)).left =
      Spec.map (CommRingCat.ofHom σ.toRingHom) ≫
        (fiberObjEquivHom (langCoverRationalPoint k c Ω y).val V z).left := by
    rw [mulAction_def (fiber (langCoverRationalPoint k c Ω y).val),
      fieldSourceAbsoluteGaloisHom_apply_toAut]
    exact fundamentalGroupHom_field_fiberLift y.val V σ z
  apply AlgPoints.toPoint_injective
  apply Subtype.ext
  change
    (fiberObjEquivHom (langCoverRationalPoint k c Ω y).val V
      (fieldSourceAbsoluteGaloisHom k Ω y.val σ • z)).left ≫ pullback.fst langMap a.val =
      Spec.map (CommRingCat.ofHom σ.toRingHom) ≫
        ((fiberObjEquivHom (langCoverRationalPoint k c Ω y).val V z).left ≫
          pullback.fst langMap a.val)
  exact (congrArg (fun t : Spec (.of Ω) ⟶ (V).left =>
    t ≫ pullback.fst langMap a.val) hl).trans (Category.assoc _ _ _)

/-- The native arithmetic Frobenius displacement on the original Lang
cover is the actual value at the original rational point. -/
theorem langNativeFrobenius_displacement
    (y : SchemeHomOver (𝟙 (Spec (.of k))) c)
    (z : (fiber (langCoverRationalPoint k c Ω y).val).obj V) :
    langNativeCoordinate k A G hc hA c a Ω (langCoverRationalPoint k c Ω y)
        (fieldSourceAbsoluteGaloisHom k Ω y.val
          (FiniteField.frobeniusAlgEquivOfAlgebraic k Ω) • z) -
      langNativeCoordinate k A G hc hA c a Ω (langCoverRationalPoint k c Ω y) z =
        AlgPoints.ofPoint (L := G) (hc := hc)
          (NeronModelInfra.schemeHomOverComp (langCoverRationalPoint k c Ω y) a) := by
  rw [langNativeCoordinate_fieldSource]
  exact langNativeCoordinate_displacement k A G hc hA c a Ω
    (langCoverRationalPoint k c Ω y) z

end AnabelianGeometry.FiniteField
