/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.AlgebraicCurves.Geometry.Curves.SmoothProductIntegral
public import Nyll.AlgebraicCurves.Geometry.Picard.BaseChange.IsPullbackBaseChangeSnd
public import Nyll.AlgebraicCurves.Geometry.Picard.DivisionPullback
public import Nyll.AlgebraicCurves.Geometry.Picard.Functor.Functor
public import Nyll.EtaleCohomology.Classical.CupAbelianCechResolution
public import Nyll.EtaleCohomology.Classical.EtaleRestriction
public import Nyll.EtaleCohomology.Classical.FreeAbelianCechOverlap
public import Nyll.EtaleCohomology.Classical.FreeAbelianYoneda
public import Nyll.EtaleCohomology.Classical.InvertibleCycleClass
public import Nyll.EtaleCohomology.Classical.InvertibleRootCechDescent
public import Nyll.EtaleCohomology.Classical.KummerH1Kernel
public import Nyll.EtaleCohomology.Classical.KummerRestriction
public import Nyll.EtaleCohomology.Classical.KummerSequence
public import Nyll.EtaleCohomology.Classical.MultiplicativeGroup
public import Nyll.EtaleCohomology.Classical.ProperKummerH1
public import Nyll.EtaleCohomology.Sites.GaloisSections
public import Nyll.JacobianVarieties.Kummer.DiagonalDivisionDescent
public import Nyll.JacobianVarieties.Kummer.DiagonalDivisionKummerTransition
public import Nyll.JacobianVarieties.Kummer.DiagonalDivisionRoot
public import Nyll.SchemeTheory.LocalGeometry.SmoothStalks
public import Nyll.SchemeTheory.Modules.Invertible.Invertible
public import Nyll.SchemeTheory.Normalization.Normal
public import Nyll.SchemeTheory.Pi1.FiniteEtale.Basic
public import Nyll.SchemeTheory.RingTheory.RegularLocal.RegularLocalTrace
public import Mathlib.Algebra.Homology.DerivedCategory.Ext.Basic
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.AlgebraicGeometry.Properties
public import Mathlib.CategoryTheory.Opposites

/-!
# The actual division-root descent class on an overlap

An integral component of a parameter overlap has two finite étale
maps to the original integral parameter curve. The class on the first
Cech kernel constructed from the retained Poincaré root restricts to
the original native Kummer class of the corresponding division-point
difference. Its coefficient image is computed in the original Gm
cohomology; properness gives uniqueness of the native Kummer lift.

The parameter component map into the original division cover is kept
throughout. The statement uses the coefficient equation already
supplied by `diagonalSignedCycleClass_exists_picard_division_descent`.
It makes no assertion about a tensor decomposition of H².
-/

@[expose] public section

noncomputable section

universe u

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory Opposite Abelian
open NeronModelInfra GoodReductionJacobian EtaleCohomology

namespace AlgebraicGeometry.RelPicard.RepresentsRelSubPic

variable {K : Type u} [Field K] [IsAlgClosed K] {C : Scheme.{u}}
  [IsIntegral C] {c : C ⟶ Spec (.of K)} [Smooth c] [IsProper c]
  {ε : SchemeHomOver (𝟙 (Spec (.of K))) c}
  {P : SubPicGroupCondition c ε} {D : RelativePic0Designation K c}
  (h : RepresentsRelSubPic c ε P.toSubPicCondition D)
  (aj : SchemeHomOver c D.toBase) (n : ℕ)
  (B : FiniteEtale C) [IsIntegral B.left]
  (z : SchemeHomOver (B.hom ≫ c) (h.divisionStructure aj n))
  (hz : postComp (h.divisionBaseMap aj n) z =
    (⟨B.hom, rfl⟩ : SchemeHomOver (B.hom ≫ c) c))
  (Z : FiniteEtale B.left) [IsIntegral Z.left]
  (y : Z.left ⟶ B.left) [IsFinite y] [Etale y]
  (hy : y ≫ B.hom = Z.hom ≫ B.hom)

omit [IsAlgClosed K] [IsIntegral C] [Smooth c] [IsProper c]
  [IsIntegral B.left] [IsIntegral Z.left] [IsFinite y] [Etale y] in
/-- The original map between parameter covers, regarded over the coefficient field. -/
def parameterOverlapMap (W₀ : FiniteEtale C) (m : W₀ ⟶ B) :
    SchemeHomOver (W₀.hom ≫ c) (B.hom ≫ c) :=
  ⟨m.left, (Category.assoc m.left B.hom c).symm.trans (congrArg (· ≫ c) m.w)⟩

include hz in
omit [IsAlgClosed K] [IsIntegral C] [Smooth c] [IsProper c]
  [IsIntegral B.left] [IsIntegral Z.left] [IsFinite y] [Etale y] in
/-- The two actual parameter-cover maps give division points with
the same original projection to the curve. -/
theorem parameterOverlapMaps_division_projection_eq
    (W₀ : FiniteEtale C) (m₀ m₁ : W₀ ⟶ B) :
    postComp (h.divisionBaseMap aj n)
        (postComp z (parameterOverlapMap (c := c) B W₀ m₀)) =
      postComp (h.divisionBaseMap aj n)
        (postComp z (parameterOverlapMap (c := c) B W₀ m₁)) := by
  apply Subtype.ext
  have hz' := congrArg Subtype.val hz
  change z.1 ≫ (h.divisionBaseMap aj n).1 = B.hom at hz'
  change (m₀.left ≫ z.1) ≫ (h.divisionBaseMap aj n).1 =
    (m₁.left ≫ z.1) ≫ (h.divisionBaseMap aj n).1
  rw [Category.assoc, Category.assoc, hz']
  exact (show m₀.left ≫ B.hom = W₀.hom from m₀.w).trans
    (show m₁.left ≫ B.hom = W₀.hom from m₁.w).symm

omit [IsAlgClosed K] [IsIntegral C] [Smooth c] [IsProper c]
  [IsIntegral B.left] [IsIntegral Z.left] in
/-- The first original parameter map from the integral overlap cover. -/
def parameterOverlapFirst :
    SchemeHomOver ((Z.hom ≫ B.hom) ≫ c) (B.hom ≫ c) :=
  ⟨Z.hom, (Category.assoc Z.hom B.hom c).symm⟩

omit [IsAlgClosed K] [IsIntegral C] [Smooth c] [IsProper c]
  [IsIntegral B.left] [IsIntegral Z.left] [IsFinite y] [Etale y] in
/-- The second original parameter map, with its given equality over the curve. -/
def parameterOverlapSecond :
    SchemeHomOver ((Z.hom ≫ B.hom) ≫ c) (B.hom ≫ c) :=
  ⟨y, (Category.assoc y B.hom c).symm.trans (congrArg (· ≫ c) hy)⟩

include hz in
omit [IsAlgClosed K] [IsIntegral C] [Smooth c] [IsProper c]
  [IsIntegral B.left] [IsIntegral Z.left] [IsFinite y] [Etale y] in
/-- Both actual parameter-overlap points retain their common division projection. -/
theorem parameterOverlap_division_projection_eq :
    postComp (h.divisionBaseMap aj n) (postComp z (parameterOverlapFirst (c := c) B Z)) =
      postComp (h.divisionBaseMap aj n)
        (postComp z (parameterOverlapSecond (c := c) B Z y hy)) := by
  let BZ : FiniteEtale C := FiniteEtale.mk (Z.hom ≫ B.hom)
  let m₀ : BZ ⟶ B := MorphismProperty.Over.homMk Z.hom rfl
  let m₁ : BZ ⟶ B := MorphismProperty.Over.homMk y hy
  exact h.parameterOverlapMaps_division_projection_eq aj n B z hz BZ m₀ m₁

omit [IsAlgClosed K] [IsIntegral C] [IsProper c] [IsIntegral B.left] in
/-- Smoothness of the actual parameter product supplies the normality
used by the native invertible-module restriction theorem. -/
private theorem parameterProduct_isNormalIntegral
    [IsIntegral (pullback c (B.hom ≫ c))] :
    IsNormalIntegral (pullback c (B.hom ≫ c)) := by
  apply IsNormalIntegral.of_stalks
  intro u
  have : IsRegularLocalRing ((pullback c (B.hom ≫ c)).presheaf.stalk u) :=
    Smooth.isRegularLocalRing_stalk (f := pullback.snd c (B.hom ≫ c) ≫ (B.hom ≫ c)) u
  exact SchemeTheory.isIntegrallyClosed_of_isRegularLocalRing _

include hz in
/-- Any two original maps from an integral finite parameter cover give
the original Kummer class of their division transition. The retained root
may be transported to an isomorphic covering object, with any original
terminal representative. -/
theorem divisionRootDescent_overlap_maps_of_iso
    (W₀ : FiniteEtale C) [IsIntegral W₀.left] (m₀ m₁ : W₀ ⟶ B)
    (hn : 0 < n) (hnK : IsUnit (n : K)) :
    let Y := pullback c c
    let U := diagonalParameterProductCover c B
    let hU : IsIntegral U.left :=
      isIntegral_pullback_of_smooth_of_isAlgClosed (X := C) (Y := B.left) c (B.hom ≫ c)
    let : IsIntegral (pullback c (B.hom ≫ c)) := hU
    let V := (finiteEtaleInclusion Y).obj U
    let : IsIntegral V.left := hU
    ∀ {V' T : Y.Etale} (e : V ≅ V') (hT : IsTerminal T) (f : V' ⟶ T),
    let _ : IsIntegral V'.left := by
      have : IsIso e.hom.left := inferInstanceAs
        (IsIso ((Scheme.Etale.forget Y ⋙ Over.forget Y).map e.hom))
      exact IsIntegral.of_isIso e.hom.left
    let A := abelianCechAugmentationSequence Y.smallEtaleTopology hT f
    let L := (Scheme.Modules.pullback (baseChangeSnd c z)).obj (h.divisionRootFamily aj n).L
    let hL := (h.divisionRootFamily aj n).isInvertible.pullback (baseChangeSnd c z)
    let _ := (Scheme.Modules.pullback e.inv.left).obj L
    let hL' := hL.pullback e.inv.left
    let UZ := diagonalParameterProductCover c W₀
    let hUZ : IsIntegral UZ.left :=
      isIntegral_pullback_of_smooth_of_isAlgClosed (X := C) (Y := W₀.left) c (W₀.hom ≫ c)
    let : IsIntegral (pullback c (W₀.hom ≫ c)) := hUZ
    let W := (finiteEtaleInclusion Y).obj UZ
    let : IsIntegral W.left := hUZ
    let x₀ := parameterOverlapMap (c := c) B W₀ m₀
    let y₀ := parameterOverlapMap (c := c) B W₀ m₁
    let x : W ⟶ V := MorphismProperty.Over.homMk (baseChangeSnd c x₀)
      ((baseChangeSnd_comp c (⟨B.hom, rfl⟩ : SchemeHomOver (B.hom ≫ c) c) x₀).trans
        (congrArg (baseChangeSnd c) (Subtype.ext m₀.w)))
    let y' : W ⟶ V := MorphismProperty.Over.homMk (baseChangeSnd c y₀)
      ((baseChangeSnd_comp c (⟨B.hom, rfl⟩ : SchemeHomOver (B.hom ≫ c) c) y₀).trans
        (congrArg (baseChangeSnd c) (Subtype.ext m₁.w)))
    let l := pullback.lift (x ≫ e.hom) (y' ≫ e.hom)
      (hT.hom_ext ((x ≫ e.hom) ≫ f) ((y' ≫ e.hom) ≫ f))
    let m := (freeAbelianSheafYoneda Y.smallEtaleTopology).map l ≫
      (freeCechEdgeSheafIso Y.smallEtaleTopology f).inv ≫
        abelianCechFirstRelationMap Y.smallEtaleTopology hT f
    ∀ (a : Ext.{u} A.X₁ (etaleRootsOfUnitySheaf Y n) 1),
      a.comp (Ext.mk₀ (kernel.ι (etaleMultiplicativeGroupPower Y n))) (add_zero 1) =
        (Ext.mk₀ A.f).comp (invertibleModuleCohomologyPresheafH1 V' hL') (zero_add 1) →
      etaleRootsOfUnityCohomologyPresheafRestriction n W 1
          ((Ext.mk₀ m).comp a (zero_add 1)) =
        h.divisionTransitionKummerClass aj n hn hnK (postComp z x₀) (postComp z y₀)
          (h.parameterOverlapMaps_division_projection_eq aj n B z hz W₀ m₀ m₁) := by
  intro Y U _hU _hProduct V _hV V' T e hT f hV' A L hL L' hL' UZ _hUZ
    _hOverlapProduct W _hW x₀ y₀ x y' l m a hcoeff
  have hnormal : IsNormalIntegral U.left := parameterProduct_isNormalIntegral (c := c) B
  have : IsNormalIntegral V.left := hnormal
  have : IsFinite x.left := MorphismProperty.of_isPullback
    (P := @IsFinite) (isPullback_baseChangeSnd c x₀).flip (inferInstance : IsFinite m₀.left)
  have : IsFinite y'.left := MorphismProperty.of_isPullback
    (P := @IsFinite) (isPullback_baseChangeSnd c y₀).flip (inferInstance : IsFinite m₁.left)
  have hboundary : m ≫ A.f =
      (freeAbelianSheafYoneda Y.smallEtaleTopology).map (y' ≫ e.hom) -
        (freeAbelianSheafYoneda Y.smallEtaleTopology).map (x ≫ e.hom) := by
    change ((freeAbelianSheafYoneda Y.smallEtaleTopology).map l ≫
      (freeCechEdgeSheafIso Y.smallEtaleTopology f).inv ≫
        abelianCechFirstRelationMap Y.smallEtaleTopology hT f) ≫
          kernel.ι (abelianCechUnitAugmentation Y.smallEtaleTopology hT f) = _
    rw [Category.assoc, Category.assoc, abelianCechFirstRelationMap_comp,
      freeCechEdgeSheafIso_boundary, Preadditive.comp_sub,
      ← Functor.map_comp, ← Functor.map_comp, pullback.lift_snd, pullback.lift_fst]
  have : IsIso e.inv.left := inferInstanceAs
    (IsIso ((Scheme.Etale.forget Y ⋙ Over.forget Y).map e.inv))
  have : IsFinite e.inv.left := inferInstance
  let β := invertibleModuleCohomologyPresheafH1 V hL
  let β' := invertibleModuleCohomologyPresheafH1 V' hL'
  have hrestriction (t : W ⟶ V) :
      ((etaleMultiplicativeGroupSheaf Y).cohomologyPresheaf 1).map (t ≫ e.hom).op β' =
        ((etaleMultiplicativeGroupSheaf Y).cohomologyPresheaf 1).map t.op β := by
    rw [show β' = ((etaleMultiplicativeGroupSheaf Y).cohomologyPresheaf 1).map e.inv.op β
      from (invertibleModuleCohomologyPresheafH1_finiteEtale_restriction V hL e.inv).symm]
    change (((etaleMultiplicativeGroupSheaf Y).cohomologyPresheaf 1).map e.inv.op ≫
      ((etaleMultiplicativeGroupSheaf Y).cohomologyPresheaf 1).map (t ≫ e.hom).op) β = _
    rw [← Functor.map_comp, ← op_comp, Category.assoc, Iso.hom_inv_id, Category.comp_id]
  let H :
      ((freeAbelianSheafYoneda Y.smallEtaleTopology).obj W ⟶
        (freeAbelianSheafYoneda Y.smallEtaleTopology).obj V') →+
      Ext.{u} ((freeAbelianSheafYoneda Y.smallEtaleTopology).obj W)
        (etaleMultiplicativeGroupSheaf Y) 1 :=
    (Ext.postcomp β' ((freeAbelianSheafYoneda Y.smallEtaleTopology).obj W)
      (zero_add 1)).comp Ext.addEquiv₀.symm.toAddMonoidHom
  have hHsub := H.map_sub
    ((freeAbelianSheafYoneda Y.smallEtaleTopology).map (y' ≫ e.hom))
    ((freeAbelianSheafYoneda Y.smallEtaleTopology).map (x ≫ e.hom))
  have hHcompute
      (q : (freeAbelianSheafYoneda Y.smallEtaleTopology).obj W ⟶
        (freeAbelianSheafYoneda Y.smallEtaleTopology).obj V') :
      H q = (Ext.mk₀ q).comp β' (zero_add 1) := rfl
  have hcohomCompute (t : W ⟶ V') :
      (Ext.mk₀ ((freeAbelianSheafYoneda Y.smallEtaleTopology).map t)).comp β'
          (zero_add 1) =
        ((etaleMultiplicativeGroupSheaf Y).cohomologyPresheaf 1).map t.op β' := rfl
  have hraw :
      (((Sheaf.cohomologyPresheafFunctor Y.smallEtaleTopology 1).map
        (kernel.ι (etaleMultiplicativeGroupPower Y n))).app (op W))
          ((Ext.mk₀ m).comp a (zero_add 1)) =
      ((etaleMultiplicativeGroupSheaf Y).cohomologyPresheaf 1).map (y' ≫ e.hom).op β' -
        ((etaleMultiplicativeGroupSheaf Y).cohomologyPresheaf 1).map (x ≫ e.hom).op β' := by
    change ((Ext.mk₀ m).comp a (zero_add 1)).comp
      (Ext.mk₀ (kernel.ι (etaleMultiplicativeGroupPower Y n))) (add_zero 1) = _
    refine (Ext.comp_assoc_of_third_deg_zero (Ext.mk₀ m) a
      (Ext.mk₀ (kernel.ι (etaleMultiplicativeGroupPower Y n))) (zero_add 1)).trans ?_
    refine (congrArg (fun α => (Ext.mk₀ m).comp α (zero_add 1)) hcoeff).trans ?_
    refine (Ext.mk₀_comp_mk₀_assoc m A.f
      (invertibleModuleCohomologyPresheafH1 V' hL')).trans ?_
    rw [hboundary]
    exact (hHcompute _).symm.trans (hHsub.trans (congrArg₂ (· - ·)
      ((hHcompute _).trans (hcohomCompute (y' ≫ e.hom)))
      ((hHcompute _).trans (hcohomCompute (x ≫ e.hom)))))
  have hroot (t : SchemeHomOver (W₀.hom ≫ c) (B.hom ≫ c)) :
      invertibleModuleMultiplicativeGroupH1 (hL.pullback (baseChangeSnd c t)) =
        invertibleModuleMultiplicativeGroupH1
          ((h.divisionRootFamily aj n).isInvertible.pullback (baseChangeSnd c (postComp z t))) :=
    invertibleModuleMultiplicativeGroupH1_iso _ _
      ((Scheme.Modules.pullbackComp (baseChangeSnd c t) (baseChangeSnd c z)).app
        (h.divisionRootFamily aj n).L ≪≫
          (Scheme.Modules.pullbackCongr (baseChangeSnd_comp c z t)).app
            (h.divisionRootFamily aj n).L)
  have : IsIntegral ((𝟭 Scheme).obj W.left) := _hW
  let d := pullback.snd c (W₀.hom ≫ c) ≫ (W₀.hom ≫ c)
  apply (properIntegralKummerH1EquivPowerKernel d hn hnK).injective
  apply Subtype.ext
  refine (properIntegralKummerH1EquivPowerKernel_apply d hn hnK
    (etaleRootsOfUnityCohomologyPresheafRestriction n W 1
      ((Ext.mk₀ m).comp a (zero_add 1)))).trans ?_
  refine Eq.trans ?_ (properIntegralKummerH1EquivPowerKernel_apply d hn hnK
    (h.divisionTransitionKummerClass aj n hn hnK (postComp z x₀) (postComp z y₀)
      (h.parameterOverlapMaps_division_projection_eq aj n B z hz W₀ m₀ m₁))).symm
  refine (etaleRootsOfUnityCohomologyPresheafRestriction_inclusion n W 1
    ((Ext.mk₀ m).comp a (zero_add 1))).trans ?_
  refine Eq.trans ?_ (h.divisionTransitionKummerClass_inclusion aj n hn hnK
    (postComp z x₀) (postComp z y₀)
    (h.parameterOverlapMaps_division_projection_eq aj n B z hz W₀ m₀ m₁)).symm
  rw [hraw,
    hrestriction y', hrestriction x,
    invertibleModuleCohomologyPresheafH1_finiteEtale_restriction V hL y',
    invertibleModuleCohomologyPresheafH1_finiteEtale_restriction V hL x,
    map_sub, map_sub]
  let eW := etaleCohomologyPresheafRestrictionEquiv W (etaleMultiplicativeGroupSheaf Y) 1
  let uW := etaleRestrictionMultiplicativeGroupIso W.hom
  change Sheaf.H.map uW.hom 1
      (eW (eW.symm (Sheaf.H.map uW.inv 1
        (invertibleModuleMultiplicativeGroupH1 (hL.pullback y'.left))))) -
    Sheaf.H.map uW.hom 1
      (eW (eW.symm (Sheaf.H.map uW.inv 1
        (invertibleModuleMultiplicativeGroupH1 (hL.pullback x.left))))) = _
  rw [eW.apply_symm_apply, eW.apply_symm_apply,
    ← Sheaf.H.map_comp_apply, Iso.inv_hom_id, Sheaf.H.map_id_apply,
    ← Sheaf.H.map_comp_apply, Iso.inv_hom_id, Sheaf.H.map_id_apply]
  exact (congrArg₂ (· - ·) (hroot y₀) (hroot x₀)).trans
    (h.divisionTransitionH1_eq_rootDifference aj n (postComp z x₀) (postComp z y₀)).symm

include hz hy in
omit [IsFinite y] [Etale y] in
/-- The class supplied by actual root descent restricts, on each
integral finite parameter overlap, to the original Kummer class of
the actual division transition family. This remains true on an
isomorphic covering object, with the original root pulled back along
the inverse isomorphism and with any actual terminal object. -/
theorem divisionRootDescent_overlap_of_iso
    (hn : 0 < n) (hnK : IsUnit (n : K)) :
    let Y := pullback c c
    let U := diagonalParameterProductCover c B
    let hU : IsIntegral U.left :=
      isIntegral_pullback_of_smooth_of_isAlgClosed (X := C) (Y := B.left) c (B.hom ≫ c)
    let : IsIntegral (pullback c (B.hom ≫ c)) := hU
    let V := (finiteEtaleInclusion Y).obj U
    let : IsIntegral V.left := hU
    ∀ {V' T : Y.Etale} (e : V ≅ V') (hT : IsTerminal T) (f : V' ⟶ T),
    let _ : IsIntegral V'.left := by
      have : IsIso e.hom.left := inferInstanceAs
        (IsIso ((Scheme.Etale.forget Y ⋙ Over.forget Y).map e.hom))
      exact IsIntegral.of_isIso e.hom.left
    let A := abelianCechAugmentationSequence Y.smallEtaleTopology hT f
    let L := (Scheme.Modules.pullback (baseChangeSnd c z)).obj (h.divisionRootFamily aj n).L
    let hL := (h.divisionRootFamily aj n).isInvertible.pullback (baseChangeSnd c z)
    let _ := (Scheme.Modules.pullback e.inv.left).obj L
    let hL' := hL.pullback e.inv.left
    let BZ : FiniteEtale C := FiniteEtale.mk (Z.hom ≫ B.hom)
    let : IsIntegral BZ.left := inferInstanceAs (IsIntegral Z.left)
    let UZ := diagonalParameterProductCover c BZ
    let hUZ : IsIntegral UZ.left :=
      isIntegral_pullback_of_smooth_of_isAlgClosed (X := C) (Y := Z.left) c
        ((Z.hom ≫ B.hom) ≫ c)
    let : IsIntegral (pullback c ((Z.hom ≫ B.hom) ≫ c)) := hUZ
    let W := (finiteEtaleInclusion Y).obj UZ
    let : IsIntegral W.left := hUZ
    let x₀ := parameterOverlapFirst (c := c) B Z
    let y₀ := parameterOverlapSecond (c := c) B Z y hy
    let x : W ⟶ V := MorphismProperty.Over.homMk (baseChangeSnd c x₀)
      (baseChangeSnd_comp c (⟨B.hom, rfl⟩ : SchemeHomOver (B.hom ≫ c) c) x₀)
    let y' : W ⟶ V := MorphismProperty.Over.homMk (baseChangeSnd c y₀)
      ((baseChangeSnd_comp c (⟨B.hom, rfl⟩ : SchemeHomOver (B.hom ≫ c) c) y₀).trans
        (congrArg (baseChangeSnd c) (Subtype.ext hy)))
    let l := pullback.lift (x ≫ e.hom) (y' ≫ e.hom)
      (hT.hom_ext ((x ≫ e.hom) ≫ f) ((y' ≫ e.hom) ≫ f))
    let m := (freeAbelianSheafYoneda Y.smallEtaleTopology).map l ≫
      (freeCechEdgeSheafIso Y.smallEtaleTopology f).inv ≫
        abelianCechFirstRelationMap Y.smallEtaleTopology hT f
    ∀ (a : Ext.{u} A.X₁ (etaleRootsOfUnitySheaf Y n) 1),
      a.comp (Ext.mk₀ (kernel.ι (etaleMultiplicativeGroupPower Y n))) (add_zero 1) =
        (Ext.mk₀ A.f).comp (invertibleModuleCohomologyPresheafH1 V' hL') (zero_add 1) →
      etaleRootsOfUnityCohomologyPresheafRestriction n W 1
          ((Ext.mk₀ m).comp a (zero_add 1)) =
        h.divisionTransitionKummerClass aj n hn hnK (postComp z x₀) (postComp z y₀)
          (h.parameterOverlap_division_projection_eq aj n B z hz Z y hy) := by
  intro Y U _hU _hProduct V _hV V' T e hT f hV' A L hL L' hL' BZ _hBZ UZ _hUZ
    _hOverlapProduct W _hW x₀ y₀ x y' l m a hcoeff
  let m₀ : BZ ⟶ B := MorphismProperty.Over.homMk Z.hom rfl
  let m₁ : BZ ⟶ B := MorphismProperty.Over.homMk y hy
  exact h.divisionRootDescent_overlap_maps_of_iso aj n B z hz BZ m₀ m₁ hn hnK
    e hT f a hcoeff

include hz hy in
omit [IsFinite y] [Etale y] in
/-- The class supplied by actual root descent restricts, on each
integral finite parameter overlap, to the original Kummer class of
the actual division transition family. Its two lifts and its original
coefficient inclusion are retained explicitly. -/
theorem divisionRootDescent_overlap
    (hn : 0 < n) (hnK : IsUnit (n : K)) :
    let Y := pullback c c
    let U := diagonalParameterProductCover c B
    let hU : IsIntegral U.left :=
      isIntegral_pullback_of_smooth_of_isAlgClosed (X := C) (Y := B.left) c (B.hom ≫ c)
    let : IsIntegral (pullback c (B.hom ≫ c)) := hU
    let V := (finiteEtaleInclusion Y).obj U
    let : IsIntegral V.left := hU
    let T : Y.Etale := Scheme.Etale.mk (𝟙 Y)
    let hT : IsTerminal T := MorphismProperty.Over.mkIdTerminal
      (show MorphismProperty Scheme.{u} from @Etale) Y
    let f := finiteEtaleCoverBaseMap Y U
    let A := abelianCechAugmentationSequence Y.smallEtaleTopology hT f
    let _ := (Scheme.Modules.pullback (baseChangeSnd c z)).obj (h.divisionRootFamily aj n).L
    let hL := (h.divisionRootFamily aj n).isInvertible.pullback (baseChangeSnd c z)
    let BZ : FiniteEtale C := FiniteEtale.mk (Z.hom ≫ B.hom)
    let : IsIntegral BZ.left := inferInstanceAs (IsIntegral Z.left)
    let UZ := diagonalParameterProductCover c BZ
    let hUZ : IsIntegral UZ.left :=
      isIntegral_pullback_of_smooth_of_isAlgClosed (X := C) (Y := Z.left) c
        ((Z.hom ≫ B.hom) ≫ c)
    let : IsIntegral (pullback c ((Z.hom ≫ B.hom) ≫ c)) := hUZ
    let W := (finiteEtaleInclusion Y).obj UZ
    let : IsIntegral W.left := hUZ
    let x₀ := parameterOverlapFirst (c := c) B Z
    let y₀ := parameterOverlapSecond (c := c) B Z y hy
    let x : W ⟶ V := MorphismProperty.Over.homMk (baseChangeSnd c x₀)
      (baseChangeSnd_comp c (⟨B.hom, rfl⟩ : SchemeHomOver (B.hom ≫ c) c) x₀)
    let y' : W ⟶ V := MorphismProperty.Over.homMk (baseChangeSnd c y₀)
      ((baseChangeSnd_comp c (⟨B.hom, rfl⟩ : SchemeHomOver (B.hom ≫ c) c) y₀).trans
        (congrArg (baseChangeSnd c) (Subtype.ext hy)))
    let l := pullback.lift x y' (hT.hom_ext (x ≫ f) (y' ≫ f))
    let m := (freeAbelianSheafYoneda Y.smallEtaleTopology).map l ≫
      (freeCechEdgeSheafIso Y.smallEtaleTopology f).inv ≫
        abelianCechFirstRelationMap Y.smallEtaleTopology hT f
    ∀ (a : Ext.{u} A.X₁ (etaleRootsOfUnitySheaf Y n) 1),
      a.comp (Ext.mk₀ (kernel.ι (etaleMultiplicativeGroupPower Y n))) (add_zero 1) =
        (Ext.mk₀ A.f).comp (invertibleModuleCohomologyPresheafH1 V hL) (zero_add 1) →
      etaleRootsOfUnityCohomologyPresheafRestriction n W 1
          ((Ext.mk₀ m).comp a (zero_add 1)) =
        h.divisionTransitionKummerClass aj n hn hnK (postComp z x₀) (postComp z y₀)
          (h.parameterOverlap_division_projection_eq aj n B z hz Z y hy) := by
  intro Y U _hU _hProduct V _hV T hT f A L hL BZ _hBZ UZ _hUZ _hOverlapProduct
    W _hW x₀ y₀ x y' l m a hcoeff
  have hnormal : IsNormalIntegral U.left := parameterProduct_isNormalIntegral (c := c) B
  have : IsNormalIntegral V.left := hnormal
  have : IsFinite (𝟙 V : V ⟶ V).left := by
    change IsFinite (𝟙 V.left)
    infer_instance
  have hβ :
      invertibleModuleCohomologyPresheafH1 V hL =
        invertibleModuleCohomologyPresheafH1 V (hL.pullback (𝟙 V.left)) := by
    have hid := ConcreteCategory.congr_hom
      (((etaleMultiplicativeGroupSheaf Y).cohomologyPresheaf 1).map_id (op V))
      (invertibleModuleCohomologyPresheafH1 V hL)
    exact (hid.trans (ConcreteCategory.id_apply _)).symm.trans
      (invertibleModuleCohomologyPresheafH1_finiteEtale_restriction V hL (𝟙 V))
  have hcoeff' :
      a.comp (Ext.mk₀ (kernel.ι (etaleMultiplicativeGroupPower Y n))) (add_zero 1) =
        (Ext.mk₀ A.f).comp
          (invertibleModuleCohomologyPresheafH1 V (hL.pullback (𝟙 V.left))) (zero_add 1) :=
    hcoeff.trans (congrArg (fun β => (Ext.mk₀ A.f).comp β (zero_add 1)) hβ)
  have hh := h.divisionRootDescent_overlap_of_iso aj n B z hz Z y hy hn hnK
    (Iso.refl V) hT f a hcoeff'
  have hlift :
      pullback.lift (x ≫ 𝟙 V) (y' ≫ 𝟙 V)
          (hT.hom_ext ((x ≫ 𝟙 V) ≫ f) ((y' ≫ 𝟙 V) ≫ f)) = l := by
    apply pullback.hom_ext
    · exact (pullback.lift_fst (x ≫ 𝟙 V) (y' ≫ 𝟙 V)
        (hT.hom_ext ((x ≫ 𝟙 V) ≫ f) ((y' ≫ 𝟙 V) ≫ f))).trans
        ((Category.comp_id x).trans
          (pullback.lift_fst x y' (hT.hom_ext (x ≫ f) (y' ≫ f))).symm)
    · exact (pullback.lift_snd (x ≫ 𝟙 V) (y' ≫ 𝟙 V)
        (hT.hom_ext ((x ≫ 𝟙 V) ≫ f) ((y' ≫ 𝟙 V) ≫ f))).trans
        ((Category.comp_id y').trans
          (pullback.lift_snd x y' (hT.hom_ext (x ≫ f) (y' ≫ f))).symm)
  exact (congrArg (fun k : W ⟶ pullback f f =>
    etaleRootsOfUnityCohomologyPresheafRestriction n W 1
      ((Ext.mk₀ ((freeAbelianSheafYoneda Y.smallEtaleTopology).map k ≫
        (freeCechEdgeSheafIso Y.smallEtaleTopology f).inv ≫
          abelianCechFirstRelationMap Y.smallEtaleTopology hT f)).comp a (zero_add 1)))
    hlift).symm.trans hh

end AlgebraicGeometry.RelPicard.RepresentsRelSubPic
