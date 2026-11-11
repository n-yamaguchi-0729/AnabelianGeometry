/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.EtaleCohomology.Classical.AbelianSheafFunctors
public import Nyll.EtaleCohomology.Classical.AbelianRestrictionPullback
public import Nyll.EtaleCohomology.Classical.AffineGenericUnitQuotient
public import Nyll.EtaleCohomology.Classical.EtaleRestriction
public import Nyll.EtaleCohomology.Classical.GenericUnitRationalSections
public import Nyll.EtaleCohomology.Classical.MultiplicativeGroup
public import Nyll.EtaleCohomology.Classical.MultiplicativeGroupPushforward
public import Nyll.EtaleCohomology.Classical.PullbackCohomology
public import Nyll.EtaleCohomology.Sites.BaseChange
public import Nyll.EtaleCohomology.Sites.GaloisSections
public import Nyll.EtaleFundamentalGroups.FiniteEtale.FunctionField
public import Nyll.EtaleFundamentalGroups.FiniteEtale.Integral
public import Nyll.SchemeTheory.FunctionFields.GenericFieldSourceNaturality
public import Nyll.SchemeTheory.Normalization.FiniteNormalFormalSplitting
public import Mathlib.Algebra.Group.Units.Equiv
public import Mathlib.AlgebraicGeometry.FunctionField
public import Mathlib.AlgebraicGeometry.Stalk
public import Mathlib.Algebra.Homology.ShortComplex.Basic
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Basic

/-!
# Actual generic units on a connected finite étale cover

The original generic-point square of a connected finite étale cover is
cartesian. Its canonical function-field map supplies restriction of the
original generic-unit sequence, including both original coefficient maps.
Evaluating the same square identifies its sections with units of the
cover's function field, equivariantly for actual deck transformations.
-/

@[expose] public section

noncomputable section

universe u

open AlgebraicGeometry CategoryTheory Limits Opposite TopologicalSpace
open CategoryTheory.PreGaloisCategory EtaleFundamentalGroups

namespace EtaleCohomology

variable {X : Scheme.{u}} [IsIntegral X] [IsNormalIntegral X]
  (Y : FiniteEtale X) [IsConnected Y]

/-- The actual function field of a connected finite étale cover is its
generic fibre, with the canonical map of function fields. -/
theorem finiteEtaleGenericPointIsPullback :
    let _ : IsIntegral Y.left := isIntegral_left_of_isConnected_finiteEtale Y
    IsPullback (Y.left.fromSpecStalk (genericPoint Y.left))
      (Spec.map (CommRingCat.ofHom
        ((show Y.left ⟶ X from Y.hom).functionFieldMap
          (finiteEtale_hom_denseRange_of_isConnected Y))))
      Y.hom (X.fromSpecStalk (genericPoint X)) := by
  intro hY
  let _ : Algebra X.functionField Y.left.functionField := finiteEtaleFunctionFieldAlgebra Y
  have : FiniteDimensional X.functionField Y.left.functionField :=
    finiteDimensional_functionField_of_finiteEtale_isConnected Y
  have : IsNormalIntegral Y.left := isNormalIntegral_left_of_isConnected_finiteEtale Y
  have : IsFiniteEtale (show Y.left ⟶ X from Y.hom) := Y.prop
  exact (show Y.left ⟶ X from Y.hom).isPullback_finiteNormal_generic
    (Spec_functionFieldMap_fromSpecStalk (show Y.left ⟶ X from Y.hom)
      (finiteEtale_hom_denseRange_of_isConnected Y)).symm

/-- Restriction of the original direct image of generic units to the
cover is the direct image from its own actual generic point. -/
def etaleRestrictionFiniteGenericUnitPushforwardIso :
    let _ : IsIntegral Y.left := isIntegral_left_of_isConnected_finiteEtale Y
    (etaleRestriction Y.hom AddCommGrpCat.{u}).obj
        ((etaleAbelianPushforward (X.fromSpecStalk (genericPoint X))).obj
          (etaleMultiplicativeGroupSheaf (Spec X.functionField))) ≅
      (etaleAbelianPushforward (Y.left.fromSpecStalk (genericPoint Y.left))).obj
        (etaleMultiplicativeGroupSheaf (Spec Y.left.functionField)) := by
  intro hY
  let g : Spec (CommRingCat.of Y.left.functionField) ⟶
      Spec (CommRingCat.of X.functionField) := Spec.map (CommRingCat.ofHom
    ((show Y.left ⟶ X from Y.hom).functionFieldMap (finiteEtale_hom_denseRange_of_isConnected Y)))
  have : Etale g := MorphismProperty.of_isPullback (P := @Etale)
    (finiteEtaleGenericPointIsPullback Y) Y.prop.toEtale
  exact etaleRestrictionMultiplicativeGroupPushforwardIsoOfIsPullback Y.hom
    (X.fromSpecStalk (genericPoint X)) (Y.left.fromSpecStalk (genericPoint Y.left))
    g (finiteEtaleGenericPointIsPullback Y)

/-- The finite-cover comparison preserves the original inclusion of
regular units into generic units. -/
theorem etaleRestrictionFiniteGenericUnitPushforwardIso_unit :
    let _ : IsIntegral Y.left := isIntegral_left_of_isConnected_finiteEtale Y
    (etaleRestriction Y.hom AddCommGrpCat.{u}).map
        (etaleMultiplicativeGroupToPushforward (X.fromSpecStalk (genericPoint X))) ≫
      (etaleRestrictionFiniteGenericUnitPushforwardIso Y).hom =
    (etaleRestrictionMultiplicativeGroupIso Y.hom).hom ≫
      etaleMultiplicativeGroupToPushforward (Y.left.fromSpecStalk (genericPoint Y.left)) := by
  intro hY
  let g : Spec (CommRingCat.of Y.left.functionField) ⟶
      Spec (CommRingCat.of X.functionField) := Spec.map (CommRingCat.ofHom
    ((show Y.left ⟶ X from Y.hom).functionFieldMap (finiteEtale_hom_denseRange_of_isConnected Y)))
  have : Etale g := MorphismProperty.of_isPullback (P := @Etale)
    (finiteEtaleGenericPointIsPullback Y) Y.prop.toEtale
  exact etaleRestrictionMultiplicativeGroupToPushforwardOfIsPullback Y.hom
    (X.fromSpecStalk (genericPoint X)) (Y.left.fromSpecStalk (genericPoint Y.left))
    g (finiteEtaleGenericPointIsPullback Y)

/-- Restriction preserves the actual quotient of generic units by
regular units on a connected finite étale cover. -/
def etaleRestrictionFiniteGenericUnitQuotientIso :
    let _ : IsIntegral Y.left := isIntegral_left_of_isConnected_finiteEtale Y
    (etaleRestriction Y.hom AddCommGrpCat.{u}).obj (etaleGenericUnitQuotient X) ≅
      etaleGenericUnitQuotient Y.left := by
  intro hY
  let g : Spec (CommRingCat.of Y.left.functionField) ⟶
      Spec (CommRingCat.of X.functionField) := Spec.map (CommRingCat.ofHom
    ((show Y.left ⟶ X from Y.hom).functionFieldMap (finiteEtale_hom_denseRange_of_isConnected Y)))
  have : Etale g := MorphismProperty.of_isPullback (P := @Etale)
    (finiteEtaleGenericPointIsPullback Y) Y.prop.toEtale
  exact etaleRestrictionUnitQuotientIsoOfIsPullback Y.hom
    (X.fromSpecStalk (genericPoint X)) (Y.left.fromSpecStalk (genericPoint Y.left))
    g (finiteEtaleGenericPointIsPullback Y)

/-- The finite-cover quotient comparison retains the original
cokernel projection from generic units. -/
theorem etaleRestrictionFiniteGenericUnitQuotientIso_π :
    let _ : IsIntegral Y.left := isIntegral_left_of_isConnected_finiteEtale Y
    (etaleRestriction Y.hom AddCommGrpCat.{u}).map
        (cokernel.π (etaleMultiplicativeGroupToPushforward
          (X.fromSpecStalk (genericPoint X)))) ≫
      (etaleRestrictionFiniteGenericUnitQuotientIso Y).hom =
    (etaleRestrictionFiniteGenericUnitPushforwardIso Y).hom ≫
      cokernel.π (etaleMultiplicativeGroupToPushforward
        (Y.left.fromSpecStalk (genericPoint Y.left))) := by
  intro hY
  let g : Spec (CommRingCat.of Y.left.functionField) ⟶
      Spec (CommRingCat.of X.functionField) := Spec.map (CommRingCat.ofHom
    ((show Y.left ⟶ X from Y.hom).functionFieldMap (finiteEtale_hom_denseRange_of_isConnected Y)))
  have : Etale g := MorphismProperty.of_isPullback (P := @Etale)
    (finiteEtaleGenericPointIsPullback Y) Y.prop.toEtale
  exact etaleRestrictionUnitQuotientIsoOfIsPullback_π Y.hom
    (X.fromSpecStalk (genericPoint X)) (Y.left.fromSpecStalk (genericPoint Y.left))
    g (finiteEtaleGenericPointIsPullback Y)

/-- The original generic-unit short complexes are related by actual
finite étale pullback, including all three coefficient maps. -/
def finiteGenericUnitPullbackComplex [IsIntegral Y.left] :
    (etaleGenericUnitShortComplex X).map (etaleAbelianPullback Y.hom) ⟶
      etaleGenericUnitShortComplex Y.left := by
  let S := etaleGenericUnitShortComplex X
  let R := etaleRestriction Y.hom AddCommGrpCat.{u}
  let φ : S.map R ⟶ etaleGenericUnitShortComplex Y.left :=
    { τ₁ := (etaleRestrictionMultiplicativeGroupIso Y.hom).hom
      τ₂ := (etaleRestrictionFiniteGenericUnitPushforwardIso Y).hom
      τ₃ := (etaleRestrictionFiniteGenericUnitQuotientIso Y).hom
      comm₁₂ := (etaleRestrictionFiniteGenericUnitPushforwardIso_unit Y).symm
      comm₂₃ := (etaleRestrictionFiniteGenericUnitQuotientIso_π Y).symm }
  exact S.mapNatTrans (etaleAbelianPullbackRestrictionIso Y.hom).hom ≫ φ

/-- The native H⁰ pullback of the original generic-unit quotient,
using the same map of actual short complexes. -/
def finiteGenericUnitH0Pullback [IsIntegral Y.left] :
    Sheaf.H.{u} (etaleGenericUnitQuotient X) 0 →+
      Sheaf.H.{u} (etaleGenericUnitQuotient Y.left) 0 :=
  (Sheaf.H.map (finiteGenericUnitPullbackComplex Y).τ₃ 0).comp
    (etaleAbelianCohomologyPullbackMap Y.hom (etaleGenericUnitQuotient X) 0)

/-- The finite-cover restriction comparison sends the original
rational unit to its image under the canonical function-field map. -/
theorem etaleRestrictionFiniteGenericUnitPushforwardIso_rationalUnit
    (V : Y.left.Etale) (a : Additive X.functionFieldˣ) :
    let _ : IsIntegral Y.left := isIntegral_left_of_isConnected_finiteEtale Y
    (etaleRestrictionFiniteGenericUnitPushforwardIso Y).hom.hom.app (op V)
        (rationalUnitDirectImageSection (X.fromSpecStalk (genericPoint X))
          ((etalePostcompose Y.hom).obj V) a) =
      rationalUnitDirectImageSection (Y.left.fromSpecStalk (genericPoint Y.left)) V
        (Additive.ofMul (Units.map
          ((show Y.left ⟶ X from Y.hom).functionFieldMap
            (finiteEtale_hom_denseRange_of_isConnected Y)).toMonoidHom
          a.toMul)) := by
  intro hY
  let φ : X.functionField →+* Y.left.functionField :=
    (show Y.left ⟶ X from Y.hom).functionFieldMap
      (finiteEtale_hom_denseRange_of_isConnected Y)
  have hg : Etale (Spec.map (CommRingCat.ofHom φ)) :=
    MorphismProperty.of_isPullback (P := @Etale)
      (finiteEtaleGenericPointIsPullback Y) Y.prop.toEtale
  exact @etaleRestrictionUnitPushforwardIsoOfIsPullback_rationalUnit
    X.functionField Y.left.functionField inferInstance inferInstance
    X Y.left Y.hom Y.prop.toEtale (X.fromSpecStalk (genericPoint X))
    (Y.left.fromSpecStalk (genericPoint Y.left)) φ hg
    (finiteEtaleGenericPointIsPullback Y) V a

/-- The finite-cover quotient comparison retains the same rational
representative in the cover's function field. -/
theorem etaleRestrictionFiniteGenericUnitQuotientIso_rationalUnit
    (V : Y.left.Etale) (a : Additive X.functionFieldˣ) :
    let _ : IsIntegral Y.left := isIntegral_left_of_isConnected_finiteEtale Y
    (etaleRestrictionFiniteGenericUnitQuotientIso Y).hom.hom.app (op V)
        (genericPointRationalUnitQuotientSection X ((etalePostcompose Y.hom).obj V) a) =
      genericPointRationalUnitQuotientSection Y.left V
        (Additive.ofMul (Units.map
          ((show Y.left ⟶ X from Y.hom).functionFieldMap
            (finiteEtale_hom_denseRange_of_isConnected Y)).toMonoidHom
          a.toMul)) := by
  intro hY
  have h := congrArg (fun z => z.hom.app (op V))
    (etaleRestrictionFiniteGenericUnitQuotientIso_π Y)
  have hs := ConcreteCategory.congr_hom h
    (rationalUnitDirectImageSection (X.fromSpecStalk (genericPoint X))
      ((etalePostcompose Y.hom).obj V) a)
  change _ = (cokernel.π (etaleMultiplicativeGroupToPushforward
    (Y.left.fromSpecStalk (genericPoint Y.left)))).hom.app (op V)
      ((etaleRestrictionFiniteGenericUnitPushforwardIso Y).hom.hom.app (op V)
        (rationalUnitDirectImageSection (X.fromSpecStalk (genericPoint X))
          ((etalePostcompose Y.hom).obj V) a)) at hs
  rw [etaleRestrictionFiniteGenericUnitPushforwardIso_rationalUnit] at hs
  exact hs

/-- Sections of the original generic-unit sheaf at the actual cover
are units of that cover's function field. -/
def finiteEtaleGenericUnitSectionsEquiv :
    let _ : IsIntegral Y.left := isIntegral_left_of_isConnected_finiteEtale Y
    ((etaleAbelianPushforward (X.fromSpecStalk (genericPoint X))).obj
      (etaleMultiplicativeGroupSheaf (Spec X.functionField))).obj.obj
        (op ((finiteEtaleInclusion X).obj Y)) ≃+ Additive Y.left.functionFieldˣ := by
  intro hY
  let e : Spec (CommRingCat.of Y.left.functionField) ≅
      pullback Y.hom (X.fromSpecStalk (genericPoint X)) :=
    (finiteEtaleGenericPointIsPullback Y).isoPullback
  let eΓ : Γ(pullback Y.hom (X.fromSpecStalk (genericPoint X)), ⊤) ≅
      CommRingCat.of Y.left.functionField :=
    (Scheme.Γ.mapIso e.op) ≪≫ Scheme.ΓSpecIso (CommRingCat.of Y.left.functionField)
  exact (Units.mapEquiv eΓ.commRingCatIsoToRingEquiv.toMulEquiv).toAdditive

/-- In function-field coordinates the original section is evaluated
by the same cartesian generic-point isomorphism. -/
theorem finiteEtaleGenericUnitSectionsEquiv_apply :
    let _ : IsIntegral Y.left := isIntegral_left_of_isConnected_finiteEtale Y
    ∀ s, finiteEtaleGenericUnitSectionsEquiv Y s =
      Additive.ofMul (Units.map
        (((finiteEtaleGenericPointIsPullback Y).isoPullback.hom.appTop ≫
          (Scheme.ΓSpecIso (CommRingCat.of Y.left.functionField)).hom).hom.toMonoidHom)
        s.toMul) := by
  intro hY s
  rfl

/-- The same section equivalence sends base rational units to their
actual function-field images on the finite cover. -/
theorem finiteEtaleGenericUnitSectionsEquiv_rationalUnit (a : Additive X.functionFieldˣ) :
    let _ : IsIntegral Y.left := isIntegral_left_of_isConnected_finiteEtale Y
    finiteEtaleGenericUnitSectionsEquiv Y
        (rationalUnitDirectImageSection (X.fromSpecStalk (genericPoint X))
          ((finiteEtaleInclusion X).obj Y) a) =
      Additive.ofMul (Units.map
        ((show Y.left ⟶ X from Y.hom).functionFieldMap
          (finiteEtale_hom_denseRange_of_isConnected Y)).toMonoidHom
        a.toMul) := by
  intro hY
  let f : Y.left ⟶ X := Y.hom
  let j : Spec (CommRingCat.of X.functionField) ⟶ X :=
    X.fromSpecStalk (genericPoint X)
  let p : Spec (CommRingCat.of Y.left.functionField) ⟶ Y.left :=
    Y.left.fromSpecStalk (genericPoint Y.left)
  let φ : X.functionField →+* Y.left.functionField :=
    (show Y.left ⟶ X from Y.hom).functionFieldMap
      (finiteEtale_hom_denseRange_of_isConnected Y)
  have H : IsPullback p (Spec.map (CommRingCat.ofHom φ)) f j :=
    finiteEtaleGenericPointIsPullback Y
  let e : Spec (CommRingCat.of Y.left.functionField) ≅ pullback f j := H.isoPullback
  let γX : Γ(Spec (CommRingCat.of X.functionField), ⊤) ≅
      CommRingCat.of X.functionField := Scheme.ΓSpecIso (CommRingCat.of X.functionField)
  let γY : Γ(Spec (CommRingCat.of Y.left.functionField), ⊤) ≅
      CommRingCat.of Y.left.functionField := Scheme.ΓSpecIso (CommRingCat.of Y.left.functionField)
  have hesnd : e.hom ≫ pullback.snd f j = Spec.map (CommRingCat.ofHom φ) :=
    H.isoPullback_hom_snd
  have hnat : (Spec.map (CommRingCat.ofHom φ)).appTop ≫ γY.hom =
      γX.hom ≫ CommRingCat.ofHom φ :=
    Scheme.ΓSpecIso_naturality (CommRingCat.ofHom φ)
  have hr : (γX.inv ≫ (pullback.snd f j).appTop) ≫
      (e.hom.appTop ≫ γY.hom) = CommRingCat.ofHom φ := by
    calc
      _ = γX.inv ≫ ((e.hom ≫ pullback.snd f j).appTop ≫ γY.hom) := by
        simp only [Scheme.Hom.comp_appTop, Category.assoc]
      _ = γX.inv ≫ ((Spec.map (CommRingCat.ofHom φ)).appTop ≫ γY.hom) :=
        congrArg (fun q : Spec (CommRingCat.of Y.left.functionField) ⟶
          Spec (CommRingCat.of X.functionField) => γX.inv ≫ (q.appTop ≫ γY.hom)) hesnd
      _ = γX.inv ≫ (γX.hom ≫ CommRingCat.ofHom φ) :=
        congrArg (fun q => γX.inv ≫ q) hnat
      _ = CommRingCat.ofHom φ := γX.inv_hom_id_assoc _
  have hs := finiteEtaleGenericUnitSectionsEquiv_apply Y
    (rationalUnitDirectImageSection (X.fromSpecStalk (genericPoint X))
      ((finiteEtaleInclusion X).obj Y) a)
  refine hs.trans ?_
  apply Additive.toMul.injective
  apply Units.ext
  exact ConcreteCategory.congr_hom hr a.toMul.val

/-- Actual deck pullback on generic-unit sections is the original
pullback on the cover's function field. -/
theorem finiteEtaleGenericUnitSectionsEquiv_deck (σ : Aut Y) :
    let _ : IsIntegral Y.left := isIntegral_left_of_isConnected_finiteEtale Y
    ∀ s, finiteEtaleGenericUnitSectionsEquiv Y
        (((etaleAbelianPushforward (X.fromSpecStalk (genericPoint X))).obj
          (etaleMultiplicativeGroupSheaf (Spec X.functionField))).obj.map
            ((finiteEtaleInclusion X).map σ.asIso.hom).op s) =
      Additive.ofMul (Units.map
        (σ.asIso.hom.left.functionFieldMap σ.asIso.hom.left.surjective.denseRange).toMonoidHom
        (finiteEtaleGenericUnitSectionsEquiv Y s).toMul) := by
  intro hY s
  let f : Y.left ⟶ X := Y.hom
  let j : Spec (CommRingCat.of X.functionField) ⟶ X :=
    X.fromSpecStalk (genericPoint X)
  let p : Spec (CommRingCat.of Y.left.functionField) ⟶ Y.left :=
    Y.left.fromSpecStalk (genericPoint Y.left)
  let φ₀ : X.functionField →+* Y.left.functionField :=
    (show Y.left ⟶ X from Y.hom).functionFieldMap
      (finiteEtale_hom_denseRange_of_isConnected Y)
  have H : IsPullback p (Spec.map (CommRingCat.ofHom φ₀)) f j :=
    finiteEtaleGenericPointIsPullback Y
  let e : Spec (CommRingCat.of Y.left.functionField) ≅ pullback f j := H.isoPullback
  let γY : Γ(Spec (CommRingCat.of Y.left.functionField), ⊤) ≅
      CommRingCat.of Y.left.functionField := Scheme.ΓSpecIso (CommRingCat.of Y.left.functionField)
  let k : pullback f j ⟶ pullback f j :=
    ((etaleBaseChange j).map ((finiteEtaleInclusion X).map σ.asIso.hom)).left
  let σY : Y.left ⟶ Y.left := σ.asIso.hom.left
  have hσ : DenseRange σY := σ.asIso.hom.left.surjective.denseRange
  let φ : Y.left.functionField →+* Y.left.functionField := σY.functionFieldMap hσ
  let φSpec : Spec (CommRingCat.of Y.left.functionField) ⟶
      Spec (CommRingCat.of Y.left.functionField) := Spec.map (CommRingCat.ofHom φ)
  have hk : k ≫ pullback.fst f j = pullback.fst f j ≫ σY := by
    dsimp only [k, etaleBaseChange]
    exact pullback.lift_fst _ _ _
  have hefst : e.hom ≫ pullback.fst f j = p := H.isoPullback_hom_fst
  have hj : Mono j := inferInstanceAs (Mono (X.fromSpecStalk (genericPoint X)))
  have : Mono (pullback.fst f j) := inferInstance
  have he : e.hom ≫ k = φSpec ≫ e.hom := by
    apply (cancel_mono (pullback.fst f j)).mp
    rw [Category.assoc, hk, ← Category.assoc, hefst, Category.assoc, hefst]
    exact (Spec_functionFieldMap_fromSpecStalk σY hσ).symm
  have hnat : φSpec.appTop ≫ γY.hom = γY.hom ≫ CommRingCat.ofHom φ :=
    Scheme.ΓSpecIso_naturality (CommRingCat.ofHom φ)
  have hr : k.appTop ≫ (e.hom.appTop ≫ γY.hom) =
      (e.hom.appTop ≫ γY.hom) ≫ CommRingCat.ofHom φ := by
    calc
      _ = (e.hom ≫ k).appTop ≫ γY.hom := by
        simp only [Scheme.Hom.comp_appTop, Category.assoc]
      _ = (φSpec ≫ e.hom).appTop ≫ γY.hom :=
        congrArg (fun q : Spec (CommRingCat.of Y.left.functionField) ⟶
          pullback f j => q.appTop ≫ γY.hom) he
      _ = e.hom.appTop ≫ (φSpec.appTop ≫ γY.hom) := by
        simp only [Scheme.Hom.comp_appTop, Category.assoc]
      _ = e.hom.appTop ≫ (γY.hom ≫ CommRingCat.ofHom φ) :=
        congrArg (fun q => e.hom.appTop ≫ q) hnat
      _ = (e.hom.appTop ≫ γY.hom) ≫ CommRingCat.ofHom φ :=
        (Category.assoc _ _ _).symm
  let mapφ : Additive Y.left.functionFieldˣ → Additive Y.left.functionFieldˣ :=
    fun z => Additive.ofMul (Units.map φ.toMonoidHom z.toMul)
  have hvalue :
      Additive.ofMul (Units.map (e.hom.appTop ≫ γY.hom).hom.toMonoidHom
        (Units.map k.appTop.hom.toMonoidHom s.toMul)) =
      mapφ (Additive.ofMul (Units.map (e.hom.appTop ≫ γY.hom).hom.toMonoidHom s.toMul)) := by
    apply Additive.toMul.injective
    apply Units.ext
    exact ConcreteCategory.congr_hom hr s.toMul.val
  have hs₀ := finiteEtaleGenericUnitSectionsEquiv_apply Y
    (((etaleAbelianPushforward (X.fromSpecStalk (genericPoint X))).obj
      (etaleMultiplicativeGroupSheaf (Spec X.functionField))).obj.map
        ((finiteEtaleInclusion X).map σ.asIso.hom).op s)
  have hs₁ := finiteEtaleGenericUnitSectionsEquiv_apply Y s
  exact hs₀.trans (hvalue.trans (congrArg mapφ hs₁).symm)

/-- The original inclusion of a regular unit is evaluated by its actual
germ at the generic point of the same covering scheme. -/
theorem finiteEtaleGenericUnitSectionsEquiv_regularUnit
    (s : (etaleMultiplicativeGroupSheaf X).obj.obj
      (op ((finiteEtaleInclusion X).obj Y))) :
    let _ : IsIntegral Y.left := isIntegral_left_of_isConnected_finiteEtale Y
    finiteEtaleGenericUnitSectionsEquiv Y
        ((etaleGenericUnitShortComplex X).f.hom.app
          (op ((finiteEtaleInclusion X).obj Y)) s) =
      Additive.ofMul (Units.map
        (Y.left.presheaf.germ ⊤ (genericPoint Y.left) trivial).hom.toMonoidHom
        s.toMul) := by
  intro hY
  let f : Y.left ⟶ X := Y.hom
  let j : Spec (CommRingCat.of X.functionField) ⟶ X :=
    X.fromSpecStalk (genericPoint X)
  let p : Spec (CommRingCat.of Y.left.functionField) ⟶ Y.left :=
    Y.left.fromSpecStalk (genericPoint Y.left)
  let φ : X.functionField →+* Y.left.functionField :=
    (show Y.left ⟶ X from Y.hom).functionFieldMap
      (finiteEtale_hom_denseRange_of_isConnected Y)
  have H : IsPullback p (Spec.map (CommRingCat.ofHom φ)) f j :=
    finiteEtaleGenericPointIsPullback Y
  let e : Spec (CommRingCat.of Y.left.functionField) ≅ pullback f j := H.isoPullback
  let γY : Γ(Spec (CommRingCat.of Y.left.functionField), ⊤) ≅
      CommRingCat.of Y.left.functionField := Scheme.ΓSpecIso (CommRingCat.of Y.left.functionField)
  have hfst : e.hom ≫ pullback.fst f j = p := H.isoPullback_hom_fst
  have htop : (Spec (CommRingCat.of Y.left.functionField)).presheaf.map
      (homOfLE (le_top : (⊤ : (Spec (CommRingCat.of Y.left.functionField)).Opens) ≤ ⊤)).op =
        𝟙 _ := by
    rw [show (homOfLE _).op = 𝟙 (op ⊤) from Subsingleton.elim _ _]
    exact CategoryTheory.Functor.map_id _ _
  have hfrom : p.appTop =
      Y.left.presheaf.germ ⊤ (genericPoint Y.left) trivial ≫ γY.inv ≫
        (Spec (CommRingCat.of Y.left.functionField)).presheaf.map
          (homOfLE (le_top : (⊤ : (Spec (CommRingCat.of Y.left.functionField)).Opens) ≤ ⊤)).op :=
    Scheme.fromSpecStalk_appTop
  rw [htop, Category.comp_id] at hfrom
  have hr : (pullback.fst f j).appTop ≫ (e.hom.appTop ≫ γY.hom) =
      Y.left.presheaf.germ ⊤ (genericPoint Y.left) trivial := by
    calc
      _ = (e.hom ≫ pullback.fst f j).appTop ≫ γY.hom := by
        simp only [Scheme.Hom.comp_appTop, Category.assoc]
      _ = p.appTop ≫ γY.hom :=
        congrArg (fun q : Spec (CommRingCat.of Y.left.functionField) ⟶ Y.left =>
          q.appTop ≫ γY.hom) hfst
      _ = (Y.left.presheaf.germ ⊤ (genericPoint Y.left) trivial ≫ γY.inv) ≫ γY.hom :=
        congrArg (fun q => q ≫ γY.hom) hfrom
      _ = Y.left.presheaf.germ ⊤ (genericPoint Y.left) trivial := by
        let r : Γ(Y.left, ⊤) ⟶ CommRingCat.of Y.left.functionField :=
          Y.left.presheaf.germ ⊤ (genericPoint Y.left) trivial
        exact (Category.assoc r γY.inv γY.hom).trans
          ((congrArg
            (fun q : CommRingCat.of Y.left.functionField ⟶
              CommRingCat.of Y.left.functionField => r ≫ q)
            γY.inv_hom_id).trans (Category.comp_id r))
  have hs := finiteEtaleGenericUnitSectionsEquiv_apply Y
    ((etaleGenericUnitShortComplex X).f.hom.app (op ((finiteEtaleInclusion X).obj Y)) s)
  refine hs.trans ?_
  apply Additive.toMul.injective
  apply Units.ext
  exact ConcreteCategory.congr_hom hr s.toMul.val

end EtaleCohomology
