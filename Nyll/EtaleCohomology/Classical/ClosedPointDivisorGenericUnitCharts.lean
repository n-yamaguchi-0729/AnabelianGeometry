/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.EtaleCohomology.Classical.ClosedPointDivisorOpenRestriction
public import Nyll.EtaleCohomology.Classical.ClosedPointDivisorSheaf
public import Nyll.EtaleCohomology.Classical.ClosedPointDivisorIsoRestriction
public import Nyll.EtaleCohomology.Classical.ClosedPointDivisorRestrictionCoefficients
public import Nyll.EtaleCohomology.Classical.GenericUnitOpenRestriction
public import Nyll.EtaleCohomology.Classical.MultiplicativeGroupPushforward
public import Nyll.EtaleCohomology.Classical.AffineGenericUnitQuotient
public import Nyll.EtaleCohomology.Sites.EtaleRestriction
public import Nyll.EtaleCohomology.Sites.EtaleRestrictionSections
public import Nyll.EtaleCohomology.Sites.EtaleSlice
public import Nyll.EtaleCohomology.Sites.ZariskiGlobalSections
public import Nyll.EtaleFundamentalGroups.Cohomology.AffineGenericPointStalkComparison
public import Nyll.EtaleFundamentalGroups.Cohomology.AffineEtaleCoordinateComparison
public import Nyll.EtaleFundamentalGroups.Cohomology.AffineEtaleCoordinateComparisonSections
public import Nyll.EtaleFundamentalGroups.Cohomology.AffineEtaleGenericUnitDivisorCompatibility
public import Nyll.EtaleFundamentalGroups.Cohomology.AffineEtaleGenericUnitDivisorData
public import Nyll.EtaleFundamentalGroups.Cohomology.GenericUnitDivisorSections
public import Nyll.EtaleFundamentalGroups.Cohomology.AffineEtaleClosedPointDivisorSections
public import Nyll.EtaleFundamentalGroups.Cohomology.IntegralAffineEtaleBasis
public import Nyll.SchemeTheory.Affine.UnramifiedGenericFiber
public import Mathlib.AlgebraicGeometry.Properties
public import Mathlib.AlgebraicGeometry.AffineScheme
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Basic
public import Mathlib.CategoryTheory.MorphismProperty.Comma
public import Mathlib.CategoryTheory.Sites.SheafHom
public import Mathlib.CategoryTheory.Sites.Over
public import Mathlib.CategoryTheory.Functor.FullyFaithful
public import Mathlib.CategoryTheory.Sites.CoversTop.Basic
public import Mathlib.CategoryTheory.Sites.LocalProperties
public import Mathlib.Data.Sigma.Basic
public import Mathlib.RingTheory.Flat.TorsionFree
public import Mathlib.RingTheory.Localization.FractionRing

/-!
# Affine charts for the original global divisor comparison

Each chart compares the restriction of the original global generic-unit
quotient directly with the quotient defined by the chart's fraction field.
The cartesian square is constructed from the canonical function-field map
and the existing affine stalk/fraction-field equivalence. The original
regular-unit and cokernel maps are retained.
-/

@[expose] public section

noncomputable section

universe u

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open EtaleFundamentalGroups.StrictHenselian

namespace EtaleCohomology

namespace DivisorGenericUnitGlobal

section GenericCharts

variable (R : Type u) [CommRing R] [IsDomain R]

/-- The fraction-field spectrum is the generic-point spectrum of the affine scheme. -/
def affineFractionGenericIso :
    Spec (CommRingCat.of (FractionRing R)) ≅
      Spec (Spec (CommRingCat.of R)).functionField :=
  Scheme.Spec.mapIso
    (affineGenericPointStalkFractionRingAlgEquiv R).symm.toRingEquiv.toCommRingCatIso.op

private theorem affineFractionGenericIso_hom_fromSpecStalk :
    (affineFractionGenericIso R).hom ≫
        (Spec (CommRingCat.of R)).fromSpecStalk
          (genericPoint (Spec (CommRingCat.of R))) =
      Spec.map (CommRingCat.ofHom (algebraMap R (FractionRing R))) := by
  rw [affineGenericPoint_fromSpecStalk_eq_specMap]
  change Spec.map (CommRingCat.ofHom
      (affineGenericPointStalkFractionRingAlgEquiv R).symm.toRingHom) ≫
        Spec.map (affineGenericPointGermMap R) = _
  rw [← Spec.map_comp]
  apply congrArg Spec.map
  apply CommRingCat.hom_ext
  ext r
  change (affineGenericPointStalkFractionRingAlgEquiv R).symm
      (algebraMap R (affineGenericPointStalk R) r) = algebraMap R (FractionRing R) r
  exact (affineGenericPointStalkFractionRingAlgEquiv R).symm.commutes r

variable {X : Scheme.{u}} [IsIntegral X]
  (i : Spec (CommRingCat.of R) ⟶ X) [IsOpenImmersion i]

/-- The actual generic-point identification for an affine open chart. -/
def affineChartGenericIso :
    Spec (CommRingCat.of (FractionRing R)) ≅ Spec X.functionField :=
  affineFractionGenericIso R ≪≫ genericPointOpenIso i

theorem affineChartGenericIsPullback :
    IsPullback (Spec.map (CommRingCat.ofHom (algebraMap R (FractionRing R))))
      (affineChartGenericIso R i).hom i (X.fromSpecStalk (genericPoint X)) := by
  apply IsPullback.of_vert_isIso_mono
  refine ⟨?_⟩
  calc
    Spec.map (CommRingCat.ofHom (algebraMap R (FractionRing R))) ≫ i =
        ((affineFractionGenericIso R).hom ≫
          (Spec (CommRingCat.of R)).fromSpecStalk
            (genericPoint (Spec (CommRingCat.of R)))) ≫ i :=
      congrArg (fun p => p ≫ i) (affineFractionGenericIso_hom_fromSpecStalk R).symm
    _ = (affineFractionGenericIso R).hom ≫
        ((genericPointOpenIso i).hom ≫ X.fromSpecStalk (genericPoint X)) := by
      rw [Category.assoc, (genericPointOpenIsPullback i).w]
    _ = (affineChartGenericIso R i).hom ≫ X.fromSpecStalk (genericPoint X) :=
      (Category.assoc _ _ _).symm

/-- The actual global quotient on an affine open chart is the chart's own
fraction-ring quotient. Its generic-point square is constructed, not assumed. -/
def affineChartGenericUnitQuotientIso :
    (etaleRestriction i AddCommGrpCat.{u}).obj (etaleGenericUnitQuotient X) ≅
      affineEtaleFractionRingUnitQuotient R :=
  @etaleRestrictionUnitQuotientIsoOfIsPullback
    X (Spec X.functionField) (Spec (CommRingCat.of R))
    (Spec (CommRingCat.of (FractionRing R))) i inferInstance
    (X.fromSpecStalk (genericPoint X))
    (Spec.map (CommRingCat.ofHom (algebraMap R (FractionRing R))))
    (affineChartGenericIso R i).hom inferInstance (affineChartGenericIsPullback R i)

/-- The chart comparison preserves the original quotient projection of
generic rational units. -/
theorem affineChartGenericUnitQuotientIso_π :
    (etaleRestriction i AddCommGrpCat.{u}).map
        (cokernel.π (etaleMultiplicativeGroupToPushforward
          (X.fromSpecStalk (genericPoint X)))) ≫
      (affineChartGenericUnitQuotientIso R i).hom =
    (etaleRestrictionMultiplicativeGroupPushforwardIsoOfIsPullback i
      (X.fromSpecStalk (genericPoint X))
      (Spec.map (CommRingCat.ofHom (algebraMap R (FractionRing R))))
      (affineChartGenericIso R i).hom (affineChartGenericIsPullback R i)).hom ≫
        cokernel.π (etaleMultiplicativeGroupToPushforward
          (Spec.map (CommRingCat.ofHom (algebraMap R (FractionRing R))))) :=
  etaleRestrictionUnitQuotientIsoOfIsPullback_π i
    (X.fromSpecStalk (genericPoint X))
    (Spec.map (CommRingCat.ofHom (algebraMap R (FractionRing R))))
    (affineChartGenericIso R i).hom (affineChartGenericIsPullback R i)

/-- Pasting of restriction comparisons retains every section of the
original source object, before taking global sections. -/
theorem restrictionComparison_arbitrarySection
    {V U X : Scheme.{u}} (j : V ⟶ U) (i : U ⟶ X) [Etale j] [Etale i]
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u})
    (G : Sheaf U.smallEtaleTopology AddCommGrpCat.{u})
    (H : Sheaf V.smallEtaleTopology AddCommGrpCat.{u})
    (a : (etaleRestriction i AddCommGrpCat.{u}).obj F ≅ G)
    (b : (etaleRestriction j AddCommGrpCat.{u}).obj G ≅ H)
    (c : (etaleRestriction (j ≫ i) AddCommGrpCat.{u}).obj F ≅ H)
    (hc : (etaleRestriction j AddCommGrpCat.{u}).map a.hom ≫ b.hom =
      (etaleRestrictionCompIso j i AddCommGrpCat.{u}).hom.app F ≫ c.hom) :
    (etaleRestrictionTopObjectSectionIso (j ≫ i) F).inv ≫
        c.hom.hom.app (op ((zariskiToEtale V).obj ⊤)) =
      a.hom.hom.app (op (Scheme.Etale.mk j)) ≫
        (etaleRestrictionTopObjectSectionIso j G).inv ≫
          b.hom.hom.app (op ((zariskiToEtale V).obj ⊤)) := by
  let W := (zariskiToEtale V).obj ⊤
  let cs := (MorphismProperty.Over.mapComp
    (P := show MorphismProperty Scheme.{u} from @Etale) (Q := ⊤)
    (f := j) inferInstance (g := i) inferInstance).app W
  let tj := (etalePostcomposeTopObjectIso j).hom
  let tc := (etalePostcomposeTopObjectIso (j ≫ i)).hom
  have ht : cs.hom ≫ (etalePostcompose i).map tj = tc := by
    apply MorphismProperty.Over.Hom.ext
    change 𝟙 W.left ≫ ((zariskiToEtaleTopIso V).hom.left ≫ 𝟙 V) =
      (zariskiToEtaleTopIso V).hom.left ≫ 𝟙 V
    exact Category.id_comp _
  have htF : F.obj.map tc.op =
      F.obj.map ((etalePostcompose i).map tj).op ≫ F.obj.map cs.hom.op := by
    exact (congrArg (fun k => F.obj.map k.op) ht.symm).trans
      (F.obj.map_comp ((etalePostcompose i).map tj).op cs.hom.op)
  have hp := congrArg (fun k => k.hom.app (op W)) hc
  change a.hom.hom.app (op ((etalePostcompose j).obj W)) ≫
      b.hom.hom.app (op W) =
    F.obj.map cs.hom.op ≫ c.hom.hom.app (op W) at hp
  have hn := a.hom.hom.naturality tj.op
  change F.obj.map ((etalePostcompose i).map tj).op ≫
      a.hom.hom.app (op ((etalePostcompose j).obj W)) =
    a.hom.hom.app (op (Scheme.Etale.mk j)) ≫ G.obj.map tj.op at hn
  simp only [etaleRestrictionTopObjectSectionIso_inv]
  change F.obj.map tc.op ≫ c.hom.hom.app (op W) =
    a.hom.hom.app (op (Scheme.Etale.mk j)) ≫
      G.obj.map tj.op ≫ b.hom.hom.app (op W)
  have h₁ := congrArg (fun k => k ≫ c.hom.hom.app (op W)) htF
  have h₂ := (Category.assoc (F.obj.map ((etalePostcompose i).map tj).op)
    (F.obj.map cs.hom.op) (c.hom.hom.app (op W))).trans
      (congrArg (fun k => F.obj.map ((etalePostcompose i).map tj).op ≫ k) hp.symm)
  have h₃ := (Category.assoc (F.obj.map ((etalePostcompose i).map tj).op)
    (a.hom.hom.app (op ((etalePostcompose j).obj W)))
    (b.hom.hom.app (op W))).symm.trans
      (congrArg (fun k => k ≫ b.hom.hom.app (op W)) hn)
  exact h₁.trans (h₂.trans (h₃.trans (Category.assoc _ _ _)))

section CommonSource

variable (S : Type u) [CommRing S] [IsDomain S] [Algebra R S] [Algebra.Etale R S]
  [algRE : Algebra R (FractionRing S)]
  [hRS : @IsScalarTower R S (FractionRing S)
    (inferInstance : Algebra R S).toSMul
    (inferInstance : Algebra S (FractionRing S)).toSMul algRE.toSMul]
  [algKE : Algebra (FractionRing R) (FractionRing S)]
  [hKS : @IsScalarTower R (FractionRing R) (FractionRing S)
    (inferInstance : Algebra R (FractionRing R)).toSMul algKE.toSMul algRE.toSMul]

/-- The generic-point map from an integral affine source through its original chart. -/
def chartSourceGenericMap :
    Spec (CommRingCat.of (FractionRing S)) ⟶ Spec X.functionField :=
  Spec.map (CommRingCat.ofHom (algebraMap (FractionRing R) (FractionRing S))) ≫
    (affineChartGenericIso R i).hom

/-- The original affine source and its fraction field form the generic-point pullback. -/
theorem chartSourceGenericIsPullback
    (q : Spec (CommRingCat.of S) ⟶ X)
    (hq : Spec.map (CommRingCat.ofHom (algebraMap R S)) ≫ i = q) :
    IsPullback (Spec.map (CommRingCat.ofHom (algebraMap S (FractionRing S))))
      (chartSourceGenericMap R i S) q (X.fromSpecStalk (genericPoint X)) := by
  rw [← hq]
  exact (EtaleFundamentalGroups.isPullback_spec_unramified_generic
    R S (FractionRing R) (FractionRing S)).paste_vert
      (affineChartGenericIsPullback R i)

/-- Normalize on a common integral affine étale source, using its literal
coordinate fraction field and the original composite map to the curve. -/
def affineChartGenericUnitSourceIso
    (q : Spec (CommRingCat.of S) ⟶ X) [Etale q]
    (hq : Spec.map (CommRingCat.ofHom (algebraMap R S)) ≫ i = q) :
    (etaleRestriction q AddCommGrpCat.{u}).obj (etaleGenericUnitQuotient X) ≅
      affineEtaleFractionRingUnitQuotient S := by
  let H := chartSourceGenericIsPullback R i S q hq
  have hg : Etale (chartSourceGenericMap R i S) :=
    MorphismProperty.of_isPullback (P := @Etale) H (show Etale q from inferInstance)
  exact @etaleRestrictionUnitQuotientIsoOfIsPullback
    X (Spec X.functionField) (Spec (CommRingCat.of S))
    (Spec (CommRingCat.of (FractionRing S))) q inferInstance
    (X.fromSpecStalk (genericPoint X))
    (Spec.map (CommRingCat.ofHom (algebraMap S (FractionRing S))))
    (chartSourceGenericMap R i S) hg H

/-- The common-source normalization agrees with the original chart
normalization followed by the existing fraction-field restriction. This is
an equality of sheaf morphisms and therefore covers arbitrary sections. -/
theorem affineChartGenericUnitSourceIso_paste :
    (etaleRestriction (Spec.map (CommRingCat.ofHom (algebraMap R S)))
      AddCommGrpCat.{u}).map (affineChartGenericUnitQuotientIso R i).hom ≫
      (affineEtaleFractionRingUnitQuotientIso R S).hom =
    (etaleRestrictionCompIso
      (Spec.map (CommRingCat.ofHom (algebraMap R S))) i
      AddCommGrpCat.{u}).hom.app (etaleGenericUnitQuotient X) ≫
      (affineChartGenericUnitSourceIso R i S
        (Spec.map (CommRingCat.ofHom (algebraMap R S)) ≫ i) rfl).hom := by
  let H := EtaleFundamentalGroups.isPullback_spec_unramified_generic
    R S (FractionRing R) (FractionRing S)
  have hg : Etale
      (Spec.map (CommRingCat.ofHom (algebraMap (FractionRing R) (FractionRing S)))) :=
    MorphismProperty.of_isPullback (P := @Etale) H
      (show Etale (Spec.map (CommRingCat.ofHom (algebraMap R S))) from inferInstance)
  exact etaleRestrictionUnitQuotient_paste i
    (Spec.map (CommRingCat.ofHom (algebraMap R S)))
    (X.fromSpecStalk (genericPoint X))
    (Spec.map (CommRingCat.ofHom (algebraMap R (FractionRing R))))
    (affineChartGenericIso R i).hom
    (Spec.map (CommRingCat.ofHom (algebraMap S (FractionRing S))))
    (Spec.map (CommRingCat.ofHom (algebraMap (FractionRing R) (FractionRing S))))
    (affineChartGenericIsPullback R i) H

/-- The chart and common-source comparisons agree on every section of the
original affine source, without requiring it to extend to the chart. -/
theorem affineChartGenericUnitSourceIso_sections :
    (etaleRestrictionTopObjectSectionIso
      (Spec.map (CommRingCat.ofHom (algebraMap R S)) ≫ i)
      (etaleGenericUnitQuotient X)).inv ≫
        (affineChartGenericUnitSourceIso R i S
          (Spec.map (CommRingCat.ofHom (algebraMap R S)) ≫ i) rfl).hom.hom.app
            (op ((zariskiToEtale (Spec (CommRingCat.of S))).obj ⊤)) =
      (affineChartGenericUnitQuotientIso R i).hom.hom.app
        (op (affineEtaleSpecObject (R := R) (S := S))) ≫
      (etaleRestrictionTopObjectSectionIso
        (Spec.map (CommRingCat.ofHom (algebraMap R S)))
        (affineEtaleFractionRingUnitQuotient R)).inv ≫
      (affineEtaleFractionRingUnitQuotientIso R S).hom.hom.app
        (op ((zariskiToEtale (Spec (CommRingCat.of S))).obj ⊤)) :=
  restrictionComparison_arbitrarySection
    (Spec.map (CommRingCat.ofHom (algebraMap R S))) i
    (etaleGenericUnitQuotient X) (affineEtaleFractionRingUnitQuotient R)
    (affineEtaleFractionRingUnitQuotient S)
    (affineChartGenericUnitQuotientIso R i)
    (affineEtaleFractionRingUnitQuotientIso R S)
    (affineChartGenericUnitSourceIso R i S
      (Spec.map (CommRingCat.ofHom (algebraMap R S)) ≫ i) rfl)
    (affineChartGenericUnitSourceIso_paste R i S)

end CommonSource

/-- The original generic-point monomorphism makes the quotient
comparison independent of the map used to exhibit its cartesian square. -/
theorem quotientComparison_independent_of_genericMap
    {V P : Scheme.{u}} (q : V ⟶ X) [Etale q] (p : P ⟶ V)
    (g h : P ⟶ Spec X.functionField) [Etale g] [Etale h]
    (Hg : IsPullback p g q (X.fromSpecStalk (genericPoint X)))
    (Hh : IsPullback p h q (X.fromSpecStalk (genericPoint X))) :
    etaleRestrictionUnitQuotientIsoOfIsPullback q
        (X.fromSpecStalk (genericPoint X)) p g Hg =
      etaleRestrictionUnitQuotientIsoOfIsPullback q
        (X.fromSpecStalk (genericPoint X)) p h Hh := by
  have hgh : g = h := (cancel_mono (X.fromSpecStalk (genericPoint X))).mp
    (Hg.w.symm.trans Hh.w)
  subst h
  rfl

/-- Two affine charts give the same normalization on the same original
integral affine étale source. The comparison follows from the monomorphism
of the original generic-point map, not from an assumed chart compatibility. -/
theorem affineChartGenericUnitSourceIso_independent
    (S : Type u) [CommRing S] [IsDomain S] [Algebra R S] [Algebra.Etale R S]
    [algRE : Algebra R (FractionRing S)]
    [hRS : @IsScalarTower R S (FractionRing S)
      (inferInstance : Algebra R S).toSMul
      (inferInstance : Algebra S (FractionRing S)).toSMul algRE.toSMul]
    [algKE : Algebra (FractionRing R) (FractionRing S)]
    [hKS : @IsScalarTower R (FractionRing R) (FractionRing S)
      (inferInstance : Algebra R (FractionRing R)).toSMul algKE.toSMul algRE.toSMul]
    (B : Type u) [CommRing B] [IsDomain B] [Algebra B S] [Algebra.Etale B S]
    [algBE : Algebra B (FractionRing S)]
    [hBS : @IsScalarTower B S (FractionRing S)
      (inferInstance : Algebra B S).toSMul
      (inferInstance : Algebra S (FractionRing S)).toSMul algBE.toSMul]
    [algLE : Algebra (FractionRing B) (FractionRing S)]
    [hLS : @IsScalarTower B (FractionRing B) (FractionRing S)
      (inferInstance : Algebra B (FractionRing B)).toSMul algLE.toSMul algBE.toSMul]
    (j : Spec (CommRingCat.of B) ⟶ X) [IsOpenImmersion j]
    (q : Spec (CommRingCat.of S) ⟶ X) [Etale q]
    (hi : Spec.map (CommRingCat.ofHom (algebraMap R S)) ≫ i = q)
    (hj : Spec.map (CommRingCat.ofHom (algebraMap B S)) ≫ j = q) :
    affineChartGenericUnitSourceIso R i S q hi =
      affineChartGenericUnitSourceIso B j S q hj := by
  let Hi := chartSourceGenericIsPullback R i S q hi
  let Hj := chartSourceGenericIsPullback B j S q hj
  have hgi : Etale (chartSourceGenericMap R i S) :=
    MorphismProperty.of_isPullback (P := @Etale) Hi (show Etale q from inferInstance)
  have hgj : Etale (chartSourceGenericMap B j S) :=
    MorphismProperty.of_isPullback (P := @Etale) Hj (show Etale q from inferInstance)
  exact quotientComparison_independent_of_genericMap q
    (Spec.map (CommRingCat.ofHom (algebraMap S (FractionRing S))))
    (chartSourceGenericMap R i S) (chartSourceGenericMap B j S) Hi Hj

end GenericCharts

section DivisorCharts

variable (R : Type u) [CommRing R] {X : Scheme.{u}} [JacobsonSpace X]
  (U : X.Opens) (e : Spec (CommRingCat.of R) ≅ (U : Scheme))

/-- The chart restriction of the original divisor sheaf, using the existing
open restriction and scheme-isomorphism transport without changing its summands. -/
def affineChartDivisorIso :
    (etaleRestriction (e.hom ≫ U.ι) AddCommGrpCat.{u}).obj
        (closedPointDivisorSheaf X) ≅
      closedPointDivisorSheaf (Spec (CommRingCat.of R)) :=
  ((etaleRestrictionCompIso e.hom U.ι AddCommGrpCat.{u}).app
      (closedPointDivisorSheaf X)).symm ≪≫
    (etaleRestriction e.hom AddCommGrpCat.{u}).mapIso
      (closedPointDivisorOpenRestrictionIso U) ≪≫
    closedPointDivisorIsoRestrictionIso e

/-- The actual chart comparison retains each coefficient of the original
global divisor section, including its original residue-fiber point. -/
theorem affineChartDivisorIso_coefficient
    (y : closedPoints (Spec (CommRingCat.of R)))
    (V : (Spec (CommRingCat.of R)).Etale) :
    let yU : closedPoints (U : Scheme) :=
      (e.hom.homeomorph.sets e.hom.isClosedEmbedding.preimage_closedPoints.symm).toEquiv y
    let x : closedPoints X := ((closedPointsOpenEquiv U) yU).1
    ∀ (s : (closedPointDivisorSheaf X).obj.obj
      (op ((etalePostcompose (e.hom ≫ U.ι)).obj V)))
      (z : closedPointResidueFiber (Spec (CommRingCat.of R)) y V),
      closedPointDivisorSummandSectionsAddEquiv (Spec (CommRingCat.of R)) y V
        ((closedPointDivisorSheafComponentProjection (Spec (CommRingCat.of R)) y).hom.app
          (op V) ((affineChartDivisorIso R U e).hom.hom.app (op V) s)) z =
      closedPointDivisorSummandSectionsAddEquiv X x
        ((etalePostcompose (e.hom ≫ U.ι)).obj V)
        ((closedPointDivisorSheafComponentProjection X x).hom.app
          (op ((etalePostcompose (e.hom ≫ U.ι)).obj V)) s)
        ⟨z.1, by
          change U.ι (e.hom (V.hom z.1)) = U.ι (e.hom y.1)
          exact congrArg (fun p => U.ι (e.hom p)) z.2⟩ := by
  intro yU x s z
  let DX := closedPointDivisorSheaf X
  let VU := (etalePostcompose e.hom).obj V
  let Vn := (etalePostcompose U.ι).obj VU
  let Vd := (etalePostcompose (e.hom ≫ U.ι)).obj V
  let c : Vd ≅ Vn :=
    (MorphismProperty.Over.mapComp
      (P := show MorphismProperty Scheme.{u} from @Etale) (Q := ⊤)
      (f := e.hom) inferInstance (g := U.ι) inferInstance).app V
  let s₀ := DX.obj.map c.inv.op s
  let t := (closedPointDivisorOpenRestrictionIso U).hom.hom.app (op VU) s₀
  let zU : closedPointResidueFiber (U : Scheme) yU VU :=
    ⟨z.1, congrArg e.hom z.2⟩
  let zn : closedPointResidueFiber X x Vn :=
    ⟨z.1, congrArg Subtype.val zU.2⟩
  have hc : ((etaleRestrictionCompIso e.hom U.ι AddCommGrpCat.{u}).inv.app
      DX).hom.app (op V) = DX.obj.map c.inv.op := by
    change DX.obj.map c.inv.op ≫ 𝟙 _ = _
    exact Category.comp_id _
  have hd : (affineChartDivisorIso R U e).hom.hom.app (op V) s =
      (closedPointDivisorIsoRestrictionIso e).hom.hom.app (op V) t := by
    change (closedPointDivisorIsoRestrictionIso e).hom.hom.app (op V)
        ((closedPointDivisorOpenRestrictionIso U).hom.hom.app (op VU)
          (((etaleRestrictionCompIso e.hom U.ι AddCommGrpCat.{u}).inv.app DX).hom.app
            (op V) s)) = _
    rw [hc]
    rfl
  have he := closedPointDivisorIsoRestrictionIso_coefficient e y V t z
  have ho := closedPointDivisorOpenRestrictionIso_coefficient U yU VU s₀ zU
  let p := closedPointDivisorSheafComponentProjection X x
  have hp := ConcreteCategory.congr_hom (p.hom.naturality c.inv.op) s
  change p.hom.app (op Vn) s₀ =
    (closedPointDivisorSummand X x).obj.map c.inv.op (p.hom.app (op Vd) s) at hp
  have hn := closedPointDivisorSummandSectionsAddEquiv_naturality
    X x Vn Vd c.inv (p.hom.app (op Vd) s) zn
  calc
    _ = closedPointDivisorSummandSectionsAddEquiv (Spec (CommRingCat.of R)) y V
        ((closedPointDivisorSheafComponentProjection (Spec (CommRingCat.of R)) y).hom.app
          (op V) ((closedPointDivisorIsoRestrictionIso e).hom.hom.app (op V) t)) z :=
      congrArg (fun w => closedPointDivisorSummandSectionsAddEquiv
        (Spec (CommRingCat.of R)) y V
        ((closedPointDivisorSheafComponentProjection (Spec (CommRingCat.of R)) y).hom.app
          (op V) w) z) hd
    _ = closedPointDivisorSummandSectionsAddEquiv X x Vn
        (p.hom.app (op Vn) s₀) zn := he.trans ho
    _ = closedPointDivisorSummandSectionsAddEquiv X x Vn
        ((closedPointDivisorSummand X x).obj.map c.inv.op
          (p.hom.app (op Vd) s)) zn :=
      congrArg (fun w => closedPointDivisorSummandSectionsAddEquiv X x Vn w zn) hp
    _ = _ := hn

end DivisorCharts

section DedekindCharts

variable (R : Type u) [CommRing R] [IsDedekindDomain R]
  {X : Scheme.{u}} [IsIntegral X] [JacobsonSpace X]
  (U : X.Opens) (e : Spec (CommRingCat.of R) ≅ (U : Scheme))
  (hR : ¬ IsField R)

/-- The original affine divisor comparison gives an isomorphism between
the restrictions of the original global divisor and generic-unit sheaves.
All quotients are transported through the actual chart generic-point square. -/
def affineChartDivisorGenericUnitIso :
    (etaleRestriction (e.hom ≫ U.ι) AddCommGrpCat.{u}).obj
        (closedPointDivisorSheaf X) ≅
      (etaleRestriction (e.hom ≫ U.ι) AddCommGrpCat.{u}).obj
        (etaleGenericUnitQuotient X) := by
  let : HasColimitsOfShape (Discrete (closedPoints (Spec (CommRingCat.of R))))
      (Sheaf (Spec (CommRingCat.of R)).smallEtaleTopology AddCommGrpCat.{u}) :=
    closedPointDivisorSheafHasColimitsOfShape (Spec (CommRingCat.of R))
  exact affineChartDivisorIso R U e ≪≫
    affineClosedPointDivisorGenericUnitSheafIso R hR ≪≫
    affineGenericPointUnitQuotientFractionRingIso R ≪≫
    (affineChartGenericUnitQuotientIso R (e.hom ≫ U.ι)).symm

/-- The local divisor comparison keeps the original affine comparison after
normalizing its target by the actual chart generic-point square. -/
theorem affineChartDivisorGenericUnitIso_hom_comp :
    let _ : HasColimitsOfShape (Discrete (closedPoints (Spec (CommRingCat.of R))))
        (Sheaf (Spec (CommRingCat.of R)).smallEtaleTopology AddCommGrpCat.{u}) :=
      closedPointDivisorSheafHasColimitsOfShape (Spec (CommRingCat.of R))
    (affineChartDivisorGenericUnitIso R U e hR).hom ≫
        (affineChartGenericUnitQuotientIso R (e.hom ≫ U.ι)).hom =
      (affineChartDivisorIso R U e).hom ≫
        (affineClosedPointDivisorGenericUnitSheafIso R hR).hom ≫
        (affineGenericPointUnitQuotientFractionRingIso R).hom := by
  intro hShape
  simp only [affineChartDivisorGenericUnitIso, Iso.trans_hom, Iso.symm_hom,
    Category.assoc, Iso.inv_hom_id, Category.comp_id]

private theorem wholeDivisorCoefficient_naturality
    {Y : Scheme.{u}} (x : closedPoints Y) (V W : Y.Etale) (m : V ⟶ W)
    (s : (closedPointDivisorSheaf Y).obj.obj (op W))
    (z : closedPointResidueFiber Y x V) :
    closedPointDivisorSummandSectionsAddEquiv Y x V
      ((closedPointDivisorSheafComponentProjection Y x).hom.app (op V)
        ((closedPointDivisorSheaf Y).obj.map m.op s)) z =
    closedPointDivisorSummandSectionsAddEquiv Y x W
      ((closedPointDivisorSheafComponentProjection Y x).hom.app (op W) s)
      ⟨m.left z.1, by
        have hm := congrArg (fun f => f z.1)
          (MorphismProperty.Over.w
            (P := show MorphismProperty Scheme.{u} from @Etale) (Q := ⊤) m)
        exact hm.trans z.2⟩ := by
  let p := closedPointDivisorSheafComponentProjection Y x
  have hp := ConcreteCategory.congr_hom (p.hom.naturality m.op) s
  change p.hom.app (op V) ((closedPointDivisorSheaf Y).obj.map m.op s) =
    (closedPointDivisorSummand Y x).obj.map m.op (p.hom.app (op W) s) at hp
  exact (congrArg (fun t =>
    closedPointDivisorSummandSectionsAddEquiv Y x V t z) hp).trans
      (closedPointDivisorSummandSectionsAddEquiv_naturality
        Y x V W m (p.hom.app (op W) s) z)

section CommonDivisorSource

variable (S : Type u) [CommRing S] [IsDedekindDomain S]
  [Algebra R S] [Algebra.Etale R S]
  (q : Spec (CommRingCat.of S) ⟶ X) [Etale q]
  (hq : Spec.map (CommRingCat.ofHom (algebraMap R S)) ≫ (e.hom ≫ U.ι) = q)

/-- The chart object and the original common affine source have the same
underlying scheme. This is its actual isomorphism on the small étale site. -/
def affineChartDivisorSourceObjectIso :
    (etalePostcompose (e.hom ≫ U.ι)).obj
        (affineEtaleSpecObject (R := R) (S := S)) ≅ Scheme.Etale.mk q :=
  MorphismProperty.Over.isoMk
    (P := show MorphismProperty Scheme.{u} from @Etale) (Q := ⊤)
    (Iso.refl (Spec (CommRingCat.of S)))
    ((Category.id_comp q).trans hq.symm)

/-- Transport an original global-divisor section to its affine chart using
the identity on the original common source and the native chart isomorphism. -/
def affineChartDivisorSourceSection
    (s : (closedPointDivisorSheaf X).obj.obj (op (Scheme.Etale.mk q))) :
    (closedPointDivisorSheaf (Spec (CommRingCat.of R))).obj.obj
      (op (affineEtaleSpecObject (R := R) (S := S))) :=
  (affineChartDivisorIso R U e).hom.hom.app
    (op (affineEtaleSpecObject (R := R) (S := S)))
    ((closedPointDivisorSheaf X).obj.map
      (affineChartDivisorSourceObjectIso R U e S q hq).hom.op s)

/-- The original closed point and residue-fiber point read by a height-one
coefficient after transporting along an affine open chart. -/
def affineChartDivisorSourceFiberPoint (w : IsDedekindDomain.HeightOneSpectrum S) :
    Σ x : closedPoints X, closedPointResidueFiber X x (Scheme.Etale.mk q) := by
  let p := affineEtaleHeightOneToClosedPointFiber (R := R) (S := S) hR w
  let yU : closedPoints (U : Scheme) :=
    (e.hom.homeomorph.sets e.hom.isClosedEmbedding.preimage_closedPoints.symm).toEquiv p.1
  let x : closedPoints X := ((closedPointsOpenEquiv U) yU).1
  refine ⟨x, p.2.1, ?_⟩
  change q p.2.1 = (e.hom ≫ U.ι) p.1.1
  calc
    q p.2.1 = (e.hom ≫ U.ι)
        (Spec.map (CommRingCat.ofHom (algebraMap R S)) p.2.1) := by
      exact congrArg (fun f : Spec (CommRingCat.of S) ⟶ X => f p.2.1) hq.symm
    _ = (e.hom ≫ U.ι) p.1.1 := congrArg (e.hom ≫ U.ι) p.2.2

omit [IsIntegral X] in
/-- The common-source fiber point has the original prime ideal of its height-one point. -/
theorem affineChartDivisorSourceFiberPoint_point
    (w : IsDedekindDomain.HeightOneSpectrum S) :
    (affineChartDivisorSourceFiberPoint R U e hR S q hq w).2.1 =
      (⟨w.asIdeal, w.isPrime⟩ : PrimeSpectrum S) := by
  let p := affineEtaleHeightOneToClosedPointFiber (R := R) (S := S) hR w
  change p.2.1 = (⟨w.asIdeal, w.isPrime⟩ : PrimeSpectrum S)
  apply PrimeSpectrum.ext
  have hw := congrArg IsDedekindDomain.HeightOneSpectrum.asIdeal
    (affineEtaleClosedPointFiberEquivHeightOne_apply_heightOneToFiber
      (R := R) (S := S) hR w)
  exact (affineEtaleClosedPointResidueFiberEquivHeightOneFiber_asIdeal
    (R := R) (S := S) hR p.1 p.2).symm.trans hw

omit [IsIntegral X] in
/-- Every coefficient of the transported section is the coefficient of the
original global section at the original point of the common affine source. -/
theorem affineChartDivisorSourceSection_coefficient :
    let _ : HasColimitsOfShape (Discrete (closedPoints (Spec (CommRingCat.of R))))
        (Sheaf (Spec (CommRingCat.of R)).smallEtaleTopology AddCommGrpCat.{u}) :=
      closedPointDivisorSheafHasColimitsOfShape (Spec (CommRingCat.of R))
    ∀ (w : IsDedekindDomain.HeightOneSpectrum S)
      (s : (closedPointDivisorSheaf X).obj.obj (op (Scheme.Etale.mk q))),
      affineEtaleClosedPointDivisorCoefficient (R := R) (S := S) hR w
        (affineChartDivisorSourceSection R U e S q hq s) =
      (closedPointDivisorSummandSectionsAddEquiv X
        (affineChartDivisorSourceFiberPoint R U e hR S q hq w).1
        (Scheme.Etale.mk q)
        ((closedPointDivisorSheafComponentProjection X
          (affineChartDivisorSourceFiberPoint R U e hR S q hq w).1).hom.app
          (op (Scheme.Etale.mk q)) s)
        (affineChartDivisorSourceFiberPoint R U e hR S q hq w).2).down := by
  intro hShape w s
  let p := affineEtaleHeightOneToClosedPointFiber (R := R) (S := S) hR w
  let V := affineEtaleSpecObject (R := R) (S := S)
  let V' := (etalePostcompose (e.hom ≫ U.ι)).obj V
  let a := affineChartDivisorSourceFiberPoint R U e hR S q hq w
  let c := affineChartDivisorSourceObjectIso R U e S q hq
  let z : closedPointResidueFiber X a.1 V' :=
    ⟨p.2.1, congrArg (e.hom ≫ U.ι) p.2.2⟩
  have hc := affineChartDivisorIso_coefficient R U e p.1 V
    ((closedPointDivisorSheaf X).obj.map c.hom.op s) p.2
  have hn := wholeDivisorCoefficient_naturality a.1 V' (Scheme.Etale.mk q) c.hom s z
  change (closedPointDivisorSummandSectionsAddEquiv (Spec (CommRingCat.of R)) p.1 V
    ((closedPointDivisorSheafComponentProjection (Spec (CommRingCat.of R)) p.1).hom.app
      (op V) (affineChartDivisorSourceSection R U e S q hq s)) p.2).down = _
  exact congrArg ULift.down (hc.trans hn)

omit [IsIntegral X] in
/-- Two affine charts read the same finite divisor on the same original
affine étale source. The proof identifies their original residue-fiber points. -/
theorem affineChartDivisorSourceSection_finsupp_independent
    (B : Type u) [CommRing B] [IsDedekindDomain B]
    [Algebra B S] [Algebra.Etale B S]
    (W : X.Opens) (d : Spec (CommRingCat.of B) ≅ (W : Scheme))
    (hB : ¬ IsField B)
    (hqB : Spec.map (CommRingCat.ofHom (algebraMap B S)) ≫ (d.hom ≫ W.ι) = q) :
    let _ : HasColimitsOfShape (Discrete (closedPoints (Spec (CommRingCat.of R))))
        (Sheaf (Spec (CommRingCat.of R)).smallEtaleTopology AddCommGrpCat.{u}) :=
      closedPointDivisorSheafHasColimitsOfShape (Spec (CommRingCat.of R))
    let _ : HasColimitsOfShape (Discrete (closedPoints (Spec (CommRingCat.of B))))
        (Sheaf (Spec (CommRingCat.of B)).smallEtaleTopology AddCommGrpCat.{u}) :=
      closedPointDivisorSheafHasColimitsOfShape (Spec (CommRingCat.of B))
    ∀ (s : (closedPointDivisorSheaf X).obj.obj (op (Scheme.Etale.mk q))),
      affineEtaleClosedPointDivisorSectionFinsupp (R := R) (S := S) hR
        (affineChartDivisorSourceSection R U e S q hq s) =
      affineEtaleClosedPointDivisorSectionFinsupp (R := B) (S := S) hB
        (affineChartDivisorSourceSection B W d S q hqB s) := by
  intro hShapeR hShapeB s
  ext w
  change affineEtaleClosedPointDivisorCoefficient (R := R) (S := S) hR w
      (affineChartDivisorSourceSection R U e S q hq s) =
    affineEtaleClosedPointDivisorCoefficient (R := B) (S := S) hB w
      (affineChartDivisorSourceSection B W d S q hqB s)
  rw [affineChartDivisorSourceSection_coefficient R U e hR S q hq,
    affineChartDivisorSourceSection_coefficient B W d hB S q hqB]
  let a := affineChartDivisorSourceFiberPoint R U e hR S q hq w
  let b := affineChartDivisorSourceFiberPoint B W d hB S q hqB w
  have hp : a.2.1 = b.2.1 :=
    (affineChartDivisorSourceFiberPoint_point R U e hR S q hq w).trans
      (affineChartDivisorSourceFiberPoint_point B W d hB S q hqB w).symm
  have hab : a = b := by
    apply Sigma.subtype_ext
    · apply Subtype.ext
      exact a.2.2.symm.trans ((congrArg q hp).trans b.2.2)
    · exact hp
  exact congrArg (fun p : Σ x : closedPoints X,
      closedPointResidueFiber X x (Scheme.Etale.mk q) =>
    (closedPointDivisorSummandSectionsAddEquiv X p.1 (Scheme.Etale.mk q)
      ((closedPointDivisorSheafComponentProjection X p.1).hom.app
        (op (Scheme.Etale.mk q)) s) p.2).down) hab

end CommonDivisorSource

omit [IsDedekindDomain R] [IsIntegral X] in
/-- The original chart map on divisor sections commutes with a coordinate-spectrum
isomorphism, using the identity on the original source scheme. -/
theorem chartDivisorSourceSection_of_coordinate
    (S : Type u) [CommRing S] [IsDedekindDomain S]
    [Algebra R S] [Algebra.Etale R S]
    (V : (Spec (CommRingCat.of R)).Etale)
    (E : V ≅ affineEtaleSpecObject (R := R) (S := S))
    (s : (closedPointDivisorSheaf X).obj.obj
      (op ((etalePostcompose (e.hom ≫ U.ι)).obj V))) :
    affineChartDivisorSourceSection R U e S
        (Spec.map (CommRingCat.ofHom (algebraMap R S)) ≫ (e.hom ≫ U.ι)) rfl
        ((closedPointDivisorSheaf X).obj.map
          ((etalePostcompose (e.hom ≫ U.ι)).map E.inv).op s) =
      (closedPointDivisorSheaf (Spec (CommRingCat.of R))).obj.map E.inv.op
        ((affineChartDivisorIso R U e).hom.hom.app (op V) s) := by
  let i := e.hom ≫ U.ι
  let q := Spec.map (CommRingCat.ofHom (algebraMap R S)) ≫ i
  let DX := closedPointDivisorSheaf X
  let c := affineChartDivisorSourceObjectIso R U e S q rfl
  let m : Scheme.Etale.mk q ⟶ (etalePostcompose i).obj V :=
    (etalePostcompose i).map E.inv
  have hcomp : c.hom ≫ m = (etalePostcompose i).map E.inv := by
    apply MorphismProperty.Over.Hom.ext
    change (𝟙 _) ≫ E.inv.left = E.inv.left
    exact Category.id_comp _
  have hmap : DX.obj.map m.op ≫ DX.obj.map c.hom.op =
      DX.obj.map ((etalePostcompose i).map E.inv).op := by
    calc
      _ = DX.obj.map (m.op ≫ c.hom.op) := (DX.obj.map_comp _ _).symm
      _ = DX.obj.map (c.hom ≫ m).op := rfl
      _ = _ := congrArg (fun z => DX.obj.map z.op) hcomp
  have hn := ConcreteCategory.congr_hom
    ((affineChartDivisorIso R U e).hom.hom.naturality E.inv.op) s
  change (affineChartDivisorIso R U e).hom.hom.app
      (op (affineEtaleSpecObject (R := R) (S := S)))
      (DX.obj.map c.hom.op (DX.obj.map m.op s)) = _
  exact (congrArg ((affineChartDivisorIso R U e).hom.hom.app
    (op (affineEtaleSpecObject (R := R) (S := S))))
      (ConcreteCategory.congr_hom hmap s)).trans hn

end DedekindCharts

end DivisorGenericUnitGlobal

end EtaleCohomology
