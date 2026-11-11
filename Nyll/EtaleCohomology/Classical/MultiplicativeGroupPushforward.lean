/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.EtaleCohomology.Sites.EtaleRestrictionSections
public import Nyll.EtaleCohomology.Classical.MultiplicativeGroup
public import Nyll.EtaleCohomology.Classical.KummerSequence
public import Nyll.EtaleCohomology.Classical.AbelianSheafFunctors
public import Nyll.EtaleCohomology.Classical.EtaleRestriction
public import Nyll.SchemeTheory.CategoryTheory.CokernelNsmulQuotient
public import Mathlib.AlgebraicGeometry.FunctionField
public import Mathlib.AlgebraicGeometry.Stalk
public import Mathlib.AlgebraicGeometry.Morphisms.SchemeTheoreticallyDominant
public import Mathlib.CategoryTheory.Limits.FunctorCategory.EpiMono
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Kernels
public import Mathlib.Algebra.Homology.ShortComplex.ShortExact

/-!
# The actual unit map to direct image

For an arbitrary scheme morphism, restriction of units along the actual
base-change projection gives Gm on the target a map to the direct image
of Gm on the source. This is the map used at the generic point in the
divisor sequence. Its construction uses the existing sheaf of units.
-/

@[expose] public section

noncomputable section
universe u
open AlgebraicGeometry CategoryTheory Limits Opposite

namespace EtaleCohomology

variable {X Y : Scheme.{u}} (f : X ⟶ Y)

/-- Restriction along base-change projections is natural on the original étale site. -/
theorem unitProjection_naturality
    (P : Scheme.{u}ᵒᵖ ⥤ AddCommGrpCat.{u})
    {V W : Y.Etale} (g : V ⟶ W) :
    P.map g.left.op ≫ P.map (pullback.fst V.hom f).op =
      P.map (pullback.fst W.hom f).op ≫
        P.map (((etaleBaseChange f).map g).left).op := by
  have hproj :
      ((etaleBaseChange f).map g).left ≫ pullback.fst W.hom f =
        pullback.fst V.hom f ≫ g.left := by
    dsimp only [etaleBaseChange]
    exact pullback.lift_fst _ _ _
  exact (P.map_comp g.left.op (pullback.fst V.hom f).op).symm.trans
    ((congrArg (fun k : pullback V.hom f ⟶ W.left => P.map k.op)
      hproj.symm).trans
        (P.map_comp (pullback.fst W.hom f).op
          (((etaleBaseChange f).map g).left).op))

/-- Pullback of actual units along base-change projections, as a
morphism to the actual abelian direct image. -/
def etaleMultiplicativeGroupToPushforward :
    etaleMultiplicativeGroupSheaf Y ⟶
      (etaleAbelianPushforward f).obj (etaleMultiplicativeGroupSheaf X) :=
  ⟨{ app V := FppfRepresentableGroupSchemeSheaf.GmAbelianSheaf.obj.map
        (pullback.fst V.unop.hom f).op
     naturality {_ _} g :=
       unitProjection_naturality f
         FppfRepresentableGroupSchemeSheaf.GmAbelianSheaf.obj g.unop }⟩

/-- On sections the direct-image map is exactly pullback of units by the
global-section ring homomorphism of the base-change projection. -/
theorem etaleMultiplicativeGroupToPushforward_apply
    (V : Y.Etale) (s : (etaleMultiplicativeGroupSheaf Y).obj.obj (op V)) :
    etaleMultiplicativeGroupSectionsEquiv X ((etaleBaseChange f).obj V)
      ((etaleMultiplicativeGroupToPushforward f).hom.app (op V) s) =
      Additive.ofMul (Units.map ((pullback.fst V.hom f).appTop.hom.toMonoidHom)
        (etaleMultiplicativeGroupSectionsEquiv Y V s).toMul) := rfl

/-- A unit of an affine generic point defines a natural section of the
actual direct image of units on every etale object over the affine base. -/
theorem rationalUnitDirectImage_naturality
    {R K : Type u} [CommRing R] [CommRing K] [Algebra R K]
    (W V : (Spec (CommRingCat.of R)).Etale) (m : V ⟶ W)
    (a : Additive Kˣ) :
    ((etaleAbelianPushforward
      (Spec.map (CommRingCat.ofHom (algebraMap R K)))).obj
      (etaleMultiplicativeGroupSheaf (Spec (CommRingCat.of K)))).obj.map
      m.op
      (Additive.ofMul (Units.map
        (((Scheme.ΓSpecIso (CommRingCat.of K)).inv ≫
          (pullback.snd W.hom
            (Spec.map (CommRingCat.ofHom (algebraMap R K)))).appTop).hom.toMonoidHom)
        a.toMul)) =
    Additive.ofMul (Units.map
      (((Scheme.ΓSpecIso (CommRingCat.of K)).inv ≫
        (pullback.snd V.hom
          (Spec.map (CommRingCat.ofHom (algebraMap R K)))).appTop).hom.toMonoidHom)
      a.toMul) := by
  let j := Spec.map (CommRingCat.ofHom (algebraMap R K))
  let k := ((etaleBaseChange j).map m).left
  have hsnd : k ≫ pullback.snd W.hom j = pullback.snd V.hom j := by
    dsimp only [k, etaleBaseChange]
    exact pullback.lift_snd _ _ _
  have hrings :
      (Scheme.ΓSpecIso (CommRingCat.of K)).inv ≫ (pullback.snd V.hom j).appTop =
      ((Scheme.ΓSpecIso (CommRingCat.of K)).inv ≫
        (pullback.snd W.hom j).appTop) ≫ k.appTop := by
    exact (congrArg
      (fun l : pullback V.hom j ⟶ Spec (CommRingCat.of K) =>
        (Scheme.ΓSpecIso (CommRingCat.of K)).inv ≫ l.appTop) hsnd.symm).trans
      ((congrArg (fun l => (Scheme.ΓSpecIso (CommRingCat.of K)).inv ≫ l)
        (Scheme.Hom.comp_appTop k (pullback.snd W.hom j))).trans
          (Category.assoc _ _ _).symm)
  change ((etaleAbelianPushforward j).obj
    (etaleMultiplicativeGroupSheaf (Spec (CommRingCat.of K)))).obj.map
      m.op _ = _
  apply Additive.toMul.injective
  apply Units.ext
  exact (ConcreteCategory.congr_hom hrings a.toMul.val).symm

/-- The actual unit direct-image map commutes with nth powers. -/
theorem etaleMultiplicativeGroupToPushforward_power (n : ℕ) :
    etaleMultiplicativeGroupPower Y n ≫ etaleMultiplicativeGroupToPushforward f =
      etaleMultiplicativeGroupToPushforward f ≫
        (etaleAbelianPushforward f).map (etaleMultiplicativeGroupPower X n) := by
  rw [etaleMultiplicativeGroupPower, etaleMultiplicativeGroupPower,
    (etaleAbelianPushforward f).map_nsmul,
    (etaleAbelianPushforward f).map_id]
  rw [Preadditive.nsmul_comp, Preadditive.comp_nsmul,
    Category.id_comp, Category.comp_id]

/-- Schematic dominance makes restriction of unit sections injective
after every actual etale base change. -/
theorem etaleMultiplicativeGroupToPushforward_app_injective
    [IsSchemeTheoreticallyDominant f] [QuasiCompact f] (V : Y.Etale) :
    Function.Injective ((etaleMultiplicativeGroupToPushforward f).hom.app (op V)) := by
  intro a b h
  have hu := congrArg
    (etaleMultiplicativeGroupSectionsEquiv X ((etaleBaseChange f).obj V)) h
  rw [etaleMultiplicativeGroupToPushforward_apply,
    etaleMultiplicativeGroupToPushforward_apply] at hu
  apply (etaleMultiplicativeGroupSectionsEquiv Y V).injective
  apply Additive.toMul.injective
  apply Units.ext
  have hf : Function.Injective (pullback.fst V.hom f).appTop :=
    (pullback.fst V.hom f).app_injective ⊤
  apply hf
  exact congrArg (fun z : Additive ((Γ(((etaleBaseChange f).obj V).left, ⊤) : Type u)ˣ) =>
    z.toMul.val) hu

/-- The actual map from Gm to its direct image is monic for a
quasi-compact schematically dominant morphism. -/
theorem etaleMultiplicativeGroupToPushforward_mono
    [IsSchemeTheoreticallyDominant f] [QuasiCompact f] :
    Mono (etaleMultiplicativeGroupToPushforward f) := by
  have : ∀ V : Y.Etaleᵒᵖ,
      Mono ((etaleMultiplicativeGroupToPushforward f).hom.app V) := by
    intro V
    exact (AddCommGrpCat.mono_iff_injective _).mpr
      (etaleMultiplicativeGroupToPushforward_app_injective f V.unop)
  have hm : Mono (etaleMultiplicativeGroupToPushforward f).hom :=
    NatTrans.mono_of_mono_app _
  exact (sheafToPresheaf Y.smallEtaleTopology AddCommGrpCat.{u}).mono_of_mono_map hm

/-- Restriction of units to the actual fraction-field generic point is
monic for an affine integral scheme. -/
theorem etaleMultiplicativeGroupToFractionField_mono
    (R : Type u) [CommRing R] [IsDomain R] :
    Mono (etaleMultiplicativeGroupToPushforward
      (Spec.map (CommRingCat.ofHom (algebraMap R (FractionRing R))))) := by
  let j := Spec.map (CommRingCat.ofHom (algebraMap R (FractionRing R)))
  have : IsDominant j := by
    rw [isDominant_iff]
    change DenseRange (PrimeSpectrum.comap (algebraMap R (FractionRing R)))
    apply (PrimeSpectrum.denseRange_comap_iff_ker_le_nilRadical _).mpr
    rw [(RingHom.injective_iff_ker_eq_bot _).mp
      (IsFractionRing.injective R (FractionRing R))]
    exact bot_le
  have : IsSchemeTheoreticallyDominant j :=
    IsSchemeTheoreticallyDominant.of_isDominant j
  exact etaleMultiplicativeGroupToPushforward_mono j

/-- At the actual generic point of an integral scheme, the unit map to
the actual direct image is monic. No dominance hypothesis is required:
it follows from the generic point itself. -/
theorem etaleMultiplicativeGroupToGenericPoint_mono
    (Z : Scheme.{u}) [IsIntegral Z] :
    Mono (etaleMultiplicativeGroupToPushforward
      (Z.fromSpecStalk (genericPoint Z))) := by
  let j := Z.fromSpecStalk (genericPoint Z)
  have : QuasiCompact j :=
    { isCompact_preimage := fun U _ _ => (Set.toFinite (j ⁻¹' U)).isCompact }
  have : IsDominant j := by
    rw [isDominant_iff, DenseRange, dense_iff_closure_eq]
    apply Set.eq_univ_of_forall
    intro z
    apply (genericPoint_specializes z).mem_closed isClosed_closure
    exact subset_closure
      ⟨IsLocalRing.closedPoint (CommRingCat.of Z.functionField),
        Scheme.fromSpecStalk_closedPoint (X := Z)
          (x := genericPoint Z)⟩
  have : IsSchemeTheoreticallyDominant j :=
    IsSchemeTheoreticallyDominant.of_isDominant j
  exact etaleMultiplicativeGroupToPushforward_mono j

/-- The actual quotient of generic-point units by regular units.
Its identification with the closed-point divisor sheaf is a separate
geometric statement, not part of this definition. -/
def etaleGenericUnitQuotient (X : Scheme.{u}) [IsIntegral X] :
    Sheaf X.smallEtaleTopology AddCommGrpCat.{u} :=
  cokernel (etaleMultiplicativeGroupToPushforward
    (X.fromSpecStalk (genericPoint X)))

/-- The actual generic-point unit sequence, with its categorical quotient. -/
def etaleGenericUnitShortComplex (X : Scheme.{u}) [IsIntegral X] :
    ShortComplex (Sheaf X.smallEtaleTopology AddCommGrpCat.{u}) :=
  ShortComplex.mk
    (etaleMultiplicativeGroupToPushforward (X.fromSpecStalk (genericPoint X)))
    (cokernel.π _)
    (cokernel.condition _)

/-- The generic-point unit sequence is short exact as a sequence of
actual etale sheaves. This does not assert surjectivity on global sections. -/
theorem etaleGenericUnitShortComplex_shortExact
    (X : Scheme.{u}) [IsIntegral X] :
    (etaleGenericUnitShortComplex X).ShortExact := by
  have : Mono (etaleMultiplicativeGroupToPushforward
      (X.fromSpecStalk (genericPoint X))) :=
    etaleMultiplicativeGroupToGenericPoint_mono X
  unfold etaleGenericUnitShortComplex
  exact { exact := ShortComplex.exact_cokernel _ }

/-- For invertible n, the actual quotient map from direct-image units
induces an isomorphism modulo nth powers. -/
def etalePushforwardPowerCokernelIso {n : ℕ} (hn : 0 < n)
    (hnY : IsUnit (n : Γ(Y, ⊤))) :
    cokernel ((etaleAbelianPushforward f).map (etaleMultiplicativeGroupPower X n)) ≅
      cokernel (n • 𝟙 (cokernel (etaleMultiplicativeGroupToPushforward f))) := by
  have : Epi (n • 𝟙 (etaleMultiplicativeGroupSheaf Y)) :=
    etaleMultiplicativeGroupPower_epi Y hn hnY
  rw [etaleMultiplicativeGroupPower, (etaleAbelianPushforward f).map_nsmul,
    (etaleAbelianPushforward f).map_id]
  exact cokernelNsmulQuotientIso (etaleMultiplicativeGroupToPushforward f) n

end EtaleCohomology

namespace EtaleCohomology

section EtaleUnitCartesianBaseChange

variable {X Y U P₀ : Scheme.{u}} (i : U ⟶ X) [Etale i] (f : Y ⟶ X)
  (p : P₀ ⟶ U) (g : P₀ ⟶ Y) [Etale g] (H : IsPullback p g i f)

/-- Actual direct image of units commutes with restriction on any cartesian
square whose right projection is étale. -/
def etaleRestrictionMultiplicativeGroupPushforwardIsoOfIsPullback :
    (etaleRestriction i AddCommGrpCat.{u}).obj
      ((etaleAbelianPushforward f).obj (etaleMultiplicativeGroupSheaf Y)) ≅
    (etaleAbelianPushforward p).obj (etaleMultiplicativeGroupSheaf P₀) :=
  (etaleRestrictionPushforwardBaseChangeIsoOfIsPullback i f AddCommGrpCat.{u}
      p g H).app (etaleMultiplicativeGroupSheaf Y) ≪≫
    (etaleAbelianPushforward p).mapIso
      (etaleRestrictionMultiplicativeGroupIso g)

/-- On sections, the cartesian pushforward comparison is the actual map
induced by its canonical pullback-square isomorphism. -/
theorem etaleRestrictionMultiplicativeGroupPushforwardIsoOfIsPullback_app
    {P : Scheme.{u}} (p : P ⟶ U) (g : P ⟶ Y) [Etale g]
    (H : IsPullback p g i f) (V : U.Etale)
    (s : (etaleAbelianPushforward f).obj
      (etaleMultiplicativeGroupSheaf Y) |>.obj.obj
        (op ((etalePostcompose i).obj V))) :
    ConcreteCategory.hom
      ((((sheafToPresheaf U.smallEtaleTopology AddCommGrpCat).mapIso
        (etaleRestrictionMultiplicativeGroupPushforwardIsoOfIsPullback
          i f p g H)).hom.app (op V))) s =
    ConcreteCategory.hom
      ((FppfRepresentableGroupSchemeSheaf.GmAbelianSheaf.obj.map
        (((IsPullback.of_hasPullback V.hom p).paste_vert H).isoPullback.hom).op)) s := by
  rfl

/-- The cartesian-square comparison commutes with the actual map of units
to direct-image units. -/
theorem etaleRestrictionMultiplicativeGroupToPushforwardOfIsPullback :
    (etaleRestriction i AddCommGrpCat.{u}).map
        (etaleMultiplicativeGroupToPushforward f) ≫
      (etaleRestrictionMultiplicativeGroupPushforwardIsoOfIsPullback
        i f p g H).hom =
    (etaleRestrictionMultiplicativeGroupIso i).hom ≫
      etaleMultiplicativeGroupToPushforward p := by
  apply Sheaf.hom_ext
  apply NatTrans.ext
  funext V
  let P := FppfRepresentableGroupSchemeSheaf.GmAbelianSheaf.obj
  change P.map (pullback.fst (V.unop.hom ≫ i) f).op ≫
    P.map (((IsPullback.of_hasPullback V.unop.hom p).paste_vert H).isoPullback).hom.op =
      P.map (pullback.fst V.unop.hom p).op
  rw [← P.map_comp, ← op_comp,
    ((IsPullback.of_hasPullback V.unop.hom p).paste_vert H).isoPullback_hom_fst]

/-- The quotient of direct-image units by regular units commutes with
restriction on any cartesian square. -/
def etaleRestrictionUnitQuotientIsoOfIsPullback :
    (etaleRestriction i AddCommGrpCat.{u}).obj
      (cokernel (etaleMultiplicativeGroupToPushforward f)) ≅
    cokernel (etaleMultiplicativeGroupToPushforward p) :=
  PreservesCokernel.iso (etaleRestriction i AddCommGrpCat.{u})
      (etaleMultiplicativeGroupToPushforward f) ≪≫
    cokernel.mapIso
      (f := (etaleRestriction i AddCommGrpCat.{u}).map
        (etaleMultiplicativeGroupToPushforward f))
      (f' := etaleMultiplicativeGroupToPushforward p)
      (etaleRestrictionMultiplicativeGroupIso i)
      (etaleRestrictionMultiplicativeGroupPushforwardIsoOfIsPullback
        i f p g H)
      (etaleRestrictionMultiplicativeGroupToPushforwardOfIsPullback
        i f p g H)

/-- The cartesian-square quotient comparison preserves the cokernel
projection. -/
theorem etaleRestrictionUnitQuotientIsoOfIsPullback_π :
    (etaleRestriction i AddCommGrpCat.{u}).map
        (cokernel.π (etaleMultiplicativeGroupToPushforward f)) ≫
      (etaleRestrictionUnitQuotientIsoOfIsPullback i f p g H).hom =
    (etaleRestrictionMultiplicativeGroupPushforwardIsoOfIsPullback
      i f p g H).hom ≫
      cokernel.π (etaleMultiplicativeGroupToPushforward p) := by
  change (etaleRestriction i AddCommGrpCat.{u}).map
      (cokernel.π (etaleMultiplicativeGroupToPushforward f)) ≫
    ((PreservesCokernel.iso (etaleRestriction i AddCommGrpCat.{u})
      (etaleMultiplicativeGroupToPushforward f)) ≪≫
      cokernel.mapIso
        (f := (etaleRestriction i AddCommGrpCat.{u}).map
          (etaleMultiplicativeGroupToPushforward f))
        (f' := etaleMultiplicativeGroupToPushforward p)
        (etaleRestrictionMultiplicativeGroupIso i)
        (etaleRestrictionMultiplicativeGroupPushforwardIsoOfIsPullback
          i f p g H)
        (etaleRestrictionMultiplicativeGroupToPushforwardOfIsPullback
          i f p g H)).hom = _
  rw [Iso.trans_hom, ← Category.assoc, PreservesCokernel.π_iso_hom]
  rw [cokernel.mapIso_hom, cokernel.map]
  exact cokernel.π_desc _ _ _

end EtaleUnitCartesianBaseChange

section EtaleUnitBaseChange

variable {X Y U : Scheme.{u}} (i : U ⟶ X) [Etale i] (f : Y ⟶ X)

/-- Actual direct image of the unit sheaf restricts to the unit direct image
on the étale pullback square. -/
def etaleRestrictionMultiplicativeGroupPushforwardIso :
    (etaleRestriction i AddCommGrpCat.{u}).obj
      ((etaleAbelianPushforward f).obj (etaleMultiplicativeGroupSheaf Y)) ≅
    (etaleAbelianPushforward (pullback.fst i f)).obj
      (etaleMultiplicativeGroupSheaf (pullback i f)) :=
  etaleRestrictionMultiplicativeGroupPushforwardIsoOfIsPullback i f
    (pullback.fst i f) (pullback.snd i f) (IsPullback.of_hasPullback i f)

/-- The étale base-change comparison commutes with the actual map of units
to generic or other direct-image units. -/
theorem etaleRestrictionMultiplicativeGroupToPushforward :
    (etaleRestriction i AddCommGrpCat.{u}).map
        (etaleMultiplicativeGroupToPushforward f) ≫
      (etaleRestrictionMultiplicativeGroupPushforwardIso i f).hom =
    (etaleRestrictionMultiplicativeGroupIso i).hom ≫
      etaleMultiplicativeGroupToPushforward (pullback.fst i f) :=
  etaleRestrictionMultiplicativeGroupToPushforwardOfIsPullback i f
    (pullback.fst i f) (pullback.snd i f) (IsPullback.of_hasPullback i f)

/-- The actual quotient of direct-image units by regular units commutes
with étale restriction. -/
def etaleRestrictionUnitQuotientIso :
    (etaleRestriction i AddCommGrpCat.{u}).obj
      (cokernel (etaleMultiplicativeGroupToPushforward f)) ≅
    cokernel (etaleMultiplicativeGroupToPushforward (pullback.fst i f)) :=
  etaleRestrictionUnitQuotientIsoOfIsPullback i f
    (pullback.fst i f) (pullback.snd i f) (IsPullback.of_hasPullback i f)

/-- The quotient comparison preserves the actual cokernel projection. -/
theorem etaleRestrictionUnitQuotientIso_π :
    (etaleRestriction i AddCommGrpCat.{u}).map
        (cokernel.π (etaleMultiplicativeGroupToPushforward f)) ≫
      (etaleRestrictionUnitQuotientIso i f).hom =
    (etaleRestrictionMultiplicativeGroupPushforwardIso i f).hom ≫
      cokernel.π (etaleMultiplicativeGroupToPushforward (pullback.fst i f)) :=
  etaleRestrictionUnitQuotientIsoOfIsPullback_π i f
    (pullback.fst i f) (pullback.snd i f) (IsPullback.of_hasPullback i f)

end EtaleUnitBaseChange

/-- The actual unit pushforward comparison respects vertical pasting of
cartesian squares. -/
theorem etaleRestrictionUnitPushforward_paste
    {X Y U V P₀ Q₀ : Scheme.{u}}
    (i : U ⟶ X) [Etale i] (j : V ⟶ U) [Etale j]
    (f : Y ⟶ X) (p : P₀ ⟶ U) (g : P₀ ⟶ Y) [Etale g]
    (q : Q₀ ⟶ V) (h : Q₀ ⟶ P₀) [Etale h]
    (H : IsPullback p g i f) (H' : IsPullback q h j p) :
    (etaleRestriction j AddCommGrpCat.{u}).map
        (etaleRestrictionMultiplicativeGroupPushforwardIsoOfIsPullback
          i f p g H).hom ≫
      (etaleRestrictionMultiplicativeGroupPushforwardIsoOfIsPullback
        j p q h H').hom =
    (etaleRestrictionCompIso j i AddCommGrpCat.{u}).hom.app
        ((etaleAbelianPushforward f).obj (etaleMultiplicativeGroupSheaf Y)) ≫
      (etaleRestrictionMultiplicativeGroupPushforwardIsoOfIsPullback
        (j ≫ i) f q (h ≫ g) (H'.paste_vert H)).hom := by
  apply Sheaf.hom_ext
  apply NatTrans.ext
  funext W
  let M := FppfRepresentableGroupSchemeSheaf.GmAbelianSheaf.obj
  let c₁ := ((IsPullback.of_hasPullback (W.unop.hom ≫ j) p).paste_vert H).isoPullback
  let c₂ := ((IsPullback.of_hasPullback W.unop.hom q).paste_vert H').isoPullback
  let c₃ := ((IsPullback.of_hasPullback W.unop.hom q).paste_vert
    (H'.paste_vert H)).isoPullback
  let a : pullback (W.unop.hom ≫ (j ≫ i)) f ⟶
      pullback ((W.unop.hom ≫ j) ≫ i) f := ((etaleBaseChange f).map
    ((MorphismProperty.Over.mapComp
      (P := show MorphismProperty Scheme.{u} from @Etale) (Q := ⊤)
      (f := j) inferInstance (g := i) inferInstance).hom.app W.unop)).left
  change M.map c₁.hom.op ≫ M.map c₂.hom.op =
    M.map a.op ≫ M.map c₃.hom.op
  rw [← M.map_comp]
  rw [← M.map_comp a.op c₃.hom.op]
  rw [← op_comp]
  rw [← op_comp (f := c₃.hom) (g := a)]
  apply congrArg
  apply congrArg
  have ha₁ : a ≫ pullback.fst ((W.unop.hom ≫ j) ≫ i) f =
      pullback.fst (W.unop.hom ≫ (j ≫ i)) f := by
    change (pullback.lift
      (pullback.fst (W.unop.hom ≫ (j ≫ i)) f ≫ 𝟙 W.unop.left)
      (pullback.snd (W.unop.hom ≫ (j ≫ i)) f) _) ≫
        pullback.fst ((W.unop.hom ≫ j) ≫ i) f = _
    exact (pullback.lift_fst
      (pullback.fst (W.unop.hom ≫ (j ≫ i)) f ≫ 𝟙 W.unop.left)
      (pullback.snd (W.unop.hom ≫ (j ≫ i)) f) _).trans
        (Category.comp_id _)
  have ha₂ : a ≫ pullback.snd ((W.unop.hom ≫ j) ≫ i) f =
      pullback.snd (W.unop.hom ≫ (j ≫ i)) f := by
    dsimp only [a, etaleBaseChange]
    exact pullback.lift_snd _ _ _
  apply pullback.hom_ext
  · rw [Category.assoc c₂.hom c₁.hom (pullback.fst ((W.unop.hom ≫ j) ≫ i) f),
      Category.assoc c₃.hom a (pullback.fst ((W.unop.hom ≫ j) ≫ i) f), ha₁]
    dsimp only [c₁, c₂, c₃]
    simp only [IsPullback.isoPullback_hom_fst]
  · rw [Category.assoc c₂.hom c₁.hom (pullback.snd ((W.unop.hom ≫ j) ≫ i) f),
      Category.assoc c₃.hom a (pullback.snd ((W.unop.hom ≫ j) ≫ i) f), ha₂]
    have hc₁ : c₁.hom ≫ pullback.snd ((W.unop.hom ≫ j) ≫ i) f =
        pullback.snd (W.unop.hom ≫ j) p ≫ g :=
      ((IsPullback.of_hasPullback (W.unop.hom ≫ j) p).paste_vert H).isoPullback_hom_snd
    have hc₂ : c₂.hom ≫ pullback.snd (W.unop.hom ≫ j) p =
        pullback.snd W.unop.hom q ≫ h :=
      ((IsPullback.of_hasPullback W.unop.hom q).paste_vert H').isoPullback_hom_snd
    have hc₃ : c₃.hom ≫ pullback.snd (W.unop.hom ≫ (j ≫ i)) f =
        pullback.snd W.unop.hom q ≫ (h ≫ g) :=
      ((IsPullback.of_hasPullback W.unop.hom q).paste_vert
        (H'.paste_vert H)).isoPullback_hom_snd
    rw [hc₁, hc₃, ← Category.assoc c₂.hom (pullback.snd (W.unop.hom ≫ j) p) g, hc₂]
    exact Category.assoc _ _ _


/-- The quotient comparison for units respects vertical pasting of
cartesian squares. -/
theorem etaleRestrictionUnitQuotient_paste
    {X Y U V P₀ Q₀ : Scheme.{u}}
    (i : U ⟶ X) [Etale i] (j : V ⟶ U) [Etale j]
    (f : Y ⟶ X) (p : P₀ ⟶ U) (g : P₀ ⟶ Y) [Etale g]
    (q : Q₀ ⟶ V) (h : Q₀ ⟶ P₀) [Etale h]
    (H : IsPullback p g i f) (H' : IsPullback q h j p) :
    (etaleRestriction j AddCommGrpCat.{u}).map
        (etaleRestrictionUnitQuotientIsoOfIsPullback i f p g H).hom ≫
      (etaleRestrictionUnitQuotientIsoOfIsPullback j p q h H').hom =
    (etaleRestrictionCompIso j i AddCommGrpCat.{u}).hom.app
        (cokernel (etaleMultiplicativeGroupToPushforward f)) ≫
      (etaleRestrictionUnitQuotientIsoOfIsPullback
        (j ≫ i) f q (h ≫ g) (H'.paste_vert H)).hom := by
  let Ri := etaleRestriction i AddCommGrpCat.{u}
  let Rj := etaleRestriction j AddCommGrpCat.{u}
  let Rc := etaleRestriction (j ≫ i) AddCommGrpCat.{u}
  let πf := cokernel.π (etaleMultiplicativeGroupToPushforward f)
  let πp := cokernel.π (etaleMultiplicativeGroupToPushforward p)
  let πq := cokernel.π (etaleMultiplicativeGroupToPushforward q)
  let u₁ := (etaleRestrictionUnitQuotientIsoOfIsPullback i f p g H).hom
  let u₂ := (etaleRestrictionUnitQuotientIsoOfIsPullback j p q h H').hom
  let u₃ := (etaleRestrictionUnitQuotientIsoOfIsPullback
    (j ≫ i) f q (h ≫ g) (H'.paste_vert H)).hom
  let v₁ := (etaleRestrictionMultiplicativeGroupPushforwardIsoOfIsPullback
    i f p g H).hom
  let v₂ := (etaleRestrictionMultiplicativeGroupPushforwardIsoOfIsPullback
    j p q h H').hom
  let v₃ := (etaleRestrictionMultiplicativeGroupPushforwardIsoOfIsPullback
    (j ≫ i) f q (h ≫ g) (H'.paste_vert H)).hom
  let c := (etaleRestrictionCompIso j i AddCommGrpCat.{u}).hom
  have h₁ : Ri.map πf ≫ u₁ = v₁ ≫ πp :=
    etaleRestrictionUnitQuotientIsoOfIsPullback_π i f p g H
  have h₂ : Rj.map πp ≫ u₂ = v₂ ≫ πq :=
    etaleRestrictionUnitQuotientIsoOfIsPullback_π j p q h H'
  have h₃ : Rc.map πf ≫ u₃ = v₃ ≫ πq :=
    etaleRestrictionUnitQuotientIsoOfIsPullback_π
      (j ≫ i) f q (h ≫ g) (H'.paste_vert H)
  have hv : Rj.map v₁ ≫ v₂ = c.app _ ≫ v₃ :=
    etaleRestrictionUnitPushforward_paste i j f p g q h H H'
  change Rj.map u₁ ≫ u₂ = c.app _ ≫ u₃
  apply (cancel_epi (Rj.map (Ri.map πf))).mp
  calc
    Rj.map (Ri.map πf) ≫ (Rj.map u₁ ≫ u₂) =
        Rj.map (Ri.map πf ≫ u₁) ≫ u₂ := by
      rw [Rj.map_comp, Category.assoc]
    _ = Rj.map (v₁ ≫ πp) ≫ u₂ := by rw [h₁]
    _ = Rj.map v₁ ≫ (Rj.map πp ≫ u₂) := by
      rw [Rj.map_comp, Category.assoc]
    _ = Rj.map v₁ ≫ (v₂ ≫ πq) := by rw [h₂]
    _ = (c.app _ ≫ v₃) ≫ πq := by rw [← Category.assoc, hv]
    _ = c.app _ ≫ (Rc.map πf ≫ u₃) := by
      rw [Category.assoc, h₃]
    _ = Rj.map (Ri.map πf) ≫ (c.app _ ≫ u₃) := by
      rw [← Category.assoc, ← c.naturality πf]
      rfl


/-- The quotient comparison on actual base-site objects commutes with
restriction along a tower of cartesian étale squares. -/
theorem etaleRestrictionUnitQuotient_sections_tower
    {X Y U V P₀ Q₀ : Scheme.{u}}
    (i : U ⟶ X) [Etale i] (j : V ⟶ U) [Etale j]
    (f : Y ⟶ X) (p : P₀ ⟶ U) (g : P₀ ⟶ Y) [Etale g]
    (q : Q₀ ⟶ V) (h : Q₀ ⟶ P₀) [Etale h]
    (H : IsPullback p g i f) (H' : IsPullback q h j p) :
    let W := (zariskiToEtale V).obj ⊤
    let WU := (zariskiToEtale U).obj ⊤
    let t : (etalePostcompose j).obj W ⟶ WU :=
      (show (etalePostcompose j).obj W ⟶ Scheme.Etale.mk (𝟙 U) from
        MorphismProperty.Over.homMk ((etalePostcompose j).obj W).hom
          (Category.comp_id _)) ≫ (zariskiToEtaleTopIso U).inv
    let m : Scheme.Etale.mk (j ≫ i) ⟶ Scheme.Etale.mk i :=
      MorphismProperty.Over.homMk j rfl
    let F := cokernel (etaleMultiplicativeGroupToPushforward f)
    let G := cokernel (etaleMultiplicativeGroupToPushforward p)
    let a := (etaleRestrictionUnitQuotientIsoOfIsPullback i f p g H).hom
    let b := (etaleRestrictionUnitQuotientIsoOfIsPullback j p q h H').hom
    let d := (etaleRestrictionUnitQuotientIsoOfIsPullback
      (j ≫ i) f q (h ≫ g) (H'.paste_vert H)).hom
    F.obj.map m.op ≫ F.obj.map (etalePostcomposeTopObjectIso (j ≫ i)).hom.op ≫
        d.hom.app (op W) =
      F.obj.map (etalePostcomposeTopObjectIso i).hom.op ≫ a.hom.app (op WU) ≫
        G.obj.map t.op ≫ b.hom.app (op W) := by
  intro W WU t m F G a b d
  let c := (MorphismProperty.Over.mapComp
    (P := show MorphismProperty Scheme.{u} from @Etale) (Q := ⊤)
    (f := j) inferInstance (g := i) inferInstance).hom.app W
  have ht := etaleTopObjectSections_tower j i F
  have hn := a.hom.naturality t.op
  have hp := congrArg (fun e => e.hom.app (op W))
    (etaleRestrictionUnitQuotient_paste i j f p g q h H H')
  change F.obj.map m.op ≫ F.obj.map (etalePostcomposeTopObjectIso (j ≫ i)).hom.op =
    F.obj.map (etalePostcomposeTopObjectIso i).hom.op ≫
      F.obj.map ((etalePostcompose i).map t).op ≫ F.obj.map c.op at ht
  change F.obj.map ((etalePostcompose i).map t).op ≫
      a.hom.app (op ((etalePostcompose j).obj W)) =
    a.hom.app (op WU) ≫ G.obj.map t.op at hn
  change a.hom.app (op ((etalePostcompose j).obj W)) ≫ b.hom.app (op W) =
    F.obj.map c.op ≫ d.hom.app (op W) at hp
  have hc {A B C D E F₁ G₁ : AddCommGrpCat.{u}}
      (α : A ⟶ B) (β : B ⟶ C) (γ : C ⟶ D) (δ : D ⟶ E)
      (ε : C ⟶ F₁) (ζ : F₁ ⟶ E) (η : B ⟶ G₁) (θ : G₁ ⟶ F₁)
      (h₁ : ε ≫ ζ = γ ≫ δ) (h₂ : β ≫ ε = η ≫ θ) :
      (α ≫ β ≫ γ) ≫ δ = α ≫ η ≫ θ ≫ ζ := by
    simp only [Category.assoc]
    rw [← h₁, ← Category.assoc β ε ζ, h₂, Category.assoc]
  calc
    _ = (F.obj.map m.op ≫
        F.obj.map (etalePostcomposeTopObjectIso (j ≫ i)).hom.op) ≫
        d.hom.app (op W) := (Category.assoc _ _ _).symm
    _ = (F.obj.map (etalePostcomposeTopObjectIso i).hom.op ≫
        F.obj.map ((etalePostcompose i).map t).op ≫ F.obj.map c.op) ≫
        d.hom.app (op W) := congrArg (fun e => e ≫ d.hom.app (op W)) ht
    _ = _ := hc _ _ _ _ _ _ _ _ hp hn

/-- The section comparison is invariant under identifying the composite maps. -/
theorem etaleRestrictionUnitQuotient_sections_tower_eq
    {X Y U V P₀ Q₀ : Scheme.{u}}
    (i : U ⟶ X) [Etale i] (j : V ⟶ U) [Etale j]
    (f : Y ⟶ X) (p : P₀ ⟶ U) (g : P₀ ⟶ Y) [Etale g]
    (q : Q₀ ⟶ V) (h : Q₀ ⟶ P₀) [Etale h]
    (H : IsPullback p g i f) (H' : IsPullback q h j p)
    (k : V ⟶ X) [Etale k] (l : Q₀ ⟶ Y) [Etale l]
    (hi : j ≫ i = k) (hg : h ≫ g = l) (H'' : IsPullback q l k f) :
    let W := (zariskiToEtale V).obj ⊤
    let WU := (zariskiToEtale U).obj ⊤
    let t : (etalePostcompose j).obj W ⟶ WU :=
      (show (etalePostcompose j).obj W ⟶ Scheme.Etale.mk (𝟙 U) from
        MorphismProperty.Over.homMk ((etalePostcompose j).obj W).hom
          (Category.comp_id _)) ≫ (zariskiToEtaleTopIso U).inv
    let m : Scheme.Etale.mk k ⟶ Scheme.Etale.mk i :=
      MorphismProperty.Over.homMk j hi
    let F := cokernel (etaleMultiplicativeGroupToPushforward f)
    let G := cokernel (etaleMultiplicativeGroupToPushforward p)
    let a := (etaleRestrictionUnitQuotientIsoOfIsPullback i f p g H).hom
    let b := (etaleRestrictionUnitQuotientIsoOfIsPullback j p q h H').hom
    let d := (etaleRestrictionUnitQuotientIsoOfIsPullback
      k f q l H'').hom
    F.obj.map m.op ≫ F.obj.map (etalePostcomposeTopObjectIso k).hom.op ≫
        d.hom.app (op W) =
      F.obj.map (etalePostcomposeTopObjectIso i).hom.op ≫ a.hom.app (op WU) ≫
        G.obj.map t.op ≫ b.hom.app (op W) := by
  subst k
  subst l
  exact etaleRestrictionUnitQuotient_sections_tower i j f p g q h H H'


end EtaleCohomology

