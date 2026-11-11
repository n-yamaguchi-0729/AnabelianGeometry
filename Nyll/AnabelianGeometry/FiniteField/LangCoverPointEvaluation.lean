/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.AbelianVarieties.Geometry.OriginalFiniteFieldLang
public import Nyll.JacobianVarieties.Picard.AbelJacobi.UnpointedAbelJacobi
public import Nyll.JacobianVarieties.Picard.Unpointed.UnpointedJacobian
public import Nyll.AnabelianGeometry.WeightFiltration.FrobeniusFixedTate
public import Nyll.SchemeTheory.Pi1.FiniteEtale.Basic
public import Nyll.SchemeTheory.Morphisms.QuasiFinite
public import Mathlib.AlgebraicGeometry.Morphisms.LocalFlatDescent
public import Mathlib.AlgebraicGeometry.ZariskisMainTheorem
public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
public import Nyll.SchemeTheory.CategoryTheory.SchemeHomOver

/-!
# Frobenius evaluation on the original Abel–Jacobi Lang cover

The Lang morphism and its pullback are constructed over the original finite
field. Their geometric fibers retain the original scheme points. Frobenius
displacement is the actual Abel–Jacobi point, hence classifies the line bundle
of the evaluated point minus the chosen basepoint.
-/

@[expose] public section

universe u

noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open AlgebraicGeometry NeronModelInfra GoodReductionJacobian
open GoodReductionJacobian.RelativeGroupLaw


namespace AnabelianGeometry.FiniteField

section LangFibers

variable (k : Type u) [Field k] [Fintype k]
  (A : Scheme.{u}) [A.Over (Spec (.of k))]
  (G : RelativeGroupLaw k (A ↘ Spec (.of k))) (hc : G.IsCommutative)
  {C : Scheme.{u}} (c : C ⟶ Spec (.of k))
  (a : SchemeHomOver c (A ↘ Spec (.of k)))

local notation "f" => (A ↘ Spec (CommRingCat.of k))
local notation "λₖ" => Subtype.val (originalFiniteFieldLangMap k A G hc)

/-- The literal pullback of the original Lang morphism along the given map. -/
abbrev langCoverScheme : Scheme.{u} := pullback λₖ a.val

/-- The original covering map to the curve. -/
def langCoverProjection : langCoverScheme k A G hc c a ⟶ C := pullback.snd λₖ a.val

variable (Ω : Type u) [Field Ω] [Algebra k Ω] [Algebra.IsAlgebraic k Ω]

local notation "b" => Spec.map (CommRingCat.ofHom (algebraMap k Ω))
local notation "σ" => FiniteField.frobeniusAlgEquivOfAlgebraic k Ω

/-- The actual Lang pullback is finite étale, including when it is disconnected. -/
theorem langCoverProjection_finiteEtale [IsAlgClosed Ω]
    (hA : AbelianSchemePropertyBundle k f) :
    IsFiniteEtale (langCoverProjection k A G hc c a) := by
  obtain ⟨hf, he⟩ := originalFiniteFieldLangMap_finite_etale k A G hc Ω hA
  have : IsFiniteEtale λₖ := ⟨⟩
  exact inferInstanceAs (IsFiniteEtale (pullback.snd λₖ a.val))

/-- Geometric points in a specified fiber of the original Lang pullback. -/
def LangCoverFiber (y : SchemeHomOver b c) : Type u :=
  {w : Spec (.of Ω) ⟶ langCoverScheme k A G hc c a //
    w ≫ langCoverProjection k A G hc c a = y.val}

/-- The original Jacobian coordinate of an actual covering point. -/
def langCoverFiberCoordinate (y : SchemeHomOver b c)
    (w : LangCoverFiber k A G hc c a Ω y) : G.AlgPoints hc Ω :=
  AlgPoints.ofPoint ⟨w.val ≫ pullback.fst λₖ a.val, by
    have hw : (w.val ≫ pullback.fst λₖ a.val) ≫ λₖ = y.val ≫ a.val := by
      rw [Category.assoc, pullback.condition, ← Category.assoc]
      exact congrArg (· ≫ a.val) w.property
    calc
      (w.val ≫ pullback.fst λₖ a.val) ≫ f =
          ((w.val ≫ pullback.fst λₖ a.val) ≫ λₖ) ≫ f :=
        (congrArg (fun q => (w.val ≫ pullback.fst λₖ a.val) ≫ q)
          (originalFiniteFieldLangMap k A G hc).property).symm.trans
            (Category.assoc _ _ _).symm
      _ = (y.val ≫ a.val) ≫ f := congrArg (· ≫ f) hw
      _ = b := (Category.assoc _ _ _).trans
        ((congrArg (y.val ≫ ·) a.property).trans y.property)⟩

/-- Frobenius displacement of the original covering point is its prescribed
image under the map used to pull back the Lang cover. -/
theorem langCoverFiberCoordinate_displacement (y : SchemeHomOver b c)
    (w : LangCoverFiber k A G hc c a Ω y) :
    σ • langCoverFiberCoordinate k A G hc c a Ω y w -
        langCoverFiberCoordinate k A G hc c a Ω y w =
      AlgPoints.ofPoint (L := G) (hc := hc) (NeronModelInfra.schemeHomOverComp y a) := by
  rw [← originalFiniteFieldLangMap_point k A G hc Ω]
  apply AlgPoints.ofPoint_injective (L := G) (hc := hc)
  apply Subtype.ext
  change (w.val ≫ pullback.fst λₖ a.val) ≫ λₖ = y.val ≫ a.val
  rw [Category.assoc, pullback.condition, ← Category.assoc]
  exact congrArg (· ≫ a.val) w.property

/-- Exact coordinates on the actual geometric fiber, with no selected
component or abstract replacement of the covering. -/
def langCoverFiberEquiv (y : SchemeHomOver b c) :
    LangCoverFiber k A G hc c a Ω y ≃
      {z : G.AlgPoints hc Ω // σ • z - z =
        AlgPoints.ofPoint (NeronModelInfra.schemeHomOverComp y a)} where
  toFun w := ⟨langCoverFiberCoordinate k A G hc c a Ω y w,
    langCoverFiberCoordinate_displacement k A G hc c a Ω y w⟩
  invFun z :=
    ⟨pullback.lift (AlgPoints.toPoint z.val).val y.val (by
      have hz := (originalFiniteFieldLangMap_point k A G hc Ω z.val).trans z.property
      exact congrArg (fun t : G.AlgPoints hc Ω => (AlgPoints.toPoint t).val) hz),
      pullback.lift_snd _ _ _⟩
  left_inv w := by
    apply Subtype.ext
    apply pullback.hom_ext
    · exact pullback.lift_fst _ _ _
    · exact (pullback.lift_snd _ _ _).trans w.property.symm
  right_inv z := by
    apply Subtype.ext
    apply AlgPoints.toPoint_injective
    exact Subtype.ext (pullback.lift_fst _ _ _)

/-- Every original geometric fiber is inhabited by the proved Lang theorem. -/
theorem langCoverFiber_nonempty [IsAlgClosed Ω]
    (hA : AbelianSchemePropertyBundle k f) (y : SchemeHomOver b c) :
    Nonempty (LangCoverFiber k A G hc c a Ω y) := by
  obtain ⟨z, hz⟩ := surjective_frobenius_sub k Ω A G hc hA
    (AlgPoints.ofPoint (NeronModelInfra.schemeHomOverComp y a))
  exact ⟨(langCoverFiberEquiv k A G hc c a Ω y).symm ⟨z, hz⟩⟩

/-- The actual coefficient-Frobenius-fixed translation subgroup. -/
def langTranslationGroup : AddSubgroup (G.AlgPoints hc Ω) :=
  (AlgPoints.map (L := G) (hc := hc) (σ).toAlgHom).eqLocus
    (AddMonoidHom.id (G.AlgPoints hc Ω))

/-- The translation group is finite for the actual abelian variety. -/
theorem langTranslationGroup_finite (hA : AbelianSchemePropertyBundle k f) :
    Finite (langTranslationGroup k A G hc Ω) := by
  have : IsProper f := hA.proper
  have : CompactSpace A := QuasiCompact.compactSpace_of_compactSpace f
  exact WeightFiltration.finite_frobenius_fixed_algebraicPoints k Ω A f G hc

/-- Translation by a Frobenius-fixed point on the original cover fiber. -/
def langCoverFiberTranslate (y : SchemeHomOver b c)
    (t : langTranslationGroup k A G hc Ω)
    (w : LangCoverFiber k A G hc c a Ω y) : LangCoverFiber k A G hc c a Ω y :=
  (langCoverFiberEquiv k A G hc c a Ω y).symm
    ⟨t.val + langCoverFiberCoordinate k A G hc c a Ω y w, by
      have ht : σ • t.val = t.val := t.property
      rw [smul_add, ht, add_sub_add_left_eq_sub]
      exact langCoverFiberCoordinate_displacement k A G hc c a Ω y w⟩

theorem langCoverFiberCoordinate_translate (y : SchemeHomOver b c)
    (t : langTranslationGroup k A G hc Ω)
    (w : LangCoverFiber k A G hc c a Ω y) :
    langCoverFiberCoordinate k A G hc c a Ω y
        (langCoverFiberTranslate k A G hc c a Ω y t w) =
      t.val + langCoverFiberCoordinate k A G hc c a Ω y w :=
  congrArg Subtype.val ((langCoverFiberEquiv k A G hc c a Ω y).apply_symm_apply _)

/-- Translations give the finite group action on every actual fiber. -/
@[instance_reducible]
def langCoverFiberAddAction (y : SchemeHomOver b c) :
    AddAction (langTranslationGroup k A G hc Ω) (LangCoverFiber k A G hc c a Ω y) where
  vadd := langCoverFiberTranslate k A G hc c a Ω y
  zero_vadd w := by
    apply (langCoverFiberEquiv k A G hc c a Ω y).injective
    apply Subtype.ext
    exact (langCoverFiberCoordinate_translate k A G hc c a Ω y 0 w).trans (zero_add _)
  add_vadd s t w := by
    apply (langCoverFiberEquiv k A G hc c a Ω y).injective
    apply Subtype.ext
    change langCoverFiberCoordinate k A G hc c a Ω y
        (langCoverFiberTranslate k A G hc c a Ω y (s + t) w) =
      langCoverFiberCoordinate k A G hc c a Ω y
        (langCoverFiberTranslate k A G hc c a Ω y s
          (langCoverFiberTranslate k A G hc c a Ω y t w))
    rw [langCoverFiberCoordinate_translate, langCoverFiberCoordinate_translate,
      langCoverFiberCoordinate_translate]
    exact add_assoc s.val t.val _

/-- The finite translation action is simply transitive on every actual fiber. -/
theorem langCoverFiber_existsUnique_translate (y : SchemeHomOver b c)
    (w v : LangCoverFiber k A G hc c a Ω y) :
    ∃! t : langTranslationGroup k A G hc Ω,
      langCoverFiberTranslate k A G hc c a Ω y t w = v := by
  let z := langCoverFiberCoordinate k A G hc c a Ω y
  have hF (u : LangCoverFiber k A G hc c a Ω y) :
      σ • z u = AlgPoints.ofPoint (NeronModelInfra.schemeHomOverComp y a) + z u :=
    sub_eq_iff_eq_add.mp (langCoverFiberCoordinate_displacement k A G hc c a Ω y u)
  let t : langTranslationGroup k A G hc Ω := ⟨z v - z w, by
    change σ • (z v - z w) = z v - z w
    rw [smul_sub, hF, hF, add_sub_add_left_eq_sub]⟩
  refine ⟨t, ?_, ?_⟩
  · apply (langCoverFiberEquiv k A G hc c a Ω y).injective
    apply Subtype.ext
    exact (langCoverFiberCoordinate_translate k A G hc c a Ω y t w).trans
      (sub_add_cancel (z v) (z w))
  · intro s hs
    apply Subtype.ext
    have h := congrArg z hs
    change langCoverFiberCoordinate k A G hc c a Ω y
        (langCoverFiberTranslate k A G hc c a Ω y s w) = z v at h
    rw [langCoverFiberCoordinate_translate] at h
    exact eq_sub_iff_add_eq.mpr h

/-- The original rational point viewed over the extended constant field. -/
abbrev langCoverRationalPoint (y : SchemeHomOver (𝟙 (Spec (.of k))) c) :
    SchemeHomOver b c :=
  ⟨b ≫ y.val, by rw [Category.assoc, y.property, Category.comp_id]⟩

/-- Frobenius on an actual geometric point of the original cover is
precomposition by the actual coefficient Frobenius. -/
def langCoverFiberFrobenius (y : SchemeHomOver (𝟙 (Spec (.of k))) c)
    (w : LangCoverFiber k A G hc c a Ω (langCoverRationalPoint k c Ω y)) :
    LangCoverFiber k A G hc c a Ω (langCoverRationalPoint k c Ω y) :=
  ⟨Spec.map (CommRingCat.ofHom (σ).toAlgHom.toRingHom) ≫ w.val, by
    rw [Category.assoc, w.property]
    change Spec.map (CommRingCat.ofHom (σ).toAlgHom.toRingHom) ≫ (b ≫ y.val) = b ≫ y.val
    rw [← Category.assoc, AlgPoints.specMap_comp_algebraMap]⟩

theorem langCoverFiberCoordinate_frobenius
    (y : SchemeHomOver (𝟙 (Spec (.of k))) c)
    (w : LangCoverFiber k A G hc c a Ω (langCoverRationalPoint k c Ω y)) :
    langCoverFiberCoordinate k A G hc c a Ω (langCoverRationalPoint k c Ω y)
        (langCoverFiberFrobenius k A G hc c a Ω y w) =
      σ • langCoverFiberCoordinate k A G hc c a Ω (langCoverRationalPoint k c Ω y) w := by
  apply AlgPoints.toPoint_injective
  apply Subtype.ext
  exact Category.assoc _ _ _

/-- The Lang value at a rational point is an element of the same finite
translation group, not an additional chosen comparison group. -/
def langCoverRationalValue (y : SchemeHomOver (𝟙 (Spec (.of k))) c) :
    langTranslationGroup k A G hc Ω :=
  ⟨AlgPoints.ofPoint
      (NeronModelInfra.schemeHomOverComp (langCoverRationalPoint k c Ω y) a), by
    change σ • (AlgPoints.ofPoint
      (NeronModelInfra.schemeHomOverComp (langCoverRationalPoint k c Ω y) a) :
        G.AlgPoints hc Ω) = _
    apply AlgPoints.toPoint_injective
    apply Subtype.ext
    simpa only [AlgPoints.toPoint_smul_coe, AlgPoints.toPoint_ofPoint, AddMonoidHom.id_apply,
      NeronModelInfra.schemeHomOverComp_coe, langCoverRationalPoint, Category.assoc] using
      congrArg (fun q => q ≫ y.val ≫ a.val)
        (AlgPoints.specMap_comp_algebraMap (σ).toAlgHom)⟩

/-- On the original fiber over a rational point, coefficient Frobenius is
translation by the value of the map defining the Lang pullback. -/
theorem langCoverFiberFrobenius_eq_translate
    (y : SchemeHomOver (𝟙 (Spec (.of k))) c)
    (w : LangCoverFiber k A G hc c a Ω (langCoverRationalPoint k c Ω y)) :
    langCoverFiberFrobenius k A G hc c a Ω y w =
      langCoverFiberTranslate k A G hc c a Ω (langCoverRationalPoint k c Ω y)
        (langCoverRationalValue k A G hc c a Ω y) w := by
  apply (langCoverFiberEquiv k A G hc c a Ω (langCoverRationalPoint k c Ω y)).injective
  apply Subtype.ext
  change langCoverFiberCoordinate k A G hc c a Ω (langCoverRationalPoint k c Ω y)
      (langCoverFiberFrobenius k A G hc c a Ω y w) =
    langCoverFiberCoordinate k A G hc c a Ω (langCoverRationalPoint k c Ω y)
      (langCoverFiberTranslate k A G hc c a Ω (langCoverRationalPoint k c Ω y)
        (langCoverRationalValue k A G hc c a Ω y) w)
  rw [langCoverFiberCoordinate_frobenius, langCoverFiberCoordinate_translate]
  exact sub_eq_iff_eq_add.mp
    (langCoverFiberCoordinate_displacement k A G hc c a Ω
      (langCoverRationalPoint k c Ω y) w)

end LangFibers

section AbelJacobi

open JacobianVarieties.Picard.Unpointed

variable (k : Type u) [Field k] [Fintype k] {C : Scheme.{u}}
  (c : C ⟶ Spec (.of k))
  [IsProper c] [SmoothOfRelativeDimension 1 c] [GeometricallyIrreducible c]
  (x : SchemeHomOver (𝟙 (Spec (.of k))) c)

/-- Lang constructions use the original structure morphism of the chosen Jacobian. -/
local instance jacobianOver : (Jacobian k c).Over (Spec (.of k)) :=
  ⟨toBase k c⟩

/-- The finite étale cover obtained by pulling the original Jacobian Lang map
back along the actual point-minus-basepoint Abel–Jacobi morphism. -/
def abelJacobiLangCover : FiniteEtale C := by
  have : IsFiniteEtale
      (langCoverProjection k (Jacobian k c) (groupLaw k c) (groupLaw_commutative k c)
        c (abelJacobi c x)) :=
    langCoverProjection_finiteEtale k (Jacobian k c) (groupLaw k c)
      (groupLaw_commutative k c) c (abelJacobi c x) (AlgebraicClosure k)
      (abelianSchemePropertyBundle k c)
  exact FiniteEtale.mk
    (langCoverProjection k (Jacobian k c) (groupLaw k c) (groupLaw_commutative k c)
      c (abelJacobi c x))

variable (Ω : Type u) [Field Ω] [Algebra k Ω] [Algebra.IsAlgebraic k Ω]

local notation "b" => Spec.map (CommRingCat.ofHom (algebraMap k Ω))
local notation "σ" => FiniteField.frobeniusAlgEquivOfAlgebraic k Ω

/-- The geometric fiber of that same original finite étale cover at a rational point. -/
abbrev AbelJacobiLangFiber (y : SchemeHomOver (𝟙 (Spec (.of k))) c) : Type u :=
  {w : Spec (.of Ω) ⟶ (abelJacobiLangCover k c x).left //
    w ≫ (abelJacobiLangCover k c x).hom = (langCoverRationalPoint k c Ω y).val}

/-- Every rational point has geometric lifts to this actual cover. -/
theorem abelJacobiLangFiber_nonempty [IsAlgClosed Ω]
    (y : SchemeHomOver (𝟙 (Spec (.of k))) c) :
    Nonempty (AbelJacobiLangFiber k c x Ω y) :=
  langCoverFiber_nonempty k (Jacobian k c) (groupLaw k c) (groupLaw_commutative k c)
    c (abelJacobi c x) Ω (abelianSchemePropertyBundle k c) (langCoverRationalPoint k c Ω y)

/-- The actual Frobenius displacement on the Abel–Jacobi Lang cover is the
actual point-minus-basepoint class. The second formula identifies that
displacement with the original Poincaré line bundle of `y - x`. -/
theorem abelJacobiLangCover_displacement_classifies_point_difference
    (y : SchemeHomOver (𝟙 (Spec (.of k))) c)
    (w : AbelJacobiLangFiber k c x Ω y) :
    let Jpoints : AddCommGroup ((groupLaw k c).AlgPoints (groupLaw_commutative k c) Ω) :=
      AlgPoints.instAddCommGroup (L := groupLaw k c) (hc := groupLaw_commutative k c)
    let M := pointedAbelJacobiData c x
    let yΩ := langCoverRationalPoint k c Ω y
    let z := langCoverFiberCoordinate k (Jacobian k c) (groupLaw k c)
      (groupLaw_commutative k c) c (abelJacobi c x) Ω yΩ w
    let δ := @Sub.sub _ Jpoints.toAddGroup.toSubNegMonoid.toSub
      (AlgPoints.map (L := groupLaw k c) (hc := groupLaw_commutative k c) (σ).toAlgHom z) z
    let d : SchemeHomOver b M.designation.toBase :=
      ⟨(AlgPoints.toPoint (L := groupLaw k c) (hc := groupLaw_commutative k c) δ).val ≫
        (abelJacobiComparison c x).hom, by
        rw [Category.assoc,
          show (abelJacobiComparison c x).hom ≫ M.designation.toBase = toBase k c from
            pointedComparison_over c x M.representation]
        exact (AlgPoints.toPoint (L := groupLaw k c)
          (hc := groupLaw_commutative k c) δ).property⟩
    (δ = AlgPoints.ofPoint (L := groupLaw k c) (hc := groupLaw_commutative k c)
      (NeronModelInfra.schemeHomOverComp yΩ (abelJacobi c x))) ∧
      Nonempty ((M.representation.poincare.pullbackAlong d).L ≅
        (RelEffCartierDiv.ofPoint c yΩ.val yΩ.property).lineBundle ⊗
          (RelEffCartierDiv.ofPoint c (b ≫ x.val)
            ((Category.assoc _ _ _).trans
              ((congrArg (b ≫ ·) x.property).trans (Category.comp_id b)))).idealModule) := by
  intro Jpoints M yΩ z δ d
  have hz : δ = AlgPoints.ofPoint (L := groupLaw k c) (hc := groupLaw_commutative k c)
      (NeronModelInfra.schemeHomOverComp yΩ (abelJacobi c x)) :=
    langCoverFiberCoordinate_displacement k (Jacobian k c) (groupLaw k c)
      (groupLaw_commutative k c) c (abelJacobi c x) Ω yΩ w
  refine ⟨hz, ?_⟩
  have hd : d =
      ⟨yΩ.val ≫ (abelJacobi c x).val ≫ (abelJacobiComparison c x).hom, by
        rw [abelJacobi_comp_comparison, Category.assoc, M.map.property, yΩ.property]⟩ := by
    apply Subtype.ext
    change (AlgPoints.toPoint (L := groupLaw k c) (hc := groupLaw_commutative k c) δ).val ≫
      (abelJacobiComparison c x).hom = _
    rw [hz]
    exact Category.assoc _ _ _
  rw [hd]
  exact abelJacobi_classifies_point_difference c x Ω b yΩ

end AbelJacobi

end AnabelianGeometry.FiniteField
