/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.SchemeTheory.GroupSchemes.RelativeGroupLaw.Kernel
public import Nyll.AlgebraicCurves.Geometry.AbelianSchemes.Theorems.RelativeGroupLawEtaleSchemeNsmul
public import Nyll.AlgebraicCurves.Geometry.AbelianSchemes.Theorems.RelativeGroupLawSmoothOfRelativeDimension
public import Nyll.AlgebraicCurves.Geometry.AbelianSchemes.Theorems.RelativeGroupLawSurjectiveSchemeNsmulFlat
public import Nyll.AlgebraicCurves.Geometry.Picard.BaseChange.IsPullbackBaseChangeSnd
public import Nyll.AlgebraicCurves.Geometry.Picard.Functor.Functor
public import Nyll.AlgebraicCurves.Geometry.Picard.Representability.RepresentsRelSubPicGroup
public import Nyll.SchemeTheory.Morphisms.QuasiFinite
public import Nyll.SchemeTheory.Morphisms.SmoothGeometricallyIntegral
public import Mathlib.AlgebraicGeometry.Geometrically.Integral
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.AlgebraicGeometry.PullbackCarrier
public import Mathlib.AlgebraicGeometry.ZariskisMainTheorem
public import Mathlib.CategoryTheory.MorphismProperty.Limits

/-!
# The actual division pullback of a Picard-valued family

Pulling back the original multiplication morphism along a classifying
morphism gives a genuine division point. Its power is the original
classifying morphism after the first projection. When the representing
Picard scheme is smooth and geometrically connected and the integer is
invertible, both this projection and its product with the curve are
surjective étale morphisms. No connectedness of the division pullback is
asserted.
-/

@[expose] public section

noncomputable section

universe u

open AlgebraicGeometry CategoryTheory Limits
open NeronModelInfra GoodReductionJacobian

namespace AlgebraicGeometry.RelPicard.RepresentsRelSubPic

section CommRing

variable {R : Type u} [CommRing R] {C : Scheme.{u}}
  {c : C ⟶ Spec (.of R)} {ε : SchemeHomOver (𝟙 (Spec (.of R))) c}
  {P : SubPicGroupCondition c ε} {D : RelativePic0Designation R c}
  (h : RepresentsRelSubPic c ε P.toSubPicCondition D)
  {T : Scheme.{u}} {t : T ⟶ Spec (.of R)}
  (a : SchemeHomOver t D.toBase) (n : ℕ)

/-- The fibre product with the original multiplication morphism. -/
abbrev divisionPullback : Scheme.{u} :=
  pullback a.1 (h.relativeGroupLaw.schemeNsmul n)

/-- The actual projection of the division pullback to its parameter
scheme. -/
def divisionProjection : h.divisionPullback a n ⟶ T :=
  pullback.fst a.1 (h.relativeGroupLaw.schemeNsmul n)

/-- The structure morphism of the actual division pullback. -/
def divisionStructure : h.divisionPullback a n ⟶ Spec (.of R) :=
  h.divisionProjection a n ≫ t

/-- The projection regarded as a morphism over the original base. -/
def divisionBaseMap : SchemeHomOver (h.divisionStructure a n) t :=
  ⟨h.divisionProjection a n, rfl⟩

/-- The actual Picard-valued point on the division pullback. -/
def divisionPoint : SchemeHomOver (h.divisionStructure a n) D.toBase :=
  ⟨pullback.snd a.1 (h.relativeGroupLaw.schemeNsmul n), by
    change pullback.snd a.1 (h.relativeGroupLaw.schemeNsmul n) ≫ D.toBase =
      pullback.fst a.1 (h.relativeGroupLaw.schemeNsmul n) ≫ t
    calc
      _ = pullback.snd a.1 (h.relativeGroupLaw.schemeNsmul n) ≫
          (h.relativeGroupLaw.schemeNsmul n ≫ D.toBase) :=
        congrArg (pullback.snd a.1 (h.relativeGroupLaw.schemeNsmul n) ≫ ·)
          (h.relativeGroupLaw.schemeNsmul_over n).symm
      _ = (pullback.fst a.1 (h.relativeGroupLaw.schemeNsmul n) ≫ a.1) ≫
          D.toBase := by rw [← Category.assoc, ← pullback.condition]
      _ = _ := by rw [Category.assoc, a.2]⟩

/-- The original group law computes the power of the actual division
point as the original classifying map after the projection. -/
theorem divisionPoint_pow :
    let _ := h.relativeGroupLaw.pointGroup (h.divisionStructure a n)
    (h.divisionPoint a n) ^ n = postComp a (h.divisionBaseMap a n) := by
  intro pointGroup
  let b := h.divisionPoint a n
  have hp (m : ℕ) :
      b ^ m = h.relativeGroupLaw.nsmul (h.divisionStructure a n) m b := by
    induction m with
    | zero => rfl
    | succ m ih =>
        rw [pow_succ, GoodReductionJacobian.RelativeGroupLaw.nsmul_succ, ih]; rfl
  apply Subtype.ext
  change (b ^ n).1 = (h.divisionProjection a n) ≫ a.1
  calc
    _ = (h.relativeGroupLaw.nsmul (h.divisionStructure a n) n b).1 :=
      congrArg Subtype.val (hp n)
    _ = b.1 ≫ h.relativeGroupLaw.schemeNsmul n := by
      have hb : schemeHomOverComp b.1 b.2
          (GoodReductionJacobian.RelativeGroupLaw.idPoint (f := D.toBase)) = b := by
        apply Subtype.ext
        exact Category.comp_id b.1
      have hnatural := h.relativeGroupLaw.nsmul_natural D.toBase
        (h.divisionStructure a n) b.1 b.2 n
        GoodReductionJacobian.RelativeGroupLaw.idPoint
      rw [hb] at hnatural
      exact (congrArg Subtype.val hnatural).symm
    _ = _ := pullback.condition.symm

/-- The product projection on which the pulled-back Poincaré family
will acquire its actual root. -/
def divisionProductProjection :
    pullback c (h.divisionStructure a n) ⟶ pullback c t :=
  baseChangeSnd c (h.divisionBaseMap a n)

variable [IsLocalRing R] [Smooth D.toBase]

/-- Invertibility of the integer makes the original division projection
étale, in arbitrary characteristic. -/
theorem divisionProjection_etale (hn : IsUnit (n : R)) :
    Etale (h.divisionProjection a n) := by
  obtain ⟨d, hd⟩ :=
    h.relativeGroupLaw.exists_smoothOfRelativeDimension_of_smooth_of_isLocalRing
  have : SmoothOfRelativeDimension d D.toBase := hd
  have : Etale (h.relativeGroupLaw.schemeNsmul n) :=
    h.relativeGroupLaw.etale_schemeNsmul_of_isUnit_of_smoothOfRelativeDimension
      h.relativeGroupLaw_isCommutative d n hn
  change Etale (pullback.fst a.1 (h.relativeGroupLaw.schemeNsmul n))
  infer_instance

/-- The actual product projection is étale by its original Cartesian
square. -/
theorem divisionProductProjection_etale (hn : IsUnit (n : R)) :
    Etale (h.divisionProductProjection a n) := by
  have he : Etale (h.divisionProjection a n) := h.divisionProjection_etale a n hn
  exact MorphismProperty.of_isPullback
    (isPullback_baseChangeSnd c (h.divisionBaseMap a n)).flip he

/-- Properness of the representing Picard scheme makes the actual
étale division projection finite. -/
theorem divisionProjection_finite [IsProper D.toBase] (hn : IsUnit (n : R)) :
    IsFinite (h.divisionProjection a n) := by
  have : IsProper (h.relativeGroupLaw.schemeNsmul n ≫ D.toBase) := by
    rw [h.relativeGroupLaw.schemeNsmul_over]
    infer_instance
  have : IsProper (h.relativeGroupLaw.schemeNsmul n) :=
    IsProper.of_comp _ D.toBase
  have : IsProper (h.divisionProjection a n) := by
    change IsProper (pullback.fst a.1 (h.relativeGroupLaw.schemeNsmul n))
    infer_instance
  have : Etale (h.divisionProjection a n) := h.divisionProjection_etale a n hn
  have : LocallyQuasiFinite (h.divisionProjection a n) :=
    LocallyQuasiFinite.of_formallyUnramified_of_locallyOfFiniteType _
  exact IsFinite.of_isProper_of_locallyQuasiFinite _

/-- The original product cover is finite over the curve product when
the representing Picard scheme is proper. -/
theorem divisionProductProjection_finite [IsProper D.toBase] (hn : IsUnit (n : R)) :
    IsFinite (h.divisionProductProjection a n) :=
  MorphismProperty.of_isPullback
    (isPullback_baseChangeSnd c (h.divisionBaseMap a n)).flip
      (h.divisionProjection_finite a n hn)

end CommRing

section Field

variable {K : Type u} [Field K] {C : Scheme.{u}}
  {c : C ⟶ Spec (.of K)} {ε : SchemeHomOver (𝟙 (Spec (.of K))) c}
  {P : SubPicGroupCondition c ε} {D : RelativePic0Designation K c}
  (h : RepresentsRelSubPic c ε P.toSubPicCondition D)
  {T : Scheme.{u}} {t : T ⟶ Spec (.of K)}
  (a : SchemeHomOver t D.toBase) (n : ℕ)
  [Smooth D.toBase] [GeometricallyConnected D.toBase]

/-- The actual division projection is surjective. The argument uses
smoothness and connectedness of the Picard carrier, and makes no
connectedness claim about the division pullback. -/
theorem divisionProjection_surjective
    (hn : IsUnit (n : K)) : Surjective (h.divisionProjection a n) := by
  have : GeometricallyIntegral D.toBase :=
    Smooth.geometricallyIntegral_of_geometricallyConnected D.toBase
  have : IrreducibleSpace D.P :=
    GeometricallyIrreducible.irreducibleSpace_of_subsingleton (f := D.toBase)
  obtain ⟨d, hd⟩ :=
    h.relativeGroupLaw.exists_smoothOfRelativeDimension_of_smooth_of_isLocalRing
  have : SmoothOfRelativeDimension d D.toBase := hd
  have : Etale (h.relativeGroupLaw.schemeNsmul n) :=
    h.relativeGroupLaw.etale_schemeNsmul_of_isUnit_of_smoothOfRelativeDimension
      h.relativeGroupLaw_isCommutative d n hn
  have : Surjective (h.relativeGroupLaw.schemeNsmul n) :=
    h.relativeGroupLaw.surjective_schemeNsmul_of_flat_of_field
      h.relativeGroupLaw_isCommutative n
  change Surjective (pullback.fst a.1 (h.relativeGroupLaw.schemeNsmul n))
  infer_instance

/-- The actual product projection is surjective by the same Cartesian
square. -/
theorem divisionProductProjection_surjective
    (hn : IsUnit (n : K)) : Surjective (h.divisionProductProjection a n) := by
  have he : Surjective (h.divisionProjection a n) :=
    h.divisionProjection_surjective a n hn
  exact MorphismProperty.of_isPullback
    (isPullback_baseChangeSnd c (h.divisionBaseMap a n)).flip he

end Field

end AlgebraicGeometry.RelPicard.RepresentsRelSubPic
