/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.SchemeTheory.RingTheory.LocalRing.FixedPointIdeal
public import Mathlib.AlgebraicGeometry.GammaSpecAdjunction
public import Mathlib.AlgebraicGeometry.Limits
public import Mathlib.CategoryTheory.Limits.Shapes.Equalizers
public import Mathlib.CategoryTheory.Limits.Shapes.Opposites.Equalizers
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Equalizers
public import Mathlib.RingTheory.Ideal.Quotient.Defs

/-!
# The actual affine fixed-point scheme

The quotient by the original differences `f(a) - a` is the coequalizer of
`f` and the identity in commutative rings. The spectrum adjunction carries
this universal property to the actual scheme equalizer. In particular the
comparison is not an assumed description of its coordinate ring.
-/

@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

namespace CommRingCat

universe u

variable {R : Type u} [CommRing R] (f : R →+* R)

/-- The fixed-point quotient coequalizes the endomorphism and the identity. -/
theorem fixedPointQuotient_condition :
    CommRingCat.ofHom f ≫ CommRingCat.ofHom (Ideal.Quotient.mk f.fixedPointIdeal) =
      𝟙 (CommRingCat.of R) ≫ CommRingCat.ofHom (Ideal.Quotient.mk f.fixedPointIdeal) := by
  apply CommRingCat.hom_ext
  ext x
  exact (Ideal.Quotient.eq (I := f.fixedPointIdeal)).mpr (Ideal.subset_span ⟨x, rfl⟩)

/-- The actual fixed-point quotient is a coequalizer in commutative rings. -/
def fixedPointQuotientIsColimit :
    IsColimit (Cofork.ofπ (CommRingCat.ofHom (Ideal.Quotient.mk f.fixedPointIdeal))
      (fixedPointQuotient_condition f)) := by
  refine Cofork.IsColimit.mk' _ fun s => ?_
  have hker : f.fixedPointIdeal ≤ RingHom.ker s.π.hom := by
    apply Ideal.span_le.mpr
    rintro _ ⟨x, rfl⟩
    change s.π.hom (f x - x) = 0
    rw [map_sub, sub_eq_zero]
    exact congrArg (fun v : CommRingCat.of R ⟶ s.pt => v.hom x) s.condition
  let d : CommRingCat.of (R ⧸ f.fixedPointIdeal) ⟶ s.pt :=
    CommRingCat.ofHom (Ideal.Quotient.lift f.fixedPointIdeal s.π.hom hker)
  have hfac : CommRingCat.ofHom (Ideal.Quotient.mk f.fixedPointIdeal) ≫ d = s.π := by
    apply CommRingCat.hom_ext
    ext x
    exact Ideal.Quotient.lift_mk f.fixedPointIdeal s.π.hom hker
  refine ⟨d, hfac, ?_⟩
  intro m hm
  apply CommRingCat.hom_ext
  apply Ideal.Quotient.ringHom_ext (I := f.fixedPointIdeal) (f := m.hom) (g := d.hom)
  exact congrArg CommRingCat.Hom.hom (hm.trans hfac.symm)

end CommRingCat

namespace AlgebraicGeometry

universe u

variable {R : Type u} [CommRing R] (f : R →+* R)

/-- Transport a limiting fork along equality of its second parallel morphism. -/
def isLimitForkOfRightEq
    {X Y P : Scheme.{u}} {a b b' : X ⟶ Y} {i : P ⟶ X}
    {w : i ≫ a = i ≫ b} {w' : i ≫ a = i ≫ b'}
    (hb : b = b') (h : IsLimit (Fork.ofι i w)) :
    IsLimit (Fork.ofι i w') := by
  subst b'
  exact h

/-- The quotient's spectrum is the actual equalizer of the induced affine
endomorphism and the identity, for arbitrary test schemes. -/
def fixedPointQuotientSpecIsLimit :
    IsLimit (Fork.ofι (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk f.fixedPointIdeal)))
      (show Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk f.fixedPointIdeal)) ≫
          Spec.map (CommRingCat.ofHom f) =
        Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk f.fixedPointIdeal)) ≫
          𝟙 (Spec (CommRingCat.of R)) from by
        rw [← Spec.map_comp, Category.comp_id]
        apply congrArg Spec.map
        simpa only [Category.id_comp] using CommRingCat.fixedPointQuotient_condition f)) := by
  let q := CommRingCat.ofHom (Ideal.Quotient.mk f.fixedPointIdeal)
  let w := CommRingCat.fixedPointQuotient_condition f
  have wop : q.op ≫ (CommRingCat.ofHom f).op =
      q.op ≫ (𝟙 (CommRingCat.of R)).op :=
    congrArg Quiver.Hom.op w
  have hl : IsLimit (Fork.ofι q.op wop) :=
    (Cofork.isColimitOfπEquivIsLimitOp q q w wop rfl)
      (CommRingCat.fixedPointQuotientIsColimit f)
  have hm := isLimitForkMapOfIsLimit Scheme.Spec wop hl
  change IsLimit (Fork.ofι (Spec.map q)
    (f := Spec.map (CommRingCat.ofHom f))
    (g := Spec.map (𝟙 (CommRingCat.of R))) _) at hm
  exact isLimitForkOfRightEq
    (X := Spec (CommRingCat.of R)) (Y := Spec (CommRingCat.of R))
    (P := Spec (CommRingCat.of (R ⧸ f.fixedPointIdeal)))
    (a := Spec.map (CommRingCat.ofHom f))
    (b := Spec.map (𝟙 (CommRingCat.of R)))
    (b' := 𝟙 (Spec (CommRingCat.of R))) (i := Spec.map q)
    (Spec.map_id (CommRingCat.of R)) hm

/-- The actual scheme equalizer has the original quotient coordinate ring. -/
def fixedPointQuotientSpecIsoEqualizer :
    Spec (CommRingCat.of (R ⧸ f.fixedPointIdeal)) ≅
      equalizer (Spec.map (CommRingCat.ofHom f)) (𝟙 (Spec (CommRingCat.of R))) :=
  (fixedPointQuotientSpecIsLimit f).conePointUniqueUpToIso
    (limit.isLimit (parallelPair (Spec.map (CommRingCat.ofHom f))
      (𝟙 (Spec (CommRingCat.of R)))))

/-- The comparison preserves the original closed-immersion map into the affine scheme. -/
theorem fixedPointQuotientSpecIsoEqualizer_hom_ι :
    (fixedPointQuotientSpecIsoEqualizer f).hom ≫
        equalizer.ι (Spec.map (CommRingCat.ofHom f)) (𝟙 (Spec (CommRingCat.of R))) =
      Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk f.fixedPointIdeal)) :=
  IsLimit.conePointUniqueUpToIso_hom_comp (fixedPointQuotientSpecIsLimit f)
    (limit.isLimit (parallelPair (Spec.map (CommRingCat.ofHom f))
      (𝟙 (Spec (CommRingCat.of R))))) WalkingParallelPair.zero

end AlgebraicGeometry
