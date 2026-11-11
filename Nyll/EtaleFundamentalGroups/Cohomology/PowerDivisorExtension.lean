/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.EtaleFundamentalGroups.Cohomology.ExtensionKernelRestriction
public import Nyll.EtaleFundamentalGroups.Cohomology.ExtensionPullbackClass
public import Mathlib.CategoryTheory.Preadditive.Basic

/-!
# The actual extension attached to a divisible divisor

For an original short exact sequence `A → B → C`, retain a section
`d : Y → C` and an actual lift `b : Y → B` of `n • d`. On the original
pullback of `d`, the difference `n • r - b z` lies in `A`. Its kernel
is an actual extension of `Y` by `ker (n • id A)`. Its class maps to
the original connecting class of `d`, and its original middle
coordinate satisfies the specified power equation involving `b`.
-/

@[expose] public section

noncomputable section

universe w v u

open CategoryTheory CategoryTheory.Abelian Limits

namespace EtaleFundamentalGroups.Cohomology

variable {C : Type u} [Category.{v} C] [Abelian C]
  (S : ShortComplex C) (hS : S.ShortExact) (n : ℕ)
  {Y : C} (d : Y ⟶ S.X₃) (b : Y ⟶ S.X₂)
  (hb : b ≫ S.g = n • d)

include hb in
/-- The actual difference between the multiple of a divisor lift and
the specified rational section maps to zero in the original quotient. -/
theorem powerDivisorDefect_zero :
    (n • pullback.fst S.g d - pullback.snd S.g d ≫ b) ≫ S.g = 0 := by
  rw [Preadditive.sub_comp, Preadditive.nsmul_comp,
    Category.assoc, hb, Preadditive.comp_nsmul, pullback.condition, sub_self]

/-- The original regular coefficient determined by `n • r - b z`.
Its construction uses the actual kernel property of the given sequence. -/
def powerDivisorDefect : pullback S.g d ⟶ S.X₁ := by
  have : Mono S.f := hS.mono_f
  exact hS.exact.lift
    (n • pullback.fst S.g d - pullback.snd S.g d ≫ b)
    (powerDivisorDefect_zero S n d b hb)

/-- The defect retains both original pullback projections and the
specified rational section. -/
theorem powerDivisorDefect_comp_f :
    powerDivisorDefect S hS n d b hb ≫ S.f =
      n • pullback.fst S.g d - pullback.snd S.g d ≫ b := by
  have : Mono S.f := hS.mono_f
  exact hS.exact.lift_f _ _

/-- On the original coefficient inclusion the defect is exactly
multiplication by the specified integer. -/
theorem powerDivisorDefect_inclusion :
    (coefficientPullbackExtension S (Iso.refl S.X₁) d).f ≫
        powerDivisorDefect S hS n d b hb = n • 𝟙 S.X₁ := by
  have : Mono S.f := hS.mono_f
  apply (cancel_mono S.f).mp
  change ((𝟙 S.X₁ ≫
    pullback.lift S.f (0 : S.X₁ ⟶ Y) (S.zero.trans (zero_comp).symm)) ≫
      powerDivisorDefect S hS n d b hb) ≫ S.f = (n • 𝟙 S.X₁) ≫ S.f
  rw [Category.id_comp, Category.assoc, powerDivisorDefect_comp_f,
    Preadditive.comp_sub, Preadditive.comp_nsmul, pullback.lift_fst,
    ← Category.assoc, pullback.lift_snd, zero_comp, sub_zero,
    Preadditive.nsmul_comp, Category.id_comp]

/-- The actual extension obtained by imposing the specified power
equation on the original divisor pullback. -/
def powerDivisorExtension : ShortComplex C :=
  kernelRestrictionExtension
    (coefficientPullbackExtension S (Iso.refl S.X₁) d)
    (n • 𝟙 S.X₁) (powerDivisorDefect S hS n d b hb)
    (powerDivisorDefect_inclusion S hS n d b hb)

/-- The power-divisor extension is short exact whenever the original
coefficient power map is epimorphic. -/
theorem powerDivisorExtension_shortExact [Epi (n • 𝟙 S.X₁)] :
    (powerDivisorExtension S hS n d b hb).ShortExact :=
  kernelRestrictionExtension_shortExact
    (coefficientPullbackExtension S (Iso.refl S.X₁) d)
    (n • 𝟙 S.X₁) (powerDivisorDefect S hS n d b hb)
    (powerDivisorDefect_inclusion S hS n d b hb)
    (coefficientPullbackExtension_shortExact S (Iso.refl S.X₁) d hS)

/-- The original middle coordinate of the power-divisor extension. -/
def powerDivisorExtensionRoot :
    (powerDivisorExtension S hS n d b hb).X₂ ⟶ S.X₂ :=
  kernel.ι (powerDivisorDefect S hS n d b hb) ≫ pullback.fst S.g d

/-- The actual middle coordinate satisfies the original power equation. -/
theorem powerDivisorExtensionRoot_power :
    n • powerDivisorExtensionRoot S hS n d b hb =
      (powerDivisorExtension S hS n d b hb).g ≫ b := by
  have hz := congrArg (fun k =>
      kernel.ι (powerDivisorDefect S hS n d b hb) ≫ k)
    (powerDivisorDefect_comp_f S hS n d b hb)
  rw [← Category.assoc, kernel.condition, zero_comp,
    Preadditive.comp_sub, Preadditive.comp_nsmul] at hz
  change n • (kernel.ι (powerDivisorDefect S hS n d b hb) ≫
      pullback.fst S.g d) =
    (kernel.ι (powerDivisorDefect S hS n d b hb) ≫ pullback.snd S.g d) ≫ b
  simpa only [Category.assoc] using sub_eq_zero.mp hz.symm

/-- The original middle coordinate carries the actual coefficient
kernel to its original inclusion in `B`. -/
theorem powerDivisorExtensionRoot_inclusion :
    (powerDivisorExtension S hS n d b hb).f ≫
        powerDivisorExtensionRoot S hS n d b hb =
      kernel.ι (n • 𝟙 S.X₁) ≫ S.f := by
  let P : ShortComplex C := coefficientPullbackExtension S (Iso.refl S.X₁) d
  let i : kernel (n • 𝟙 S.X₁) ⟶ kernel (powerDivisorDefect S hS n d b hb) :=
    (powerDivisorExtension S hS n d b hb).f
  let p : S.X₁ ⟶ pullback S.g d := P.f
  have hι : i ≫ kernel.ι (powerDivisorDefect S hS n d b hb) =
      kernel.ι (n • 𝟙 S.X₁) ≫ p :=
    kernelRestrictionExtension_f_ι P (n • 𝟙 S.X₁)
      (powerDivisorDefect S hS n d b hb)
      (powerDivisorDefect_inclusion S hS n d b hb)
  have hfst : p ≫ pullback.fst S.g d = S.f :=
    (coefficientPullbackExtension_f_fst S (Iso.refl S.X₁) d).trans
      (Category.id_comp S.f)
  change i ≫
      (kernel.ι (powerDivisorDefect S hS n d b hb) ≫ pullback.fst S.g d) =
    kernel.ι (n • 𝟙 S.X₁) ≫ S.f
  have hpost : (i ≫ kernel.ι (powerDivisorDefect S hS n d b hb)) ≫
      pullback.fst S.g d =
      (kernel.ι (n • 𝟙 S.X₁) ≫ p) ≫ pullback.fst S.g d :=
    congrArg (fun a : kernel (n • 𝟙 S.X₁) ⟶ pullback S.g d =>
      a ≫ pullback.fst S.g d) hι
  have htarget : kernel.ι (n • 𝟙 S.X₁) ≫ (p ≫ pullback.fst S.g d) =
      kernel.ι (n • 𝟙 S.X₁) ≫ S.f :=
    congrArg (fun a : S.X₁ ⟶ S.X₂ => kernel.ι (n • 𝟙 S.X₁) ≫ a) hfst
  exact (Category.assoc i
    (kernel.ι (powerDivisorDefect S hS n d b hb)) (pullback.fst S.g d)).symm.trans
      (hpost.trans ((Category.assoc (kernel.ι (n • 𝟙 S.X₁)) p
        (pullback.fst S.g d)).trans htarget))

/-- The original kernel inclusion sends the actual power-divisor
class to the connecting class of the specified divisor section. -/
theorem powerDivisorExtension_extClass [HasExt.{w} C]
    [Epi (n • 𝟙 S.X₁)] :
    (powerDivisorExtension_shortExact S hS n d b hb).extClass.comp
        (Ext.mk₀ (kernel.ι (n • 𝟙 S.X₁))) (add_zero 1) =
      (Ext.mk₀ d).comp hS.extClass (zero_add 1) := by
  calc
    _ = (coefficientPullbackExtension_shortExact
        S (Iso.refl S.X₁) d hS).extClass :=
      kernelRestrictionExtension_extClass
        (coefficientPullbackExtension S (Iso.refl S.X₁) d)
        (n • 𝟙 S.X₁) (powerDivisorDefect S hS n d b hb)
        (powerDivisorDefect_inclusion S hS n d b hb)
        (coefficientPullbackExtension_shortExact S (Iso.refl S.X₁) d hS)
    _ = _ := by
      simpa only [Iso.refl_inv, Ext.comp_mk₀_id] using
        coefficientPullbackExtension_extClass S (Iso.refl S.X₁) d hS

end EtaleFundamentalGroups.Cohomology
