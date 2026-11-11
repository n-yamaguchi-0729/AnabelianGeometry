/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Mathlib.Algebra.Homology.DerivedCategory.Ext.ExtClass
public import Mathlib.Algebra.Homology.ShortComplex.Exact
public import Mathlib.Algebra.Homology.ShortComplex.ShortExact

/-!
# Computing a Yoneda product from two successive lifts

A lift of an augmentation into a short extension has a difference on
the augmentation kernel. A lift of that difference into a second
extension has a second difference on the first relation kernel. The
native Yoneda product is the native two-step connecting class of this
second difference.

The differences are constructed by the actual kernel universal
properties. The formula follows from actual morphisms of short exact
sequences; a comparison with a separately defined cup product is not
an input. In applications the two lifts are supplied by local sections
on a cover and on its first relation object.
-/

@[expose] public section

noncomputable section

universe u v w

open CategoryTheory Limits Abelian

namespace EtaleCohomology.CupTwoStepExtension

variable {C : Type u} [Category.{v} C] [Abelian C]

/-- The actual kernel difference of a lift of a morphism of augmentations. -/
def difference (A S : ShortComplex C) (hS : S.ShortExact)
    (r : A.X₃ ⟶ S.X₃) (t : A.X₂ ⟶ S.X₂)
    (ht : t ≫ S.g = A.g ≫ r) : A.X₁ ⟶ S.X₁ := by
  have : Mono S.f := hS.mono_f
  exact hS.exact.lift (A.f ≫ t) (by
    rw [Category.assoc, ht, ← Category.assoc, A.zero, zero_comp])

/-- The difference is characterized before passing to cohomology. -/
theorem difference_comp (A S : ShortComplex C) (hS : S.ShortExact)
    (r : A.X₃ ⟶ S.X₃) (t : A.X₂ ⟶ S.X₂)
    (ht : t ≫ S.g = A.g ≫ r) :
    difference A S hS r t ht ≫ S.f = A.f ≫ t := by
  have : Mono S.f := hS.mono_f
  exact hS.exact.lift_f (A.f ≫ t) _

/-- Isomorphisms on the two augmentation objects induce an
isomorphism on their actual kernels. The inverse is the same kernel
construction applied to the inverse augmentation maps. -/
theorem difference_isIso (A S : ShortComplex C)
    (hA : A.ShortExact) (hS : S.ShortExact)
    (r : A.X₃ ⟶ S.X₃) (t : A.X₂ ⟶ S.X₂) [IsIso r] [IsIso t]
    (ht : t ≫ S.g = A.g ≫ r) :
    IsIso (difference A S hS r t ht) := by
  have : Mono A.f := hA.mono_f
  have : Mono S.f := hS.mono_f
  have ht' : inv t ≫ A.g = S.g ≫ inv r := by
    apply (cancel_mono r).mp
    simp only [Category.assoc]
    rw [IsIso.inv_hom_id, Category.comp_id, ← ht, IsIso.inv_hom_id_assoc]
  let a := difference A S hS r t ht
  let b := difference S A hA (inv r) (inv t) ht'
  have hab : a ≫ b = 𝟙 A.X₁ := by
    apply (cancel_mono A.f).mp
    rw [Category.assoc, difference_comp, ← Category.assoc,
      difference_comp, Category.assoc, IsIso.hom_inv_id, Category.comp_id,
      Category.id_comp]
  have hba : b ≫ a = 𝟙 S.X₁ := by
    apply (cancel_mono S.f).mp
    rw [Category.assoc, difference_comp, ← Category.assoc,
      difference_comp, Category.assoc, IsIso.inv_hom_id, Category.comp_id,
      Category.id_comp]
  exact ⟨⟨b, hab, hba⟩⟩

/-- A chosen middle lift and its constructed difference give an actual
morphism of short complexes. -/
def liftMorphism (A S : ShortComplex C) (hS : S.ShortExact)
    (r : A.X₃ ⟶ S.X₃) (t : A.X₂ ⟶ S.X₂)
    (ht : t ≫ S.g = A.g ≫ r) : A ⟶ S where
  τ₁ := difference A S hS r t ht
  τ₂ := t
  τ₃ := r
  comm₁₂ := difference_comp A S hS r t ht
  comm₂₃ := ht

/-- The class of a lifted short extension is its actual connecting
class applied to the constructed difference. -/
theorem extClass_difference [HasExt.{w} C]
    (A S : ShortComplex C) (hA : A.ShortExact) (hS : S.ShortExact)
    (r : A.X₃ ⟶ S.X₃) (t : A.X₂ ⟶ S.X₂)
    (ht : t ≫ S.g = A.g ≫ r) :
    hA.extClass.comp (Ext.mk₀ (difference A S hS r t ht)) (add_zero 1) =
      (Ext.mk₀ r).comp hS.extClass (zero_add 1) :=
  hA.extClass_naturality hS (liftMorphism A S hS r t ht)

/-- Two successive actual lifts compute the native Yoneda product.
The first two short exact sequences are the extensions being multiplied;
the last two are an augmentation and its first relation sequence. -/
theorem extClass_comp_eq_twoStep_difference [HasExt.{w} C]
    {X Y Z E F K P L Q : C}
    (i : Y ⟶ E) (p : E ⟶ X) (hip : i ≫ p = 0)
    (hS : (ShortComplex.mk i p hip).ShortExact)
    (j : Z ⟶ F) (q : F ⟶ Y) (hjq : j ≫ q = 0)
    (hT : (ShortComplex.mk j q hjq).ShortExact)
    (d : K ⟶ P) (a : P ⟶ X) (hda : d ≫ a = 0)
    (hA : (ShortComplex.mk d a hda).ShortExact)
    (e : L ⟶ Q) (b : Q ⟶ K) (heb : e ≫ b = 0)
    (hB : (ShortComplex.mk e b heb).ShortExact)
    (t₀ : P ⟶ E) (ht₀ : t₀ ≫ p = a)
    (t₁ : Q ⟶ F)
    (ht₁ : t₁ ≫ q = b ≫ difference
      (ShortComplex.mk d a hda) (ShortComplex.mk i p hip) hS
      (𝟙 X) t₀ (ht₀.trans (Category.comp_id a).symm)) :
    hS.extClass.comp hT.extClass (show 1 + 1 = 2 from rfl) =
      (hA.extClass.comp hB.extClass (show 1 + 1 = 2 from rfl)).comp
        (Ext.mk₀ (difference
          (ShortComplex.mk e b heb) (ShortComplex.mk j q hjq) hT
          (difference (ShortComplex.mk d a hda) (ShortComplex.mk i p hip) hS
            (𝟙 X) t₀ (ht₀.trans (Category.comp_id a).symm)) t₁ ht₁)) (add_zero 2) := by
  let A := ShortComplex.mk d a hda
  let B := ShortComplex.mk e b heb
  let S := ShortComplex.mk i p hip
  let T := ShortComplex.mk j q hjq
  let k : K ⟶ Y := difference A S hS (𝟙 X) t₀
    (ht₀.trans (Category.comp_id a).symm)
  let z : L ⟶ Z := difference B T hT k t₁ ht₁
  have hk : hA.extClass.comp (Ext.mk₀ k) (add_zero 1) = hS.extClass := by
    exact (extClass_difference A S hA hS (𝟙 X) t₀
      (ht₀.trans (Category.comp_id a).symm)).trans
        (Ext.mk₀_id_comp hS.extClass)
  have hz : hB.extClass.comp (Ext.mk₀ z) (add_zero 1) =
      (Ext.mk₀ k).comp hT.extClass (zero_add 1) :=
    extClass_difference B T hB hT k t₁ ht₁
  change hS.extClass.comp hT.extClass rfl =
    (hA.extClass.comp hB.extClass rfl).comp (Ext.mk₀ z) (add_zero 2)
  calc
    hS.extClass.comp hT.extClass rfl =
        (hA.extClass.comp (Ext.mk₀ k) (add_zero 1)).comp hT.extClass rfl := by
      rw [hk]
    _ = hA.extClass.comp
        ((Ext.mk₀ k).comp hT.extClass (zero_add 1)) rfl :=
      Ext.comp_assoc_of_second_deg_zero _ _ _ rfl
    _ = hA.extClass.comp
        (hB.extClass.comp (Ext.mk₀ z) (add_zero 1)) rfl := by rw [hz]
    _ = (hA.extClass.comp hB.extClass rfl).comp (Ext.mk₀ z) (add_zero 2) :=
      (Ext.comp_assoc_of_third_deg_zero _ _ _ rfl).symm

end EtaleCohomology.CupTwoStepExtension
