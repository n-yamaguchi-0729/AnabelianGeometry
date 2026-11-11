/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Mathlib.CategoryTheory.Preadditive.Basic
public import Mathlib.CategoryTheory.Limits.Shapes.Kernels
public import Mathlib.CategoryTheory.Abelian.Basic

/-!
# Cokernels after quotienting by an n-divisible image

If multiplication by `n` is epic on `A`, quotienting `B` by the image of
`A` does not change the cokernel of multiplication by `n` on `B`.
-/

@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory.Limits

variable {C : Type*} [Category C] [Preadditive C] [HasCokernels C]
  {A B : C}

/-- Quotienting by an n-divisible image does not change the cokernel of
multiplication by n. The comparison is induced by the actual quotient map. -/
def cokernelNsmulQuotientIso (f : A ⟶ B) (n : ℕ) [Epi (n • 𝟙 A)] :
    cokernel (n • 𝟙 B) ≅ cokernel (n • 𝟙 (cokernel f)) := by
  let q := cokernel.π f
  let p := cokernel.π (n • 𝟙 B)
  have hf : f ≫ p = 0 := by
    apply (cancel_epi (n • 𝟙 A)).mp
    calc
      (n • 𝟙 A) ≫ f ≫ p = f ≫ (n • 𝟙 B) ≫ p := by
        simp only [Preadditive.nsmul_comp, Preadditive.comp_nsmul,
          Category.id_comp]
      _ = 0 := by rw [cokernel.condition, comp_zero]
      _ = (n • 𝟙 A) ≫ 0 := (comp_zero).symm
  let b : cokernel f ⟶ cokernel (n • 𝟙 B) := cokernel.desc f p hf
  have hqb : q ≫ b = p := cokernel.π_desc _ _ _
  have hb : (n • 𝟙 (cokernel f)) ≫ b = 0 := by
    apply (cancel_epi q).mp
    calc
      q ≫ (n • 𝟙 (cokernel f)) ≫ b = (n • 𝟙 B) ≫ q ≫ b := by
        simp only [Preadditive.nsmul_comp, Preadditive.comp_nsmul,
          Category.id_comp]
      _ = (n • 𝟙 B) ≫ p := by rw [hqb]
      _ = 0 := cokernel.condition _
      _ = q ≫ 0 := (comp_zero).symm
  have hnq : (n • 𝟙 B) ≫ q = q ≫ (n • 𝟙 (cokernel f)) := by
    simp only [Preadditive.nsmul_comp, Preadditive.comp_nsmul,
      Category.id_comp, Category.comp_id]
  let a := cokernel.map (n • 𝟙 B) (n • 𝟙 (cokernel f)) q q hnq
  let c := cokernel.desc (n • 𝟙 (cokernel f)) b hb
  have hpa : p ≫ a = q ≫ cokernel.π (n • 𝟙 (cokernel f)) :=
    cokernel.π_desc _ _ _
  have hpc : cokernel.π (n • 𝟙 (cokernel f)) ≫ c = b :=
    cokernel.π_desc _ _ _
  have hba : b ≫ a = cokernel.π (n • 𝟙 (cokernel f)) := by
    apply (cancel_epi q).mp
    rw [← Category.assoc, hqb, hpa]
  refine ⟨a, c, ?_, ?_⟩
  · apply (cancel_epi p).mp
    rw [← Category.assoc, hpa, Category.assoc, hpc, hqb, Category.comp_id]
  · apply (cancel_epi (cokernel.π (n • 𝟙 (cokernel f)))).mp
    rw [← Category.assoc, hpc, hba, Category.comp_id]

/-- The comparison on power cokernels is induced by the quotient map. -/
theorem cokernelNsmulQuotientIso_π_hom (f : A ⟶ B) (n : ℕ) [Epi (n • 𝟙 A)] :
    cokernel.π (n • 𝟙 B) ≫ (cokernelNsmulQuotientIso f n).hom =
      cokernel.π f ≫ cokernel.π (n • 𝟙 (cokernel f)) := by
  exact cokernel.π_desc _ _ _

section Abelian

variable {D : Type*} [Category D] [Abelian D] {A B : D}

/-- A subobject with n-torsion-free quotient has exactly the same n-torsion
as its ambient object. The isomorphism is induced by the subobject map. -/
def kernelNsmulSubobjectIso (f : A ⟶ B) [Mono f] (n : ℕ)
    [Mono (n • 𝟙 (cokernel f))] :
    kernel (n • 𝟙 A) ≅ kernel (n • 𝟙 B) := by
  let q := cokernel.π f
  let k := kernel.ι (n • 𝟙 B)
  have hkq : k ≫ q = 0 := by
    apply (cancel_mono (n • 𝟙 (cokernel f))).mp
    calc
      (k ≫ q) ≫ (n • 𝟙 (cokernel f)) =
          (k ≫ (n • 𝟙 B)) ≫ q := by
        simp only [Preadditive.nsmul_comp, Preadditive.comp_nsmul,
          Category.comp_id]
      _ = 0 := by rw [kernel.condition, zero_comp]
      _ = 0 ≫ (n • 𝟙 (cokernel f)) := (zero_comp).symm
  let b : kernel (n • 𝟙 B) ⟶ A := Abelian.monoLift f k hkq
  have hbf : b ≫ f = k := Abelian.monoLift_comp _ _ _
  have hbn : b ≫ (n • 𝟙 A) = 0 := by
    apply (cancel_mono f).mp
    calc
      (b ≫ (n • 𝟙 A)) ≫ f = (b ≫ f) ≫ (n • 𝟙 B) := by
        simp only [Preadditive.nsmul_comp, Preadditive.comp_nsmul,
          Category.comp_id]
      _ = 0 := by rw [hbf, kernel.condition]
      _ = 0 ≫ f := (zero_comp).symm
  have hnf : (n • 𝟙 A) ≫ f = f ≫ (n • 𝟙 B) := by
    simp only [Preadditive.nsmul_comp, Preadditive.comp_nsmul,
      Category.id_comp, Category.comp_id]
  let a := kernel.map (n • 𝟙 A) (n • 𝟙 B) f f hnf
  let c := kernel.lift (n • 𝟙 A) b hbn
  have hak : a ≫ k = kernel.ι (n • 𝟙 A) ≫ f :=
    kernel.lift_ι _ _ _
  have hci : c ≫ kernel.ι (n • 𝟙 A) = b := kernel.lift_ι _ _ _
  have hab : a ≫ b = kernel.ι (n • 𝟙 A) := by
    apply (cancel_mono f).mp
    rw [Category.assoc, hbf, hak]
  refine ⟨a, c, ?_, ?_⟩
  · apply (cancel_mono (kernel.ι (n • 𝟙 A))).mp
    rw [Category.assoc, hci, hab, Category.id_comp]
  · apply (cancel_mono k).mp
    rw [Category.assoc, hak, ← Category.assoc, hci, hbf, Category.id_comp]

/-- The comparison on torsion kernels is induced by the subobject map. -/
theorem kernelNsmulSubobjectIso_hom_ι (f : A ⟶ B) [Mono f] (n : ℕ)
    [Mono (n • 𝟙 (cokernel f))] :
    (kernelNsmulSubobjectIso f n).hom ≫ kernel.ι (n • 𝟙 B) =
      kernel.ι (n • 𝟙 A) ≫ f := by
  exact kernel.lift_ι _ _ _

end Abelian

end CategoryTheory.Limits
