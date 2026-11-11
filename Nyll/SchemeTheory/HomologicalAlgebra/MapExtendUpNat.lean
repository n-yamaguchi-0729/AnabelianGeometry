/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/


module

public import Mathlib.Algebra.Homology.Additive
public import Mathlib.Algebra.Homology.Embedding.Extend
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Zero
public import Mathlib.CategoryTheory.Limits.Shapes.ZeroObjects

/-!
# Mapping the zero extension of a nonnegative complex

A zero-preserving functor commutes with extension from nonnegative to
integer degrees. The actual comparison uses the canonical extension
isomorphisms in nonnegative degrees and zero objects in negative degrees.
-/

@[expose] public section

noncomputable section

universe uC vC uD vD

open CategoryTheory Limits

namespace CategoryTheory.Functor

variable {C : Type uC} [Category.{vC} C] [HasZeroMorphisms C] [HasZeroObject C]
  {D : Type uD} [Category.{vD} D] [HasZeroMorphisms D] [HasZeroObject D]
  (F : C ⥤ D) [F.PreservesZeroMorphisms]

/-- The extension of a nonnegative cochain complex is zero in negative degrees. -/
theorem isZero_extend_negSucc (K : CochainComplex C ℕ) (n : ℕ) :
    IsZero ((K.extend ComplexShape.embeddingUpNat).X (Int.negSucc n)) :=
  K.isZero_extend_X ComplexShape.embeddingUpNat (Int.negSucc n) (fun i h => by
    change Int.ofNat i = Int.negSucc n at h
    cases h)

/-- The degreewise comparison between mapping a complex and extending it by zero. -/
def mapExtendUpNatXIso (K : CochainComplex C ℕ) (j : ℤ) :
    ((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj
      (K.extend ComplexShape.embeddingUpNat)).X j ≅
      (((F.mapHomologicalComplex (ComplexShape.up ℕ)).obj K).extend
        ComplexShape.embeddingUpNat).X j := by
  cases j with
  | ofNat n =>
      exact F.mapIso (K.extendXIso ComplexShape.embeddingUpNat (i := n) rfl) ≪≫
        (((F.mapHomologicalComplex (ComplexShape.up ℕ)).obj K).extendXIso
          ComplexShape.embeddingUpNat (i := n) rfl).symm
  | negSucc n =>
      exact (F.map_isZero (isZero_extend_negSucc K n)).iso
        (isZero_extend_negSucc ((F.mapHomologicalComplex (ComplexShape.up ℕ)).obj K) n)

/-- Mapping a nonnegative complex commutes with its actual zero extension. -/
def mapExtendUpNatIso (K : CochainComplex C ℕ) :
    (F.mapHomologicalComplex (ComplexShape.up ℤ)).obj (K.extend ComplexShape.embeddingUpNat) ≅
      ((F.mapHomologicalComplex (ComplexShape.up ℕ)).obj K).extend
        ComplexShape.embeddingUpNat :=
  HomologicalComplex.Hom.isoOfComponents (mapExtendUpNatXIso F K) (by
    intro i j _
    cases i with
    | negSucc i =>
        exact (F.map_isZero (isZero_extend_negSucc K i)).eq_of_src _ _
    | ofNat i =>
        cases j with
        | negSucc j =>
            exact (isZero_extend_negSucc
              ((F.mapHomologicalComplex (ComplexShape.up ℕ)).obj K) j).eq_of_tgt _ _
        | ofNat j =>
            have hi : ComplexShape.embeddingUpNat.f i = (i : ℤ) := rfl
            have hj : ComplexShape.embeddingUpNat.f j = (j : ℤ) := rfl
            let ai := K.extendXIso ComplexShape.embeddingUpNat hi
            let aj := K.extendXIso ComplexShape.embeddingUpNat hj
            let bi := ((F.mapHomologicalComplex (ComplexShape.up ℕ)).obj K).extendXIso
              ComplexShape.embeddingUpNat hi
            let bj := ((F.mapHomologicalComplex (ComplexShape.up ℕ)).obj K).extendXIso
              ComplexShape.embeddingUpNat hj
            change (F.map ai.hom ≫ bi.inv) ≫
                (((F.mapHomologicalComplex (ComplexShape.up ℕ)).obj K).extend
                  ComplexShape.embeddingUpNat).d (i : ℤ) (j : ℤ) =
              F.map ((K.extend ComplexShape.embeddingUpNat).d (i : ℤ) (j : ℤ)) ≫
                F.map aj.hom ≫ bj.inv
            rw [HomologicalComplex.extend_d_eq _ ComplexShape.embeddingUpNat hi hj,
              HomologicalComplex.extend_d_eq K ComplexShape.embeddingUpNat hi hj]
            change (F.map ai.hom ≫ bi.inv) ≫ (bi.hom ≫ F.map (K.d i j) ≫ bj.inv) =
              F.map (ai.hom ≫ K.d i j ≫ aj.inv) ≫ F.map aj.hom ≫ bj.inv
            have hcancel : F.map aj.inv ≫ F.map aj.hom ≫ bj.inv = bj.inv := by
              rw [← F.map_comp_assoc, aj.inv_hom_id, F.map_id, Category.id_comp]
            simp only [Functor.map_comp, Category.assoc, Iso.inv_hom_id_assoc, hcancel])

/-- In a nonnegative degree, the comparison uses the two original
extension isomorphisms. -/
theorem mapExtendUpNatIso_hom_f_ofNat (K : CochainComplex C ℕ) (n : ℕ) :
    (F.mapExtendUpNatIso K).hom.f (n : ℤ) =
      F.map (K.extendXIso ComplexShape.embeddingUpNat (i := n) rfl).hom ≫
        (((F.mapHomologicalComplex (ComplexShape.up ℕ)).obj K).extendXIso
          ComplexShape.embeddingUpNat (i := n) rfl).inv := rfl

/-- The inverse comparison in a nonnegative degree. -/
theorem mapExtendUpNatIso_inv_f_ofNat (K : CochainComplex C ℕ) (n : ℕ) :
    (F.mapExtendUpNatIso K).inv.f (n : ℤ) =
      (((F.mapHomologicalComplex (ComplexShape.up ℕ)).obj K).extendXIso
          ComplexShape.embeddingUpNat (i := n) rfl).hom ≫
        F.map (K.extendXIso ComplexShape.embeddingUpNat (i := n) rfl).inv := rfl

/-- The actual extension comparison commutes with every chain map. -/
theorem mapExtendUpNatIso_hom_naturality
    {K L : CochainComplex C ℕ} (φ : K ⟶ L) :
    (F.mapHomologicalComplex (ComplexShape.up ℤ)).map
        (HomologicalComplex.extendMap φ ComplexShape.embeddingUpNat) ≫
      (F.mapExtendUpNatIso L).hom =
    (F.mapExtendUpNatIso K).hom ≫
      HomologicalComplex.extendMap
        ((F.mapHomologicalComplex (ComplexShape.up ℕ)).map φ)
        ComplexShape.embeddingUpNat := by
  ext j
  cases j with
  | negSucc n =>
      exact (F.map_isZero (isZero_extend_negSucc K n)).eq_of_src _ _
  | ofNat n =>
      have hn : ComplexShape.embeddingUpNat.f n = (n : ℤ) := rfl
      let aK := K.extendXIso ComplexShape.embeddingUpNat hn
      let aL := L.extendXIso ComplexShape.embeddingUpNat hn
      let bK := ((F.mapHomologicalComplex (ComplexShape.up ℕ)).obj K).extendXIso
        ComplexShape.embeddingUpNat hn
      let bL := ((F.mapHomologicalComplex (ComplexShape.up ℕ)).obj L).extendXIso
        ComplexShape.embeddingUpNat hn
      change F.map ((HomologicalComplex.extendMap φ ComplexShape.embeddingUpNat).f
          (n : ℤ)) ≫ (F.map aL.hom ≫ bL.inv) =
        (F.map aK.hom ≫ bK.inv) ≫
          (HomologicalComplex.extendMap
            ((F.mapHomologicalComplex (ComplexShape.up ℕ)).map φ)
            ComplexShape.embeddingUpNat).f (n : ℤ)
      rw [HomologicalComplex.extendMap_f φ ComplexShape.embeddingUpNat hn,
        HomologicalComplex.extendMap_f
          ((F.mapHomologicalComplex (ComplexShape.up ℕ)).map φ)
          ComplexShape.embeddingUpNat hn]
      change F.map (aK.hom ≫ φ.f n ≫ aL.inv) ≫ (F.map aL.hom ≫ bL.inv) =
        (F.map aK.hom ≫ bK.inv) ≫ (bK.hom ≫ F.map (φ.f n) ≫ bL.inv)
      have hcancel : F.map aL.inv ≫ F.map aL.hom ≫ bL.inv = bL.inv := by
        rw [← F.map_comp_assoc, aL.inv_hom_id, F.map_id, Category.id_comp]
      simp only [Functor.map_comp, Category.assoc, Iso.inv_hom_id_assoc, hcancel]

end CategoryTheory.Functor
