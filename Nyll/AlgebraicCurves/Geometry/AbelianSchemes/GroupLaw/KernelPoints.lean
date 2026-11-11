/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.SchemeTheory.GroupSchemes.RelativeGroupLaw.EndDegree
public import Nyll.SchemeTheory.GroupSchemes.RelativeGroupLaw.Kernel
public import Nyll.SchemeTheory.CategoryTheory.SchemeHomOver
public import Mathlib.AlgebraicGeometry.Pullbacks

/-!
# Points of the multiplication kernel

The original relative points killed by multiplication identify with points
of the actual scheme theoretic kernel, over any test scheme.
-/

@[expose] public section

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra

namespace GoodReductionJacobian.RelativeGroupLaw

variable {K : Type u} [CommRing K] {A : Scheme.{u}}
  {f : A ⟶ Spec (CommRingCat.of K)} (G : RelativeGroupLaw K f)

private theorem comp_nsmul_idPoint {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of K))
    (n : ℕ) (x : SchemeHomOver t f) :
    NeronModelInfra.schemeHomOverComp x (G.nsmul f n idPoint) = G.nsmul t n x := by
  have hid : GoodReductionJacobian.schemeHomOverComp x.1 x.2
      (idPoint : SchemeHomOver f f) = x := by
    apply Subtype.ext
    exact Category.comp_id x.1
  have h := G.nsmul_natural f t x.1 x.2 n idPoint
  rw [hid] at h
  exact h

/-- Torsion points over any test scheme are points of the multiplication kernel. -/
def torsionSubsetEquivSchemeKerPoints {T : Scheme.{u}}
    (t : T ⟶ Spec (CommRingCat.of K)) (n : ℕ) :
    G.torsionSubset t n ≃ SchemeHomOver t (G.schemeKerStr n) where
  toFun x := ⟨pullback.lift x.1.1 t (by
    have h := congrArg Subtype.val (comp_nsmul_idPoint G t n x.1)
    have he := congrArg Subtype.val
      (G.one_natural (𝟙 (Spec (CommRingCat.of K))) t t (Category.comp_id t))
    change x.1.1 ≫ G.schemeNsmul n = (G.nsmul t n x.1).1 at h
    rw [x.2] at h
    exact h.trans he.symm), by
      exact pullback.lift_snd _ _ _⟩
  invFun z := ⟨⟨z.1 ≫ pullback.fst (G.schemeNsmul n) (G.one (𝟙 (Spec (CommRingCat.of K)))).1, by
      have hb : pullback.fst (G.schemeNsmul n)
          (G.one (𝟙 (Spec (CommRingCat.of K)))).1 ≫ f = G.schemeKerStr n :=
        G.endKerι_comp_base (G.nsmul f n idPoint)
      rw [Category.assoc, hb]
      exact z.2⟩, by
    apply Subtype.ext
    rw [← comp_nsmul_idPoint]
    change (z.1 ≫ pullback.fst (G.schemeNsmul n)
      (G.one (𝟙 (Spec (CommRingCat.of K)))).1) ≫ G.schemeNsmul n =
      (G.one t).1
    rw [Category.assoc, pullback.condition, ← Category.assoc, z.2]
    exact congrArg Subtype.val
      (G.one_natural (𝟙 (Spec (CommRingCat.of K))) t t (Category.comp_id t))⟩
  left_inv x := by
    apply Subtype.ext
    apply Subtype.ext
    exact pullback.lift_fst _ _ _
  right_inv z := by
    apply Subtype.ext
    apply pullback.hom_ext
    · exact pullback.lift_fst _ _ _
    · exact (pullback.lift_snd _ _ _).trans z.2.symm

/-- The kernel comparison retains the underlying point over any test scheme. -/
theorem torsionSubsetEquivSchemeKerPoints_comp_fst {T : Scheme.{u}}
    (t : T ⟶ Spec (CommRingCat.of K)) (n : ℕ) (x : G.torsionSubset t n) :
    (G.torsionSubsetEquivSchemeKerPoints t n x).1 ≫
        pullback.fst (G.schemeNsmul n) (G.one (𝟙 (Spec (CommRingCat.of K)))).1 = x.1.1 :=
  pullback.lift_fst _ _ _

end GoodReductionJacobian.RelativeGroupLaw
