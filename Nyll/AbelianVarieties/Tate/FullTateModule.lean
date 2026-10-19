/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.AlgebraicCurves.Geometry.AbelianSchemes.GroupLaw.AlgebraicPoints
import Nyll.AlgebraicCurves.Geometry.AbelianSchemes.GroupLaw.EndDegree
import Nyll.AlgebraicCurves.Geometry.AbelianSchemes.GroupLaw.Kernel
import Nyll.AlgebraicCurves.Geometry.AbelianSchemes.Theorems.RelativeGroupLawEtaleSchemeNsmul
import Nyll.AlgebraicCurves.Geometry.AbelianSchemes.Theorems.RelativeGroupLawFiniteEndKerStrNatCardEqEndDegree
import Nyll.AlgebraicCurves.Geometry.Picard.GroupLaw.RelativeGroupLaw
import Nyll.AlgebraicCurves.Geometry.Schemes.SchemeHomOver
import Mathlib.AlgebraicGeometry.Pullbacks
import Nyll.ProCGroups.Abelian.FullTateModule

/-!
# The full Tate module of algebraic-group points

The actual torsion levels of the additive group of algebraic points identify
with points of the multiplication kernel. For a proper smooth commutative
group scheme over an algebraically closed field of characteristic zero,
these kernels are finite étale. Thus the full Tate module has finite levels
and is compact in its canonical topology. Its Hausdorff, totally disconnected,
and torsion-free structures are supplied by the general full Tate construction.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra

namespace GoodReductionJacobian.RelativeGroupLaw

open AlgebraicCurves.Geometry.AbelianSchemes.Theorems.Proofs
open RelativeGroupLaw_isFinite_endKerStr_and_natCard_eq_endDegree_of_etale.P2mSepKer

section General

variable {K : Type} [CommRing K] {A : Scheme.{0}} {f : A ⟶ Spec (CommRingCat.of K)}
variable (G : RelativeGroupLaw K f) (hc : G.IsCommutative)

private theorem comp_nsmul_idPoint {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of K))
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
def torsionSubsetEquivSchemeKerPoints {T : Scheme.{0}}
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
theorem torsionSubsetEquivSchemeKerPoints_comp_fst {T : Scheme.{0}}
    (t : T ⟶ Spec (CommRingCat.of K)) (n : ℕ) (x : G.torsionSubset t n) :
    (G.torsionSubsetEquivSchemeKerPoints t n x).1 ≫
        pullback.fst (G.schemeNsmul n) (G.one (𝟙 (Spec (CommRingCat.of K)))).1 = x.1.1 :=
  pullback.lift_fst _ _ _

/-- Actual torsion in any coefficient algebra is represented by the kernel scheme. -/
def torsionLevelEquivAlgSchemeKerPoints (T : Type) [CommRing T] [Algebra K T]
    (n : ℕ+) :
    ProCGroups.torsionLevel (G.AlgPoints hc T) n ≃
      SchemeHomOver (Spec.algebraMap K T) (G.schemeKerStr (n : ℕ)) :=
  ((AlgPoints.equivPoint (L := G) (hc := hc) (T := T)).subtypeEquiv
    (fun x => AlgPoints.nsmul_eq_zero_iff (n : ℕ) x)).trans
      (G.torsionSubsetEquivSchemeKerPoints (Spec.algebraMap K T) (n : ℕ))

/-- The algebra-valued kernel comparison retains the original point. -/
theorem torsionLevelEquivAlgSchemeKerPoints_comp_fst
    (T : Type) [CommRing T] [Algebra K T] (n : ℕ+)
    (x : ProCGroups.torsionLevel (G.AlgPoints hc T) n) :
    (G.torsionLevelEquivAlgSchemeKerPoints hc T n x).1 ≫
        pullback.fst (G.schemeNsmul (n : ℕ))
          (G.one (𝟙 (Spec (CommRingCat.of K)))).1 = (AlgPoints.toPoint x.1).1 :=
  pullback.lift_fst _ _ _

/-- Extension of coefficients is the actual precomposition on kernel points. -/
theorem torsionLevelEquivAlgSchemeKerPoints_map
    {T T' : Type} [CommRing T] [CommRing T'] [Algebra K T] [Algebra K T']
    (a : T →ₐ[K] T') (n : ℕ+)
    (x : ProCGroups.torsionLevel (G.AlgPoints hc T) n)
    (y : ProCGroups.torsionLevel (G.AlgPoints hc T') n)
    (hy : y.1 = AlgPoints.map a x.1) :
    (G.torsionLevelEquivAlgSchemeKerPoints hc T' n y).1 =
      Spec.map (CommRingCat.ofHom a.toRingHom) ≫
        (G.torsionLevelEquivAlgSchemeKerPoints hc T n x).1 := by
  apply pullback.hom_ext
  · rw [G.torsionLevelEquivAlgSchemeKerPoints_comp_fst,
      Category.assoc, G.torsionLevelEquivAlgSchemeKerPoints_comp_fst]
    rw [hy, AlgPoints.toPoint_map_coe]
  · change (G.torsionLevelEquivAlgSchemeKerPoints hc T' n y).1 ≫
        G.schemeKerStr (n : ℕ) = _
    rw [(G.torsionLevelEquivAlgSchemeKerPoints hc T' n y).2,
      Category.assoc, (G.torsionLevelEquivAlgSchemeKerPoints hc T n x).2]
    exact (AlgPoints.specMap_comp_algebraMap a).symm

private def torsionSubsetChangeBase (n : ℕ)
    (t t' : Spec (CommRingCat.of K) ⟶ Spec (CommRingCat.of K)) (h : t = t') :
    G.torsionSubset t n ≃ G.torsionSubset t' n where
  toFun x := ⟨⟨x.1.1, x.1.2.trans h⟩, by
    subst t'
    exact x.2⟩
  invFun x := ⟨⟨x.1.1, x.1.2.trans h.symm⟩, by
    subst t'
    exact x.2⟩
  left_inv x := by
    apply Subtype.ext
    apply Subtype.ext
    rfl
  right_inv x := by
    apply Subtype.ext
    apply Subtype.ext
    rfl

/-- The actual torsion subgroup of algebraic points is the point set of the
scheme theoretic multiplication kernel. -/
def torsionLevelEquivSchemeKerPoints (n : ℕ+) :
    ProCGroups.torsionLevel (G.AlgPoints hc K) n ≃
      SchemeHomOver (𝟙 (Spec (CommRingCat.of K))) (G.schemeKerStr (n : ℕ)) := by
  let t : Spec (CommRingCat.of K) ⟶ Spec (CommRingCat.of K) :=
    Spec.map (CommRingCat.ofHom (algebraMap K K))
  let e₁ : ProCGroups.torsionLevel (G.AlgPoints hc K) n ≃ G.torsionSubset t (n : ℕ) :=
    (AlgPoints.equivPoint (L := G) (hc := hc) (T := K)).subtypeEquiv
      (fun x => AlgPoints.nsmul_eq_zero_iff (n : ℕ) x)
  have ht : t = 𝟙 (Spec (CommRingCat.of K)) := by
    change Spec.map (CommRingCat.ofHom (RingHom.id K)) = _
    rw [CommRingCat.ofHom_id]
    exact Spec.map_id (CommRingCat.of K)
  let e₂ : G.torsionSubset t (n : ℕ) ≃
      G.torsionSubset (𝟙 (Spec (CommRingCat.of K))) (n : ℕ) :=
    torsionSubsetChangeBase G (n : ℕ) t (𝟙 (Spec (CommRingCat.of K))) ht
  exact (e₁.trans e₂).trans
    (G.torsionSubsetEquivSchemeKerPoints (𝟙 (Spec (CommRingCat.of K))) (n : ℕ))

/-- The scheme-kernel comparison preserves the underlying point of the group scheme. -/
theorem torsionLevelEquivSchemeKerPoints_comp_fst (n : ℕ+)
    (x : ProCGroups.torsionLevel (G.AlgPoints hc K) n) :
    (G.torsionLevelEquivSchemeKerPoints hc n x).1 ≫
        pullback.fst (G.schemeNsmul (n : ℕ)) (G.one (𝟙 (Spec (CommRingCat.of K)))).1 =
      (AlgPoints.toPoint x.1).1 := by
  change pullback.lift _ (𝟙 _) _ ≫ pullback.fst _ _ = _
  exact pullback.lift_fst _ _ _

end General

section Field

variable {K : Type} [Field K] {A : Scheme.{0}} {f : A ⟶ Spec (CommRingCat.of K)}
variable (G : RelativeGroupLaw K f) (hc : G.IsCommutative)

/-- Properness and smoothness make every positive torsion level finite in
characteristic zero, without any separate finiteness hypothesis on points. -/
theorem finite_torsionLevel [IsAlgClosed K] [CharZero K] [IsProper f]
    (d : ℕ) [SmoothOfRelativeDimension d f] (n : ℕ+) :
    Finite (ProCGroups.torsionLevel (G.AlgPoints hc K) n) := by
  have hn : IsUnit ((n : ℕ) : K) :=
    isUnit_iff_ne_zero.mpr (Nat.cast_ne_zero.mpr (Nat.ne_of_gt n.property))
  have : Etale (G.schemeNsmul (n : ℕ)) :=
    G.etale_schemeNsmul_of_isUnit_of_smoothOfRelativeDimension hc d (n : ℕ) hn
  have : Etale (G.endKerStr (G.nsmul f (n : ℕ) idPoint)) :=
    inferInstanceAs (Etale (G.schemeKerStr (n : ℕ)))
  have hfinite : Finite (KerPts G (G.nsmul f (n : ℕ) idPoint)) :=
    (G.isFinite_endKerStr_and_natCard_eq_endDegree_of_etale K f
      (G.nsmul f (n : ℕ) idPoint)).2.1
  have : Finite (SchemeHomOver (𝟙 (Spec (CommRingCat.of K)))
      (G.schemeKerStr (n : ℕ))) :=
    Finite.of_equiv _ (kerPtsEquiv G (G.nsmul f (n : ℕ) idPoint)).symm
  exact Finite.of_equiv _ (G.torsionLevelEquivSchemeKerPoints hc n).symm

/-- The full Tate module of actual algebraic points is compact. -/
theorem compactSpace_fullTateModule [IsAlgClosed K] [CharZero K] [IsProper f]
    (d : ℕ) [SmoothOfRelativeDimension d f] :
    CompactSpace (ProCGroups.FullTateModule (G.AlgPoints hc K)) := by
  have : ∀ n : ℕ+, Finite (ProCGroups.torsionLevel (G.AlgPoints hc K) n) :=
    fun n => G.finite_torsionLevel hc d n
  infer_instance

end Field

end GoodReductionJacobian.RelativeGroupLaw
