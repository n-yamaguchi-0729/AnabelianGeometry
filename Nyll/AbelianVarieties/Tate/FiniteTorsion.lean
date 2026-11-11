/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.SchemeTheory.GroupSchemes.RelativeGroupLaw.AlgebraicPoints
public import Nyll.SchemeTheory.GroupSchemes.RelativeGroupLaw.Kernel
public import Nyll.AlgebraicCurves.Geometry.AbelianSchemes.GroupLaw.KernelPoints
public import Nyll.AlgebraicCurves.Geometry.AbelianSchemes.Theorems.RelativeGroupLawEtaleSchemeNsmul
public import Nyll.AlgebraicCurves.Geometry.AbelianSchemes.Theorems.RelativeGroupLawSmoothOfRelativeDimension
public import Nyll.SchemeTheory.CategoryTheory.SchemeHomOver
public import Nyll.SchemeTheory.Morphisms.QuasiFinite
public import Nyll.SchemeTheory.FiniteEtale.PointSections
public import Nyll.ProCGroups.Abelian.FullTateModule
public import Mathlib.AlgebraicGeometry.Pullbacks
public import Mathlib.AlgebraicGeometry.ZariskisMainTheorem
public import Mathlib.LinearAlgebra.FreeModule.Finite.Matrix
public import Mathlib.RingTheory.LocalRing.Module

/-!
# Actual torsion kernels and their finite coefficient points

The original torsion-to-kernel comparisons and finite étale kernel covers live here once.
Over a local base, their actual section algebra is finite and flat, hence free. Its algebra
maps to any field form a finite set. This supplies the same unit-index finiteness theorem to
full Tate modules, geometric torsion fibres and coefficient specialization.
-/

@[expose] public section

universe u

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra
open AlgebraicGeometry.FiniteEtale

namespace GoodReductionJacobian.RelativeGroupLaw

section General

variable {K : Type u} [CommRing K] {A : Scheme.{u}} {f : A ⟶ Spec (CommRingCat.of K)}
variable (G : RelativeGroupLaw K f) (hc : G.IsCommutative)

/-- Actual torsion in any coefficient algebra is represented by the kernel scheme. -/
def torsionLevelEquivAlgSchemeKerPoints (T : Type u) [CommRing T] [Algebra K T]
    (n : ℕ+) :
    ProCGroups.torsionLevel (G.AlgPoints hc T) n ≃
      SchemeHomOver (Spec.algebraMap K T) (G.schemeKerStr (n : ℕ)) :=
  ((AlgPoints.equivPoint (L := G) (hc := hc) (T := T)).subtypeEquiv
    (fun x => AlgPoints.nsmul_eq_zero_iff (n : ℕ) x)).trans
      (G.torsionSubsetEquivSchemeKerPoints (Spec.algebraMap K T) (n : ℕ))

/-- The algebra-valued kernel comparison retains the original point. -/
theorem torsionLevelEquivAlgSchemeKerPoints_comp_fst
    (T : Type u) [CommRing T] [Algebra K T] (n : ℕ+)
    (x : ProCGroups.torsionLevel (G.AlgPoints hc T) n) :
    (G.torsionLevelEquivAlgSchemeKerPoints hc T n x).1 ≫
        pullback.fst (G.schemeNsmul (n : ℕ))
          (G.one (𝟙 (Spec (CommRingCat.of K)))).1 = (AlgPoints.toPoint x.1).1 :=
  pullback.lift_fst _ _ _

/-- Extension of coefficients is the actual precomposition on kernel points. -/
theorem torsionLevelEquivAlgSchemeKerPoints_map
    {T T' : Type u} [CommRing T] [CommRing T'] [Algebra K T] [Algebra K T']
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

/-- Transport torsion points along an equality of their base maps. -/
def torsionSubsetChangeBase (n : ℕ)
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
  exact G.torsionSubsetEquivSchemeKerPoints_comp_fst
    (𝟙 (Spec (CommRingCat.of K))) (n : ℕ) _

end General

section LocalRingMultiplication

variable {K : Type u} [CommRing K] [IsLocalRing K] {A : Scheme.{u}} {f : A ⟶ Spec (.of K)}
  [IsProper f] [Smooth f] (G : RelativeGroupLaw K f) (hc : G.IsCommutative)

include hc in
/-- Multiplication by an invertible integer is an actual finite étale morphism. -/
theorem isFiniteEtale_schemeNsmul_of_isUnit (n : ℕ) (hn : IsUnit (n : K)) :
    IsFiniteEtale (G.schemeNsmul n) := by
  obtain ⟨d, hd⟩ := G.exists_smoothOfRelativeDimension_of_smooth_of_isLocalRing
  have _ : SmoothOfRelativeDimension d f := hd
  have _ : Etale (G.schemeNsmul n) :=
    G.etale_schemeNsmul_of_isUnit_of_smoothOfRelativeDimension hc d n hn
  have _ : IsProper (G.schemeNsmul n) := by
    have _ : IsProper (G.schemeNsmul n ≫ f) := by
      rw [G.schemeNsmul_over]
      infer_instance
    exact IsProper.of_comp _ f
  have _ : LocallyQuasiFinite (G.schemeNsmul n) :=
    LocallyQuasiFinite.of_formallyUnramified_of_locallyOfFiniteType _
  have _ : IsFinite (G.schemeNsmul n) := IsFinite.of_isProper_of_locallyQuasiFinite _
  exact IsFiniteEtale.mk

end LocalRingMultiplication

section LocalRingKernel

variable {H : Type u} [CommRing H] [IsLocalRing H]
  {A : Scheme.{u}} {f : A ⟶ Spec (.of H)} [IsProper f] [Smooth f]
  (G : RelativeGroupLaw H f) (hc : G.IsCommutative)

include hc in
/-- The actual multiplication kernel at an invertible index is finite étale. -/
theorem isFiniteEtale_schemeKerStr_of_isUnit (n : ℕ) (hn : IsUnit (n : H)) :
    IsFiniteEtale (G.schemeKerStr n) := by
  have : IsFiniteEtale (G.schemeNsmul n) :=
    G.isFiniteEtale_schemeNsmul_of_isUnit hc n hn
  have : IsFinite (G.schemeKerStr n) := inferInstance
  have : Etale (G.schemeKerStr n) := inferInstance
  exact IsFiniteEtale.mk

/-- The existing multiplication kernel bundled over the original local ring. -/
def unitTorsionCover (n : ℕ+) (hn : IsUnit ((n : ℕ) : H)) :
    FiniteEtale (Spec (.of H)) := by
  have : IsFiniteEtale (G.schemeKerStr (n : ℕ)) :=
    G.isFiniteEtale_schemeKerStr_of_isUnit hc (n : ℕ) hn
  exact FiniteEtale.mk (G.schemeKerStr (n : ℕ))

/-- Torsion points over any coefficient algebra are actual points of this cover. -/
def torsionLevelEquivUnitKernelPoints (T : Type u) [CommRing T] [Algebra H T]
    (n : ℕ+) (hn : IsUnit ((n : ℕ) : H)) :
    ProCGroups.torsionLevel (G.AlgPoints hc T) n ≃
      (Over.mk (Spec.algebraMap H T) ⟶ (G.unitTorsionCover hc n hn).toComma) :=
  (G.torsionLevelEquivAlgSchemeKerPoints hc T n).trans
    (schemeHomOverEquivOverHom (Spec.algebraMap H T) (G.schemeKerStr (n : ℕ)))

/-- Torsion points are algebra maps on the actual finite kernel's section algebra. -/
def torsionLevelEquivKernelSections (T : Type u) [CommRing T] [Algebra H T]
    (n : ℕ+) (hn : IsUnit ((n : ℕ) : H)) :
    ProCGroups.torsionLevel (G.AlgPoints hc T) n ≃
      (Γ((G.unitTorsionCover hc n hn).left, ⊤) →ₐ[H] T) :=
  (G.torsionLevelEquivUnitKernelPoints hc T n hn).trans
    (pointHomAlgEquiv H T (G.unitTorsionCover hc n hn))

/-- Every unit-index torsion level over field-valued coefficients is finite. -/
theorem finite_torsionLevel_of_isUnit
    (L : Type u) [Field L] [Algebra H L] (n : ℕ+) (hn : IsUnit ((n : ℕ) : H)) :
    Finite (ProCGroups.torsionLevel (G.AlgPoints hc L) n) := by
  let X := G.unitTorsionCover hc n hn
  have : Module.Finite H Γ(X.left, ⊤) := sections_moduleFinite H X
  have : Module.Free H Γ(X.left, ⊤) := Module.free_of_flat_of_isLocalRing
  exact Finite.of_injective (G.torsionLevelEquivKernelSections hc L n hn)
    (G.torsionLevelEquivKernelSections hc L n hn).injective


end LocalRingKernel

end GoodReductionJacobian.RelativeGroupLaw
