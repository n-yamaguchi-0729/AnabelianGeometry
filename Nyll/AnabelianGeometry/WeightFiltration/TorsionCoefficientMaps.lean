/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.AnabelianGeometry.WeightFiltration.TorsionSpecialization

/-!
# Coefficient maps in the actual torsion and section-algebra descriptions

The kernel comparison respects the original coefficient extension on points.
This identifies the additive torsion map with composition on the existing
section algebra, so actual integral lifting and reduction can retain the group law.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra
open AlgebraicGeometry.FiniteEtale

namespace GoodReductionJacobian.RelativeGroupLaw

variable {H : Type} [CommRing H] {A : Scheme} {f : A ⟶ Spec (.of H)}
  (G : RelativeGroupLaw H f) (hc : G.IsCommutative)

/-- The actual coefficient extension restricted to a torsion level. -/
def torsionCoefficientMap {T T' : Type} [CommRing T] [CommRing T']
    [Algebra H T] [Algebra H T'] (a : T →ₐ[H] T') (n : ℕ+) :
    ProCGroups.torsionLevel (G.AlgPoints hc T) n →+
      ProCGroups.torsionLevel (G.AlgPoints hc T') n where
  toFun x := ⟨AlgPoints.map a x.1, by
    change (n : ℕ) • AlgPoints.map a x.1 = 0
    rw [← map_nsmul, x.2, map_zero]⟩
  map_zero' := Subtype.ext (map_zero _)
  map_add' x y := Subtype.ext (map_add _ x.1 y.1)

/-- Coefficient extension commutes with the existing multiplication transitions. -/
theorem torsionCoefficientMap_transition
    {T T' : Type} [CommRing T] [CommRing T'] [Algebra H T] [Algebra H T']
    (a : T →ₐ[H] T') (n m : ℕ+)
    (x : ProCGroups.torsionLevel (G.AlgPoints hc T) (n * m)) :
    ProCGroups.torsionTransition (G.AlgPoints hc T') n m
        (G.torsionCoefficientMap hc a (n * m) x) =
      G.torsionCoefficientMap hc a n
        (ProCGroups.torsionTransition (G.AlgPoints hc T) n m x) := by
  apply Subtype.ext
  change (m : ℕ) • AlgPoints.map a x.1 = AlgPoints.map a ((m : ℕ) • x.1)
  rw [map_nsmul]

variable [IsLocalRing H] [IsProper f] [Smooth f]

/-- Torsion points are algebra maps on the actual finite kernel's section algebra. -/
def torsionLevelEquivKernelSections (T : Type) [CommRing T] [Algebra H T]
    (n : ℕ+) (hn : IsUnit ((n : ℕ) : H)) :
    ProCGroups.torsionLevel (G.AlgPoints hc T) n ≃
      (Γ((G.unitTorsionCover hc n hn).left, ⊤) →ₐ[H] T) :=
  (G.torsionLevelEquivUnitKernelPoints hc T n hn).trans
    (pointHomAlgEquiv H T (G.unitTorsionCover hc n hn))

/-- The kernel's section algebra sees coefficient extension as composition. -/
theorem torsionLevelEquivKernelSections_map
    {T T' : Type} [CommRing T] [CommRing T'] [Algebra H T] [Algebra H T']
    (a : T →ₐ[H] T') (n : ℕ+) (hn : IsUnit ((n : ℕ) : H))
    (x : ProCGroups.torsionLevel (G.AlgPoints hc T) n) :
    G.torsionLevelEquivKernelSections hc T' n hn
        (G.torsionCoefficientMap hc a n x) =
      a.comp (G.torsionLevelEquivKernelSections hc T n hn x) := by
  apply AlgHom.coe_ringHom_injective
  refine congrArg (fun k : Γ((G.unitTorsionCover hc n hn).left, ⊤) ⟶
      CommRingCat.of T' => k.hom) ?_
  apply Spec.map_injective
  let X := G.unitTorsionCover hc n hn
  change Spec.map (CommRingCat.ofHom
      (pointHomAlgEquiv H T' X
        (G.torsionLevelEquivUnitKernelPoints hc T' n hn
          (G.torsionCoefficientMap hc a n x))).toRingHom) = _
  rw [pointHomAlgEquiv_specMap]
  have h := G.torsionLevelEquivAlgSchemeKerPoints_map hc a n x
    (G.torsionCoefficientMap hc a n x) rfl
  change (G.torsionLevelEquivUnitKernelPoints hc T' n hn
      (G.torsionCoefficientMap hc a n x)).left =
    Spec.map (CommRingCat.ofHom a.toRingHom) ≫
      (G.torsionLevelEquivUnitKernelPoints hc T n hn x).left at h
  rw [h, Category.assoc]
  rw [← pointHomAlgEquiv_specMap H T X]
  exact (Spec.map_comp
    (CommRingCat.ofHom (G.torsionLevelEquivKernelSections hc T n hn x).toRingHom)
    (CommRingCat.ofHom a.toRingHom)).symm

end GoodReductionJacobian.RelativeGroupLaw
