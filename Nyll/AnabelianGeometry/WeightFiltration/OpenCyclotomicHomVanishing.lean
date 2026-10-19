/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.AnabelianGeometry.WeightFiltration.ScalarExtensionCyclotomicHom
import Mathlib.FieldTheory.KrullTopology

/-!
# Cyclotomic Hom vanishing on every open Galois subgroup

An open subgroup contains the fixing subgroup of a finite intermediate
number field. Apply scalar-extension vanishing without changing the original
roots limit or the original Jacobian point group.
-/

noncomputable section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.RelPicard
open AlgebraicGeometry.SmoothProperCurve NeronModelInfra GoodReductionJacobian ProCGroups
open EtaleFundamentalGroups.Inertia

namespace AnabelianGeometry.WeightFiltration

variable (K Ω : Type) [Field K] [NumberField K]
  [Field Ω] [Algebra K Ω] [IsAlgClosure K Ω]

/-- Actual cyclotomic Hom vanishing remains valid after restricting to any
open subgroup of the original absolute Galois group. -/
theorem numberField_cyclotomicHom_eq_one_of_open_subgroup
    {C : Scheme} (c : C ⟶ Spec (.of K))
    [IsProper c] [SmoothOfRelativeDimension 1 c] [GeometricallyIntegral c]
    (ε : SchemeHomOver (𝟙 (Spec (.of K))) c)
    (D : RelativePic0Designation K c)
    (hD : RepresentsRelSubPic c ε (algEquivZeroCut c ε) D)
    [Smooth D.toBase] [IsProper D.toBase] [GeometricallyConnected D.toBase]
    (H : OpenSubgroup (Ω ≃ₐ[K] Ω)) :
    let G := RepresentsRelSubPic.relativeGroupLaw (P := algEquivZeroGroupCut c ε) hD
    let hc : G.IsCommutative :=
      RepresentsRelSubPic.relativeGroupLaw_isCommutative (P := algEquivZeroGroupCut c ε) hD
    ∀ φ : (primeToRootsSystem Ω Ω).inverseLimit →*
        Multiplicative (FullTateModule (G.AlgPoints hc Ω)),
      (∀ (σ : Ω ≃ₐ[K] Ω), σ ∈ H → ∀ t,
        φ (primeToRootsCoefficientMap Ω Ω σ.toRingHom t) =
          FullTateModule.mapHom
            (RelativeGroupLaw.AlgPoints.map σ.toAlgHom) (φ t)) →
      φ = 1 := by
  intro G hc φ hφ
  have : IsAlgClosed Ω := IsAlgClosure.isAlgClosed K
  obtain ⟨L, hLfin, hLH⟩ :=
    (krullTopology_mem_nhds_one_iff K Ω (H : Set (Ω ≃ₐ[K] Ω))).mp
      (H.isOpen.mem_nhds H.one_mem)
  have : FiniteDimensional K L := hLfin
  have : NumberField L := NumberField.of_module_finite K L
  have : Algebra.IsAlgebraic L Ω := Algebra.IsAlgebraic.tower_top (K := K) L
  have : IsAlgClosure L Ω := ⟨inferInstance, inferInstance⟩
  apply numberField_cyclotomicHom_eq_one_of_scalar_extension K L Ω c ε D hD φ
  intro σ t
  exact hφ (σ.restrictScalars K) (hLH (L.fixingSubgroupEquiv.symm σ).property) t

end AnabelianGeometry.WeightFiltration
