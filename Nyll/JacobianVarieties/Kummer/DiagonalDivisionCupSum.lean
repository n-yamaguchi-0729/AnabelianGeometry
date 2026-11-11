/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.AlgebraicCurves.Models.Construction.Basic
public import Nyll.EtaleCohomology.Classical.Adic
public import Nyll.EtaleCohomology.Classical.AdicPullback
public import Nyll.EtaleCohomology.Classical.CupAbelianCechResolution
public import Nyll.EtaleCohomology.Classical.ExternalCupPullbackComposition
public import Nyll.EtaleCohomology.Classical.FiniteCechKernelCup
public import Nyll.EtaleCohomology.Classical.FiniteCechKernelCupRestriction
public import Nyll.EtaleCohomology.Classical.FiniteCechKernelScalar
public import Nyll.EtaleCohomology.Classical.FiniteLevelCup
public import Nyll.EtaleCohomology.Classical.FreeAbelianCechOverlap
public import Nyll.EtaleCohomology.Classical.FreeAbelianYoneda
public import Nyll.EtaleCohomology.Sites.BaseChange
public import Nyll.JacobianVarieties.Kummer.CurveNativeCupPairing
public import Nyll.JacobianVarieties.Kummer.CurveNativeH2Degree
public import Nyll.JacobianVarieties.Kummer.CurveTensorIntegralExpansion
public import Mathlib.Algebra.Homology.DerivedCategory.Ext.Basic

/-!
# The actual finite cup sum on a division overlap

The genuine scalar representatives on the parameter cover are pulled to
the actual product cover. Each cup restricts to its native cup-degree
coefficient times the original first-factor class. The integral tensor
contraction then identifies the whole sum with the denominator times the
original transition class. Both pullbacks and the original Ext maps are
kept throughout this calculation.
-/

@[expose] public section

universe u

noncomputable section

open AlgebraicGeometry CategoryTheory Limits Opposite
open EtaleCohomology EtaleCohomology.Classical

namespace AlgebraicCurve.CurveModel

variable {K F : Type u} [Field K] [IsAlgClosed K] [Field F] [Algebra K F]
  (M : CurveModel K F) (ℓ : ℕ) [Fact ℓ.Prime] (hℓ : IsUnit (ℓ : K))

local notation "HZ" => ellAdicCohomology M.C ℓ 1

/-- On the actual base-changed overlap, the finite sum constructed from
the original integral tensor is the positive denominator times the
original transition class. The scalar hypotheses are the literal
coefficient equations proved by `exists_diagonalDivision_nativeCupKernels`;
the contraction is supplied by the canonical negative identity tensor. -/
theorem diagonalDivisionCupSum_restriction
    (c : ℤ_[ℓ]) (S : Finset (HZ × HZ))
    (hIntegral : ∀ z : HZ, ∑ v ∈ S,
      M.nativeEllAdicCupPairing ℓ hℓ 1 1 rfl z v.2 • v.1 = (-c) • z)
    (n : ℕ) {X : Scheme.{u}} (p₁ p₂ : X ⟶ M.C)
    {T V W : M.C.Etale} (hT : IsTerminal T) (f : V ⟶ T)
    (hf : Sieve.generate (Presieve.singleton f) ∈ M.C.smallEtaleTopology T)
    (x y : W ⟶ V)
    (d : finiteLevelCohomology M.C ℓ n 1 →
      (kernel (abelianCechUnitAugmentation M.C.smallEtaleTopology hT f) ⟶
        (constantSheaf M.C.smallEtaleTopology AddCommGrpCat.{u}).obj (ellPowerCoefficients ℓ n)))
    (δ : finiteLevelCohomology M.C ℓ n 1) :
    let B := etaleBaseChange p₂
    let hB := hT.isTerminalObj B T
    let fB := B.map f
    let l := pullback.lift x y (hT.hom_ext (x ≫ f) (y ≫ f))
    let lB := pullback.lift (B.map x) (B.map y)
      (hB.hom_ext (B.map x ≫ fB) (B.map y ≫ fB))
    let edge := (freeAbelianSheafYoneda M.C.smallEtaleTopology).map l ≫
      (freeCechEdgeSheafIso M.C.smallEtaleTopology f).inv ≫
        abelianCechFirstRelationMap M.C.smallEtaleTopology hT f
    let edgeB := (freeAbelianSheafYoneda X.smallEtaleTopology).map lB ≫
      (freeCechEdgeSheafIso X.smallEtaleTopology fB).inv ≫
        abelianCechFirstRelationMap X.smallEtaleTopology hB fB
    (∀ v ∈ S,
      freeAbelianSheafYonedaHomEquiv M.C.smallEtaleTopology W _
          (edge ≫ d (ellAdicProjection M.C ℓ 1 n v.2)) =
        (toSheafify M.C.smallEtaleTopology
          ((Functor.const M.C.Etaleᵒᵖ).obj (ellPowerCoefficients ℓ n))).app (op W)
            (ULift.up (M.nativeFiniteLevelH2DegreeEquiv ℓ hℓ n
              (finiteLevelCup M.C ℓ n 1 1 2 rfl
                (ellAdicProjection M.C ℓ 1 n v.2) δ)))) →
      finiteLevelCohomologyPresheafRestriction X ℓ n (B.obj W) 1
        ((Abelian.Ext.mk₀ edgeB).comp
          (∑ v ∈ S, finiteCechKernelCupClass X ℓ n hB fB
            (finiteCechKernelPullback p₂ ℓ n hT f hf
              (d (ellAdicProjection M.C ℓ 1 n v.2)))
            (finiteLevelCohomologyPullback ℓ p₁ n 1
              (ellAdicProjection M.C ℓ 1 n v.1))) (zero_add 1)) =
        c • finiteLevelCohomologyPullback ℓ ((B.obj W).hom ≫ p₁) n 1 δ := by
  intro B hB fB l lB edge edgeB hscalar
  classical
  have : NeZero (ℓ ^ (n + 1)) := ⟨pow_ne_zero _ (Fact.out : ℓ.Prime).ne_zero⟩
  let A := (constantSheaf X.smallEtaleTopology AddCommGrpCat.{u}).obj (ellPowerCoefficients ℓ n)
  let Φ : Abelian.Ext.{u} (kernel (abelianCechUnitAugmentation X.smallEtaleTopology hB fB)) A 1 →+
      finiteLevelCohomology (B.obj W).left ℓ n 1 :=
    (finiteLevelCohomologyPresheafRestriction X ℓ n (B.obj W) 1).comp
      ((Abelian.Ext.mk₀ edgeB).precomp A (zero_add 1))
  let P := finiteLevelCohomologyPullback ℓ ((B.obj W).hom ≫ p₁) n 1
  let r (v : HZ × HZ) := (M.nativeFiniteLevelH2DegreeEquiv ℓ hℓ n
    (finiteLevelCup M.C ℓ n 1 1 2 rfl (ellAdicProjection M.C ℓ 1 n v.2) δ)).val
  have hterm (v : HZ × HZ) (hv : v ∈ S) :
      Φ (finiteCechKernelCupClass X ℓ n hB fB
        (finiteCechKernelPullback p₂ ℓ n hT f hf
          (d (ellAdicProjection M.C ℓ 1 n v.2)))
        (finiteLevelCohomologyPullback ℓ p₁ n 1
          (ellAdicProjection M.C ℓ 1 n v.1))) =
        P (r v • ellAdicProjection M.C ℓ 1 n v.1) := by
    have hmap := finiteCechKernelPullback_overlap_eq_nsmul p₂ ℓ n hT f hf x y
      (d (ellAdicProjection M.C ℓ 1 n v.2))
      (ULift.up (M.nativeFiniteLevelH2DegreeEquiv ℓ hℓ n
        (finiteLevelCup M.C ℓ n 1 1 2 rfl
          (ellAdicProjection M.C ℓ 1 n v.2) δ))) (hscalar v hv)
    have hres := finiteCechKernelCupClass_restriction X ℓ n hB fB
      (B.obj W) (B.map x ≫ fB) edgeB
      (finiteCechKernelPullback p₂ ℓ n hT f hf
        (d (ellAdicProjection M.C ℓ 1 n v.2))) (r v) hmap
      (finiteLevelCohomologyPullback ℓ p₁ n 1 (ellAdicProjection M.C ℓ 1 n v.1))
    rw [← LinearMap.comp_apply, ← finiteLevelCohomologyPullback_comp] at hres
    exact hres.trans (map_nsmul P (r v) (ellAdicProjection M.C ℓ 1 n v.1)).symm
  change Φ (∑ v ∈ S, finiteCechKernelCupClass X ℓ n hB fB
    (finiteCechKernelPullback p₂ ℓ n hT f hf
      (d (ellAdicProjection M.C ℓ 1 n v.2)))
    (finiteLevelCohomologyPullback ℓ p₁ n 1
      (ellAdicProjection M.C ℓ 1 n v.1))) = c • P δ
  rw [map_sum]
  calc
    (∑ v ∈ S, Φ (finiteCechKernelCupClass X ℓ n hB fB
        (finiteCechKernelPullback p₂ ℓ n hT f hf
          (d (ellAdicProjection M.C ℓ 1 n v.2)))
        (finiteLevelCohomologyPullback ℓ p₁ n 1
          (ellAdicProjection M.C ℓ 1 n v.1)))) =
        ∑ v ∈ S, P (r v • ellAdicProjection M.C ℓ 1 n v.1) :=
      Finset.sum_congr rfl hterm
    _ = P (∑ v ∈ S, r v • ellAdicProjection M.C ℓ 1 n v.1) :=
      (map_sum P (fun v : HZ × HZ => r v • ellAdicProjection M.C ℓ 1 n v.1) S).symm
    _ = P (c • δ) := congrArg P
      (M.nativeFiniteCup_reversed_integral_contraction ℓ hℓ c S hIntegral n δ)
    _ = c • P δ := P.map_smul c δ

end AlgebraicCurve.CurveModel
