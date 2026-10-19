/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.EtaleFundamentalGroups.FiniteEtale.FiniteField.ConstantFieldTower
import Nyll.EtaleFundamentalGroups.FiniteEtale.FiniteField.ModelOverlap
import Nyll.EtaleFundamentalGroups.GeometricFiber.FundamentalGroup
import Nyll.AlgebraicCurves.Geometry.Curves.SmoothProperCurveBase

/-! # The unchanged coefficient coordinate in recovered covers -/

noncomputable section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.FiniteEtale
open CategoryTheory.PreGaloisCategory EtaleFundamentalGroups
open AlgebraicGeometry.SmoothProperCurve NeronModelInfra

universe u

namespace AnabelianGeometry.WeightFiltration

private theorem recoveredCoefficient_congrHom_hom_fst
    {A B D : Scheme.{u}} {f₁ f₂ : A ⟶ D} {g₁ g₂ : B ⟶ D}
    (hf : f₁ = f₂) (hg : g₁ = g₂) :
    (Limits.pullback.congrHom hf hg).hom ≫ Limits.pullback.fst f₂ g₂ =
      Limits.pullback.fst f₁ g₁ := by
  simp only [Limits.pullback.congrHom_hom, Limits.pullback.lift_fst,
    Category.comp_id]

/-- The actual finite-stage recovery preserves the literal κ coordinate. -/
theorem finiteStageRecovery_coefficientProjection
    (k κ : Type u) [Field k] [Field κ] [Algebra k κ]
    (E : IntermediateField k κ) (X : Scheme.{u}) (f : X ⟶ Spec (.of k))
    (N : FiniteEtale (Limits.pullback (specMap k E) f))
    (W : FiniteEtale (Limits.pullback (specMap k κ) f))
    (R : Limits.pullback (specMap E κ)
      (N.hom ≫ Limits.pullback.fst (specMap k E) f) ≅ W.left)
    (hR : R.hom ≫ W.hom =
      coefficientModelMap (specMap E κ) (Limits.pullback.fst (specMap k E) f) N.hom ≫
        (constantFieldTowerIso k κ E X f).hom) :
    (R.hom ≫ W.hom) ≫ Limits.pullback.fst (specMap k κ) f =
      Limits.pullback.fst (specMap E κ)
        (N.hom ≫ Limits.pullback.fst (specMap k E) f) := by
  let m :=
    coefficientModelMap (specMap E κ) (Limits.pullback.fst (specMap k E) f) N.hom
  let T := constantFieldTowerIso k κ E X f
  have hT : T.hom ≫ Limits.pullback.fst (specMap k κ) f =
      Limits.pullback.fst (specMap E κ) (Limits.pullback.fst (specMap k E) f) :=
    constantFieldTowerIso_hom_fst k κ E X f
  calc
    (R.hom ≫ W.hom) ≫ Limits.pullback.fst (specMap k κ) f =
        (m ≫ T.hom) ≫ Limits.pullback.fst (specMap k κ) f :=
      congrArg (fun t => t ≫ Limits.pullback.fst (specMap k κ) f) hR
    _ = m ≫ (T.hom ≫ Limits.pullback.fst (specMap k κ) f) :=
      Category.assoc _ _ _
    _ = m ≫ Limits.pullback.fst (specMap E κ)
        (Limits.pullback.fst (specMap k E) f) :=
      congrArg (fun t => m ≫ t) hT
    _ = Limits.pullback.fst (specMap E κ)
        (N.hom ≫ Limits.pullback.fst (specMap k E) f) := by
      simp only [m, coefficientModelMap, Limits.pullback.lift_fst]

/-- Changing the displayed structural map by an actual equality preserves
the κ coordinate. In the compactification application, take g₁ = j ≫ c,
g₂ = cN and hg equal to the compactification's structural equation. -/
theorem recoveredCover_congrHom_coefficientProjection
    {A N B S : Scheme.{u}} (φ : A ⟶ B) {g₁ g₂ : N ⟶ B}
    (hg : g₁ = g₂) (W : FiniteEtale S)
    (R : Limits.pullback φ g₂ ≅ W.left) (p : S ⟶ A)
    (hκ : (R.hom ≫ W.hom) ≫ p = Limits.pullback.fst φ g₂) :
    let R' := Limits.pullback.congrHom rfl hg ≪≫ R
    (R'.hom ≫ W.hom) ≫ p = Limits.pullback.fst φ g₁ := by
  intro R'
  let Q : Limits.pullback φ g₁ ≅ Limits.pullback φ g₂ :=
    Limits.pullback.congrHom rfl hg
  calc
    (R'.hom ≫ W.hom) ≫ p = Q.hom ≫ ((R.hom ≫ W.hom) ≫ p) := by
      change ((Q.hom ≫ R.hom) ≫ W.hom) ≫ p = _
      simp only [Category.assoc]
    _ = Q.hom ≫ Limits.pullback.fst φ g₂ :=
      congrArg (fun t => Q.hom ≫ t) hκ
    _ = Limits.pullback.fst φ g₁ :=
      recoveredCoefficient_congrHom_hom_fst rfl hg

/-- The exact tower-and-congruence recovery used by finite refinement
preserves the original κ coordinate. No action or kernel comparison is an
input. In the application, c₀ is the literal map j ≫ c. -/
theorem refinedRecovery_constantSquare
    (E κ : Type u) [Field E] [Field κ] [Algebra E κ]
    (F : IntermediateField E κ)
    {N Y S CF : Scheme.{u}} (c₀ : N ⟶ Spec (.of E))
    (R : Limits.pullback (specMap E κ) c₀ ≅ Y)
    (w : Y ⟶ S) (p : S ⟶ Spec (.of κ))
    (hκ : (R.hom ≫ w) ≫ p = Limits.pullback.fst (specMap E κ) c₀)
    (jF : Limits.pullback (specMap E F) c₀ ⟶ CF)
    (cF : CF ⟶ Spec (.of F))
    (hjF : jF ≫ cF = Limits.pullback.fst (specMap E F) c₀) :
    let RF := Limits.pullback.congrHom rfl hjF ≪≫
      constantFieldTowerIso E κ F N c₀ ≪≫ R
    (RF.hom ≫ w) ≫ p =
      Limits.pullback.fst (specMap F κ) (jF ≫ cF) := by
  intro RF
  let Q : Limits.pullback (specMap F κ) (jF ≫ cF) ≅
      Limits.pullback (specMap F κ) (Limits.pullback.fst (specMap E F) c₀) :=
    Limits.pullback.congrHom rfl hjF
  let T :
      Limits.pullback (specMap F κ) (Limits.pullback.fst (specMap E F) c₀) ≅
        Limits.pullback (specMap E κ) c₀ :=
    constantFieldTowerIso E κ F N c₀
  have hT : T.hom ≫ Limits.pullback.fst (specMap E κ) c₀ =
      Limits.pullback.fst (specMap F κ) (Limits.pullback.fst (specMap E F) c₀) :=
    constantFieldTowerIso_hom_fst E κ F N c₀
  have hQ : Q.hom ≫ Limits.pullback.fst (specMap F κ)
      (Limits.pullback.fst (specMap E F) c₀) =
        Limits.pullback.fst (specMap F κ) (jF ≫ cF) :=
    recoveredCoefficient_congrHom_hom_fst rfl hjF
  have hQT :
      Q.hom ≫ (T.hom ≫ ((R.hom ≫ w) ≫ p)) =
        Limits.pullback.fst (specMap F κ) (jF ≫ cF) := by
    rw [hκ, hT, hQ]
  change ((Q.hom ≫ (T.hom ≫ R.hom)) ≫ w) ≫ p =
    Limits.pullback.fst (specMap F κ) (jF ≫ cF)
  simpa only [Category.assoc] using hQT

/-- The very same recovered point has the very same κ-coordinate. The
point is supplied together with its actual recovery equation; none is chosen. -/
theorem recoveredCover_coefficientPoint
    (κ : Type u) [Field κ] {S Y : Scheme.{u}}
    (p : S ⟶ Spec (.of κ)) (W : FiniteEtale S) (R : Y ≅ W.left)
    (c : Y ⟶ Spec (.of κ)) (hκ : (R.hom ≫ W.hom) ≫ p = c)
    {Ω : Type u} [Field Ω] [IsSepClosed Ω]
    (xi : Spec (.of Ω) ⟶ S) (w : (fiber xi).obj W)
    (x : Spec (.of Ω) ⟶ Y)
    (hxR : x ≫ R.hom = (fiberObjEquivHom xi W w).left) :
    x ≫ c = xi ≫ p := by
  have hgeo : x ≫ (R.hom ≫ W.hom) = xi := by
    calc
      x ≫ (R.hom ≫ W.hom) = (x ≫ R.hom) ≫ W.hom :=
        (Category.assoc _ _ _).symm
      _ = (fiberObjEquivHom xi W w).left ≫ W.hom :=
        congrArg (fun t => t ≫ W.hom) hxR
      _ = xi := (fiberObjEquivHom xi W w).w
  calc
    x ≫ c = x ≫ ((R.hom ≫ W.hom) ≫ p) :=
      congrArg (fun t => x ≫ t) hκ.symm
    _ = (x ≫ (R.hom ≫ W.hom)) ≫ p := (Category.assoc _ _ _).symm
    _ = xi ≫ p := congrArg (fun t => t ≫ p) hgeo

end AnabelianGeometry.WeightFiltration
