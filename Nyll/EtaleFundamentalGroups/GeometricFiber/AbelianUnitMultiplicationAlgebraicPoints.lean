/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.SchemeTheory.GroupSchemes.RelativeGroupLaw.AlgebraicPoints
public import Nyll.AlgebraicCurves.Geometry.AbelianSchemes.Theorems.RelativeGroupLawSchemeNsmulCompEqCompSchemeNsmul
public import Nyll.EtaleFundamentalGroups.GeometricFiber.AbelianMultiplicationTranslations
public import Nyll.EtaleFundamentalGroups.GeometricFiber.AbelianUnitMonodromy
public import Nyll.EtaleFundamentalGroups.GeometricFiber.AbelianUnitMultiplicationCover
public import Nyll.EtaleFundamentalGroups.GeometricFiber.AbelianUnitTorsionFiber
public import Nyll.EtaleFundamentalGroups.GeometricFiber.FieldMonodromyLift
public import Nyll.EtaleFundamentalGroups.GeometricFiber.FundamentalGroup
public import Nyll.EtaleFundamentalGroups.GaloisCategories.Functoriality
public import Nyll.ProCGroups.Abelian.FullTateModule
public import Mathlib.Algebra.Algebra.Hom
public import Nyll.SchemeTheory.CategoryTheory.SchemeHomOver

/-!
# Displacement of actual division points at invertible indices

The same multiplication cover supplies division points over any geometric
basepoint. Naturality of the path to the origin identifies monodromy with
the original deck translation. The actual field action on the original
geometric lift then computes its displacement, in arbitrary characteristic.
-/

@[expose] public section

universe u

noncomputable section

open CategoryTheory CategoryTheory.PreGaloisCategory AlgebraicGeometry NeronModelInfra
open AlgebraicCurves.Geometry.AbelianSchemes.Theorems.Proofs
open RelativeGroupLaw_schemeNsmul_comp_eq_comp_schemeNsmul_of_hom.S17Glue

namespace GoodReductionJacobian.RelativeGroupLaw.UnitMultiplication

variable {K : Type u} [Field K] {A : Scheme.{u}} {f : A ⟶ Spec (.of K)}
  [IsProper f] [Smooth f] (G : RelativeGroupLaw K f) (hc : G.IsCommutative)
  {Ω : Type u} [Field Ω] [IsSepClosed Ω] [Algebra K Ω]

/-- The original point of an allowed multiplication fibre, in the
additive group of algebraic points over its actual geometric field. -/
def fiberAlgPoint
    (ξ : SchemeHomOver (Spec.map (CommRingCat.ofHom (algebraMap K Ω))) f)
    (n : unitIndices K) (z : (FiniteEtale.fiber ξ.1).obj (cover G hc n)) :
    G.AlgPoints hc Ω := by
  have : IsFiniteEtale (G.schemeNsmul (n.1 : ℕ)) :=
    G.isFiniteEtale_schemeNsmul_of_isUnit hc (n.1 : ℕ) n.2
  let q := G.multiplicationFiberPointOfFiniteEtale ξ.1 (n.1 : ℕ) z
  exact AlgPoints.ofPoint ⟨q.1, q.2.trans ξ.2⟩

/-- The original multiplication-fibre point satisfies its division equation. -/
theorem nsmul_fiberAlgPoint
    (ξ : SchemeHomOver (Spec.map (CommRingCat.ofHom (algebraMap K Ω))) f)
    (n : unitIndices K) (z : (FiniteEtale.fiber ξ.1).obj (cover G hc n)) :
    (n.1 : ℕ) • fiberAlgPoint G hc ξ n z = AlgPoints.ofPoint ξ := by
  apply AlgPoints.toPoint_injective
  apply Subtype.ext
  rw [AlgPoints.toPoint_nsmul, nsmul_coe_eq_comp_schemeNsmul]
  exact Over.w (FiniteEtale.fiberObjEquivHom ξ.1 (cover G hc n) z)

variable [IsSepClosed K]

omit [IsSepClosed Ω] [Algebra K Ω] in
/-- Transport to the origin identifies the actual fibre action with the
deck translation by the same actual torsion point. -/
theorem fiber_smul_eq_translation
    (ξ : Spec (.of Ω) ⟶ A) (n : unitIndices K)
    (τ : FiniteEtale.fiber ξ ≅ FiniteEtale.fiber (G.one (𝟙 (Spec (.of K)))).1)
    (g : π₁ᵉᵗ(ξ)) (z : (FiniteEtale.fiber ξ).obj (cover G hc n)) :
    g • z = (FiniteEtale.fiber ξ).map
      (torsionDeckTranslation G hc n (monodromy G hc n (continuousConjAut τ g))).asIso.hom z := by
  let W := cover G hc n
  let t := monodromy G hc n (continuousConjAut τ g)
  let d := torsionDeckTranslation G hc n t
  have hτinj : Function.Injective (τ.hom.app W) := by
    intro x y h
    exact (FintypeCat.hom_inv_id_apply (τ.app W) x).symm.trans
      ((congrArg (τ.inv.app W) h).trans (FintypeCat.hom_inv_id_apply (τ.app W) y))
  apply hτinj
  apply (fiberEquivTorsion G hc n).injective
  have hτg : τ.hom.app W (g • z) =
      (continuousConjAut τ g) • τ.hom.app W z := by
    change τ.hom.app W (g.asIso.hom.app W z) =
      τ.hom.app W (g.asIso.hom.app W (τ.inv.app W (τ.hom.app W z)))
    exact (congrArg (fun w => τ.hom.app W (g.asIso.hom.app W w))
      (FintypeCat.hom_inv_id_apply (τ.app W) z)).symm
  have hτd : τ.hom.app W ((FiniteEtale.fiber ξ).map d.asIso.hom z) =
      (FiniteEtale.fiber (G.one (𝟙 (Spec (.of K)))).1).map d.asIso.hom (τ.hom.app W z) :=
    ConcreteCategory.congr_hom (τ.hom.naturality d.asIso.hom) z
  rw [hτg, hτd, fiberEquivTorsion_smul G hc n,
    fiberEquiv_map_torsionDeckTranslation G hc n]
  exact add_comm _ _

omit [IsSepClosed K] in
/-- On actual algebraic points, the deck translation adds its original
torsion point after extension of the constants. -/
theorem fiberAlgPoint_map_translation
    (ξ : SchemeHomOver (Spec.map (CommRingCat.ofHom (algebraMap K Ω))) f)
    (n : unitIndices K) (t : ProCGroups.torsionLevel (G.AlgPoints hc K) n.1)
    (z : (FiniteEtale.fiber ξ.1).obj (cover G hc n)) :
    fiberAlgPoint G hc ξ n
        ((FiniteEtale.fiber ξ.1).map (torsionDeckTranslation G hc n t).asIso.hom z) =
      fiberAlgPoint G hc ξ n z + AlgPoints.map (Algebra.ofId K Ω) t.1 := by
  let s := Spec.map (CommRingCat.ofHom (algebraMap K Ω))
  let q := AlgPoints.toPoint (fiberAlgPoint G hc ξ n z)
  let u := torsionPointSection G hc n t
  have hu : GoodReductionJacobian.schemeHomOverComp s (Category.comp_id s) u =
      AlgPoints.toPoint (AlgPoints.map (Algebra.ofId K Ω) t.1) := by
    apply Subtype.ext
    change s ≫ (AlgPoints.toPoint t.1).1 = _
    exact (AlgPoints.toPoint_map_coe (L := G) (hc := hc)
      (Algebra.ofId K Ω) t.1).symm
  apply AlgPoints.toPoint_injective
  apply Subtype.ext
  rw [AlgPoints.toPoint_add]
  have h := FiniteEtale.fiberObjEquivHom_naturality ξ.1
    (torsionDeckTranslation G hc n t).asIso.hom z
  have hleft := congrArg
    (fun r : Over.mk ξ.1 ⟶ (cover G hc n).toComma => r.left) h.symm
  change _ = (G.mul s q (AlgPoints.toPoint (AlgPoints.map (Algebra.ofId K Ω) t.1))).1
  exact hleft.trans ((G.point_comp_translate s q u).trans
    (congrArg (fun p : SchemeHomOver s f => (G.mul s q p).1) hu))

/-- The same geometric division point is translated by its actual
monodromy coordinate after transport to the origin. -/
theorem fiberAlgPoint_smul
    (ξ : SchemeHomOver (Spec.map (CommRingCat.ofHom (algebraMap K Ω))) f)
    (n : unitIndices K)
    (τ : FiniteEtale.fiber ξ.1 ≅ FiniteEtale.fiber (G.one (𝟙 (Spec (.of K)))).1)
    (g : π₁ᵉᵗ(ξ.1)) (z : (FiniteEtale.fiber ξ.1).obj (cover G hc n)) :
    fiberAlgPoint G hc ξ n (g • z) =
      fiberAlgPoint G hc ξ n z +
        AlgPoints.map (Algebra.ofId K Ω) (monodromy G hc n (continuousConjAut τ g)).1 := by
  rw [fiber_smul_eq_translation G hc ξ.1 n τ g z]
  exact fiberAlgPoint_map_translation G hc ξ n _ z

variable {L : Type u} [Field L] [Algebra K L] [Algebra L Ω] [IsScalarTower K L Ω]

omit [IsSepClosed K] in
/-- Coefficient automorphisms act on the same original division point
as the induced automorphism of the geometric fibre. -/
theorem fiberAlgPoint_field_smul
    (j : SchemeHomOver (Spec.map (CommRingCat.ofHom (algebraMap K L))) f)
    (n : unitIndices K) (σ : Ω ≃ₐ[L] Ω)
    (z : (FiniteEtale.fiber
      (Spec.map (CommRingCat.ofHom (algebraMap L Ω)) ≫ j.1)).obj (cover G hc n)) :
    let ξ := AlgPoints.mapPoint (IsScalarTower.toAlgHom K L Ω) j
    let η := Spec.map (CommRingCat.ofHom (algebraMap L Ω))
    let g := FiniteEtale.fundamentalGroupHom j.1 η
      (toAut (FiniteEtale.fiber η) (Ω ≃ₐ[L] Ω) σ)
    (σ.restrictScalars K) • fiberAlgPoint G hc ξ n z =
      fiberAlgPoint G hc ξ n (g • z) := by
  intro ξ η g
  apply AlgPoints.toPoint_injective
  apply Subtype.ext
  exact (FiniteEtale.fundamentalGroupHom_field_fiberLift j.1 (cover G hc n) σ z).symm

/-- The field Galois displacement of the original division point is
the base extension of the original allowed multiplication monodromy. -/
theorem fiberAlgPoint_field_displacement
    (j : SchemeHomOver (Spec.map (CommRingCat.ofHom (algebraMap K L))) f)
    (n : unitIndices K)
    (τ : FiniteEtale.fiber
        (Spec.map (CommRingCat.ofHom (algebraMap L Ω)) ≫ j.1) ≅
      FiniteEtale.fiber (G.one (𝟙 (Spec (.of K)))).1)
    (σ : Ω ≃ₐ[L] Ω)
    (z : (FiniteEtale.fiber
      (Spec.map (CommRingCat.ofHom (algebraMap L Ω)) ≫ j.1)).obj (cover G hc n)) :
    let ξ := AlgPoints.mapPoint (IsScalarTower.toAlgHom K L Ω) j
    let η := Spec.map (CommRingCat.ofHom (algebraMap L Ω))
    let g := FiniteEtale.fundamentalGroupHom j.1 η
      (toAut (FiniteEtale.fiber η) (Ω ≃ₐ[L] Ω) σ)
    (σ.restrictScalars K) • fiberAlgPoint G hc ξ n z - fiberAlgPoint G hc ξ n z =
      AlgPoints.map (Algebra.ofId K Ω)
        (monodromy G hc n (continuousConjAut τ g)).1 := by
  intro ξ η g
  exact (congrArg
    (fun w : G.AlgPoints hc Ω => w - fiberAlgPoint G hc ξ n z)
    (fiberAlgPoint_field_smul G hc j n σ z)).trans
      ((congrArg
        (fun w : G.AlgPoints hc Ω => w - fiberAlgPoint G hc ξ n z)
        (fiberAlgPoint_smul G hc ξ n τ g z)).trans (add_sub_cancel_left _ _))

end GoodReductionJacobian.RelativeGroupLaw.UnitMultiplication
