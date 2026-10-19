/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.AnabelianGeometry.WeightFiltration.GenericSourceIso
import Nyll.EtaleFundamentalGroups.GeometricFiber.CoefficientBaseChangeIso
import Nyll.EtaleFundamentalGroups.GeometricFiber.SourceIsoGalois
import Nyll.EtaleFundamentalGroups.GeometricFiber.GeometricGaloisSourceDuality

/-!
# Actual coefficient Galois action and generic H¹ duality

Every coefficient automorphism acts on the literal base change and lifts to
the supplied generic separable closure. The original arithmetic comparison
contributes one fixed inner correction for all Galois elements.
-/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.FiniteEtale
open EtaleFundamentalGroups.Cohomology EtaleCohomology.Classical

namespace AnabelianGeometry.WeightFiltration

local instance torsionTopology (S : Scheme.{u}) :
    TopologicalSpace (Multiplicative (finiteTorsionCohomology S 1)) := ⊥

/-- Every actual coefficient automorphism has a generic source lift, with one
fixed arithmetic base-point correction valid for all coefficient elements. -/
theorem exists_genericCoefficient_sourceAction
    (k L : Type u) [Field k] [Field L] [Algebra k L] [IsSepClosure k L]
    (X : Scheme.{u}) [CompactSpace X] [QuasiSeparatedSpace X]
    (f : X ⟶ Spec (.of k))
    [IsIntegral (Limits.pullback (Spec.map (CommRingCat.ofHom (algebraMap k L))) f)]
    (Ω : Type u) [Field Ω] [IsSepClosed Ω]
    [Algebra (Limits.pullback (Spec.map (CommRingCat.ofHom (algebraMap k L))) f).functionField Ω]
    [IsSepClosure
      (Limits.pullback (Spec.map (CommRingCat.ofHom (algebraMap k L))) f).functionField Ω]
    (xi : Spec (.of Ω) ⟶ Limits.pullback (Spec.map (CommRingCat.ofHom (algebraMap k L))) f)
    (hxi : xi =
      Spec.map (CommRingCat.ofHom (algebraMap
        (Limits.pullback (Spec.map (CommRingCat.ofHom (algebraMap k L))) f).functionField Ω)) ≫
      (Limits.pullback (Spec.map (CommRingCat.ofHom (algebraMap k L))) f).fromSpecStalk
        (genericPoint
          (Limits.pullback (Spec.map (CommRingCat.ofHom (algebraMap k L))) f : Scheme.{u}))) :
    ∃ α : Gal(L/k), ∀ σ : Gal(L/k),
      ∃ (a : Ω ≃+* Ω)
        (_ha : ∀ z :
          (Limits.pullback (Spec.map (CommRingCat.ofHom (algebraMap k L))) f).functionField,
          a (algebraMap _ Ω z) = algebraMap _ Ω
            ((coefficientBaseChangeIso k L f σ).hom.functionFieldRingEquivOfIsOpenImmersion z))
        (hpoint : Spec.map (CommRingCat.ofHom a.toRingHom) ≫ xi =
          xi ≫ (coefficientBaseChangeIso k L f σ).hom),
        let e := Scheme.Spec.mapIso a.toCommRingCatIso.op
        let p := Limits.pullback.snd (Spec.map (CommRingCat.ofHom (algebraMap k L))) f
        let hz : e.hom ≫ (xi ≫ p) = xi ≫ p := by
          have hp : e.hom ≫ xi = xi ≫ (coefficientBaseChangeIso k L f σ).hom := hpoint
          rw [← Category.assoc, hp, Category.assoc, coefficientBaseChangeIso_hom_snd]
        arithmeticFundamentalGroupHom k L f (xi ≫ p)
            (fiberSourceIso (xi ≫ p) e ≪≫ eqToIso (congrArg fiber hz)) =
          α * σ * α⁻¹ := by
  let φ := Spec.map (CommRingCat.ofHom (algebraMap k L))
  let c := Limits.pullback.fst φ f
  let p := Limits.pullback.snd φ f
  let ι : L →+* Ω := (Spec.preimage (xi ≫ c)).hom
  let : Algebra L Ω := ι.toAlgebra
  let : Algebra k Ω := (ι.comp (algebraMap k L)).toAlgebra
  let : IsScalarTower k L Ω := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  have hL : xi ≫ c = ξ L Ω := (Spec.map_preimage (xi ≫ c)).symm
  have hbase : (xi ≫ p) ≫ f = ξ k Ω := by
    calc
      (xi ≫ p) ≫ f = (xi ≫ c) ≫ φ := by
        simp only [p, c, Category.assoc, Limits.pullback.condition]
      _ = ξ L Ω ≫ φ := congrArg (fun z => z ≫ φ) hL
      _ = ξ k Ω := by
        change Spec.map (CommRingCat.ofHom (algebraMap L Ω)) ≫
          Spec.map (CommRingCat.ofHom (algebraMap k L)) =
            Spec.map (CommRingCat.ofHom (algebraMap k Ω))
        rw [← Spec.map_comp]
        rfl
  obtain ⟨α, hα⟩ := arithmeticFundamentalGroupHom_sourceAction k L Ω f (xi ≫ p) hbase
  refine ⟨α, ?_⟩
  intro σ
  let θ := coefficientBaseChangeIso k L f σ
  obtain ⟨a, ha, hpoint₀⟩ := exists_genericPoint_sourceIso θ Ω
  let e := Scheme.Spec.mapIso a.toCommRingCatIso.op
  have hpoint : e.hom ≫ xi = xi ≫ θ.hom := by
    change Spec.map (CommRingCat.ofHom a.toRingHom) ≫ xi = xi ≫ θ.hom
    rw [hxi]
    exact hpoint₀
  refine ⟨a, ha, hpoint, ?_⟩
  have hz : e.hom ≫ (xi ≫ p) = xi ≫ p := by
    rw [← Category.assoc, hpoint, Category.assoc, coefficientBaseChangeIso_hom_snd]
  have hρspec : Spec.map (CommRingCat.ofHom (a.toRingHom.comp (algebraMap L Ω))) =
      Spec.map (CommRingCat.ofHom ((algebraMap L Ω).comp σ.toRingHom)) := by
    change Spec.map (CommRingCat.ofHom (algebraMap L Ω) ≫ CommRingCat.ofHom a.toRingHom) =
      Spec.map (CommRingCat.ofHom σ.toRingHom ≫ CommRingCat.ofHom (algebraMap L Ω))
    rw [Spec.map_comp, Spec.map_comp]
    change e.hom ≫ ξ L Ω = ξ L Ω ≫ Spec.map (CommRingCat.ofHom σ.toRingHom)
    rw [← hL, ← Category.assoc, hpoint, Category.assoc, coefficientBaseChangeIso_hom_fst]
    exact (Category.assoc _ _ _).symm
  have hρ : a.toRingHom.comp (algebraMap L Ω) =
      (algebraMap L Ω).comp σ.toRingHom :=
    congrArg (fun m => m.hom) (Spec.map_injective hρspec)
  exact hα e a.toRingHom rfl σ hρ hz

/-- At the actual generic geometric point, existing H¹ duality intertwines
all coefficient pullbacks and arithmetic Galois actions, with one fixed
base-point correction and no assumed source lift. -/
theorem exists_genericCoefficient_duality
    (k L : Type u) [Field k] [Field L] [Algebra k L] [IsSepClosure k L]
    (X : Scheme.{u}) [CompactSpace X] [QuasiSeparatedSpace X]
    (f : X ⟶ Spec (.of k))
    [IsIntegral (Limits.pullback (Spec.map (CommRingCat.ofHom (algebraMap k L))) f)]
    (Ω : Type u) [Field Ω] [IsSepClosed Ω]
    [Algebra (Limits.pullback (Spec.map (CommRingCat.ofHom (algebraMap k L))) f).functionField Ω]
    [IsSepClosure
      (Limits.pullback (Spec.map (CommRingCat.ofHom (algebraMap k L))) f).functionField Ω]
    (xi : Spec (.of Ω) ⟶ Limits.pullback (Spec.map (CommRingCat.ofHom (algebraMap k L))) f)
    (hxi : xi =
      Spec.map (CommRingCat.ofHom (algebraMap
        (Limits.pullback (Spec.map (CommRingCat.ofHom (algebraMap k L))) f).functionField Ω)) ≫
      (Limits.pullback (Spec.map (CommRingCat.ofHom (algebraMap k L))) f).fromSpecStalk
        (genericPoint
          (Limits.pullback (Spec.map (CommRingCat.ofHom (algebraMap k L))) f : Scheme.{u}))) :
    ∃ α : Gal(L/k), ∀ (σ : Gal(L/k)) (x : TopologicalAbelianization (Aut (fiber xi))),
      abelianizationFiniteTorsionH1DualEquiv xi
          (geometricAbelianGaloisAction k L X f xi (α * σ⁻¹ * α⁻¹) x) =
        (abelianizationFiniteTorsionH1DualEquiv xi x).comp
          (finiteTorsionH1PullbackHom (coefficientBaseChangeIso k L f σ).hom) := by
  obtain ⟨α, hα⟩ := exists_genericCoefficient_sourceAction k L X f Ω xi hxi
  refine ⟨α, ?_⟩
  intro σ x
  obtain ⟨a, _, hpoint, hlabel⟩ := hα σ
  let e := Scheme.Spec.mapIso a.toCommRingCatIso.op
  let θ := coefficientBaseChangeIso k L f σ
  let p := Limits.pullback.snd (Spec.map (CommRingCat.ofHom (algebraMap k L))) f
  have hz : e.hom ≫ (xi ≫ p) = xi ≫ p := by
    have hp : e.hom ≫ xi = xi ≫ θ.hom := hpoint
    rw [← Category.assoc, hp, Category.assoc, coefficientBaseChangeIso_hom_snd]
  let g : Aut (fiber (xi ≫ p)) :=
    fiberSourceIso (xi ≫ p) e ≪≫ eqToIso (congrArg fiber hz)
  change arithmeticFundamentalGroupHom k L f (xi ≫ p) g = α * σ * α⁻¹ at hlabel
  have hinv : arithmeticFundamentalGroupHom k L f (xi ≫ p) g⁻¹ =
      α * σ⁻¹ * α⁻¹ := by
    rw [map_inv, hlabel]
    simp only [mul_inv_rev, inv_inv, mul_assoc]
  have hd := geometricAbelianGaloisAction_source_duality k L X f xi e θ.hom
    (coefficientBaseChangeIso_hom_snd k L f σ) hpoint x
  change abelianizationFiniteTorsionH1DualEquiv xi
      (geometricAbelianGaloisAction k L X f xi
        (arithmeticFundamentalGroupHom k L f (xi ≫ p) g⁻¹) x) = _ at hd
  rw [hinv] at hd
  exact hd

end AnabelianGeometry.WeightFiltration
