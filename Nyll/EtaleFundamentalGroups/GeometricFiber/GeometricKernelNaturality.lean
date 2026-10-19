/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.EtaleFundamentalGroups.GeometricFiber.GeometricAbelianGaloisAction
import Nyll.EtaleFundamentalGroups.GeometricFiber.ArithmeticKernelNaturality
import Nyll.EtaleFundamentalGroups.GeometricFiber.CanonicalPointedMaps
import Nyll.EtaleFundamentalGroups.FiniteEtale.FiniteField.ModelOverlap

/-!
# Naturality of the actual geometric-kernel comparison

The literal coefficient base-change map gives the same map as restriction
to the arithmetic kernels. Canonical pointed maps handle the single equality
of target geometric points, without introducing a new comparison choice.
-/

noncomputable section

universe u

open CategoryTheory Limits
open ProCGroups.Abelian

namespace AlgebraicGeometry.FiniteEtale

private theorem geometricKernelEquiv_transport_apply
    (k L : Type u) [Field k] [Field L] [Algebra k L] [IsSepClosure k L]
    (X : Scheme.{u}) [CompactSpace X] [QuasiSeparatedSpace X]
    (f : X ⟶ Spec (.of k))
    [ConnectedSpace ↑(Limits.pullback (Spec.map (CommRingCat.ofHom (algebraMap k L))) f)]
    {Ω : Type u} [Field Ω] [IsSepClosed Ω]
    (xi : Spec (.of Ω) ⟶ Limits.pullback (Spec.map (CommRingCat.ofHom (algebraMap k L))) f)
    (z : Spec (.of Ω) ⟶ X) (h : xi ≫ Limits.pullback.snd _ f = z)
    (g : Aut (fiber xi)) :
    let e : Aut (fiber xi) ≃ₜ* (arithmeticFundamentalGroupHom k L f z).toMonoidHom.ker :=
      h ▸ geometricFundamentalGroupKernelEquiv k L X f xi
    (e g : Aut (fiber z)) =
      pointedFundamentalGroupHom (Limits.pullback.snd _ f) xi z h g := by
  subst z
  rfl

private theorem geometricAbelianGaloisAction_transport_lift
    (k L : Type u) [Field k] [Field L] [Algebra k L] [IsSepClosure k L]
    (X : Scheme.{u}) [CompactSpace X] [QuasiSeparatedSpace X]
    (f : X ⟶ Spec (.of k))
    [ConnectedSpace ↑(Limits.pullback (Spec.map (CommRingCat.ofHom (algebraMap k L))) f)]
    {Ω : Type u} [Field Ω] [IsSepClosed Ω]
    (xi : Spec (.of Ω) ⟶ Limits.pullback (Spec.map (CommRingCat.ofHom (algebraMap k L))) f)
    (z : Spec (.of Ω) ⟶ X) (h : xi ≫ Limits.pullback.snd _ f = z)
    (g : Aut (fiber z)) (x : TopologicalAbelianization (Aut (fiber xi))) :
    let e₀ : Aut (fiber xi) ≃ₜ* (arithmeticFundamentalGroupHom k L f z).toMonoidHom.ker :=
      h ▸ geometricFundamentalGroupKernelEquiv k L X f xi
    let e := TopologicalAbelianization.congr e₀
    e (geometricAbelianGaloisAction k L X f xi
        (arithmeticFundamentalGroupHom k L f z g) x) =
      conjugationTopologicalAbelianizationContinuousAut
        (arithmeticFundamentalGroupHom k L f z).toMonoidHom.ker g (e x) := by
  subst z
  intro e₀ e
  rw [geometricAbelianGaloisAction_lift_apply]
  exact e.apply_symm_apply _

variable
    (k L : Type u) [Field k] [Field L] [Algebra k L] [IsSepClosure k L]
    {X Y : Scheme.{u}} [CompactSpace X] [QuasiSeparatedSpace X]
    [CompactSpace Y] [QuasiSeparatedSpace Y]
    (j : X ⟶ Y) (f : Y ⟶ Spec (.of k))
    [ConnectedSpace ↑(Limits.pullback (Spec.map (CommRingCat.ofHom (algebraMap k L))) (j ≫ f))]
    [ConnectedSpace ↑(Limits.pullback (Spec.map (CommRingCat.ofHom (algebraMap k L))) f)]
    {Ω : Type u} [Field Ω] [IsSepClosed Ω]
    (xi : Spec (.of Ω) ⟶
      Limits.pullback (Spec.map (CommRingCat.ofHom (algebraMap k L))) (j ≫ f))

/-- The actual base-change map agrees with the map on the original arithmetic kernels. -/
theorem geometricFundamentalGroupKernelEquiv_naturality :
    let φ := Spec.map (CommRingCat.ofHom (algebraMap k L))
    let c := EtaleFundamentalGroups.coefficientModelMap φ f j
    let z := (xi ≫ Limits.pullback.snd φ (j ≫ f)) ≫ j
    let h : (xi ≫ c) ≫ Limits.pullback.snd φ f = z := by
      simp only [z, c, Category.assoc, EtaleFundamentalGroups.coefficientModelMap,
        Limits.pullback.lift_snd]
    let eX := geometricFundamentalGroupKernelEquiv k L X (j ≫ f) xi
    let eY : Aut (fiber (xi ≫ c)) ≃ₜ*
        (arithmeticFundamentalGroupHom k L f z).toMonoidHom.ker :=
      h ▸ geometricFundamentalGroupKernelEquiv k L Y f (xi ≫ c)
    (ContinuousMonoidHom.toContinuousMonoidHom eY).comp (fundamentalGroupHom c xi) =
      (arithmeticKernelHom k L j f (xi ≫ Limits.pullback.snd φ (j ≫ f))).comp
        (ContinuousMonoidHom.toContinuousMonoidHom eX) := by
  intro φ c z h eX eY
  apply ContinuousMonoidHom.ext
  intro g
  apply Subtype.ext
  change (eY (fundamentalGroupHom c xi g) : Aut (fiber z)) =
    fundamentalGroupHom j (xi ≫ Limits.pullback.snd φ (j ≫ f))
      (fundamentalGroupHom (Limits.pullback.snd φ (j ≫ f)) xi g)
  rw [geometricKernelEquiv_transport_apply k L Y f (xi ≫ c) z h]
  change ((pointedFundamentalGroupHom (Limits.pullback.snd φ f) (xi ≫ c) z h).comp
      (pointedFundamentalGroupHom c xi (xi ≫ c) rfl)) g =
    ((pointedFundamentalGroupHom j (xi ≫ Limits.pullback.snd φ (j ≫ f)) z rfl).comp
      (pointedFundamentalGroupHom (Limits.pullback.snd φ (j ≫ f)) xi
        (xi ≫ Limits.pullback.snd φ (j ≫ f)) rfl)) g
  have hm : c ≫ Limits.pullback.snd φ f = Limits.pullback.snd φ (j ≫ f) ≫ j := by
    exact Limits.pullback.lift_snd _ _ _
  rw [pointedFundamentalGroupHom_comp, pointedFundamentalGroupHom_comp]
  simp only [hm]

/-- The actual geometric base-change map commutes with the original Galois actions. -/
theorem geometricAbelianGaloisAction_baseChange_map
    (σ : L ≃ₐ[k] L) (x : TopologicalAbelianization (Aut (fiber xi))) :
    let φ := Spec.map (CommRingCat.ofHom (algebraMap k L))
    let c := EtaleFundamentalGroups.coefficientModelMap φ f j
    TopologicalAbelianization.map (fundamentalGroupHom c xi)
        (geometricAbelianGaloisAction k L X (j ≫ f) xi σ x) =
      geometricAbelianGaloisAction k L Y f (xi ≫ c) σ
        (TopologicalAbelianization.map (fundamentalGroupHom c xi) x) := by
  intro φ c
  let z := (xi ≫ Limits.pullback.snd φ (j ≫ f)) ≫ j
  have hpoint : (xi ≫ c) ≫ Limits.pullback.snd φ f = z := by
    simp only [z, c, Category.assoc, EtaleFundamentalGroups.coefficientModelMap,
      Limits.pullback.lift_snd]
  let eX₀ := geometricFundamentalGroupKernelEquiv k L X (j ≫ f) xi
  let eY₀ : Aut (fiber (xi ≫ c)) ≃ₜ*
      (arithmeticFundamentalGroupHom k L f z).toMonoidHom.ker :=
    hpoint ▸ geometricFundamentalGroupKernelEquiv k L Y f (xi ≫ c)
  let eX := TopologicalAbelianization.congr eX₀
  let eY := TopologicalAbelianization.congr eY₀
  let A := TopologicalAbelianization.map (arithmeticKernelHom k L j f
    (xi ≫ Limits.pullback.snd φ (j ≫ f)))
  have hab (y : TopologicalAbelianization (Aut (fiber xi))) :
      eY (TopologicalAbelianization.map (fundamentalGroupHom c xi) y) = A (eX y) := by
    have hm := congrArg TopologicalAbelianization.map
      (geometricFundamentalGroupKernelEquiv_naturality k L j f xi)
    rw [TopologicalAbelianization.map_comp, TopologicalAbelianization.map_comp] at hm
    exact DFunLike.congr_fun hm y
  have h := arithmetic_exactSequence_of_isSepClosure k L X (j ≫ f) xi
  obtain ⟨g, hg⟩ := h.2.1 σ
  have hgy : arithmeticFundamentalGroupHom k L f z
      (fundamentalGroupHom j (xi ≫ Limits.pullback.snd φ (j ≫ f)) g) = σ :=
    (arithmeticFundamentalGroupHom_comp k L j f
      (xi ≫ Limits.pullback.snd φ (j ≫ f)) g).trans hg
  have hy := geometricAbelianGaloisAction_transport_lift k L Y f (xi ≫ c) z hpoint
    (fundamentalGroupHom j (xi ≫ Limits.pullback.snd φ (j ≫ f)) g)
    (TopologicalAbelianization.map (fundamentalGroupHom c xi) x)
  rw [hgy] at hy
  apply eY.injective
  rw [hab, hy, hab, ← hg, geometricAbelianGaloisAction_lift_apply]
  change A (eX (eX.symm
    (conjugationTopologicalAbelianizationContinuousAut
      (arithmeticFundamentalGroupHom k L (j ≫ f)
        (xi ≫ Limits.pullback.snd φ (j ≫ f))).toMonoidHom.ker g (eX x)))) = _
  rw [eX.apply_symm_apply]
  exact arithmeticKernelHom_abelianization_conjugate k L j f
    (xi ≫ Limits.pullback.snd φ (j ≫ f)) g (eX x)

/-- The actual geometric base-change kernel is stable under the actual Galois action. -/
theorem geometricAbelianGaloisAction_preserves_baseChangeKernel
    (σ : L ≃ₐ[k] L) (x : TopologicalAbelianization (Aut (fiber xi))) :
    let φ := Spec.map (CommRingCat.ofHom (algebraMap k L))
    let c := EtaleFundamentalGroups.coefficientModelMap φ f j
    TopologicalAbelianization.map (fundamentalGroupHom c xi) x = 1 →
      TopologicalAbelianization.map (fundamentalGroupHom c xi)
        (geometricAbelianGaloisAction k L X (j ≫ f) xi σ x) = 1 := by
  intro φ c hx
  rw [geometricAbelianGaloisAction_baseChange_map, hx, map_one]

/-- Restriction of the actual Galois action to the actual base-change kernel. -/
def geometricBaseChangeKernelGaloisAction :
    let φ := Spec.map (CommRingCat.ofHom (algebraMap k L))
    let c := EtaleFundamentalGroups.coefficientModelMap φ f j
    (L ≃ₐ[k] L) →* MulAut
      (TopologicalAbelianization.map (fundamentalGroupHom c xi)).toMonoidHom.ker := by
  intro φ c
  let A := geometricAbelianGaloisAction k L X (j ≫ f) xi
  let H := (TopologicalAbelianization.map (fundamentalGroupHom c xi)).toMonoidHom.ker
  have hmap (σ : L ≃ₐ[k] L) : H.map (A σ).toMonoidHom = H := by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact geometricAbelianGaloisAction_preserves_baseChangeKernel k L j f xi σ y hy
    · intro hx
      refine ⟨A σ⁻¹ x,
        geometricAbelianGaloisAction_preserves_baseChangeKernel k L j f xi σ⁻¹ x hx, ?_⟩
      change (A σ * A σ⁻¹) x = x
      rw [← map_mul, mul_inv_cancel, map_one]
      rfl
  refine
    { toFun := fun σ => ((A σ).subgroupMap H).trans (MulEquiv.subgroupCongr (hmap σ))
      map_one' := ?_
      map_mul' := ?_ }
  · ext x
    change A 1 x.val = x.val
    rw [map_one]
    rfl
  · intro σ τ
    ext x
    change A (σ * τ) x.val = A σ (A τ x.val)
    rw [map_mul]
    rfl

/-- The restricted action has the same value as the original geometric action. -/
@[simp] theorem geometricBaseChangeKernelGaloisAction_coe
    (σ : L ≃ₐ[k] L)
    (x : (TopologicalAbelianization.map (fundamentalGroupHom
      (EtaleFundamentalGroups.coefficientModelMap
        (Spec.map (CommRingCat.ofHom (algebraMap k L))) f j) xi)).toMonoidHom.ker) :
    (geometricBaseChangeKernelGaloisAction k L j f xi σ x :
        TopologicalAbelianization (Aut (fiber xi))) =
      geometricAbelianGaloisAction k L X (j ≫ f) xi σ x.val := rfl

/-- The original jointly continuous action stays jointly continuous on its kernel. -/
theorem continuous_geometricBaseChangeKernelGaloisAction_joint :
    let φ := Spec.map (CommRingCat.ofHom (algebraMap k L))
    let c := EtaleFundamentalGroups.coefficientModelMap φ f j
    let H := (TopologicalAbelianization.map (fundamentalGroupHom c xi)).toMonoidHom.ker
    @Continuous ((L ≃ₐ[k] L) × H) H inferInstance inferInstance
      (fun z => geometricBaseChangeKernelGaloisAction k L j f xi z.1 z.2) := by
  intro φ c H
  have hp : Continuous (fun z : (L ≃ₐ[k] L) × H =>
      (z.1, (z.2 : TopologicalAbelianization (Aut (fiber xi))))) :=
    continuous_fst.prodMk (continuous_subtype_val.comp continuous_snd)
  have ha := continuous_geometricAbelianGaloisAction_joint k L X (j ≫ f) xi
  have h := ha.comp hp
  have hsub (g : (L ≃ₐ[k] L) × H → H)
      (hg : ∀ z, (g z : TopologicalAbelianization (Aut (fiber xi))) =
        geometricAbelianGaloisAction k L X (j ≫ f) xi z.1 z.2.val) : Continuous g := by
    apply (continuous_induced_rng
      (f := (Subtype.val : H → TopologicalAbelianization (Aut (fiber xi)))) (g := g)).mpr
    change Continuous (fun z => (g z : TopologicalAbelianization (Aut (fiber xi))))
    simp_rw [hg]
    exact h
  exact hsub (fun z => geometricBaseChangeKernelGaloisAction k L j f xi z.1 z.2)
    (fun z => geometricBaseChangeKernelGaloisAction_coe k L j f xi z.1 z.2)

end AlgebraicGeometry.FiniteEtale
