/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.EtaleFundamentalGroups.GeometricFiber.ArithmeticExactSequence
import Nyll.ProCGroups.Topologies.ContinuousMulEquiv
import Nyll.ProCGroups.Abelian.TopologicalAbelianizationConjugationContinuity

/-!
# Galois action on the actual geometric abelianization

The arithmetic exact sequence identifies the original geometric fundamental
group with the arithmetic kernel. The existing quotient-conjugation action
then gives the Galois action on its topological abelianization.
-/

noncomputable section

universe u

open CategoryTheory Limits
open ProCGroups.Abelian

namespace AlgebraicGeometry.FiniteEtale

variable
    (k L : Type u) [Field k] [Field L] [Algebra k L] [IsSepClosure k L]
    (X : Scheme.{u}) [CompactSpace X] [QuasiSeparatedSpace X]
    (f : X ⟶ Spec (.of k))
    [ConnectedSpace ↑(Limits.pullback (Spec.map (CommRingCat.ofHom (algebraMap k L))) f)]
    {Ω : Type u} [Field Ω] [IsSepClosed Ω]
    (xi : Spec (.of Ω) ⟶ Limits.pullback (Spec.map (CommRingCat.ofHom (algebraMap k L))) f)

/-- The actual geometric fundamental group is the arithmetic kernel, with its induced topology. -/
def geometricFundamentalGroupKernelEquiv :
    Aut (fiber xi) ≃ₜ*
      (arithmeticFundamentalGroupHom k L f (xi ≫ Limits.pullback.snd _ f)).toMonoidHom.ker := by
  let : IsSepClosed L := IsSepClosure.sep_closed k
  let : ConnectedSpace X := connectedSpace_of_connected_constantField k L f
  let i := fundamentalGroupHom (Limits.pullback.snd _ f) xi
  let a := arithmeticFundamentalGroupHom k L f (xi ≫ Limits.pullback.snd _ f)
  have h := arithmetic_exactSequence_of_isSepClosure k L X f xi
  have hi : ∀ x, i x ∈ a.toMonoidHom.ker := by
    intro x
    rw [h.2.2]
    exact ⟨x, rfl⟩
  let φ := i.toMonoidHom.codRestrict a.toMonoidHom.ker hi
  have hφ : Function.Bijective φ := by
    constructor
    · intro x y hxy
      exact h.1 (congrArg Subtype.val hxy)
    · intro y
      have hy : y.val ∈ i.toMonoidHom.range := h.2.2 ▸ y.property
      obtain ⟨x, hx⟩ := hy
      exact ⟨x, Subtype.ext hx⟩
  exact ProCGroups.ContinuousMulEquiv.ofBijectiveCompactToT2
    φ (i.continuous_toFun.subtype_mk hi) hφ

/-- The kernel comparison retains the actual geometric fundamental-group map. -/
@[simp] theorem geometricFundamentalGroupKernelEquiv_apply (x : Aut (fiber xi)) :
    (geometricFundamentalGroupKernelEquiv k L X f xi x :
      Aut (fiber (xi ≫ Limits.pullback.snd _ f))) =
        fundamentalGroupHom (Limits.pullback.snd _ f) xi x := rfl

/-- The Galois action obtained from the actual arithmetic exact sequence and conjugation. -/
def geometricAbelianGaloisAction :
    (L ≃ₐ[k] L) →* MulAut (TopologicalAbelianization (Aut (fiber xi))) := by
  let : IsSepClosed L := IsSepClosure.sep_closed k
  let : ConnectedSpace X := connectedSpace_of_connected_constantField k L f
  let a := arithmeticFundamentalGroupHom k L f (xi ≫ Limits.pullback.snd _ f)
  have h := arithmetic_exactSequence_of_isSepClosure k L X f xi
  let q := QuotientGroup.quotientKerEquivOfSurjective a.toMonoidHom h.2.1
  let e := TopologicalAbelianization.congr (geometricFundamentalGroupKernelEquiv k L X f xi)
  exact (MulAut.congr e.symm.toMulEquiv).toMonoidHom.comp
    ((quotientConjugationTopologicalAbelianizationMap a.toMonoidHom.ker).comp
      q.symm.toMonoidHom)

/-- An arithmetic lift acts by its original conjugation on the geometric kernel. -/
theorem geometricAbelianGaloisAction_lift_apply
    (g : Aut (fiber (xi ≫ Limits.pullback.snd _ f)))
    (x : TopologicalAbelianization (Aut (fiber xi))) :
    let a := arithmeticFundamentalGroupHom k L f (xi ≫ Limits.pullback.snd _ f)
    let e := TopologicalAbelianization.congr (geometricFundamentalGroupKernelEquiv k L X f xi)
    geometricAbelianGaloisAction k L X f xi (a g) x =
      e.symm (conjugationTopologicalAbelianizationContinuousAut a.toMonoidHom.ker g (e x)) := by
  intro a e
  let : IsSepClosed L := IsSepClosure.sep_closed k
  let : ConnectedSpace X := connectedSpace_of_connected_constantField k L f
  have h := arithmetic_exactSequence_of_isSepClosure k L X f xi
  let q := QuotientGroup.quotientKerEquivOfSurjective a.toMonoidHom h.2.1
  have hq : q.symm (a g) = QuotientGroup.mk' a.toMonoidHom.ker g := by
    apply q.injective
    rw [q.apply_symm_apply]
    rfl
  change e.symm ((quotientConjugationTopologicalAbelianizationMap a.toMonoidHom.ker)
    (q.symm (a g)) (e x)) = _
  rw [hq]
  apply congrArg e.symm
  obtain ⟨n, hn⟩ := QuotientGroup.mk'_surjective
    (Subgroup.closedCommutator a.toMonoidHom.ker) (e x)
  rw [← hn]
  exact (conjugationTopologicalAbelianizationContinuousAut_toMulAut_apply_mk
    a.toMonoidHom.ker g n).symm

/-- An actual conjugation identity in the arithmetic group determines the
Galois action on the corresponding geometric abelianization class. -/
theorem geometricAbelianGaloisAction_mk_of_conjugate
    (g : Aut (fiber (xi ≫ Limits.pullback.snd _ f)))
    (v w : Aut (fiber xi))
    (h : fundamentalGroupHom (Limits.pullback.snd _ f) xi w =
      g * fundamentalGroupHom (Limits.pullback.snd _ f) xi v * g⁻¹) :
    geometricAbelianGaloisAction k L X f xi
        (arithmeticFundamentalGroupHom k L f (xi ≫ Limits.pullback.snd _ f) g)
        (TopologicalAbelianization.mk _ v) = TopologicalAbelianization.mk _ w := by
  let a := arithmeticFundamentalGroupHom k L f (xi ≫ Limits.pullback.snd _ f)
  let E₀ := geometricFundamentalGroupKernelEquiv k L X f xi
  let E := TopologicalAbelianization.congr E₀
  rw [geometricAbelianGaloisAction_lift_apply]
  apply E.injective
  rw [E.apply_symm_apply]
  simp only [TopologicalAbelianization.congr_apply_mk]
  change TopologicalAbelianization.mk a.toMonoidHom.ker (MulAut.conjNormal g (E₀ v)) =
    TopologicalAbelianization.mk a.toMonoidHom.ker (E₀ w)
  exact congrArg (TopologicalAbelianization.mk a.toMonoidHom.ker) (Subtype.ext h.symm)

/-- The Galois action on the actual geometric abelianization is jointly continuous. -/
theorem continuous_geometricAbelianGaloisAction_joint :
    Continuous (fun p : (L ≃ₐ[k] L) × TopologicalAbelianization (Aut (fiber xi)) =>
      geometricAbelianGaloisAction k L X f xi p.1 p.2) := by
  let : IsSepClosed L := IsSepClosure.sep_closed k
  let : ConnectedSpace X := connectedSpace_of_connected_constantField k L f
  let a := arithmeticFundamentalGroupHom k L f (xi ≫ Limits.pullback.snd _ f)
  have h := arithmetic_exactSequence_of_isSepClosure k L X f xi
  let q := QuotientGroup.quotientKerEquivOfSurjective a.toMonoidHom h.2.1
  let e := TopologicalAbelianization.congr (geometricFundamentalGroupKernelEquiv k L X f xi)
  have hq : Continuous q := by
    apply (QuotientGroup.isQuotientMap_mk a.toMonoidHom.ker).continuous_iff.mpr
    change Continuous a
    exact a.continuous_toFun
  have hqs : Continuous q.symm :=
    Continuous.continuous_symm_of_equiv_compact_to_t2 (f := q.toEquiv) hq
  have he (σ : L ≃ₐ[k] L) (x : TopologicalAbelianization (Aut (fiber xi))) :
      geometricAbelianGaloisAction k L X f xi σ x =
        e.symm (quotientConjugationTopologicalAbelianizationMap a.toMonoidHom.ker
          (q.symm σ) (e x)) := by
    rfl
  simp_rw [he]
  exact e.symm.continuous_toFun.comp
    ((continuous_quotientConjugationTopologicalAbelianizationMap a.toMonoidHom.ker).comp
      ((hqs.comp continuous_fst).prodMk (e.continuous_toFun.comp continuous_snd)))

/-- Each Galois element acts continuously on the actual geometric abelianization. -/
theorem continuous_geometricAbelianGaloisAction (σ : L ≃ₐ[k] L) :
    Continuous (geometricAbelianGaloisAction k L X f xi σ) := by
  have h : Continuous (fun x : TopologicalAbelianization (Aut (fiber xi)) => (σ, x)) :=
    continuous_const.prodMk continuous_id
  have hc := (continuous_geometricAbelianGaloisAction_joint k L X f xi).comp h
  exact hc

end AlgebraicGeometry.FiniteEtale
