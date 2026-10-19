/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.AnabelianGeometry.ArithmeticIsomorphisms.Basic
import Nyll.EtaleFundamentalGroups.GeometricFiber.ArithmeticKernelEquivalence
import Nyll.ProCGroups.Topologies.Conjugation
import Nyll.ProCGroups.FiniteStepSolvableQuotients.SlimnessAndTorsion

/-! # Arithmetic isomorphisms detected on their geometric kernels -/

namespace AnabelianGeometry.ArithmeticIsomorphisms

universe u v w

variable {G : Type u} {H : Type v} {Γ : Type w}
  [Group G] [Group H] [Group Γ]
  [TopologicalSpace G] [TopologicalSpace H]
  {p : G →* Γ} {q : H →* Γ}

/-- Over a fixed quotient, agreement on a center-free kernel forces agreement everywhere. -/
theorem eq_of_agreeOnKernel (e f : OverQuotientEquiv p q)
    (hcenter : Subgroup.center q.ker = ⊥)
    (h : ∀ n : p.ker, e.1 n = f.1 n) : e = f := by
  let E := ProCGroups.kernelContinuousMulEquiv e.1 p q e.2
  apply Subtype.ext
  apply ContinuousMulEquiv.ext
  intro g
  let d : q.ker := ⟨(f.1 g)⁻¹ * e.1 g, by
    change q ((f.1 g)⁻¹ * e.1 g) = 1
    rw [map_mul, map_inv, e.2 g, f.2 g, inv_mul_cancel]⟩
  have hd : d ∈ Subgroup.center q.ker := by
    rw [Subgroup.mem_center_iff]
    intro n
    obtain ⟨m, rfl⟩ := E.surjective n
    have hm := h (MulAut.conjNormal g m)
    change e.1 (g * (m : G) * g⁻¹) = f.1 (g * (m : G) * g⁻¹) at hm
    rw [map_mul, map_mul, map_inv, map_mul, map_mul, map_inv, ← h m] at hm
    have hmul := congrArg (fun a : H => (f.1 g)⁻¹ * a * e.1 g) hm
    apply Subtype.ext
    change e.1 (m : G) * ((f.1 g)⁻¹ * e.1 g) =
      ((f.1 g)⁻¹ * e.1 g) * e.1 (m : G)
    simpa only [mul_assoc, inv_mul_cancel_left, mul_inv_cancel_left,
      inv_mul_cancel, mul_inv_cancel, mul_one, one_mul] using hmul.symm
  have hd1 : d = 1 := Subgroup.mem_bot.mp (hcenter ▸ hd)
  have hdval : (f.1 g)⁻¹ * e.1 g = 1 := congrArg Subtype.val hd1
  exact (inv_mul_eq_one.mp hdval).symm

/-- In a slim geometric kernel, agreement on one open subgroup already determines the
entire isomorphism over the quotient. -/
theorem eq_of_agreeOnOpenKernel [IsTopologicalGroup G] [IsTopologicalGroup H]
    (e f : OverQuotientEquiv p q)
    (hslim : ProCGroups.FiniteStepSolvableQuotients.IsSlim q.ker)
    (U : OpenSubgroup p.ker)
    (h : ∀ n : p.ker, n ∈ U → e.1 n = f.1 n) : e = f := by
  let E := ProCGroups.kernelContinuousMulEquiv e.1 p q e.2
  apply Subtype.ext
  apply ContinuousMulEquiv.ext
  intro g
  let C := ProCGroups.Subgroup.conjNormalContinuousMulEquiv p.ker g
  let V : OpenSubgroup p.ker :=
    U ⊓ OpenSubgroup.comap C.toMulEquiv.toMonoidHom C.continuous_toFun U
  let W : OpenSubgroup q.ker :=
    OpenSubgroup.comap E.symm.toMulEquiv.toMonoidHom E.symm.continuous_toFun V
  let d : q.ker := ⟨(f.1 g)⁻¹ * e.1 g, by
    change q ((f.1 g)⁻¹ * e.1 g) = 1
    rw [map_mul, map_inv, e.2 g, f.2 g, inv_mul_cancel]⟩
  have hd : d ∈ Subgroup.centralizer (W : Set q.ker) := by
    rw [Subgroup.mem_centralizer_iff]
    intro n hn
    let m : p.ker := E.symm n
    have hmV : m ∈ V := hn
    have hmU : m ∈ U := hmV.1
    have hmC : C m ∈ U := hmV.2
    have hm := h (C m) hmC
    change e.1 (g * (m : G) * g⁻¹) = f.1 (g * (m : G) * g⁻¹) at hm
    rw [map_mul, map_mul, map_inv, map_mul, map_mul, map_inv, ← h m hmU] at hm
    have hmul := congrArg (fun a : H => (f.1 g)⁻¹ * a * e.1 g) hm
    have hnE : e.1 (m : G) = (n : H) :=
      congrArg Subtype.val (E.apply_symm_apply n)
    apply Subtype.ext
    change (n : H) * ((f.1 g)⁻¹ * e.1 g) =
      ((f.1 g)⁻¹ * e.1 g) * (n : H)
    rw [← hnE]
    simpa only [mul_assoc, inv_mul_cancel_left, mul_inv_cancel_left,
      inv_mul_cancel, mul_inv_cancel, mul_one, one_mul] using hmul.symm
  have hd1 : d = 1 := Subgroup.mem_bot.mp ((hslim W) ▸ hd)
  have hdval : (f.1 g)⁻¹ * e.1 g = 1 := congrArg Subtype.val hd1
  exact (inv_mul_eq_one.mp hdval).symm

/-- Geometric inner agreement on the whole kernel is already geometric inner agreement
of the arithmetic isomorphisms. -/
theorem geometricInnerRelated_of_kernel_conjugate [IsTopologicalGroup H]
    (e f : OverQuotientEquiv p q)
    (hcenter : Subgroup.center q.ker = ⊥)
    (c : H) (hc : q c = 1)
    (h : ∀ n : p.ker, f.1 n = c * e.1 n * c⁻¹) :
    GeometricInnerRelated e f := by
  have heq : e.innerTarget c hc = f :=
    eq_of_agreeOnKernel (e.innerTarget c hc) f hcenter (fun n => (h n).symm)
  refine ⟨c, hc, ?_⟩
  intro g
  exact congrArg (fun a : OverQuotientEquiv p q => a.1 g) heq.symm

end AnabelianGeometry.ArithmeticIsomorphisms
