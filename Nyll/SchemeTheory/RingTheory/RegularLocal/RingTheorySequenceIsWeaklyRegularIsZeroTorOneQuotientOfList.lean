/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_RingTheory_Sequence_IsWeaklyRegular_isZero_tor_one_quotient_ofList.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

import Nyll.SchemeTheory.HomologicalAlgebra.TorExactSequence
import Mathlib.CategoryTheory.Monoidal.Tor
import Mathlib.CategoryTheory.Abelian.LeftDerived
import Mathlib.CategoryTheory.Preadditive.Projective.Resolution
import Mathlib.CategoryTheory.Abelian.Projective.Resolution
import Mathlib.Algebra.Category.ModuleCat.Projective
import Mathlib.Algebra.Category.ModuleCat.Abelian
import Mathlib.Algebra.Category.ModuleCat.Monoidal.Basic
import Mathlib.Algebra.Category.ModuleCat.Monoidal.Symmetric
import Mathlib.Algebra.Category.ModuleCat.Monoidal.Closed
import Mathlib.CategoryTheory.Monoidal.Closed.Basic
import Mathlib.CategoryTheory.Monoidal.Braided.Basic
import Mathlib.CategoryTheory.Monoidal.Preadditive
import Mathlib.Algebra.Homology.HomologySequence
import Mathlib.Algebra.Homology.HomologicalComplexAbelian
import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex
import Mathlib.Algebra.Homology.Additive
import Mathlib.Algebra.Homology.ShortComplex.ShortExact
import Mathlib.Algebra.Homology.ShortComplex.Exact
import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
import Mathlib.Algebra.Category.ModuleCat.EpiMono
import Mathlib.CategoryTheory.Limits.Shapes.ZeroMorphisms
import Mathlib.CategoryTheory.Limits.Preserves.Finite
import Mathlib.RingTheory.Flat.CategoryTheory
import Mathlib.RingTheory.Flat.Basic
import Mathlib.RingTheory.Regular.RegularSequence
import Mathlib.RingTheory.Regular.IsSMulRegular
import Mathlib.LinearAlgebra.TensorProduct.Quotient
import Mathlib.LinearAlgebra.TensorProduct.RightExactness
import Mathlib.LinearAlgebra.TensorProduct.Map
import Mathlib.Algebra.Exact.Basic
import Mathlib.LinearAlgebra.Isomorphisms
import Mathlib.LinearAlgebra.Quotient.Basic
import Mathlib.RingTheory.Ideal.Span
import Mathlib.Tactic.CategoryTheory.Slice
import Mathlib.Tactic.Simps.Basic

/-!
# Ring Theory Sequence Is Weakly Regular is Zero tor one quotient of List
-/

section ProofImplementation

namespace AlgebraicCurves.Foundations.CommutativeAlgebra.Proofs
namespace RingTheory_Sequence_IsWeaklyRegular_isZero_tor_one_quotient_ofList

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory TensorProduct
open AlgebraicCurves.Foundations.Algebra.TorExactSequence

noncomputable section

namespace TorRegSeq

section Main
variable {R : Type u} [CommRing R]

theorem dv_tor_isZero_of_iso {X X' Y : ModuleCat.{u} R} (e : X ≅ X') (n : ℕ)
    (h : IsZero (((Tor (ModuleCat.{u} R) n).obj X').obj Y)) :
    IsZero (((Tor (ModuleCat.{u} R) n).obj X).obj Y) :=
  h.of_iso (((Tor (ModuleCat.{u} R) n).mapIso e).app Y)

theorem tor1_isZero_of_rTensor_injective
    {A N M : Type u} [AddCommGroup A] [Module R A] [AddCommGroup N] [Module R N]
    [AddCommGroup M] [Module R M] (e : N →ₗ[R] A) (he : Function.Injective e)
    (hA : IsZero (((Tor (ModuleCat.{u} R) 1).obj (ModuleCat.of R A)).obj (ModuleCat.of R M)))
    (hinj : Function.Injective (LinearMap.rTensor M e)) :
    IsZero (((Tor (ModuleCat.{u} R) 1).obj (ModuleCat.of R (A ⧸ LinearMap.range e))).obj
      (ModuleCat.of R M)) := by
  classical
  set S₀ : ShortComplex (ModuleCat.{u} R) := ShortComplex.mk (ModuleCat.ofHom e)
    (ModuleCat.ofHom (LinearMap.range e).mkQ)
    (by
      have hz : (LinearMap.range e).mkQ ∘ₗ e = 0 := LinearMap.ext fun a => by
        simp [Submodule.Quotient.mk_eq_zero]
      rw [← ModuleCat.ofHom_comp, hz]
      rfl) with hS₀def
  have hS : S₀.ShortExact := by
    refine ModuleCat.shortComplex_shortExact S₀ ?_ ?_ ?_
    · exact LinearMap.exact_map_mkQ_range e
    · exact he
    · exact Submodule.mkQ_surjective _
  obtain ⟨P⟩ : Nonempty (ProjectiveResolution (ModuleCat.of R M)) :=
    HasProjectiveResolution.out
  have hzero : ((Tor (ModuleCat.{u} R) 1).map S₀.g).app (ModuleCat.of R M) = 0 := hA.eq_of_src _ _
  have hδmono : Mono (torLES_torDelta P S₀ hS 0) := (torLES_tor_exact₃ P S₀ hS 0).mono_g hzero
  have : PreservesFiniteColimits ((curriedTensor (ModuleCat.{u} R)).obj S₀.X₁) :=
    PreservesColimitsOfSize.preservesFiniteColimits _
  have : PreservesFiniteColimits ((curriedTensor (ModuleCat.{u} R)).obj S₀.X₂) :=
    PreservesColimitsOfSize.preservesFiniteColimits _
  have hm2 : Mono (((curriedTensor (ModuleCat.{u} R)).map S₀.f).app (ModuleCat.of R M)) :=
    (ModuleCat.mono_iff_injective
      (((curriedTensor (ModuleCat.{u} R)).map S₀.f).app (ModuleCat.of R M))).mpr hinj
  have hsq := ar_tor0_map_fromLeftDerivedZero_naturality P S₀.f
  have hfac : ((Tor (ModuleCat.{u} R) 0).map S₀.f).app (ModuleCat.of R M) =
      (((curriedTensor (ModuleCat.{u} R)).obj S₀.X₁).fromLeftDerivedZero.app (ModuleCat.of R M) ≫
        ((curriedTensor (ModuleCat.{u} R)).map S₀.f).app (ModuleCat.of R M)) ≫
      inv (((curriedTensor (ModuleCat.{u} R)).obj S₀.X₂).fromLeftDerivedZero.app (ModuleCat.of R
        M)) :=
    (IsIso.eq_comp_inv (((curriedTensor (ModuleCat.{u} R)).obj S₀.X₂).fromLeftDerivedZero.app
      (ModuleCat.of R M))).mpr hsq
  have hmonoF : Mono (((curriedTensor (ModuleCat.{u} R)).obj S₀.X₁).fromLeftDerivedZero.app
      (ModuleCat.of R M)) := IsIso.mono_of_iso _
  have hmonoG : Mono (inv (((curriedTensor (ModuleCat.{u} R)).obj
      S₀.X₂).fromLeftDerivedZero.app (ModuleCat.of R M))) := IsIso.mono_of_iso _
  have hTor0mono : Mono (((Tor (ModuleCat.{u} R) 0).map S₀.f).app (ModuleCat.of R M)) := by
    rw [hfac]
    exact mono_comp' (mono_comp' hmonoF hm2) hmonoG
  have hδ0 : torLES_torDelta P S₀ hS 0 = 0 :=
    zero_of_comp_mono _ (torLES_torDelta_comp_eq_zero P S₀ hS 0)
  have : Mono (0 : ((Tor (ModuleCat.{u} R) 1).obj S₀.X₃).obj (ModuleCat.of R M) ⟶
      ((Tor (ModuleCat.{u} R) 0).obj S₀.X₁).obj (ModuleCat.of R M)) := by rw [← hδ0]; exact hδmono
  exact IsZero.of_mono_zero _ (((Tor (ModuleCat.{u} R) 0).obj S₀.X₁).obj (ModuleCat.of R M))

theorem step {M : Type u} [AddCommGroup M] [Module R M] (I : Ideal R) (x : R)
    (hI : IsZero (((Tor (ModuleCat.{u} R) 1).obj (ModuleCat.of R (R ⧸ I))).obj (ModuleCat.of R M)))
    (hx : IsSMulRegular (M ⧸ (I • ⊤ : Submodule R M)) x) :
    IsZero (((Tor (ModuleCat.{u} R) 1).obj (ModuleCat.of R (R ⧸ (I ⊔ Ideal.span {x})))).obj
      (ModuleCat.of R M)) := by
  classical
  let φ : (R ⧸ I) →ₗ[R] (R ⧸ I) := x • LinearMap.id
  have hφapp : ∀ a : R ⧸ I, φ a = x • a := fun a => rfl
  let N : Submodule R (R ⧸ I) := LinearMap.range φ
  have hxA : IsSMulRegular ((R ⧸ I) ⊗[R] M) x :=
    ((TensorProduct.quotTensorEquivQuotSMul M I).isSMulRegular_congr x).mpr hx
  have hφinj : Function.Injective (LinearMap.rTensor M φ) := by
    intro a b hab
    apply hxA
    have e1 : LinearMap.rTensor M φ = x • LinearMap.id := by
      change LinearMap.rTensor M (x • LinearMap.id) = x • LinearMap.id
      rw [LinearMap.rTensor_smul, LinearMap.rTensor_id]
    have ha : LinearMap.rTensor M φ a = x • a := by rw [e1]; rfl
    have hb : LinearMap.rTensor M φ b = x • b := by rw [e1]; rfl
    change x • a = x • b
    rw [← ha, ← hb, hab]
  have hcomp : LinearMap.rTensor M φ = LinearMap.rTensor M N.subtype ∘ₗ LinearMap.rTensor M
    φ.rangeRestrict := by
    rw [← LinearMap.rTensor_comp]
    rfl
  have hinj : Function.Injective (LinearMap.rTensor M N.subtype) := by
    have h1 : Function.Injective (LinearMap.rTensor M N.subtype ∘ LinearMap.rTensor M
      φ.rangeRestrict) := by
      have h2 := hφinj
      rw [hcomp] at h2
      exact h2
    exact h1.of_comp_right (LinearMap.rTensor_surjective M (LinearMap.surjective_rangeRestrict φ))
  have hB := tor1_isZero_of_rTensor_injective N.subtype N.injective_subtype hI hinj
  have hNeq : Submodule.map (Submodule.mkQ I) (I ⊔ Ideal.span {x}) = LinearMap.range N.subtype := by
    rw [Submodule.range_subtype]
    apply le_antisymm
    · rintro y ⟨t, ht, rfl⟩
      obtain ⟨i, hi, s, hs, rfl⟩ := Submodule.mem_sup.mp ht
      obtain ⟨r, rfl⟩ := Ideal.mem_span_singleton'.mp hs
      refine ⟨Submodule.mkQ I r, ?_⟩
      rw [hφapp, map_add]
      simp only [Submodule.mkQ_apply]
      rw [(Submodule.Quotient.mk_eq_zero I).mpr hi, zero_add, ← Submodule.Quotient.mk_smul,
        smul_eq_mul, mul_comm]
    · rintro y ⟨a, rfl⟩
      obtain ⟨r, rfl⟩ := Submodule.mkQ_surjective I a
      refine ⟨x * r, Submodule.mem_sup_right (Ideal.mem_span_singleton'.mpr ⟨r, mul_comm r x⟩), ?_⟩
      rw [hφapp]
      simp only [Submodule.mkQ_apply]
      rw [← Submodule.Quotient.mk_smul, smul_eq_mul]
  let e₁ : ((R ⧸ I) ⧸ LinearMap.range N.subtype) ≃ₗ[R] ((R ⧸ I) ⧸ Submodule.map (Submodule.mkQ I)
    (I ⊔ Ideal.span {x})) :=
    Submodule.quotEquivOfEq _ _ hNeq.symm
  let e₂ : ((R ⧸ I) ⧸ Submodule.map (Submodule.mkQ I) (I ⊔ Ideal.span {x})) ≃ₗ[R] (R ⧸ (I ⊔
    Ideal.span {x})) :=
    Submodule.quotientQuotientEquivQuotient I (I ⊔ Ideal.span {x}) le_sup_left
  exact dv_tor_isZero_of_iso ((e₁ ≪≫ₗ e₂).symm.toModuleIso) 1 hB

theorem main {M : Type u} [AddCommGroup M] [Module R M] {rs : List R}
    (hM : RingTheory.Sequence.IsWeaklyRegular M rs) :
    ∀ n, n ≤ rs.length →
      IsZero (((Tor (ModuleCat.{u} R) 1).obj (ModuleCat.of R (R ⧸ Ideal.ofList (rs.take n)))).obj
        (ModuleCat.of R M)) := by
  intro n
  induction n with
  | zero =>
    intro _
    have h0 : Ideal.ofList (rs.take 0) = (⊥ : Ideal R) := by rw [List.take_zero, Ideal.ofList_nil]
    let e : (R ⧸ Ideal.ofList (rs.take 0)) ≃ₗ[R] R :=
      Submodule.quotEquivOfEq _ _ h0 ≪≫ₗ Submodule.quotEquivOfEqBot _ rfl
    exact dv_tor_isZero_of_iso e.toModuleIso 1 (torFV_tor_one_isZero_of_flat (ModuleCat.of R R)
      (ModuleCat.of R M))
  | succ n ih =>
    intro hn
    have hlt : n < rs.length := Nat.lt_of_succ_le hn
    have hI := ih hlt.le
    have hx := hM.regular_mod_prev n hlt
    have hstep := step (Ideal.ofList (rs.take n)) (rs[n]) hI hx
    have heq : Ideal.ofList (rs.take (n + 1)) = Ideal.ofList (rs.take n) ⊔ Ideal.span {rs[n]} := by
      rw [List.take_succ_eq_append_getElem hlt, Ideal.ofList_append, Ideal.ofList_singleton]
    exact dv_tor_isZero_of_iso (Submodule.quotEquivOfEq _ _ heq).toModuleIso 1 hstep

end Main

end TorRegSeq

end

theorem _root_.RingTheory.Sequence.IsWeaklyRegular.isZero_tor_one_quotient_ofList
    {R : Type u} [CommRing R] {M : Type u} [AddCommGroup M] [Module R M]
    {rs : List R} (hM : RingTheory.Sequence.IsWeaklyRegular M rs) :
    IsZero (((Tor (ModuleCat.{u} R) 1).obj (ModuleCat.of R (R ⧸ Ideal.ofList rs))).obj
      (ModuleCat.of R M)) := by
  have h := TorRegSeq.main hM rs.length le_rfl
  have heq : Ideal.ofList (rs.take rs.length) = Ideal.ofList rs := by rw [List.take_length]
  exact TorRegSeq.dv_tor_isZero_of_iso (Submodule.quotEquivOfEq _ _ heq.symm).toModuleIso 1 h
end RingTheory_Sequence_IsWeaklyRegular_isZero_tor_one_quotient_ofList
end AlgebraicCurves.Foundations.CommutativeAlgebra.Proofs
end ProofImplementation
