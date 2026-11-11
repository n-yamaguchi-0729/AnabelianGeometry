/-
Anthropic FLT source port.
Original copyright, authors, license and pinned sources are retained per unit below.
-/

module

public import Mathlib.Algebra.MvPolynomial.PDeriv
public import Mathlib.Data.Matrix.Block
public import Mathlib.LinearAlgebra.Dimension.Finite
public import Mathlib.LinearAlgebra.Dimension.Free
public import Mathlib.LinearAlgebra.Dual.Lemmas
public import Mathlib.LinearAlgebra.LinearIndependent.Lemmas
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
public import Mathlib.LinearAlgebra.TensorProduct.Basis
public import Mathlib.LinearAlgebra.TensorProduct.RightExactness
public import Mathlib.LinearAlgebra.TensorProduct.Tower
public import Mathlib.RingTheory.Etale.Kaehler
public import Mathlib.RingTheory.Extension.Generators
public import Mathlib.RingTheory.Ideal.Cotangent
public import Mathlib.RingTheory.OrzechProperty
public import Mathlib.RingTheory.Kaehler.JacobiZariski
public import Mathlib.RingTheory.Kaehler.Polynomial
public import Mathlib.RingTheory.Localization.AtPrime.Basic
public import Mathlib.RingTheory.Localization.Ideal
public import Mathlib.RingTheory.Smooth.StandardSmooth
public import Mathlib.RingTheory.Smooth.StandardSmoothOfFree
public import Mathlib.Tactic.Choose
public import Mathlib.Tactic.Convert
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Tactic.Set
public import Nyll.SchemeTheory.RingTheory.Smooth.AlgebraFormallyEtaleFormallySmooth
public import Nyll.SchemeTheory.RingTheory.Localization.LocalAlgebraCriteria
public import Nyll.SchemeTheory.RingTheory.Smooth.DifferentialCriteria

/-!
# Smooth affine charts and coordinates

Polynomial presentations, differential bases and localization construct smooth affine
charts with prescribed special-fibre equations. The final construction works over a DVR.
-/

@[expose] public section

section
/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned revision):
https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_Algebra_Etale_of_formallyUnramified_of_isStandardSmoothOfRelativeDimension.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/NOTICE
Upstream per-file ATTRIBUTION: https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/ATTRIBUTION.md
Copies of these notices are retained in the AbelianVarieties directory.
Existing upstream author/copyright comments in the source are retained below.

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

namespace SchemeTheory.SmoothCharts

open _root_.KaehlerDifferential
open _root_.Algebra
open _root_.TensorProduct
open _root_.Algebra.TensorProduct

universe u

namespace EtaleCriteria

section algebra

variable {R S T : Type*} [CommRing R] [CommRing S] [CommRing T]
  [Algebra R S] [Algebra R T] [Algebra S T] [IsScalarTower R S T]

theorem mapBaseChange_surjective_of_formallyUnramified [Algebra.FormallyUnramified S T] :
    Function.Surjective (KaehlerDifferential.mapBaseChange R S T) := by
  intro y
  have hex := KaehlerDifferential.exact_mapBaseChange_map R S T
  have hy : KaehlerDifferential.map R S T T y = 0 := Subsingleton.elim _ _
  exact (hex y).mp hy

theorem bijective_of_surjective_of_finrank_eq {A : Type*} [CommRing A] [Nontrivial A]
    {M N : Type*} [AddCommGroup M] [Module A M] [AddCommGroup N] [Module A N]
    [Module.Free A M] [Module.Finite A M] [Module.Free A N] [Module.Finite A N]
    (f : M →ₗ[A] N) (hf : Function.Surjective f)
    (hrank : Module.finrank A M = Module.finrank A N) : Function.Bijective f := by
  obtain ⟨e⟩ := FiniteDimensional.nonempty_linearEquiv_of_finrank_eq hrank
  exact OrzechProperty.bijective_of_surjective_of_injective e.toLinearMap f e.injective hf

theorem formallyEtale_of_formallyUnramified_of_isStandardSmoothOfRelativeDimension (n : ℕ)
    [Algebra.IsStandardSmoothOfRelativeDimension n R S]
    [Algebra.IsStandardSmoothOfRelativeDimension n R T]
    [Algebra.FormallyUnramified S T] :
    Algebra.FormallyEtale S T := by
  have : Algebra.IsStandardSmooth R S :=
    Algebra.IsStandardSmoothOfRelativeDimension.isStandardSmooth n
  have : Algebra.IsStandardSmooth R T :=
    Algebra.IsStandardSmoothOfRelativeDimension.isStandardSmooth n
  refine Algebra.FormallyEtale.of_formallySmooth_of_bijective_mapBaseChange (R := R) ?_
  have hsurj := mapBaseChange_surjective_of_formallyUnramified (R := R) (S := S) (T := T)
  cases subsingleton_or_nontrivial T with
  | inl hT =>
      exact ⟨fun a b _ => Subsingleton.elim _ _, hsurj⟩
  | inr hT =>
      have : Nontrivial S := (algebraMap S T).domain_nontrivial
      have hS : Module.rank S Ω[S⁄R] = n :=
        Algebra.IsStandardSmoothOfRelativeDimension.rank_kaehlerDifferential n
      have hTr : Module.rank T Ω[T⁄R] = n :=
        Algebra.IsStandardSmoothOfRelativeDimension.rank_kaehlerDifferential n
      have hSf : Module.finrank S Ω[S⁄R] = n := Module.finrank_eq_of_rank_eq hS
      have hTf : Module.finrank T Ω[T⁄R] = n := Module.finrank_eq_of_rank_eq hTr
      exact bijective_of_surjective_of_finrank_eq _ hsurj
        (by rw [Module.finrank_baseChange, hSf, hTf])

theorem etale_of_formallyUnramified_of_isStandardSmoothOfRelativeDimension (n : ℕ)
    [Algebra.IsStandardSmoothOfRelativeDimension n R S]
    [Algebra.IsStandardSmoothOfRelativeDimension n R T]
    [Algebra.FormallyUnramified S T] :
    Algebra.Etale S T := by
  have : Algebra.FormallyEtale S T :=
    formallyEtale_of_formallyUnramified_of_isStandardSmoothOfRelativeDimension
    (R := R) (S := S) (T := T) n
  have : Algebra.IsStandardSmooth R S :=
    Algebra.IsStandardSmoothOfRelativeDimension.isStandardSmooth n
  have : Algebra.IsStandardSmooth R T :=
    Algebra.IsStandardSmoothOfRelativeDimension.isStandardSmooth n
  have : Algebra.FinitePresentation S T :=
    Algebra.FinitePresentation.of_restrict_scalars_finitePresentation R S T
  exact Algebra.Etale.mk

end algebra

end EtaleCriteria

end SchemeTheory.SmoothCharts

namespace Algebra.Etale

open SchemeTheory.SmoothCharts
open _root_.KaehlerDifferential _root_.TensorProduct _root_.MvPolynomial
open scoped TensorProduct

universe u v

theorem of_formallyUnramified_of_isStandardSmoothOfRelativeDimension
    {R S T : Type*} [CommRing R] [CommRing S] [CommRing T]
    [Algebra R S] [Algebra R T] [Algebra S T] [IsScalarTower R S T] (n : ℕ)
    [Algebra.IsStandardSmoothOfRelativeDimension n R S]
    [Algebra.IsStandardSmoothOfRelativeDimension n R T]
    [Algebra.FormallyUnramified S T] :
    Algebra.Etale S T :=
  EtaleCriteria.etale_of_formallyUnramified_of_isStandardSmoothOfRelativeDimension (R := R) n

end Algebra.Etale

end

section
/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned revision):
https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_MvPolynomial_isStandardSmoothOfRelativeDimension_natCard.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/NOTICE
Upstream per-file ATTRIBUTION: https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/ATTRIBUTION.md
Copies of these notices are retained in the AbelianVarieties directory.
Existing upstream author/copyright comments in the source are retained below.

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

namespace SchemeTheory.SmoothCharts

universe u v

open MvPolynomial

end SchemeTheory.SmoothCharts

namespace MvPolynomial

open SchemeTheory.SmoothCharts
open _root_.KaehlerDifferential _root_.TensorProduct _root_.MvPolynomial
open scoped TensorProduct

universe u v

theorem isStandardSmoothOfRelativeDimension_natCard
    (S : Type u) [CommRing S] (ι : Type v) [Finite ι] :
    Algebra.IsStandardSmoothOfRelativeDimension (Nat.card ι) S (MvPolynomial ι S) :=
  Algebra.IsStandardSmoothOfRelativeDimension.mvPolynomial S ι

end MvPolynomial

end

section
/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned revision):
https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_Algebra_FinitePresentation_exists_surjective_aeval_det_pderiv_not_mem_of_basis_residueField.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/NOTICE
Upstream per-file ATTRIBUTION: https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/ATTRIBUTION.md
Copies of these notices are retained in the AbelianVarieties directory.
Existing upstream author/copyright comments in the source are retained below.

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

namespace SchemeTheory.SmoothCharts

open TensorProduct KaehlerDifferential MvPolynomial

universe u

namespace JacobianSelection

section Descent

variable {R : Type*} [CommRing R] {P S : Type*} [CommRing P] [CommRing S] [Algebra R P] [Algebra R
    S]
  {M : Type*} [AddCommGroup M] [Module R M] [Module S M]

theorem exists_derivation_of_surjective (f : P →ₐ[R] S) (hf : Function.Surjective f)
    (d : P →ₗ[R] M) (hleib : ∀ p q, d (p * q) = f p • d q + f q • d p)
    (hker : ∀ p, f p = 0 → d p = 0) :
    ∃ δ : Derivation R S M, ∀ p, δ (f p) = d p := by
  have hwd : ∀ p q, f p = f q → d p = d q := by
    intro p q hpq
    have : d (p - q) = 0 := hker _ (by rw [map_sub, hpq, sub_self])
    rwa [map_sub, sub_eq_zero] at this
  let σ := Function.surjInv hf
  have hσ : ∀ s, f (σ s) = s := Function.surjInv_eq hf
  let δ₀ : S →ₗ[R] M :=
    { toFun := fun s => d (σ s)
      map_add' := fun s t => by
        change d (σ (s + t)) = d (σ s) + d (σ t)
        rw [← map_add]; exact hwd _ _ (by rw [hσ, map_add, hσ, hσ])
      map_smul' := fun c s => by
        change d (σ (c • s)) = c • d (σ s)
        rw [← map_smul]; exact hwd _ _ (by rw [hσ, map_smul, hσ]) }
  have hδ₀ : ∀ p, δ₀ (f p) = d p := fun p => hwd _ _ (hσ _)
  have h1 : d 1 = 0 := by
    have := hleib 1 1
    rw [mul_one, show f 1 = 1 from map_one f, one_smul] at this
    have h2 : d 1 + d 1 = d 1 + 0 := by rw [add_zero]; exact this.symm
    exact add_left_cancel h2
  refine ⟨{ toLinearMap := δ₀
            map_one_eq_zero' := ?_
            leibniz' := ?_ }, hδ₀⟩
  · change δ₀ 1 = 0
    rw [← map_one f]
    exact (hδ₀ 1).trans h1
  · intro a b
    change d (σ (a * b)) = a • d (σ b) + b • d (σ a)
    rw [hwd (σ (a * b)) (σ a * σ b) (by rw [hσ, map_mul, hσ, hσ]), hleib, hσ, hσ]

end Descent

section Main

variable {R : Type u} [CommRing R] {S : Type u} [CommRing S] [Algebra R S]

theorem main [Algebra.FinitePresentation R S]
    (u : Ideal S) [u.IsPrime]
    {ι : Type} [Finite ι] (w : ι → S)
    (b₀ : Module.Basis ι u.ResidueField (u.ResidueField ⊗[S] Ω[S⁄R]))
    (hb₀ : ∀ i, b₀ i = (1 : u.ResidueField) ⊗ₜ[S] D R S (w i)) :
    ∃ (m : ℕ) (x : Fin m → S) (h : Fin m → MvPolynomial (ι ⊕ Fin m) R),
      Function.Surjective (MvPolynomial.aeval (Sum.elim w x) : MvPolynomial (ι ⊕ Fin m) R →ₐ[R] S) ∧
      (∀ a, MvPolynomial.aeval (Sum.elim w x) (h a) = 0) ∧
      MvPolynomial.aeval (Sum.elim w x)
        (Matrix.det (Matrix.of fun a b : Fin m => MvPolynomial.pderiv (Sum.inr b) (h a))) ∉ u := by
  classical
  obtain ⟨s, hs⟩ := Algebra.FiniteType.out (R := R) (A := S)
  set m := s.card with hm
  let x : Fin m → S := fun a => (s.equivFin.symm a : S)
  let f : MvPolynomial (ι ⊕ Fin m) R →ₐ[R] S := MvPolynomial.aeval (Sum.elim w x)
  have hf : Function.Surjective f := by
    rw [← AlgHom.range_eq_top, ← Algebra.adjoin_range_eq_range_aeval, eq_top_iff, ← hs]
    apply Algebra.adjoin_mono
    intro y hy
    exact ⟨Sum.inr (s.equivFin ⟨y, hy⟩), congrArg Subtype.val (s.equivFin.symm_apply_apply _)⟩
  set κ := u.ResidueField with hκ
  let Xgrad : MvPolynomial (ι ⊕ Fin m) R → (Fin m → κ) := fun p b => algebraMap S κ (f (pderiv
      (Sum.inr b) p))
  have Xgrad_add : ∀ p q, Xgrad (p + q) = Xgrad p + Xgrad q := by
    intro p q; funext b; simp only [Xgrad, map_add, Pi.add_apply]
  have Xgrad_smul : ∀ (c : R) p, Xgrad (c • p) = c • Xgrad p := by
    intro c p; funext b
    change algebraMap S κ (f (pderiv (Sum.inr b) (c • p))) = c • algebraMap S κ (f (pderiv (Sum.inr
        b) p))
    rw [Derivation.map_smul, map_smul, Algebra.smul_def, map_mul, Algebra.smul_def, ←
        IsScalarTower.algebraMap_apply R S κ]
  have Xgrad_mul : ∀ p q, Xgrad (p * q) = algebraMap S κ (f p) • Xgrad q + algebraMap S κ (f q) •
      Xgrad p := by
    intro p q; funext b
    simp only [Xgrad, Derivation.leibniz, smul_eq_mul, map_add, map_mul, Pi.add_apply,
        Pi.smul_apply]
  have Xgrad_X_inl : ∀ i, Xgrad (X (Sum.inl i)) = 0 := by
    intro i; funext b
    change algebraMap S κ (f (pderiv (Sum.inr b) (X (Sum.inl i)))) = 0
    rw [pderiv_X_of_ne (Sum.inl_ne_inr), map_zero, map_zero]
  have Xgrad_X_inr : ∀ b, Xgrad (X (Sum.inr b)) = Pi.single b 1 := by
    intro b
    funext b'
    by_cases hb : b = b'
    · subst b'
      simp only [Xgrad, pderiv_X_self, map_one, Pi.single_eq_same]
    · change algebraMap S κ (f (pderiv (Sum.inr b') (X (Sum.inr b)))) =
        (Pi.single b (1 : κ) : Fin m → κ) b'
      rw [pderiv_X_of_ne (fun h => hb (Sum.inr.inj h)), map_zero, map_zero,
        Pi.single_eq_of_ne (fun h => hb h.symm)]
  let t : Set (Fin m → κ) := Set.range fun p : ↥(RingHom.ker f.toRingHom) => Xgrad p.1
  have hspan : Submodule.span κ t = ⊤ := by
    by_contra hne
    obtain ⟨φ, hφ0, hφ⟩ := Submodule.exists_dual_map_eq_bot_of_lt_top (lt_top_iff_ne_top.mpr hne)
        inferInstance
    have hφt : ∀ p : MvPolynomial (ι ⊕ Fin m) R, f p = 0 → φ (Xgrad p) = 0 := by
      intro p hp
      have : φ (Xgrad p) ∈ (Submodule.span κ t).map φ := Submodule.mem_map_of_mem
          (Submodule.subset_span ⟨⟨p, hp⟩, rfl⟩)
      rwa [hφ, Submodule.mem_bot] at this
    let d : MvPolynomial (ι ⊕ Fin m) R →ₗ[R] κ :=
      { toFun := fun p => φ (Xgrad p)
        map_add' := fun p q => by rw [Xgrad_add, map_add]
        map_smul' := fun c p => by rw [Xgrad_smul, LinearMap.map_smul_of_tower]; rfl }
    have hd : ∀ p, d p = φ (Xgrad p) := fun p => rfl
    obtain ⟨δ, hδ⟩ := exists_derivation_of_surjective f hf d
      (fun p q => by
        rw [hd, hd, hd, Xgrad_mul, map_add, map_smul, map_smul, smul_eq_mul, smul_eq_mul,
            Algebra.smul_def,
          Algebra.smul_def])
      (fun p hp => hφt p hp)
    let ℓ : Ω[S⁄R] →ₗ[S] κ := δ.liftKaehlerDifferential
    let L : κ ⊗[S] Ω[S⁄R] →ₗ[κ] κ := ℓ.liftBaseChange κ
    have hL : L = 0 := by
      refine b₀.ext fun i => ?_
      rw [hb₀ i, LinearMap.zero_apply]
      change (1 : κ) • ℓ (D R S (w i)) = 0
      rw [one_smul]
      change δ.liftKaehlerDifferential (D R S (w i)) = 0
      rw [Derivation.liftKaehlerDifferential_comp_D]
      have : f (X (Sum.inl i)) = w i := by rw [MvPolynomial.aeval_X]; rfl
      rw [← this, hδ, hd, Xgrad_X_inl, map_zero]
    have hφb : ∀ b, φ (Pi.single b 1) = 0 := by
      intro b
      have h1 : L ((1 : κ) ⊗ₜ[S] D R S (x b)) = 0 := by rw [hL, LinearMap.zero_apply]
      change (1 : κ) • ℓ (D R S (x b)) = 0 at h1
      rw [one_smul] at h1
      change δ.liftKaehlerDifferential (D R S (x b)) = 0 at h1
      rw [Derivation.liftKaehlerDifferential_comp_D] at h1
      have : f (X (Sum.inr b)) = x b := by rw [MvPolynomial.aeval_X]; rfl
      rw [← this, hδ, hd, Xgrad_X_inr] at h1
      exact h1
    apply hφ0
    refine (Pi.basisFun κ (Fin m)).ext fun b => ?_
    rw [Pi.basisFun_apply, LinearMap.zero_apply]
    exact hφb b
  obtain ⟨bs, hbt, hbspan, hli⟩ := exists_linearIndependent κ t
  rw [hspan] at hbspan
  let B : Module.Basis bs κ (Fin m → κ) := Module.Basis.mk hli (by rw [Subtype.range_coe_subtype,
      Set.ofPred_mem_eq, hbspan])
  have : Finite bs := Module.Finite.finite_basis B
  let : Fintype bs := Fintype.ofFinite bs
  have hcard : Fintype.card bs = m := by
    have := Module.finrank_eq_card_basis B
    rw [Module.finrank_fintype_fun_eq_card, Fintype.card_fin] at this
    exact this.symm
  let e : bs ≃ Fin m := Fintype.equivOfCardEq (by rw [hcard, Fintype.card_fin])
  have hmem : ∀ a : Fin m, ∃ p : ↥(RingHom.ker f.toRingHom), Xgrad p.1 = (e.symm a : Fin m → κ) :=
    fun a => hbt (e.symm a).2
  choose hp hhp using hmem
  let h : Fin m → MvPolynomial (ι ⊕ Fin m) R := fun a => (hp a).1
  refine ⟨m, x, h, hf, fun a => (hp a).2, ?_⟩
  set N : Matrix (Fin m) (Fin m) (MvPolynomial (ι ⊕ Fin m) R) :=
    Matrix.of fun a b : Fin m => MvPolynomial.pderiv (Sum.inr b) (h a) with hN
  have hrow : (N.map ((algebraMap S κ).comp f.toRingHom)) = Matrix.of fun a => (e.symm a : Fin m →
      κ) := by
    ext a b
    change algebraMap S κ (f (pderiv (Sum.inr b) (h a))) = (e.symm a : Fin m → κ) b
    rw [← hhp a]
  have hliRows : LinearIndependent κ (N.map ((algebraMap S κ).comp f.toRingHom)).row := by
    rw [hrow]
    change LinearIndependent κ (fun a => ((e.symm a : bs) : Fin m → κ))
    have hB : (fun a => ((e.symm a : bs) : Fin m → κ)) = ⇑B ∘ ⇑e.symm := by
      funext a; exact (Module.Basis.mk_apply hli _ _).symm
    rw [hB]
    exact B.linearIndependent.comp e.symm e.symm.injective
  have hunit : IsUnit (N.map ((algebraMap S κ).comp f.toRingHom)) :=
      Matrix.linearIndependent_row_iff_isUnit.mp hliRows
  have hdet : (N.map ((algebraMap S κ).comp f.toRingHom)).det ≠ 0 :=
    ((Matrix.isUnit_iff_isUnit_det _).mp hunit).ne_zero
  have hdet' : ((algebraMap S κ).comp f.toRingHom) N.det ≠ 0 := by
    rw [RingHom.map_det]; exact hdet
  intro hmemu
  apply hdet'
  change algebraMap S κ (f N.det) = 0
  exact Ideal.algebraMap_residueField_eq_zero.mpr hmemu

end Main

end JacobianSelection

end SchemeTheory.SmoothCharts

namespace Algebra.FinitePresentation

open SchemeTheory.SmoothCharts
open _root_.KaehlerDifferential _root_.TensorProduct _root_.MvPolynomial
open scoped TensorProduct

universe u v

theorem exists_surjective_aeval_det_pderiv_not_mem_of_basis_residueField
    {R : Type u} [CommRing R] {S : Type u} [CommRing S] [Algebra R S] [Algebra.FinitePresentation R
        S]
    (u : Ideal S) [u.IsPrime]
    {ι : Type} [Finite ι] (w : ι → S)
    (b₀ : Module.Basis ι u.ResidueField (u.ResidueField ⊗[S] Ω[S⁄R]))
    (hb₀ : ∀ i, b₀ i = (1 : u.ResidueField) ⊗ₜ[S] D R S (w i)) :
    ∃ (m : ℕ) (x : Fin m → S) (h : Fin m → MvPolynomial (ι ⊕ Fin m) R),
      Function.Surjective (MvPolynomial.aeval (Sum.elim w x) : MvPolynomial (ι ⊕ Fin m) R →ₐ[R] S) ∧
      (∀ a, MvPolynomial.aeval (Sum.elim w x) (h a) = 0) ∧
      MvPolynomial.aeval (Sum.elim w x)
        (Matrix.det (Matrix.of fun a b : Fin m => MvPolynomial.pderiv (Sum.inr b) (h a))) ∉ u :=
  JacobianSelection.main u w b₀ hb₀

end Algebra.FinitePresentation

end

section
/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned revision):
https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_MvPolynomial_exists_isStandardSmooth_algHom_isUnit_det_pderiv_basis_kaehlerDifferential.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/NOTICE
Upstream per-file ATTRIBUTION: https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/ATTRIBUTION.md
Copies of these notices are retained in the AbelianVarieties directory.
Existing upstream author/copyright comments in the source are retained below.

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

namespace SchemeTheory.SmoothCharts

open KaehlerDifferential MvPolynomial

universe u

namespace SubmersiveQuotient

variable {R : Type u} [CommRing R] {ι : Type} {m : ℕ} (h : Fin m → MvPolynomial (ι ⊕ Fin
    m) R)

/-- The original variables and the added inverse variable. -/
abbrev V (ι : Type) (m : ℕ) : Type := (ι ⊕ Fin m) ⊕ Unit

/-- The original equations and the added inverse equation. -/
abbrev Rel (m : ℕ) : Type := Fin m ⊕ Unit

/-- The determinant of the selected Jacobian minor. -/
noncomputable def Δ : MvPolynomial (ι ⊕ Fin m) R :=
  Matrix.det (Matrix.of fun a b : Fin m => MvPolynomial.pderiv (Sum.inr b) (h a))

/-- The polynomial inclusion adding an inverse variable. -/
noncomputable abbrev emb : MvPolynomial (ι ⊕ Fin m) R →ₐ[R] MvPolynomial (V ι m) R := rename Sum.inl

/-- The chart equations together with the Jacobian-inverse equation. -/
noncomputable def rel : Rel m → MvPolynomial (V ι m) R :=
  fun r => Sum.elim (fun a => emb (h a)) (fun _ => emb (Δ h) * X (Sum.inr ()) - 1) r

@[scoped simp] theorem rel_inl (a : Fin m) : rel h (Sum.inl a) = emb (h a) := rfl
@[scoped simp] theorem rel_inr (x : Unit) : rel h (Sum.inr x) = emb (Δ h) * X (Sum.inr ()) - 1 :=
    rfl

/-- The ideal generated by the chart equations. -/
noncomputable def I : Ideal (MvPolynomial (V ι m) R) := Ideal.span (Set.range (rel h))

/-- The quotient ring of the standard smooth chart. -/
abbrev Q : Type u := MvPolynomial (V ι m) R ⧸ I h

/-- The polynomial map into the chart ring. -/
noncomputable def φ : MvPolynomial (ι ⊕ Fin m) R →ₐ[R] Q h :=
  (Ideal.Quotient.mkₐ R (I h)).comp emb

theorem φ_apply (p : MvPolynomial (ι ⊕ Fin m) R) : φ h p = Ideal.Quotient.mk (I h) (emb p) := rfl

theorem rel_mem (r : Rel m) : rel h r ∈ I h := Ideal.subset_span ⟨r, rfl⟩

theorem φ_h (a : Fin m) : φ h (h a) = 0 := by
  rw [φ_apply, Ideal.Quotient.eq_zero_iff_mem]
  exact rel_mem h (Sum.inl a)

theorem φ_Δ_mul_Y : φ h (Δ h) * Ideal.Quotient.mk (I h) (X (Sum.inr ())) = 1 := by
  rw [φ_apply, ← map_mul, ← (Ideal.Quotient.mk (I h)).map_one, Ideal.Quotient.eq, ]
  exact rel_mem h (Sum.inr ())

theorem isUnit_φ_Δ : IsUnit (φ h (Δ h)) := isUnit_iff_exists_inv.mpr ⟨_, φ_Δ_mul_Y h⟩

theorem univ (B : Type u) [CommRing B] [Algebra R B] (ψ : MvPolynomial (ι ⊕ Fin m) R →ₐ[R] B)
    (hψ : ∀ a, ψ (h a) = 0) (hu : IsUnit (ψ (Δ h))) : ∃ χ : Q h →ₐ[R] B, χ.comp (φ h) = ψ := by
  obtain ⟨v, hv⟩ := hu
  let Ψ : MvPolynomial (V ι m) R →ₐ[R] B := aeval (Sum.elim (fun i => ψ (X i)) (fun _ => ((v⁻¹ : Bˣ)
      : B)))
  have hΨemb : ∀ p, Ψ (emb p) = ψ p := by
    intro p
    change aeval _ (rename Sum.inl p) = ψ p
    rw [aeval_rename]
    conv_rhs => rw [aeval_unique ψ]
    rfl
  have hΨI : ∀ x ∈ I h, Ψ x = 0 := by
    intro x hx
    unfold I at hx
    refine Submodule.span_induction ?_ (map_zero _) (fun x y _ _ hx hy => by rw [map_add, hx, hy,
        add_zero])
      (fun a x _ hx => by rw [smul_eq_mul, map_mul, hx, mul_zero]) hx
    rintro _ ⟨r, rfl⟩
    rcases r with a | u
    · rw [rel_inl, hΨemb, hψ]
    · rw [rel_inr, map_sub, map_mul, hΨemb, ← hv, map_one]
      change (v : B) * aeval _ (X (Sum.inr ())) - 1 = 0
      rw [aeval_X, Sum.elim_inr, Units.mul_inv, sub_self]
  refine ⟨Ideal.Quotient.liftₐ (I h) Ψ hΨI, ?_⟩
  ext p
  · change Ideal.Quotient.liftₐ (I h) Ψ hΨI (Ideal.Quotient.mk (I h) (emb (X p))) = ψ (X p)
    change Ψ (emb (X p)) = ψ (X p)
    exact hΨemb (X p)

/-- The canonical polynomial generators of the chart quotient. -/
noncomputable abbrev gens : Algebra.Generators R (Q h) (V ι m) :=
  Algebra.Generators.naive (I := I h)

theorem gens_val (v : V ι m) : (gens h).val v = Ideal.Quotient.mk (I h) (X v) := rfl

theorem gens_ker : (gens h).ker = I h := by
  change RingHom.ker (algebraMap (MvPolynomial (V ι m) R) (Q h)) = I h
  exact Ideal.mk_ker

/-- The presentation with the chosen Jacobian variables. -/
noncomputable def pres : Algebra.PreSubmersivePresentation R (Q h) (V ι m) (Rel m) where
  toGenerators := gens h
  relation := rel h
  span_range_relation_eq_ker := by rw [gens_ker]; rfl
  map := Sum.map Sum.inr id
  map_inj := Sum.map_injective.mpr ⟨Sum.inr_injective, fun _ _ h => h⟩

theorem pderiv_inr_emb (p : MvPolynomial (ι ⊕ Fin m) R) : pderiv (Sum.inr ()) (emb p : MvPolynomial
    (V ι m) R) = 0 := by
  induction p using MvPolynomial.induction_on with
  | C a =>
    rw [show (emb (MvPolynomial.C a) : MvPolynomial (V ι m) R) = MvPolynomial.C a from rename_C _ _,
        pderiv_C]
  | add p q hp hq => rw [map_add, map_add, hp, hq, add_zero]
  | mul_X p i hp =>
    rw [map_mul, Derivation.leibniz, hp, smul_zero, add_zero, show (emb (X i) : MvPolynomial (V ι m)
        R) = X (Sum.inl i) from rename_X _ _,
      pderiv_X_of_ne (Sum.inl_ne_inr), smul_zero]

theorem pderiv_inl_emb (j : ι ⊕ Fin m) (p : MvPolynomial (ι ⊕ Fin m) R) :
    pderiv (Sum.inl j) (emb p : MvPolynomial (V ι m) R) = emb (pderiv j p) :=
  pderiv_rename Sum.inl_injective j p

theorem jacobiMatrix_eq :
    (pres h).jacobiMatrix =
      Matrix.fromBlocks
        ((Matrix.of fun a b : Fin m => MvPolynomial.pderiv (Sum.inr b) (h a)).transpose.map (emb :
            MvPolynomial (ι ⊕ Fin m) R →ₐ[R] MvPolynomial (V ι m) R))
        (Matrix.of fun (a : Fin m) (_ : Unit) => pderiv (Sum.inl (Sum.inr a)) (emb (Δ h) * X
            (Sum.inr ()) - 1))
        0
        (Matrix.of fun (_ _ : Unit) => (emb (Δ h) : MvPolynomial (V ι m) R)) := by
  refine Matrix.ext fun i j => ?_
  rw [Algebra.PreSubmersivePresentation.jacobiMatrix_apply]
  rcases i with a | x <;> rcases j with b | y
  · simp only [Matrix.fromBlocks_apply₁₁, Matrix.map_apply, Matrix.transpose_apply, Matrix.of_apply]
    change pderiv (Sum.inl (Sum.inr a)) (emb (h b)) = emb (pderiv (Sum.inr a) (h b))
    exact pderiv_inl_emb _ _
  · simp only [Matrix.fromBlocks_apply₁₂, Matrix.of_apply]
    rfl
  · simp only [Matrix.fromBlocks_apply₂₁, Matrix.zero_apply]
    change pderiv (Sum.inr x) (emb (h b)) = 0
    cases x
    exact pderiv_inr_emb _
  · simp only [Matrix.fromBlocks_apply₂₂, Matrix.of_apply]
    change pderiv (Sum.inr x) (emb (Δ h) * X (Sum.inr ()) - 1) = emb (Δ h)
    cases x
    rw [map_sub, Derivation.map_one_eq_zero, sub_zero, Derivation.leibniz, pderiv_X_self,
        pderiv_inr_emb, smul_zero,
      add_zero, smul_eq_mul, mul_one]

theorem jacobian_eq : (pres h).jacobian = φ h (Δ h) * φ h (Δ h) := by
  classical
  have hD : (Matrix.of fun (_ _ : Unit) => (emb (Δ h) : MvPolynomial (V ι m) R)).det = emb (Δ h) :=
    Matrix.det_unique _
  have hA : ((Matrix.of fun a b : Fin m => MvPolynomial.pderiv (Sum.inr b) (h a)).transpose.map
      (emb : MvPolynomial (ι ⊕ Fin m) R →ₐ[R] MvPolynomial (V ι m) R)).det = emb (Δ h) := by
    change (AlgHom.mapMatrix (emb : MvPolynomial (ι ⊕ Fin m) R →ₐ[R] MvPolynomial (V ι m) R)
      (Matrix.of fun a b : Fin m => MvPolynomial.pderiv (Sum.inr b) (h a)).transpose).det = _
    rw [← AlgHom.map_det, Matrix.det_transpose]
    rfl
  rw [Algebra.PreSubmersivePresentation.jacobian_eq_jacobiMatrix_det, jacobiMatrix_eq,
      Matrix.det_fromBlocks_zero₂₁,
    hA, hD, map_mul]
  rfl

/-- The submersive presentation obtained by inverting its Jacobian. -/
noncomputable def spres : Algebra.SubmersivePresentation R (Q h) (V ι m) (Rel m) where
  toPreSubmersivePresentation := pres h
  jacobian_isUnit := by rw [jacobian_eq]; exact (isUnit_φ_Δ h).mul (isUnit_φ_Δ h)

theorem isCompl_range :
    IsCompl (Set.range (fun i : ι => (Sum.inl (Sum.inl i) : V ι m))) (Set.range (pres h).map) := by
  constructor
  · rw [Set.disjoint_iff]
    rintro v ⟨⟨i, rfl⟩, ⟨r, hr⟩⟩
    rcases r with a | x
    · exact Sum.inr_ne_inl (Sum.inl.inj hr)
    · exact Sum.inr_ne_inl hr
  · rw [codisjoint_iff, eq_top_iff]
    intro v _
    change v ∈ (Set.range fun i : ι => (Sum.inl (Sum.inl i) : V ι m)) ∪ Set.range (pres h).map
    rcases v with (i | a) | x
    · exact Or.inl ⟨i, rfl⟩
    · exact Or.inr ⟨Sum.inl a, rfl⟩
    · exact Or.inr ⟨Sum.inr x, rfl⟩

/-- The differential basis associated to the unselected variables. -/
noncomputable def basis : Module.Basis ι (Q h) Ω[Q h⁄R] :=
  (spres h).basisKaehlerOfIsCompl (f := fun i : ι => (Sum.inl (Sum.inl i) : V ι m))
    (fun _ _ hij => Sum.inl.inj (Sum.inl.inj hij)) (isCompl_range h)

theorem basis_apply (i : ι) : basis h i = D R (Q h) (φ h (X (Sum.inl i))) := by
  have hcalc := (spres h).basisKaehlerOfIsCompl_apply
    (f := fun j : ι => (Sum.inl (Sum.inl j) : V ι m))
    (Sum.inl_injective.comp Sum.inl_injective) (isCompl_range h) i
  change basis h i =
    D R (Q h) (Ideal.Quotient.mk (I h) (X (Sum.inl (Sum.inl i)))) at hcalc
  rw [φ_apply, show (emb (X (Sum.inl i)) : MvPolynomial (V ι m) R) =
    X (Sum.inl (Sum.inl i)) from rename_X _ _]
  exact hcalc

theorem main [Finite ι] :
    ∃ (C : Type u) (_ : CommRing C) (_ : Algebra R C) (φ : MvPolynomial (ι ⊕ Fin m) R →ₐ[R] C),
      Algebra.IsStandardSmooth R C ∧
      (∀ a, φ (h a) = 0) ∧
      IsUnit (φ (Matrix.det (Matrix.of fun a b : Fin m => MvPolynomial.pderiv (Sum.inr b) (h a)))) ∧
      (∀ (B : Type u) [CommRing B] [Algebra R B] (ψ : MvPolynomial (ι ⊕ Fin m) R →ₐ[R] B),
          (∀ a, ψ (h a) = 0) →
          IsUnit (ψ (Matrix.det (Matrix.of fun a b : Fin m => MvPolynomial.pderiv (Sum.inr b) (h
              a)))) →
          ∃ χ : C →ₐ[R] B, χ.comp φ = ψ) ∧
      ∃ b : Module.Basis ι C Ω[C⁄R], ∀ i, b i = D R C (φ (MvPolynomial.X (Sum.inl i))) :=
  ⟨Q h, inferInstance, inferInstance, φ h, (spres h).isStandardSmooth, φ_h h, isUnit_φ_Δ h,
    fun B _ _ ψ hψ hu => univ h B ψ hψ hu, basis h, basis_apply h⟩

end SubmersiveQuotient

end SchemeTheory.SmoothCharts

namespace MvPolynomial

open SchemeTheory.SmoothCharts
open _root_.KaehlerDifferential _root_.TensorProduct _root_.MvPolynomial
open scoped TensorProduct

universe u v

theorem exists_isStandardSmooth_algHom_isUnit_det_pderiv_basis_kaehlerDifferential
    {R : Type u} [CommRing R] {ι : Type} [Finite ι] {m : ℕ} (h : Fin m → MvPolynomial (ι ⊕ Fin m) R)
        :
    ∃ (C : Type u) (_ : CommRing C) (_ : Algebra R C) (φ : MvPolynomial (ι ⊕ Fin m) R →ₐ[R] C),
      Algebra.IsStandardSmooth R C ∧
      (∀ a, φ (h a) = 0) ∧
      IsUnit (φ (Matrix.det (Matrix.of fun a b : Fin m => MvPolynomial.pderiv (Sum.inr b) (h a)))) ∧
      (∀ (B : Type u) [CommRing B] [Algebra R B] (ψ : MvPolynomial (ι ⊕ Fin m) R →ₐ[R] B),
          (∀ a, ψ (h a) = 0) →
          IsUnit (ψ (Matrix.det (Matrix.of fun a b : Fin m => MvPolynomial.pderiv (Sum.inr b) (h
              a)))) →
          ∃ χ : C →ₐ[R] B, χ.comp φ = ψ) ∧
      ∃ b : Module.Basis ι C Ω[C⁄R], ∀ i, b i = D R C (φ (MvPolynomial.X (Sum.inl i))) :=
  SubmersiveQuotient.main h

end MvPolynomial

end

section
/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned revision):
https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_Algebra_FormallySmooth_etale_aeval_of_basis_kaehlerDifferential.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/NOTICE
Upstream per-file ATTRIBUTION: https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/ATTRIBUTION.md
Copies of these notices are retained in the AbelianVarieties directory.
Existing upstream author/copyright comments in the source are retained below.

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

namespace SchemeTheory.SmoothCharts

universe u

open KaehlerDifferential

end SchemeTheory.SmoothCharts

namespace Algebra.FormallySmooth

open SchemeTheory.SmoothCharts
open _root_.KaehlerDifferential _root_.TensorProduct _root_.MvPolynomial
open scoped TensorProduct

universe u v

theorem etale_aeval_of_basis_kaehlerDifferential
    {R : Type u} [CommRing R] {A : Type u} [CommRing A] [Algebra R A]
    [Algebra.FinitePresentation R A] [Algebra.FormallySmooth R A]
    {ι : Type u} [Finite ι] (a : ι → A)
    (b : Module.Basis ι A (Ω[A⁄R])) (hb : ∀ i, b i = KaehlerDifferential.D R A (a i)) :
    (MvPolynomial.aeval a : MvPolynomial ι R →ₐ[R] A).toRingHom.Etale := by
  classical
  let algPA : Algebra (MvPolynomial ι R) A := (MvPolynomial.aeval a).toRingHom.toAlgebra
  have : IsScalarTower R (MvPolynomial ι R) A :=
    IsScalarTower.of_algebraMap_eq fun r => ((MvPolynomial.aeval a).commutes r).symm
  have halg : ∀ p : MvPolynomial ι R, algebraMap (MvPolynomial ι R) A p = MvPolynomial.aeval a p :=
    fun _ => rfl
  let b' : Module.Basis ι A (A ⊗[MvPolynomial ι R] Ω[(MvPolynomial ι R)⁄R]) :=
    Algebra.TensorProduct.basis A (KaehlerDifferential.mvPolynomialBasis R ι)
  have hX : ∀ i, KaehlerDifferential.mvPolynomialBasis R ι i =
      D R (MvPolynomial ι R) (MvPolynomial.X i) :=
    fun i => Module.Basis.apply_eq_iff.mpr (KaehlerDifferential.mvPolynomialBasis_repr_D_X R ι i)
  have hb' : ∀ i, mapBaseChange R (MvPolynomial ι R) A (b' i) = b i := by
    intro i
    rw [Algebra.TensorProduct.basis_apply, mapBaseChange_tmul, one_smul, hX, map_D, halg,
      MvPolynomial.aeval_X, hb]
  have heq : mapBaseChange R (MvPolynomial ι R) A = (b'.equiv b (Equiv.refl ι)).toLinearMap :=
    b'.ext fun i => by rw [hb', LinearEquiv.coe_toLinearMap, Module.Basis.equiv_apply,
        Equiv.refl_apply]
  have hbij : Function.Bijective (mapBaseChange R (MvPolynomial ι R) A) := by
    rw [heq]; exact (b'.equiv b (Equiv.refl ι)).bijective
  have : Algebra.FormallyEtale (MvPolynomial ι R) A :=
    Algebra.FormallyEtale.of_formallySmooth_of_bijective_mapBaseChange hbij
  have : Algebra.FinitePresentation (MvPolynomial ι R) A :=
    Algebra.FinitePresentation.of_restrict_scalars_finitePresentation R (MvPolynomial ι R) A
  have : Algebra.Etale (MvPolynomial ι R) A := ⟨inferInstance, inferInstance⟩
  exact RingHom.etale_algebraMap.mpr this

end Algebra.FormallySmooth

end

section
/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned revision):
https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_Algebra_Etale_of_basis_eq_D.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/NOTICE
Upstream per-file ATTRIBUTION: https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/ATTRIBUTION.md
Copies of these notices are retained in the AbelianVarieties directory.
Existing upstream author/copyright comments in the source are retained below.

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

namespace SchemeTheory.SmoothCharts

open KaehlerDifferential

universe u v

end SchemeTheory.SmoothCharts

namespace Algebra.Etale

open SchemeTheory.SmoothCharts
open _root_.KaehlerDifferential _root_.TensorProduct _root_.MvPolynomial
open scoped TensorProduct

universe u v

theorem of_basis_eq_D
    {R : Type u} [CommRing R] {S : Type u} [CommRing S] [Algebra R S] [Algebra.Smooth R S]
    {ι : Type v} [Finite ι] (x : ι → S) (b : Module.Basis ι S Ω[S⁄R]) (hb : ∀ i, b i = D R S (x i))
    [Algebra (MvPolynomial ι R) S] [IsScalarTower R (MvPolynomial ι R) S]
    (hx : ∀ i, algebraMap (MvPolynomial ι R) S (MvPolynomial.X i) = x i) :
    Algebra.Etale (MvPolynomial ι R) S := by
  classical
  set A := MvPolynomial ι R with hAdef
  rcases subsingleton_or_nontrivial S with hS | hS
  · infer_instance
  have : Algebra.IsStandardSmooth R S :=
    Algebra.IsStandardSmooth.of_basis_kaehlerDifferential b (by
      rintro _ ⟨i, rfl⟩; exact ⟨x i, (hb i).symm⟩)
  have hSn : Algebra.IsStandardSmoothOfRelativeDimension (Nat.card ι) R S := by
    rw [Algebra.IsStandardSmoothOfRelativeDimension.iff_of_isStandardSmooth]
    let : Fintype ι := Fintype.ofFinite ι
    rw [rank_eq_card_basis b, Nat.card_eq_fintype_card]
  have hAn : Algebra.IsStandardSmoothOfRelativeDimension (Nat.card ι) R A :=
    MvPolynomial.isStandardSmoothOfRelativeDimension_natCard R ι
  have hrange : LinearMap.range (KaehlerDifferential.mapBaseChange R A S) = ⊤ := by
    apply top_unique
    rw [← b.span_eq]
    apply Submodule.span_le.mpr
    rintro _ ⟨i, rfl⟩
    refine ⟨(1 : S) ⊗ₜ KaehlerDifferential.D R A (MvPolynomial.X i), ?_⟩
    rw [KaehlerDifferential.mapBaseChange_tmul, one_smul, KaehlerDifferential.map_D, hx, hb]
  have : Algebra.FormallyUnramified A S := by
    refine ⟨⟨fun ω₁ ω₂ => ?_⟩⟩
    have hzero : ∀ ω : Ω[S⁄A], ω = 0 := by
      intro ω
      obtain ⟨η, rfl⟩ := KaehlerDifferential.map_surjective R A S ω
      have hη : η ∈ LinearMap.ker (KaehlerDifferential.map R A S S) := by
        rw [(KaehlerDifferential.exact_mapBaseChange_map R A S).linearMap_ker_eq, hrange]
        trivial
      exact hη
    rw [hzero ω₁, hzero ω₂]
  exact Algebra.Etale.of_formallyUnramified_of_isStandardSmoothOfRelativeDimension (R := R)
      (Nat.card ι)

end Algebra.Etale

end

section
/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned revision):
https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_Algebra_exists_isStandardSmooth_surjective_localizationAway_basis_kaehlerDifferential_of_basis_residueField.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/NOTICE
Upstream per-file ATTRIBUTION: https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/ATTRIBUTION.md
Copies of these notices are retained in the AbelianVarieties directory.
Existing upstream author/copyright comments in the source are retained below.

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

namespace SchemeTheory.SmoothCharts

open TensorProduct KaehlerDifferential MvPolynomial

universe u

namespace MinimalAmbient

theorem main
    {R : Type u} [CommRing R] {S : Type u} [CommRing S] [Algebra R S] [Algebra.FinitePresentation R
        S]
    (u : Ideal S) [u.IsPrime]
    {ι : Type} [Finite ι] (w : ι → S)
    (b₀ : Module.Basis ι u.ResidueField (u.ResidueField ⊗[S] Ω[S⁄R]))
    (hb₀ : ∀ i, b₀ i = (1 : u.ResidueField) ⊗ₜ[S] D R S (w i)) :
    ∃ (g : S) (_ : g ∉ u) (C : Type u) (_ : CommRing C) (_ : Algebra R C)
      (_ : Algebra C (Localization.Away g)) (_ : IsScalarTower R C (Localization.Away g)),
      Algebra.IsStandardSmooth R C ∧ Function.Surjective (algebraMap C (Localization.Away g)) ∧
      ∃ (W : ι → C) (b : Module.Basis ι C Ω[C⁄R]),
        (∀ i, algebraMap C (Localization.Away g) (W i) = algebraMap S (Localization.Away g) (w i)) ∧
        (∀ i, b i = D R C (W i)) := by
  obtain ⟨m, x, h, hsurj, hh, hdet⟩ :=
    Algebra.FinitePresentation.exists_surjective_aeval_det_pderiv_not_mem_of_basis_residueField u w
        b₀ hb₀
  set Δ : MvPolynomial (ι ⊕ Fin m) R := Matrix.det (Matrix.of fun a b : Fin m => MvPolynomial.pderiv
      (Sum.inr b) (h a)) with hΔ
  set g : S := MvPolynomial.aeval (Sum.elim w x) Δ with hg
  obtain ⟨C, _, _, φ, hsm, hφh, hφΔ, huniv, b, hb⟩ :=
    MvPolynomial.exists_isStandardSmooth_algHom_isUnit_det_pderiv_basis_kaehlerDifferential h
  let Sg := Localization.Away g
  let ψ : MvPolynomial (ι ⊕ Fin m) R →ₐ[R] Sg :=
    (IsScalarTower.toAlgHom R S Sg).comp (MvPolynomial.aeval (Sum.elim w x))
  have hψ : ∀ p, ψ p = algebraMap S Sg (MvPolynomial.aeval (Sum.elim w x) p) := fun p => rfl
  have hψh : ∀ a, ψ (h a) = 0 := fun a => by rw [hψ, hh a, map_zero]
  have hψΔ : IsUnit (ψ Δ) := by
    rw [hψ]
    exact IsLocalization.Away.algebraMap_isUnit (S := Sg) g
  obtain ⟨χ, hχ⟩ := huniv Sg ψ hψh hψΔ
  let : Algebra C Sg := χ.toRingHom.toAlgebra
  have : IsScalarTower R C Sg := IsScalarTower.of_algebraMap_eq fun r => (χ.commutes r).symm
  refine ⟨g, hdet, C, inferInstance, inferInstance, inferInstance, inferInstance, hsm, ?_,
    fun i => φ (MvPolynomial.X (Sum.inl i)), b, ?_, hb⟩
  · intro z
    obtain ⟨⟨s, t⟩, rfl⟩ := IsLocalization.mk'_surjective (Submonoid.powers g) z
    obtain ⟨k, hk⟩ := (Submonoid.mem_powers_iff _ _).mp t.2
    obtain ⟨p, rfl⟩ := hsurj s
    obtain ⟨v, hv⟩ := hφΔ
    refine ⟨φ p * ((v⁻¹ : Cˣ) : C) ^ k, ?_⟩
    change χ (φ p * ((v⁻¹ : Cˣ) : C) ^ k) = _
    rw [IsLocalization.eq_mk'_iff_mul_eq, map_mul, map_pow]
    have h1 : χ (φ p) = algebraMap S Sg (MvPolynomial.aeval (Sum.elim w x) p) := by
      rw [← hψ, ← hχ]; rfl
    have h2 : χ ((v⁻¹ : Cˣ) : C) * algebraMap S Sg g = 1 := by
      have : χ (v : C) = algebraMap S Sg g := by rw [hv, ← hψ Δ, ← hχ]; rfl
      rw [← this, ← map_mul, Units.inv_mul, map_one]
    rw [h1, ← hk, map_pow, mul_assoc, ← mul_pow, h2, one_pow, mul_one]
  · intro i
    change χ (φ (MvPolynomial.X (Sum.inl i))) = _
    rw [← AlgHom.comp_apply, hχ, hψ, MvPolynomial.aeval_X, Sum.elim_inl]

end MinimalAmbient

end SchemeTheory.SmoothCharts

namespace Algebra

open SchemeTheory.SmoothCharts
open _root_.KaehlerDifferential _root_.TensorProduct _root_.MvPolynomial
open scoped TensorProduct

universe u v

theorem
 exists_isStandardSmooth_surjective_localizationAway_basis_kaehlerDifferential_of_basis_residueField
    {R : Type u} [CommRing R] {S : Type u} [CommRing S] [Algebra R S] [Algebra.FinitePresentation R
        S]
    (u : Ideal S) [u.IsPrime]
    {ι : Type} [Finite ι] (w : ι → S)
    (b₀ : Module.Basis ι u.ResidueField (u.ResidueField ⊗[S] Ω[S⁄R]))
    (hb₀ : ∀ i, b₀ i = (1 : u.ResidueField) ⊗ₜ[S] D R S (w i)) :
    ∃ (g : S) (_ : g ∉ u) (C : Type u) (_ : CommRing C) (_ : Algebra R C)
      (_ : Algebra C (Localization.Away g)) (_ : IsScalarTower R C (Localization.Away g)),
      Algebra.IsStandardSmooth R C ∧ Function.Surjective (algebraMap C (Localization.Away g)) ∧
      ∃ (W : ι → C) (b : Module.Basis ι C Ω[C⁄R]),
        (∀ i, algebraMap C (Localization.Away g) (W i) = algebraMap S (Localization.Away g) (w i)) ∧
        (∀ i, b i = D R C (W i)) :=
  MinimalAmbient.main u w b₀ hb₀

end Algebra

end

section
/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned revision):
https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_Algebra_exists_notMem_map_ker_eq_bot_of_surjective_of_isSmoothAt_of_finrank_le.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/NOTICE
Upstream per-file ATTRIBUTION: https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/ATTRIBUTION.md
Copies of these notices are retained in the AbelianVarieties directory.
Existing upstream author/copyright comments in the source are retained below.

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

namespace SchemeTheory.SmoothCharts

open TensorProduct KaehlerDifferential

universe u

end SchemeTheory.SmoothCharts

namespace Algebra

open SchemeTheory.SmoothCharts
open _root_.KaehlerDifferential _root_.TensorProduct _root_.MvPolynomial
open scoped TensorProduct

universe u v

theorem exists_notMem_map_ker_eq_bot_of_surjective_of_isSmoothAt_of_finrank_le
    {k : Type u} [Field k] {B : Type u} [CommRing B] [Algebra k B] [Algebra.FiniteType k B]
        [Algebra.Smooth k B]
    {B' : Type u} [CommRing B'] [Algebra k B'] (ψ : B →ₐ[k] B') (hψ : Function.Surjective ψ)
    (v' : Ideal B') [v'.IsPrime] (v : Ideal B) [v.IsPrime] (hv' : v'.comap ψ.toRingHom = v)
    (hsm : Algebra.IsSmoothAt k v')
    (hrank : Module.finrank v.ResidueField (v.ResidueField ⊗[B] Ω[B⁄k]) ≤
      Module.finrank v'.ResidueField (v'.ResidueField ⊗[B'] Ω[B'⁄k])) :
    ∃ t : B, t ∉ v ∧ (RingHom.ker ψ.toRingHom).map (algebraMap B (Localization.Away t)) = ⊥ := by
  classical
  have : IsNoetherianRing B := Algebra.FiniteType.isNoetherianRing k B
  let algBB' : Algebra B B' := ψ.toRingHom.toAlgebra
  have : IsScalarTower k B B' := IsScalarTower.of_algebraMap_eq fun c => (ψ.commutes c).symm
  set P := Localization.AtPrime v with hP
  set S := Localization.AtPrime v' with hS
  have : v'.LiesOver v := ⟨by rw [Ideal.under_def, ← hv']; rfl⟩
  let algPS : Algebra P S := Localization.AtPrime.algebraOfLiesOver v v'
  have : Algebra.FormallySmooth k S := hsm
  have halgPS : ∀ x : B, algebraMap P S (algebraMap B P x) = algebraMap B' S (ψ x) := fun x => by
    rw [Localization.AtPrime.algebraMap_eq (p := v) (P := v'), Localization.localRingHom_to_map]
    rfl
  have hPS : Function.Surjective (algebraMap P S) := by
    intro y
    obtain ⟨⟨xb, sb⟩, rfl⟩ := IsLocalization.mk'_surjective v'.primeCompl y
    obtain ⟨x, hx⟩ := hψ xb
    obtain ⟨s, hs⟩ := hψ (sb : B')
    have hsv : s ∉ v := by
      intro h; apply sb.2; rw [← hs]; rw [← hv'] at h; exact h
    refine ⟨IsLocalization.mk' P x (⟨s, hsv⟩ : v.primeCompl), ?_⟩
    rw [Localization.AtPrime.algebraMap_eq (p := v) (P := v'), Localization.localRingHom_mk']
    congr 1
    exact Subtype.ext hs
  set κ := IsLocalRing.ResidueField S with hκ
  have : IsScalarTower P S κ := inferInstance
  have : IsScalarTower B P κ := IsScalarTower.of_algebraMap_eq fun b => by
    rw [IsScalarTower.algebraMap_apply B S κ, IsScalarTower.algebraMap_apply P S κ, ←
        IsScalarTower.algebraMap_apply B P S]
  have : IsScalarTower B v.ResidueField κ := IsScalarTower.of_algebraMap_eq fun b => by
    rw [IsScalarTower.algebraMap_apply B P v.ResidueField, IsScalarTower.algebraMap_apply B P κ,
      ← IsScalarTower.algebraMap_apply P v.ResidueField κ]
  have : Algebra.FormallyEtale B P := Algebra.FormallyEtale.of_isLocalization (Rₘ := P) v.primeCompl
  have : Algebra.FormallyEtale B' S := Algebra.FormallyEtale.of_isLocalization (Rₘ := S)
      v'.primeCompl
  let eP : P ⊗[B] Ω[B⁄k] ≃ₗ[P] Ω[P⁄k] := KaehlerDifferential.tensorKaehlerEquivOfFormallyEtale k B P
  let eS : S ⊗[B'] Ω[B'⁄k] ≃ₗ[S] Ω[S⁄k] := KaehlerDifferential.tensorKaehlerEquivOfFormallyEtale k
      B' S
  have hL : Module.finrank κ (κ ⊗[S] (S ⊗[P] Ω[P⁄k])) = Module.finrank v.ResidueField
      (v.ResidueField ⊗[B] Ω[B⁄k]) := by
    have e1 : κ ⊗[S] (S ⊗[P] Ω[P⁄k]) ≃ₗ[κ] κ ⊗[P] Ω[P⁄k] :=
        TensorProduct.AlgebraTensorModule.cancelBaseChange P S κ κ Ω[P⁄k]
    have e2 : κ ⊗[P] Ω[P⁄k] ≃ₗ[κ] κ ⊗[P] (P ⊗[B] Ω[B⁄k]) := TensorProduct.AlgebraTensorModule.congr
        (LinearEquiv.refl κ κ) eP.symm
    have e3 : κ ⊗[P] (P ⊗[B] Ω[B⁄k]) ≃ₗ[κ] κ ⊗[B] Ω[B⁄k] :=
        TensorProduct.AlgebraTensorModule.cancelBaseChange B P κ κ Ω[B⁄k]
    have e4 : κ ⊗[v.ResidueField] (v.ResidueField ⊗[B] Ω[B⁄k]) ≃ₗ[κ] κ ⊗[B] Ω[B⁄k] :=
      TensorProduct.AlgebraTensorModule.cancelBaseChange B v.ResidueField κ κ Ω[B⁄k]
    rw [(e1.trans (e2.trans (e3.trans e4.symm))).finrank_eq, Module.finrank_baseChange]
  have hR : Module.finrank κ (κ ⊗[S] Ω[S⁄k]) = Module.finrank v'.ResidueField (v'.ResidueField ⊗[B']
      Ω[B'⁄k]) := by
    have e1 : κ ⊗[S] Ω[S⁄k] ≃ₗ[κ] κ ⊗[S] (S ⊗[B'] Ω[B'⁄k]) :=
        TensorProduct.AlgebraTensorModule.congr (LinearEquiv.refl κ κ) eS.symm
    have e2 : κ ⊗[S] (S ⊗[B'] Ω[B'⁄k]) ≃ₗ[κ] κ ⊗[B'] Ω[B'⁄k] :=
      TensorProduct.AlgebraTensorModule.cancelBaseChange B' S κ κ Ω[B'⁄k]
    exact (e1.trans e2).finrank_eq
  have hker := Algebra.ker_algebraMap_eq_bot_of_formallySmooth_of_finrank_le (k := k) (P := P) (S :=
      S) hPS
    (by rw [hL, hR]; exact hrank)
  have hIP : ∀ g ∈ RingHom.ker ψ.toRingHom, algebraMap B P g = 0 := by
    intro g hg
    have : algebraMap B P g ∈ RingHom.ker (algebraMap P S) := by
      rw [RingHom.mem_ker, halgPS, show ψ g = 0 from hg, map_zero]
    rwa [hker, Ideal.mem_bot] at this
  obtain ⟨G, hG⟩ := (isNoetherian_def.mp (inferInstance : IsNoetherian B B)) (RingHom.ker
      ψ.toRingHom)
  have hann : ∀ g ∈ (G : Set B), ∃ m : v.primeCompl, (m : B) * g = 0 := fun g hg =>
    (IsLocalization.map_eq_zero_iff v.primeCompl P g).mp (hIP g (hG ▸ Submodule.subset_span hg))
  choose m hm using hann
  let tM : v.primeCompl := ∏ g ∈ G.attach, m g.1 g.2
  let t : B := tM
  have ht : t = ∏ g ∈ G.attach, (m g.1 g.2 : B) := Submonoid.coe_finsetProd _ _ _
  have htv : t ∉ v := tM.2
  refine ⟨t, htv, ?_⟩
  rw [Ideal.map_eq_bot_iff_le_ker, ← hG, Ideal.span_le]
  intro g hg
  rw [SetLike.mem_coe, RingHom.mem_ker, IsLocalization.map_eq_zero_iff (Submonoid.powers t)]
  refine ⟨⟨t, Submonoid.mem_powers t⟩, ?_⟩
  change t * g = 0
  obtain ⟨u, hu⟩ : (m g hg : B) ∣ t := by
    rw [ht]; exact Finset.dvd_prod_of_mem (fun g' : {x // x ∈ G} => (m g'.1 g'.2 : B))
        (Finset.mem_attach G ⟨g, hg⟩)
  rw [hu]
  linear_combination u * hm g hg

end Algebra

end

section
/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned revision):
https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_Algebra_exists_smooth_surjective_localizationAway_basis_kaehlerDifferential_comap_eq_span.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/NOTICE
Upstream per-file ATTRIBUTION: https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/ATTRIBUTION.md
Copies of these notices are retained in the AbelianVarieties directory.
Existing upstream author/copyright comments in the source are retained below.

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

namespace SchemeTheory.SmoothCharts

open TensorProduct KaehlerDifferential

universe u

namespace ResidueBasis

theorem span_one_tmul_D_eq_top {R A κ : Type*} [CommRing R] [CommRing A] [Algebra R A] [CommRing κ]
    [Algebra A κ] :
    Submodule.span κ (Set.range fun a : A => (1 : κ) ⊗ₜ[A] D R A a) = ⊤ := by
  have h := congrArg (fun p : Submodule A Ω[A⁄R] => p.baseChange κ)
    (KaehlerDifferential.span_range_derivation R A)
  rw [Submodule.baseChange_span, Submodule.baseChange_top, ← Set.range_comp] at h
  exact h

/-- A finite basis chosen from a spanning family, adapted to a specified subfamily. -/
theorem exists_basis_adapted {A κ M : Type u} [Field κ] [AddCommGroup M] [Module κ M]
    [Module.Finite κ M] (v : A → M) (hv : Submodule.span κ (Set.range v) = ⊤)
    (J : Set A) :
    ∃ (r n : ℕ) (yb : Fin r → A) (zb : Fin n → A), (∀ j, zb j ∈ J) ∧
      (∃ b₀ : Module.Basis (Fin r ⊕ Fin n) κ M,
        ∀ i, b₀ i = v (Sum.elim yb zb i)) ∧
      (∀ z ∈ J, v z ∈ Submodule.span κ (Set.range fun j : Fin n => v (zb j))) := by
  classical
  obtain ⟨bJ, hbJJ, -, hJspan, hbJli⟩ :=
    exists_linearIndepOn_extension (K := κ) (v := v) (linearIndepOn_empty κ v) (Set.empty_subset J)
  obtain ⟨b, -, hbJb, hspan, hbli⟩ := exists_linearIndepOn_extension (K := κ) (v := v) hbJli
      (Set.subset_univ bJ)
  have htop : ⊤ ≤ Submodule.span κ (Set.range fun i : b => v i) := by
    have hr : Set.range (fun i : b => v i) = v '' b := by
      exact (Set.image_eq_range v b).symm
    rw [hr, ← hv, Submodule.span_le, ←
        Set.image_univ]
    exact hspan
  have hlin : LinearIndependent κ (fun i : b => v i) := hbli
  let B₀ : Module.Basis b κ M := Module.Basis.mk hlin htop
  have : Finite b := Module.Finite.finite_basis B₀
  have : Finite (↥(b \ bJ) : Type u) := Finite.Set.subset b Set.sdiff_subset
  have : Finite (↥bJ : Type u) := Finite.Set.subset b hbJb
  let : Fintype (↥(b \ bJ) : Type u) := Fintype.ofFinite _
  let : Fintype (↥bJ : Type u) := Fintype.ofFinite _
  set r := Fintype.card (↥(b \ bJ) : Type u) with hr
  set n := Fintype.card (↥bJ : Type u) with hn
  let eR : (↥(b \ bJ) : Type u) ≃ Fin r := Fintype.equivFin _
  let eJ : (↥bJ : Type u) ≃ Fin n := Fintype.equivFin _
  let e' : Fin r ⊕ Fin n ≃ (b : Type u) :=
    ((Equiv.sumCongr eR.symm eJ.symm).trans (Equiv.sumComm _ _)).trans (Equiv.Set.sumDiffSubset
        hbJb)
  let yb : Fin r → A := fun i => ((eR.symm i : ↥(b \ bJ)) : A)
  let zb : Fin n → A := fun j => ((eJ.symm j : ↥bJ) : A)
  refine ⟨r, n, yb, zb, fun j => hbJJ (eJ.symm j).2, ⟨B₀.reindex e'.symm, fun i => ?_⟩, fun z hz =>
      ?_⟩
  · rw [Module.Basis.reindex_apply, Equiv.symm_symm]
    change (Module.Basis.mk hlin htop) (e' i) = v (Sum.elim yb zb i)
    rw [Module.Basis.mk_apply]
    cases i <;> rfl
  · have h1 : v z ∈ Submodule.span κ (v '' bJ) := hJspan ⟨z, hz, rfl⟩
    have hsubset : v '' bJ ⊆ Set.range (fun j : Fin n => v (zb j)) := by
      rintro _ ⟨x, hx, rfl⟩
      refine ⟨eJ ⟨x, hx⟩, ?_⟩
      exact congrArg (fun y : bJ => v y) (eJ.symm_apply_apply ⟨x, hx⟩)
    exact Submodule.span_mono hsubset h1

theorem exists_b0 {R : Type u} [CommRing R] {A : Type u} [CommRing A] [Algebra R A]
    [Algebra.FiniteType R A]
    (J : Ideal A) (𝔭 : Ideal A) [𝔭.IsPrime] :
    ∃ (r n : ℕ) (yb : Fin r → A) (zb : Fin n → A), (∀ j, zb j ∈ J) ∧
      (∃ b₀ : Module.Basis (Fin r ⊕ Fin n) 𝔭.ResidueField (𝔭.ResidueField ⊗[A] Ω[A⁄R]),
        ∀ i, b₀ i = (1 : 𝔭.ResidueField) ⊗ₜ[A] D R A (Sum.elim yb zb i)) ∧
      (∀ z ∈ J, (1 : 𝔭.ResidueField) ⊗ₜ[A] D R A z ∈
        Submodule.span 𝔭.ResidueField (Set.range fun j : Fin n => (1 : 𝔭.ResidueField) ⊗ₜ[A] D R A
            (zb j))) := by
  exact exists_basis_adapted (fun a : A => (1 : 𝔭.ResidueField) ⊗ₜ[A] D R A a)
    (span_one_tmul_D_eq_top (R := R) (A := A) (κ := 𝔭.ResidueField)) (J : Set A)

theorem ker_lTensor_mapBaseChange_le_span {R : Type u} [CommRing R] {A : Type u} [CommRing A]
    [Algebra R A]
    (J : Ideal A) (κ : Type u) [Field κ] [Algebra (A ⧸ J) κ] [Algebra A κ] [IsScalarTower A (A ⧸ J)
        κ]
    (x : κ ⊗[A ⧸ J] ((A ⧸ J) ⊗[A] Ω[A⁄R]))
    (hx : LinearMap.lTensor κ (mapBaseChange R A (A ⧸ J)) x = 0) :
    x ∈ Submodule.span κ (Set.range fun z : J => (1 : κ) ⊗ₜ[A ⧸ J] ((1 : A ⧸ J) ⊗ₜ[A] D R A (z :
        A))) := by
  set B := A ⧸ J with hB
  set G := mapBaseChange R A B with hG
  have hGs : Function.Surjective G := mapBaseChange_surjective R A B Ideal.Quotient.mk_surjective
  have hex : Function.Exact (LinearMap.ker G).subtype G := LinearMap.exact_subtype_ker_map G
  have hexκ : Function.Exact (LinearMap.lTensor κ (LinearMap.ker G).subtype) (LinearMap.lTensor κ G)
      :=
    lTensor_exact (R := B) (M := LinearMap.ker G) (N := B ⊗[A] Ω[A⁄R]) (P := Ω[B⁄R]) κ hex hGs
  have hx' : x ∈ LinearMap.ker (LinearMap.lTensor κ G) := hx
  rw [hexκ.linearMap_ker_eq] at hx'
  obtain ⟨y, rfl⟩ := hx'
  clear hx
  induction y using TensorProduct.inductionOn with
  | add y₁ y₂ h₁ h₂ => rw [map_add]; exact Submodule.add_mem _ h₁ h₂
  | tmul c w =>
    rw [LinearMap.lTensor_tmul, Submodule.subtype_apply]
    have hw : (w : B ⊗[A] Ω[A⁄R]) ∈ LinearMap.range (kerCotangentToTensor R A B) := by
      rw [← (exact_kerCotangentToTensor_mapBaseChange R A B
          Ideal.Quotient.mk_surjective).linearMap_ker_eq]
      exact w.2
    obtain ⟨t, ht⟩ := hw
    obtain ⟨z, rfl⟩ := Ideal.toCotangent_surjective _ t
    rw [kerCotangentToTensor_toCotangent] at ht
    rw [← ht]
    have hz : (z : A) ∈ J := by
      have hz2 : algebraMap A B (z : A) = 0 := z.2
      exact Ideal.Quotient.eq_zero_iff_mem.mp hz2
    have : c ⊗ₜ[B] ((1 : B) ⊗ₜ[A] D R A (z : A)) = c • ((1 : κ) ⊗ₜ[B] ((1 : B) ⊗ₜ[A] D R A (z : A)))
        := by
      rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
    rw [this]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨⟨z, hz⟩, rfl⟩)

/-- Differentials are unchanged after a surjective base-ring map. -/
noncomputable def kaehlerEquivOfSurjective {R : Type u} [CommRing R] (k : Type u) [Field k] [Algebra
    R k]
    (hk : Function.Surjective (algebraMap R k)) (B : Type u) [CommRing B] [Algebra R B] [Algebra k
        B] [IsScalarTower R k B] :
    Ω[B⁄R] ≃ₗ[B] Ω[B⁄k] :=
  LinearEquiv.ofBijective (KaehlerDifferential.map R k B B) ⟨by
    have : Subsingleton Ω[k⁄R] := subsingleton_of_surjective R k hk
    rw [injective_iff_map_eq_zero]
    intro x hx
    obtain ⟨y, rfl⟩ := (exact_mapBaseChange_map R k B x).mp hx
    clear hx
    induction y using TensorProduct.inductionOn with
    | tmul b ω => rw [Subsingleton.elim ω 0, TensorProduct.tmul_zero, map_zero]
    | add y₁ y₂ h₁ h₂ =>
      rw [map_add, h₁, h₂, add_zero], KaehlerDifferential.map_surjective R k B⟩

private theorem fibreBasis
    {R : Type u} [CommRing R] {A : Type u} [CommRing A] [Algebra R A] [Algebra.FiniteType R A]
    (k : Type u) [Field k] [Algebra R k] (hk : Function.Surjective (algebraMap R k))
    (J : Ideal A) [Algebra k (A ⧸ J)] [IsScalarTower R k (A ⧸ J)]
    (𝔭 : Ideal A) [𝔭.IsPrime] (𝔮 : Ideal (A ⧸ J)) [𝔮.IsPrime] (h𝔮 : 𝔮.comap (Ideal.Quotient.mk J) =
        𝔭) :
    ∃ (r n : ℕ) (yb : Fin r → A) (zb : Fin n → A), (∀ j, zb j ∈ J) ∧
      (∃ b₀ : Module.Basis (Fin r ⊕ Fin n) 𝔭.ResidueField (𝔭.ResidueField ⊗[A] Ω[A⁄R]),
        ∀ i, b₀ i = (1 : 𝔭.ResidueField) ⊗ₜ[A] D R A (Sum.elim yb zb i)) ∧
      (∃ b₁ : Module.Basis (Fin r ⊕ Fin n) 𝔮.ResidueField (𝔮.ResidueField ⊗[A ⧸ J] ((A ⧸ J) ⊗[A]
          Ω[A⁄R])),
        ∀ i, b₁ i = (1 : 𝔮.ResidueField) ⊗ₜ[A ⧸ J] ((1 : A ⧸ J) ⊗ₜ[A] D R A (Sum.elim yb zb i))) ∧
      Module.finrank 𝔮.ResidueField (𝔮.ResidueField ⊗[A ⧸ J] Ω[(A ⧸ J)⁄k]) = r := by
  classical
  have : 𝔮.LiesOver 𝔭 := ⟨by rw [Ideal.under_def, ← h𝔮]; rfl⟩
  let algLoc : Algebra (Localization.AtPrime 𝔭) (Localization.AtPrime 𝔮) :=
    Localization.AtPrime.algebraOfLiesOver 𝔭 𝔮
  obtain ⟨r, n, yb, zb, hzb, ⟨b₀, hb₀⟩, hJ⟩ := exists_b0 (R := R) J 𝔭
  let e1 : 𝔮.ResidueField ⊗[𝔭.ResidueField] (𝔭.ResidueField ⊗[A] Ω[A⁄R]) ≃ₗ[𝔮.ResidueField]
      𝔮.ResidueField ⊗[A] Ω[A⁄R] := TensorProduct.AlgebraTensorModule.cancelBaseChange A
      𝔭.ResidueField 𝔮.ResidueField 𝔮.ResidueField Ω[A⁄R]
  let e2 : 𝔮.ResidueField ⊗[A] Ω[A⁄R] ≃ₗ[𝔮.ResidueField] 𝔮.ResidueField ⊗[(A ⧸ J)] ((A ⧸ J) ⊗[A]
      Ω[A⁄R]) := (TensorProduct.AlgebraTensorModule.cancelBaseChange A (A ⧸ J) 𝔮.ResidueField
      𝔮.ResidueField Ω[A⁄R]).symm
  let b₁ : Module.Basis (Fin r ⊕ Fin n) 𝔮.ResidueField (𝔮.ResidueField ⊗[(A ⧸ J)] ((A ⧸ J) ⊗[A]
      Ω[A⁄R])) := (Algebra.TensorProduct.basis 𝔮.ResidueField b₀).map (e1.trans e2)
  have hb₁ : ∀ i, b₁ i = (1 : 𝔮.ResidueField) ⊗ₜ[(A ⧸ J)] ((1 : (A ⧸ J)) ⊗ₜ[A] D R A (Sum.elim yb zb
      i)) := by
    intro i
    simp only [b₁, Module.Basis.map_apply, Algebra.TensorProduct.basis_apply, hb₀,
        LinearEquiv.trans_apply, e1, e2]
    rw [TensorProduct.AlgebraTensorModule.cancelBaseChange_tmul, one_smul,
      TensorProduct.AlgebraTensorModule.cancelBaseChange_symm_tmul]
  refine ⟨r, n, yb, zb, hzb, ⟨b₀, hb₀⟩, ⟨b₁, hb₁⟩, ?_⟩
  let G : 𝔮.ResidueField ⊗[(A ⧸ J)] ((A ⧸ J) ⊗[A] Ω[A⁄R]) →ₗ[𝔮.ResidueField] 𝔮.ResidueField ⊗[(A ⧸
      J)] Ω[(A ⧸ J)⁄R] :=
    TensorProduct.AlgebraTensorModule.lTensor 𝔮.ResidueField 𝔮.ResidueField (mapBaseChange R A (A ⧸
        J))
  have hGs : Function.Surjective G :=
    LinearMap.lTensor_surjective 𝔮.ResidueField (mapBaseChange_surjective R A (A ⧸ J)
        Ideal.Quotient.mk_surjective)
  have hK : LinearMap.ker G = Submodule.span 𝔮.ResidueField (Set.range (⇑b₁ ∘ Sum.inr)) := by
    apply le_antisymm
    · intro x hx
      have hx' := ker_lTensor_mapBaseChange_le_span (R := R) J 𝔮.ResidueField x hx
      refine Submodule.span_le.mpr ?_ hx'
      rintro _ ⟨z, rfl⟩
      let φ : 𝔭.ResidueField ⊗[A] Ω[A⁄R] →ₗ[𝔭.ResidueField] 𝔮.ResidueField ⊗[(A ⧸ J)] ((A ⧸ J) ⊗[A]
          Ω[A⁄R]) :=
        ((e1.trans e2).toLinearMap.restrictScalars 𝔭.ResidueField) ∘ₗ (TensorProduct.mk
            𝔭.ResidueField 𝔮.ResidueField (𝔭.ResidueField ⊗[A] Ω[A⁄R]) 1)
      have hφ : ∀ a : A, φ ((1 : 𝔭.ResidueField) ⊗ₜ[A] D R A a) = (1 : 𝔮.ResidueField) ⊗ₜ[(A ⧸ J)]
          ((1 : (A ⧸ J)) ⊗ₜ[A] D R A a) := fun a => by
        simp only [φ, LinearMap.comp_apply, TensorProduct.mk_apply, LinearMap.restrictScalars_apply,
            LinearEquiv.coe_coe,
          LinearEquiv.trans_apply, e1, e2]
        rw [TensorProduct.AlgebraTensorModule.cancelBaseChange_tmul, one_smul,
          TensorProduct.AlgebraTensorModule.cancelBaseChange_symm_tmul]
      have h1 := Submodule.mem_map_of_mem (f := φ) (hJ z z.2)
      rw [hφ, Submodule.map_span] at h1
      refine (Submodule.span_le.mpr ?_ : _ ≤ (Submodule.span 𝔮.ResidueField (Set.range (⇑b₁ ∘
          Sum.inr))).restrictScalars 𝔭.ResidueField) h1
      rintro _ ⟨_, ⟨j, rfl⟩, rfl⟩
      rw [hφ]
      exact Submodule.subset_span ⟨j, by simp only [Function.comp_apply]; rw [hb₁]; rfl⟩
    · rw [Submodule.span_le]
      rintro _ ⟨j, rfl⟩
      change G (b₁ (Sum.inr j)) = 0
      rw [hb₁]
      change (1 : 𝔮.ResidueField) ⊗ₜ[(A ⧸ J)] (mapBaseChange R A (A ⧸ J) ((1 : (A ⧸ J)) ⊗ₜ[A] D R A
          (zb j))) = 0
      rw [mapBaseChange_tmul, one_smul, KaehlerDifferential.map_D,
        show algebraMap A (A ⧸ J) (zb j) = 0 from (Ideal.Quotient.eq_zero_iff_mem.mpr (hzb j)),
            map_zero, TensorProduct.tmul_zero]
  have hfinK : Module.finrank 𝔮.ResidueField (LinearMap.ker G) = n := by
    rw [hK, finrank_span_eq_card (b₁.linearIndependent.comp Sum.inr Sum.inr_injective),
        Fintype.card_fin]
  have hfinW : Module.finrank 𝔮.ResidueField (𝔮.ResidueField ⊗[(A ⧸ J)] ((A ⧸ J) ⊗[A] Ω[A⁄R])) = r +
      n := by
    rw [Module.finrank_eq_card_basis b₁, Fintype.card_sum, Fintype.card_fin, Fintype.card_fin]
  have : Module.Finite 𝔮.ResidueField (𝔮.ResidueField ⊗[(A ⧸ J)] ((A ⧸ J) ⊗[A] Ω[A⁄R])) :=
      Module.Finite.of_basis b₁
  have hrn := LinearMap.finrank_range_add_finrank_ker G
  rw [LinearMap.range_eq_top.mpr hGs, finrank_top, hfinK, hfinW] at hrn
  have eΩ : 𝔮.ResidueField ⊗[(A ⧸ J)] Ω[(A ⧸ J)⁄R] ≃ₗ[𝔮.ResidueField] 𝔮.ResidueField ⊗[(A ⧸ J)] Ω[(A
      ⧸ J)⁄k] :=
    TensorProduct.AlgebraTensorModule.congr (LinearEquiv.refl 𝔮.ResidueField 𝔮.ResidueField)
        (kaehlerEquivOfSurjective k hk (A ⧸ J))
  rw [← eΩ.finrank_eq]
  omega

end ResidueBasis

namespace LocalizedBasis

private theorem linIndep_of_basis_localizedModule
    {R : Type u} [CommRing R] {A : Type u} [CommRing A] [Algebra R A]
    (J : Ideal A) (t : A ⧸ J) {ι : Type} (w : ι → A)
    (bM : Module.Basis ι (Localization.Away t)
      (LocalizedModule (Submonoid.powers t) ((A ⧸ J) ⊗[A] Ω[A⁄R])))
    (hbM : ∀ i, bM i = LocalizedModule.mkLinearMap (Submonoid.powers t) ((A ⧸ J) ⊗[A] Ω[A⁄R])
      ((1 : A ⧸ J) ⊗ₜ[A] D R A (w i)))
    (S : Type u) [CommRing S] [Algebra A S] [Algebra R S] [IsScalarTower R A S]
    (M : Submonoid A) [IsLocalization M S]
    (ht : IsUnit (algebraMap (A ⧸ J) (S ⧸ J.map (algebraMap A S)) t)) :
    LinearIndependent (S ⧸ J.map (algebraMap A S))
      fun i : ι => (1 : S ⧸ J.map (algebraMap A S)) ⊗ₜ[S] D R S (algebraMap A S (w i)) := by
  let algLS' : Algebra (Localization.Away t) (S ⧸ J.map (algebraMap A S)) :=
    (Localization.awayLift (algebraMap (A ⧸ J) (S ⧸ J.map (algebraMap A S))) t ht).toAlgebra
  have : IsScalarTower (A ⧸ J) (Localization.Away t) (S ⧸ J.map (algebraMap A S)) :=
    IsScalarTower.of_algebraMap_eq fun b =>
      (IsLocalization.Away.lift_eq t ht b).symm
  have : Algebra.FormallyEtale A S := Algebra.FormallyEtale.of_isLocalization (Rₘ := S) M
  have hbc := IsLocalizedModule.isBaseChange (Submonoid.powers t) (Localization.Away t)
    (LocalizedModule.mkLinearMap (Submonoid.powers t) ((A ⧸ J) ⊗[A] Ω[A⁄R]))
  let E : (S ⧸ J.map (algebraMap A S)) ⊗[Localization.Away t] LocalizedModule (Submonoid.powers t)
      ((A ⧸ J) ⊗[A] Ω[A⁄R])
      ≃ₗ[S ⧸ J.map (algebraMap A S)] (S ⧸ J.map (algebraMap A S)) ⊗[S] Ω[S⁄R] :=
    (TensorProduct.AlgebraTensorModule.congr (LinearEquiv.refl (S ⧸ J.map (algebraMap A S)) _)
        hbc.equiv.symm).trans
    ((TensorProduct.AlgebraTensorModule.cancelBaseChange (A ⧸ J) (Localization.Away t) (S ⧸ J.map
        (algebraMap A S))
      (S ⧸ J.map (algebraMap A S)) ((A ⧸ J) ⊗[A] Ω[A⁄R])).trans
    ((TensorProduct.AlgebraTensorModule.cancelBaseChange A (A ⧸ J) (S ⧸ J.map (algebraMap A S))
      (S ⧸ J.map (algebraMap A S)) Ω[A⁄R]).trans
    ((TensorProduct.AlgebraTensorModule.cancelBaseChange A S (S ⧸ J.map (algebraMap A S))
      (S ⧸ J.map (algebraMap A S)) Ω[A⁄R]).symm.trans
    (TensorProduct.AlgebraTensorModule.congr (LinearEquiv.refl (S ⧸ J.map (algebraMap A S)) _)
      (KaehlerDifferential.tensorKaehlerEquivOfFormallyEtale R A S)))))
  have key : ∀ i, E ((1 : S ⧸ J.map (algebraMap A S)) ⊗ₜ[Localization.Away t] bM i) =
      (1 : S ⧸ J.map (algebraMap A S)) ⊗ₜ[S] D R S (algebraMap A S (w i)) := by
    intro i
    rw [hbM]
    simp only [E, LinearEquiv.trans_apply, TensorProduct.AlgebraTensorModule.congr_tmul,
        LinearEquiv.refl_apply,
      IsBaseChange.equiv_symm_apply, TensorProduct.AlgebraTensorModule.cancelBaseChange_tmul,
          one_smul,
      TensorProduct.AlgebraTensorModule.cancelBaseChange_symm_tmul,
      KaehlerDifferential.tensorKaehlerEquivOfFormallyEtale_apply, mapBaseChange_tmul,
          KaehlerDifferential.map_D]
  have li := ((Algebra.TensorProduct.basis (S ⧸ J.map (algebraMap A S)) bM).map E).linearIndependent
  convert li using 1
  funext i
  rw [Module.Basis.map_apply, Algebra.TensorProduct.basis_apply, key]

end LocalizedBasis

namespace LocalizedCentre

private theorem centre_localized_smooth_and_rank
    (k : Type u) [Field k] (T : Type u) [CommRing T] [Algebra k T] [Algebra.FiniteType k T]
    (𝔮 : Ideal T) [𝔮.IsPrime] (hsmooth : Algebra.IsSmoothAt k 𝔮)
    (r : ℕ) (hrank : Module.finrank 𝔮.ResidueField (𝔮.ResidueField ⊗[T] Ω[T⁄k]) = r)
    (t : T) (ht : t ∉ 𝔮)
    (L : Type u) [CommRing L] [Algebra T L] [IsLocalization.Away t L]
    [Algebra k L] [IsScalarTower k T L] :
    ∃ (𝔮' : Ideal L) (_ : 𝔮'.IsPrime), 𝔮'.comap (algebraMap T L) = 𝔮 ∧
      Algebra.IsSmoothAt k 𝔮' ∧
      Module.finrank 𝔮'.ResidueField (𝔮'.ResidueField ⊗[L] Ω[L⁄k]) = r := by
  have hdisj : Disjoint (Submonoid.powers t : Set T) ↑𝔮 :=
    (Ideal.disjoint_powers_iff_notMem_of_isPrime t).mpr ht
  let 𝔮' : Ideal L := 𝔮.map (algebraMap T L)
  have h𝔮' : 𝔮'.IsPrime := IsLocalization.isPrime_of_isPrime_disjoint (Submonoid.powers t) L 𝔮
      inferInstance hdisj
  have hcomap : 𝔮'.comap (algebraMap T L) = 𝔮 :=
    IsLocalization.under_map_of_isPrime_disjoint (Submonoid.powers t) L inferInstance hdisj
  refine ⟨𝔮', h𝔮', hcomap, ?_, ?_⟩
  · have hpt : PrimeSpectrum.comap (algebraMap T L) ⟨𝔮', h𝔮'⟩ = ⟨𝔮, inferInstance⟩ :=
      PrimeSpectrum.ext hcomap
    have hmem : (⟨𝔮', h𝔮'⟩ : PrimeSpectrum L) ∈ Algebra.smoothLocus k L := by
      rw [← Algebra.smoothLocus_comap_of_isLocalization (R := k) (A := T) t, Set.mem_preimage, hpt]
      exact hsmooth
    exact hmem
  · have : Algebra.FormallyEtale T L := Algebra.FormallyEtale.of_isLocalization (Rₘ := L) (M :=
      Submonoid.powers t)
    let κ := 𝔮.ResidueField
    let κ' := 𝔮'.ResidueField
    let j : κ →ₐ[T] κ' :=
      Ideal.ResidueField.mapₐ 𝔮 𝔮' (IsScalarTower.toAlgHom T T L) (by
        change 𝔮 = 𝔮'.comap (algebraMap T L)
        exact hcomap.symm)
    let : Algebra κ κ' := j.toRingHom.toAlgebra
    have : IsScalarTower T κ κ' := IsScalarTower.of_algebraMap_eq fun x => (j.commutes x).symm
    let eΩ : L ⊗[T] Ω[T⁄k] ≃ₗ[L] Ω[L⁄k] := KaehlerDifferential.tensorKaehlerEquivOfFormallyEtale k T
        L
    let e1 : κ' ⊗[L] Ω[L⁄k] ≃ₗ[κ'] κ' ⊗[L] (L ⊗[T] Ω[T⁄k]) :=
      TensorProduct.AlgebraTensorModule.congr (LinearEquiv.refl κ' κ') eΩ.symm
    let e2 : κ' ⊗[L] (L ⊗[T] Ω[T⁄k]) ≃ₗ[κ'] κ' ⊗[T] Ω[T⁄k] :=
      TensorProduct.AlgebraTensorModule.cancelBaseChange T L κ' κ' Ω[T⁄k]
    let e3 : κ' ⊗[T] Ω[T⁄k] ≃ₗ[κ'] κ' ⊗[κ] (κ ⊗[T] Ω[T⁄k]) :=
      (TensorProduct.AlgebraTensorModule.cancelBaseChange T κ κ' κ' Ω[T⁄k]).symm
    rw [(e1 ≪≫ₗ e2 ≪≫ₗ e3).finrank_eq, Module.finrank_baseChange, hrank]

end LocalizedCentre

namespace CoordinateQuotient

theorem formallySmooth_quotient_span_of_basis
    {R : Type u} [CommRing R] {C : Type u} [CommRing C] [Algebra R C] [Algebra.FormallySmooth R C]
    {r n : ℕ} (W : Fin r ⊕ Fin n → C) (b : Module.Basis (Fin r ⊕ Fin n) C Ω[C⁄R])
    (hb : ∀ i, b i = D R C (W i)) :
    Algebra.FormallySmooth R (C ⧸ Ideal.span (Set.range (W ∘ Sum.inr))) := by
  classical
  set I : Ideal C := Ideal.span (Set.range (W ∘ Sum.inr)) with hI
  set K : Ideal C := RingHom.ker (algebraMap C (C ⧸ I)) with hK
  have hKI : K = I := by rw [hK, Ideal.Quotient.algebraMap_eq, Ideal.mk_ker]
  have hz : ∀ j, W (Sum.inr j) ∈ K := fun j => by rw [hKI]; exact Ideal.subset_span ⟨j, rfl⟩
  rw [Algebra.FormallySmooth.iff_split_injection (R := R) (P := C) (A := C ⧸ I)
      Ideal.Quotient.mk_surjective]
  let lam : Ω[C⁄R] →ₗ[C] K.Cotangent :=
    b.constr C (fun i => Sum.elim (fun _ => (0 : K.Cotangent)) (fun j => K.toCotangent ⟨W (Sum.inr
        j), hz j⟩) i)
  have hlam : ∀ i, lam (b i) = Sum.elim (fun _ => (0 : K.Cotangent)) (fun j => K.toCotangent ⟨W
      (Sum.inr j), hz j⟩) i :=
    fun i => b.constr_basis C _ i
  have key' : ∀ (y : C), y ∈ Submodule.span C (Set.range (W ∘ Sum.inr)) →
      ∀ hy : y ∈ K, lam (D R C y) = K.toCotangent ⟨y, hy⟩ := by
    intro y hy'
    induction hy' using Submodule.span_induction with
    | mem x hx =>
      intro hxK
      obtain ⟨j, rfl⟩ := hx
      rw [show D R C ((W ∘ Sum.inr) j) = b (Sum.inr j) from (hb _).symm, hlam]
      rfl
    | zero =>
      intro h0
      rw [map_zero, map_zero, show (⟨0, h0⟩ : K) = 0 from rfl, map_zero]
    | add x x' hx hx' ihx ihx' =>
      intro h
      have hxK : x ∈ K := by rw [hKI]; exact hx
      have hxK' : x' ∈ K := by rw [hKI]; exact hx'
      rw [map_add, map_add, ihx hxK, ihx' hxK', ← map_add]
      rfl
    | smul a x hx ihx =>
      intro h
      have hxK : x ∈ K := by rw [hKI]; exact hx
      have hD : D R C (a • x) = a • D R C x + x • D R C a := by rw [smul_eq_mul, Derivation.leibniz]
      rw [hD, map_add, map_smul, map_smul, ihx hxK, Ideal.Cotangent.smul_eq_zero_of_mem hxK,
          add_zero, ← map_smul]
      rfl
  have key : ∀ (y : C) (hy : y ∈ K), lam (D R C y) = K.toCotangent ⟨y, hy⟩ := fun y hy =>
    key' y (by rw [hKI] at hy; exact hy) hy
  let f : C →ₗ[C] (Ω[C⁄R] →ₗ[C] K.Cotangent) := LinearMap.toSpanSingleton C _ lam
  have hf : I ≤ LinearMap.ker f := by
    intro x hx
    rw [LinearMap.mem_ker]
    refine LinearMap.ext fun ω => ?_
    change (x • lam) ω = 0
    rw [LinearMap.smul_apply]
    exact Ideal.Cotangent.smul_eq_zero_of_mem (by rw [hKI]; exact hx) _
  let μ : (C ⧸ I) →ₗ[C] (Ω[C⁄R] →ₗ[C] K.Cotangent) := Submodule.liftQ (I.restrictScalars C) f hf
  let l : (C ⧸ I) ⊗[C] Ω[C⁄R] →ₗ[C] K.Cotangent := TensorProduct.lift μ
  refine ⟨l, ?_⟩
  apply LinearMap.ext
  intro t
  obtain ⟨y, rfl⟩ := K.toCotangent_surjective t
  rw [LinearMap.comp_apply, LinearMap.id_apply, kerCotangentToTensor_toCotangent]
  change TensorProduct.lift μ ((1 : C ⧸ I) ⊗ₜ[C] D R C (y : C)) = K.toCotangent y
  rw [TensorProduct.lift.tmul]
  have : μ (1 : C ⧸ I) = lam := by
    change μ (Submodule.Quotient.mk (1 : C)) = lam
    rw [show μ (Submodule.Quotient.mk (1 : C)) = f 1 from Submodule.liftQ_apply _ _ _]
    exact one_smul C lam
  rw [this, key y y.2]

end CoordinateQuotient

namespace SpecialFibre

theorem quot_smooth
    {R : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    (π : R) (hπ : IsLocalRing.maximalIdeal R = Ideal.span {π})
    {C : Type u} [CommRing C] [Algebra R C] (hC : Algebra.IsStandardSmooth R C)
    {r n : ℕ} (W : Fin r ⊕ Fin n → C) (b : Module.Basis (Fin r ⊕ Fin n) C Ω[C⁄R])
    (hb : ∀ i, b i = D R C (W i))
    (JC : Ideal C) (hJC : JC = Ideal.span (insert (algebraMap R C π) (Set.range (W ∘ Sum.inr))))
    [Algebra (IsLocalRing.ResidueField R) (C ⧸ JC)] [IsScalarTower R (IsLocalRing.ResidueField R) (C
        ⧸ JC)] :
    Algebra.FiniteType (IsLocalRing.ResidueField R) (C ⧸ JC) ∧
    Algebra.Smooth (IsLocalRing.ResidueField R) (C ⧸ JC) := by
  classical
  have : Algebra.IsStandardSmooth R C := hC
  have : Algebra.Smooth R C := inferInstance
  set I : Ideal C := Ideal.span (Set.range (W ∘ Sum.inr)) with hI
  have hIJ : I ≤ JC := by
    rw [hJC]; exact Ideal.span_mono (Set.subset_insert _ _)
  have : Algebra.FormallySmooth R (C ⧸ I) :=
      CoordinateQuotient.formallySmooth_quotient_span_of_basis W b hb
  have : Algebra.FinitePresentation R (C ⧸ I) :=
    Algebra.FinitePresentation.quotient (Submodule.fg_span (Set.finite_range _))
  have : Algebra.Smooth R (C ⧸ I) := ⟨‹_›, ‹_›⟩
  have hk_surj : Function.Surjective (algebraMap R (IsLocalRing.ResidueField R)) :=
      Ideal.Quotient.mk_surjective
  have hpizero : algebraMap R (IsLocalRing.ResidueField R) π = 0 := by
    rw [IsLocalRing.ResidueField.algebraMap_eq, IsLocalRing.residue_eq_zero_iff, hπ]
    exact Ideal.subset_span rfl
  have : Algebra.Smooth (IsLocalRing.ResidueField R) ((IsLocalRing.ResidueField R) ⊗[R] (C ⧸ I)) :=
      inferInstance
  let g : C ⧸ I →ₐ[R] C ⧸ JC := Ideal.Quotient.liftₐ I (Ideal.Quotient.mkₐ R JC) (fun a ha =>
    Ideal.Quotient.eq_zero_iff_mem.mpr (hIJ ha))
  let toF : (IsLocalRing.ResidueField R) ⊗[R] (C ⧸ I) →ₐ[(IsLocalRing.ResidueField R)] C ⧸ JC :=
    Algebra.TensorProduct.lift (Algebra.ofId (IsLocalRing.ResidueField R) (C ⧸ JC)) g (fun _ _ =>
        Commute.all _ _)
  let g' : C →ₐ[R] (IsLocalRing.ResidueField R) ⊗[R] (C ⧸ I) :=
      Algebra.TensorProduct.includeRight.comp (Ideal.Quotient.mkₐ R I)
  have hg' : ∀ a ∈ JC, g' a = 0 := by
    intro a ha
    rw [hJC] at ha
    have : JC ≤ RingHom.ker g'.toRingHom := by
      rw [hJC, Ideal.span_le]
      rintro x hx
      rw [SetLike.mem_coe, RingHom.mem_ker]
      rcases hx with rfl | ⟨j, rfl⟩
      · change (1 : (IsLocalRing.ResidueField R)) ⊗ₜ[R] (Ideal.Quotient.mk I (algebraMap R C π)) = 0
        rw [← Ideal.Quotient.algebraMap_eq, ← IsScalarTower.algebraMap_apply,
            Algebra.algebraMap_eq_smul_one,
          ← TensorProduct.smul_tmul, Algebra.smul_def, mul_one, hpizero, TensorProduct.zero_tmul]
      · change (1 : (IsLocalRing.ResidueField R)) ⊗ₜ[R] (Ideal.Quotient.mk I ((W ∘ Sum.inr) j)) = 0
        rw [Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span (Set.mem_range_self j)),
            TensorProduct.tmul_zero]
    exact this (hJC ▸ ha)
  let inv : C ⧸ JC →ₐ[R] (IsLocalRing.ResidueField R) ⊗[R] (C ⧸ I) := Ideal.Quotient.liftₐ JC g' hg'
  have hinv_to : ∀ x, inv (toF x) = x := by
    have : (inv.comp (toF.restrictScalars R)) = AlgHom.id R _ := by
      apply Algebra.TensorProduct.ext'
      intro a c
      obtain ⟨s, rfl⟩ := hk_surj a
      obtain ⟨c, rfl⟩ := Ideal.Quotient.mk_surjective c
      simp only [AlgHom.comp_apply, AlgHom.id_apply]
      have hsplit : algebraMap R (IsLocalRing.ResidueField R) s ⊗ₜ[R] (Ideal.Quotient.mk I c) =
          algebraMap R ((IsLocalRing.ResidueField R) ⊗[R] (C ⧸ I)) s *
            ((1 : (IsLocalRing.ResidueField R)) ⊗ₜ[R] Ideal.Quotient.mk I c) := by
        rw [Algebra.TensorProduct.algebraMap_apply, Algebra.TensorProduct.tmul_mul_tmul, mul_one,
            one_mul]
      rw [hsplit, map_mul, map_mul, AlgHom.commutes, AlgHom.commutes]
      congr 1
      rw [AlgHom.restrictScalars_apply]
      change inv (toF ((1 : (IsLocalRing.ResidueField R)) ⊗ₜ[R] (Ideal.Quotient.mk I c))) = _
      rw [Algebra.TensorProduct.lift_tmul]
      change inv (algebraMap (IsLocalRing.ResidueField R) (C ⧸ JC) 1 * g (Ideal.Quotient.mk I c)) =
          _
      rw [map_one, one_mul]
      rfl
    intro x
    exact congrArg (fun φ : (IsLocalRing.ResidueField R) ⊗[R] (C ⧸ I) →ₐ[R]
        (IsLocalRing.ResidueField R) ⊗[R] (C ⧸ I) => φ x) this
  have hto_surj : Function.Surjective toF := by
    intro y
    obtain ⟨c, rfl⟩ := Ideal.Quotient.mk_surjective y
    refine ⟨(1 : (IsLocalRing.ResidueField R)) ⊗ₜ[R] Ideal.Quotient.mk I c, ?_⟩
    rw [Algebra.TensorProduct.lift_tmul]
    change algebraMap (IsLocalRing.ResidueField R) (C ⧸ JC) 1 * g (Ideal.Quotient.mk I c) = _
    rw [map_one, one_mul]
    rfl
  have hto_inj : Function.Injective toF := fun x y hxy => by
    rw [← hinv_to x, ← hinv_to y, hxy]
  let e : (IsLocalRing.ResidueField R) ⊗[R] (C ⧸ I) ≃ₐ[(IsLocalRing.ResidueField R)] C ⧸ JC :=
      AlgEquiv.ofBijective toF ⟨hto_inj, hto_surj⟩
  have : Algebra.FormallySmooth (IsLocalRing.ResidueField R) (C ⧸ JC) :=
      Algebra.FormallySmooth.of_equiv e
  have : Algebra.FinitePresentation (IsLocalRing.ResidueField R) (C ⧸ JC) :=
      Algebra.FinitePresentation.equiv e
  exact ⟨inferInstance, ⟨‹_›, ‹_›⟩⟩

end SpecialFibre

namespace ChartTransport

theorem quot_rank
    {R : Type u} [CommRing R]
    (π : R) (k : Type u) [Field k] [Algebra R k]
    {C : Type u} [CommRing C] [Algebra R C]
    {r n : ℕ} (W : Fin r ⊕ Fin n → C) (b : Module.Basis (Fin r ⊕ Fin n) C Ω[C⁄R])
    (hb : ∀ i, b i = D R C (W i))
    (JC : Ideal C) (hJC : JC = Ideal.span (insert (algebraMap R C π) (Set.range (W ∘ Sum.inr))))
    [Algebra k (C ⧸ JC)] [IsScalarTower R k (C ⧸ JC)]
    (v : Ideal (C ⧸ JC)) [v.IsPrime] :
    Module.finrank v.ResidueField (v.ResidueField ⊗[C ⧸ JC] Ω[(C ⧸ JC)⁄k]) ≤ r := by
  classical
  let u : Fin r → Ω[(C ⧸ JC)⁄k] := fun i => D k (C ⧸ JC) (algebraMap C (C ⧸ JC) (W (Sum.inl i)))
  have hz0 : ∀ j : Fin n, algebraMap C (C ⧸ JC) (W (Sum.inr j)) = 0 := by
    intro j
    rw [Ideal.Quotient.algebraMap_eq, Ideal.Quotient.eq_zero_iff_mem, hJC]
    exact Ideal.subset_span (Set.mem_insert_of_mem _ ⟨j, rfl⟩)
  have hspanB : Submodule.span (C ⧸ JC) (Set.range u) = ⊤ := by
    rw [eq_top_iff, ← KaehlerDifferential.span_range_derivation, Submodule.span_le]
    rintro _ ⟨x, rfl⟩
    obtain ⟨c, rfl⟩ := Ideal.Quotient.mk_surjective x
    have h1 : D k (C ⧸ JC) (Ideal.Quotient.mk JC c) = KaehlerDifferential.map R k C (C ⧸ JC) (D R C
        c) := by
      rw [KaehlerDifferential.map_D]; rfl
    rw [SetLike.mem_coe, h1, ← b.sum_repr (D R C c), map_sum]
    refine Submodule.sum_mem _ fun i _ => ?_
    rw [LinearMap.map_smul_of_tower, hb, KaehlerDifferential.map_D]
    refine Submodule.smul_of_tower_mem _ _ ?_
    rcases i with i | j
    · exact Submodule.subset_span ⟨i, rfl⟩
    · rw [hz0 j, map_zero]; exact Submodule.zero_mem _
  let u' : Fin r → v.ResidueField ⊗[(C ⧸ JC)] Ω[(C ⧸ JC)⁄k] := fun i => (1 : v.ResidueField) ⊗ₜ[(C ⧸
      JC)] u i
  have hspanFibre : Submodule.span v.ResidueField (Set.range u') = ⊤ := by
    have h := congrArg (fun p : Submodule (C ⧸ JC) Ω[(C ⧸ JC)⁄k] =>
      p.baseChange v.ResidueField) hspanB
    rw [Submodule.baseChange_span, Submodule.baseChange_top, ← Set.range_comp] at h
    exact h
  rw [← finrank_top, ← hspanFibre]
  exact (finrank_range_le_card u').trans_eq (Fintype.card_fin r)

theorem quot_smooth_and_rank
    {R : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    (π : R) (hπ : IsLocalRing.maximalIdeal R = Ideal.span {π})
    {C : Type u} [CommRing C] [Algebra R C] (hC : Algebra.IsStandardSmooth R C)
    {r n : ℕ} (W : Fin r ⊕ Fin n → C) (b : Module.Basis (Fin r ⊕ Fin n) C Ω[C⁄R])
    (hb : ∀ i, b i = D R C (W i))
    (JC : Ideal C) (hJC : JC = Ideal.span (insert (algebraMap R C π) (Set.range (W ∘ Sum.inr))))
    [Algebra (IsLocalRing.ResidueField R) (C ⧸ JC)] [IsScalarTower R (IsLocalRing.ResidueField R) (C
        ⧸ JC)] :
    Algebra.FiniteType (IsLocalRing.ResidueField R) (C ⧸ JC) ∧
    Algebra.Smooth (IsLocalRing.ResidueField R) (C ⧸ JC) ∧
    ∀ (v : Ideal (C ⧸ JC)) [v.IsPrime],
      Module.finrank v.ResidueField (v.ResidueField ⊗[C ⧸ JC] Ω[(C ⧸ JC)⁄IsLocalRing.ResidueField
          R]) ≤ r := by
  obtain ⟨h1, h2⟩ := SpecialFibre.quot_smooth π hπ hC W b hb JC hJC
  exact ⟨h1, h2, fun v _ => quot_rank π (IsLocalRing.ResidueField R) W
      b hb JC hJC v⟩

end ChartTransport

namespace ChartTransport

theorem linearIndependent_of_semilinear
    {R₁ R₂ : Type*} [Ring R₁] [Ring R₂] {M₁ M₂ : Type*} [AddCommGroup M₁] [AddCommGroup M₂]
    [Module R₁ M₁] [Module R₂ M₂] (σ : R₁ →+* R₂) (hσ : Function.Injective σ)
    (j : M₁ →+ M₂) (hj : ∀ (r : R₁) (m : M₁), j (r • m) = σ r • j m)
    {ι : Type*} (v : ι → M₁) (hv : LinearIndependent R₂ (j ∘ v)) : LinearIndependent R₁ v := by
  classical
  rw [linearIndependent_iff'] at hv ⊢
  intro s g hg i hi
  have h := congrArg j hg
  rw [map_sum, map_zero] at h
  simp_rw [hj] at h
  have := hv s (fun i => σ (g i)) (by simpa only [Function.comp_apply] using h) i hi
  exact hσ ((show σ (g i) = 0 from this).trans (map_zero σ).symm)

theorem finalTransport
    {R : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    (π : R) {A : Type u} [CommRing A] [Algebra R A]
    (J : Ideal A) (𝔭 : Ideal A) [𝔭.IsPrime]
    {r n : ℕ} (yb : Fin r → A) (zb : Fin n → A)
    (g₁ : A) (hg₁ : g₁ ∉ 𝔭) (C : Type u) [CommRing C] [Algebra R C]
    [Algebra C (Localization.Away g₁)] [IsScalarTower R C (Localization.Away g₁)]
    (hCstd : Algebra.IsStandardSmooth R C) (hθ : Function.Surjective (algebraMap C
        (Localization.Away g₁)))
    (W : Fin r ⊕ Fin n → C) (b : Module.Basis (Fin r ⊕ Fin n) C Ω[C⁄R])
    (hW : ∀ i, algebraMap C (Localization.Away g₁) (W i) = algebraMap A (Localization.Away g₁)
        (Sum.elim yb zb i))
    (hb : ∀ i, b i = D R C (W i))
    (c : C) (a : A) (ha : a ∉ 𝔭) (hca : algebraMap C (Localization.Away g₁) c = algebraMap A
        (Localization.Away g₁) a)
    (hIdeal : (Ideal.comap (algebraMap C (Localization.Away g₁)) (J.map (algebraMap A
        (Localization.Away g₁)))).map
        (algebraMap C (Localization.Away c)) =
      (Ideal.span (insert (algebraMap R C π) (Set.range (W ∘ Sum.inr)))).map (algebraMap C
          (Localization.Away c)))
    (g₂ : A) (hg₂a : g₂ ∣ a)
    (hlinS : ∀ (S : Type u) [CommRing S] [Algebra A S] [Algebra R S] [IsScalarTower R A S]
      (M : Submonoid A) [IsLocalization M S],
      IsUnit (algebraMap A S g₂) →
      LinearIndependent (S ⧸ J.map (algebraMap A S))
        fun j : Fin n => (1 : S ⧸ J.map (algebraMap A S)) ⊗ₜ[S] D R S (algebraMap A S (zb j))) :
    ∃ (g : A) (_ : g ∉ 𝔭) (r n : ℕ) (C : Type u) (_ : CommRing C) (_ : Algebra R C)
      (_ : Algebra C (Localization.Away g)) (_ : IsScalarTower R C (Localization.Away g)),
      Algebra.Smooth R C ∧ Function.Surjective (algebraMap C (Localization.Away g)) ∧
      ∃ (y : Fin r → C) (z : Fin n → C) (b : Module.Basis (Fin r ⊕ Fin n) C Ω[C⁄R]),
        (∀ i, b (Sum.inl i) = D R C (y i)) ∧ (∀ j, b (Sum.inr j) = D R C (z j)) ∧
        Ideal.comap (algebraMap C (Localization.Away g)) (J.map (algebraMap A (Localization.Away
            g))) =
          Ideal.span (insert (algebraMap R C π) (Set.range z)) ∧
        LinearIndependent (C ⧸ Ideal.span (insert (algebraMap R C π) (Set.range z)))
          fun j : Fin n => (1 : C ⧸ Ideal.span (insert (algebraMap R C π) (Set.range z))) ⊗ₜ[C]
            D R (Localization.Away g) (algebraMap C (Localization.Away g) (z j)) := by
  classical
  let θ : C →ₐ[R] (Localization.Away g₁) := ⟨algebraMap C (Localization.Away g₁), fun r' =>
      (IsScalarTower.algebraMap_apply R C (Localization.Away g₁) r').symm⟩
  have hAwayθc : IsLocalization.Away (θ c) (Localization.Away (algebraMap A (Localization.Away g₁)
      a)) := by
    change IsLocalization.Away (algebraMap C (Localization.Away g₁) c) (Localization.Away
        (algebraMap A (Localization.Away g₁) a)); rw [hca]; infer_instance
  let φT : (Localization.Away c) →ₐ[R] (Localization.Away (algebraMap A (Localization.Away g₁) a))
      := IsLocalization.Away.mapₐ (Localization.Away c) (Localization.Away (algebraMap A
      (Localization.Away g₁) a)) θ c
  have hφT_surj : Function.Surjective φT := IsLocalization.Away.mapₐ_surjective_of_surjective c hθ
  have hφT_apply : ∀ x : C, φT (algebraMap C (Localization.Away c) x) = algebraMap
      (Localization.Away g₁) (Localization.Away (algebraMap A (Localization.Away g₁) a)) (algebraMap
      C (Localization.Away g₁) x) := by
    intro x
    rw [IsLocalization.Away.mapₐ_apply]
    exact IsLocalization.map_eq _ _
  let e : (Localization.Away (algebraMap A (Localization.Away g₁) a)) ≃ₐ[A] (Localization.Away (g₁ *
      a)) := IsLocalization.algEquiv (Submonoid.powers (g₁ * a)) (Localization.Away (algebraMap A
      (Localization.Away g₁) a)) (Localization.Away (g₁ * a))
  let φ : (Localization.Away c) →+* (Localization.Away (g₁ * a)) := (e : (Localization.Away
      (algebraMap A (Localization.Away g₁) a)) →+* (Localization.Away (g₁ * a))).comp φT.toRingHom
  let iCSg : Algebra (Localization.Away c) (Localization.Away (g₁ * a)) := φ.toAlgebra
  have hφ_alg : ∀ x : (Localization.Away c), algebraMap (Localization.Away c) (Localization.Away (g₁
      * a)) x = e (φT x) := fun _ => rfl
  have hφC : ∀ x : C, algebraMap (Localization.Away c) (Localization.Away (g₁ * a)) (algebraMap C
      (Localization.Away c) x) = e (algebraMap (Localization.Away g₁) (Localization.Away (algebraMap
      A (Localization.Away g₁) a)) (algebraMap C (Localization.Away g₁) x)) := by
    intro x; rw [hφ_alg, hφT_apply]
  have heA₁ : ∀ y : A, e (algebraMap (Localization.Away g₁) (Localization.Away (algebraMap A
      (Localization.Away g₁) a)) (algebraMap A (Localization.Away g₁) y)) = algebraMap A
      (Localization.Away (g₁ * a)) y := by
    intro y
    rw [← IsScalarTower.algebraMap_apply A (Localization.Away g₁) (Localization.Away (algebraMap A
        (Localization.Away g₁) a))]
    exact e.commutes y
  have : IsScalarTower R (Localization.Away c) (Localization.Away (g₁ * a)) :=
      IsScalarTower.of_algebraMap_eq' (by
    ext r'
    rw [RingHom.comp_apply, IsScalarTower.algebraMap_apply R C (Localization.Away c), hφC,
      ← IsScalarTower.algebraMap_apply R C (Localization.Away g₁), IsScalarTower.algebraMap_apply R
          A (Localization.Away g₁), heA₁,
      IsScalarTower.algebraMap_apply R A (Localization.Away (g₁ * a))])
  have : Algebra.IsStandardSmooth R C := hCstd
  have : Algebra.IsStandardSmooth C (Localization.Away c) :=
      Algebra.IsStandardSmooth.localization_away c
  have : Algebra.IsStandardSmooth R (Localization.Away c) := Algebra.IsStandardSmooth.trans R C
      (Localization.Away c)
  have hCsm : Algebra.Smooth R (Localization.Away c) := inferInstance
  have hsurj : Function.Surjective (algebraMap (Localization.Away c) (Localization.Away (g₁ * a)))
      := by
    intro s; obtain ⟨t, rfl⟩ := e.surjective s; obtain ⟨x, rfl⟩ := hφT_surj t; exact ⟨x, rfl⟩
  let z' : Fin n → (Localization.Away c) := fun j => algebraMap C (Localization.Away c) (W (Sum.inr
      j))
  let b' : Module.Basis (Fin r ⊕ Fin n) (Localization.Away c) Ω[(Localization.Away c)⁄R] :=
    b.ofIsLocalizedModule (Localization.Away c) (Submonoid.powers c) (KaehlerDifferential.map R R C
        (Localization.Away c))
  have hb' : ∀ i, b' i = D R (Localization.Away c) (algebraMap C (Localization.Away c) (W i)) := by
    intro i
    rw [Module.Basis.ofIsLocalizedModule_apply, hb, KaehlerDifferential.map_D]
  have hz'S : ∀ j, algebraMap (Localization.Away c) (Localization.Away (g₁ * a)) (z' j) = algebraMap
      A (Localization.Away (g₁ * a)) (zb j) := by
    intro j; change algebraMap (Localization.Away c) (Localization.Away (g₁ * a)) (algebraMap C
        (Localization.Away c) (W (Sum.inr j))) = _; rw [hφC, hW, Sum.elim_inr, heA₁]
  have hspan_map : (Ideal.span (insert (algebraMap R C π) (Set.range (W ∘ Sum.inr)))).map
      (algebraMap C (Localization.Away c)) =
      Ideal.span (insert (algebraMap R (Localization.Away c) π) (Set.range z')) := by
    rw [Ideal.map_span, Set.image_insert_eq, ← Set.range_comp, ← IsScalarTower.algebraMap_apply R C
        (Localization.Away c)]
    rfl
  have hmapJ : (J.map (algebraMap A (Localization.Away g₁))).map ((e : (Localization.Away
      (algebraMap A (Localization.Away g₁) a)) →+* (Localization.Away (g₁ * a))).comp (algebraMap
      (Localization.Away g₁) (Localization.Away (algebraMap A (Localization.Away g₁) a)))) =
      J.map (algebraMap A (Localization.Away (g₁ * a))) := by
    rw [Ideal.map_map]; congr 1; ext y; exact heA₁ y
  have hmem_e : ∀ (I : Ideal (Localization.Away (algebraMap A (Localization.Away g₁) a))) (y :
      (Localization.Away (algebraMap A (Localization.Away g₁) a))), e y ∈ I.map (e :
      (Localization.Away (algebraMap A (Localization.Away g₁) a)) →+* (Localization.Away (g₁ * a)))
      → y ∈ I := by
    intro I y hy
    have h := Ideal.mem_map_of_mem (e.symm : (Localization.Away (g₁ * a)) →+* (Localization.Away
        (algebraMap A (Localization.Away g₁) a))) hy
    rw [Ideal.map_map] at h
    have hcomp : (e.symm : (Localization.Away (g₁ * a)) →+* (Localization.Away (algebraMap A
        (Localization.Away g₁) a))).comp (e : (Localization.Away (algebraMap A (Localization.Away
        g₁) a)) →+* (Localization.Away (g₁ * a))) = RingHom.id _ := by
      ext t; exact e.symm_apply_apply t
    rw [hcomp, Ideal.map_id] at h
    change e.symm (e y) ∈ I at h
    rwa [e.symm_apply_apply] at h
  have hJC' : Ideal.comap (algebraMap (Localization.Away c) (Localization.Away (g₁ * a))) (J.map
      (algebraMap A (Localization.Away (g₁ * a)))) =
      Ideal.span (insert (algebraMap R (Localization.Away c) π) (Set.range z')) := by
    rw [← hspan_map, ← hIdeal]
    apply le_antisymm
    · intro x' hx'
      rw [Ideal.mem_comap] at hx'
      obtain ⟨m, x, hmx⟩ := IsLocalization.Away.surj c x'
      have h1 : algebraMap (Localization.Away c) (Localization.Away (g₁ * a)) (algebraMap C
          (Localization.Away c) x) ∈ J.map (algebraMap A (Localization.Away (g₁ * a))) := by
        rw [← hmx, map_mul, map_pow]
        exact Ideal.mul_mem_right _ _ hx'
      rw [hφC, ← hmapJ, ← Ideal.map_map] at h1
      have h2 := hmem_e _ _ h1
      rw [IsLocalization.algebraMap_mem_map_algebraMap_iff (Submonoid.powers (algebraMap A
          (Localization.Away g₁) a))] at h2
      obtain ⟨_, ⟨m', rfl⟩, hm'⟩ := h2
      beta_reduce at hm'
      rw [← hca, ← map_pow, ← map_mul] at hm'
      have h3 : c ^ m' * x ∈ Ideal.comap (algebraMap C (Localization.Away g₁)) (J.map (algebraMap A
          (Localization.Away g₁))) := by
        rw [Ideal.mem_comap]; exact hm'
      have h4 := Ideal.mem_map_of_mem (algebraMap C (Localization.Away c)) h3
      rw [map_mul, map_pow] at h4
      have hcu : IsUnit (algebraMap C (Localization.Away c) c ^ m') :=
          (IsLocalization.Away.algebraMap_isUnit c).pow m'
      rw [Ideal.unit_mul_mem_iff_mem _ hcu] at h4
      have hcu' : IsUnit (algebraMap C (Localization.Away c) c ^ m) :=
          (IsLocalization.Away.algebraMap_isUnit c).pow m
      rw [← Ideal.unit_mul_mem_iff_mem _ hcu', mul_comm, hmx]
      exact h4
    · rw [Ideal.map_le_iff_le_comap]
      intro x hx
      rw [Ideal.mem_comap, Ideal.mem_comap, hφC, ← hmapJ, ← Ideal.map_map]
      apply Ideal.mem_map_of_mem
      apply Ideal.mem_map_of_mem
      rw [Ideal.mem_comap] at hx
      exact hx
  have hg₂unit : IsUnit (algebraMap A (Localization.Away (g₁ * a)) g₂) :=
    IsLocalization.Away.isUnit_of_dvd (g₁ * a) (hg₂a.trans (Dvd.intro_left g₁ rfl))
  have hlin0 := hlinS (Localization.Away (g₁ * a)) (Submonoid.powers (g₁ * a)) hg₂unit
  let Qc := (Localization.Away c) ⧸
    Ideal.span (insert (algebraMap R (Localization.Away c) π) (Set.range z'))
  let Qs := (Localization.Away (g₁ * a)) ⧸
    J.map (algebraMap A (Localization.Away (g₁ * a)))
  have hlin : LinearIndependent Qc
      fun j : Fin n => (1 : (Localization.Away c) ⧸ Ideal.span (insert (algebraMap R
          (Localization.Away c) π) (Set.range z'))) ⊗ₜ[(Localization.Away c)]
        D R (Localization.Away (g₁ * a)) (algebraMap (Localization.Away c) (Localization.Away (g₁ *
            a)) (z' j)) := by
    have hle : Ideal.span (insert (algebraMap R (Localization.Away c) π) (Set.range z')) ≤ (J.map
        (algebraMap A (Localization.Away (g₁ * a)))).comap (algebraMap (Localization.Away c)
        (Localization.Away (g₁ * a))) :=
      hJC'.symm.le
    let σ : Qc →+* Qs :=
      Ideal.quotientMap (J.map (algebraMap A (Localization.Away (g₁ * a)))) (algebraMap
          (Localization.Away c) (Localization.Away (g₁ * a))) hle
    have hσmk : ∀ x : (Localization.Away c), σ (Ideal.Quotient.mk _ x) = Ideal.Quotient.mk _
        (algebraMap (Localization.Away c) (Localization.Away (g₁ * a)) x) :=
      fun x => Ideal.quotientMap_mk
    have hσ : Function.Injective σ := Ideal.quotientMap_injective' hJC'.le
    let j0 : Qc →+ (Ω[(Localization.Away (g₁ * a))⁄R] →+ (Qs ⊗[(Localization.Away (g₁ * a))]
        Ω[(Localization.Away (g₁ * a))⁄R])) :=
      { toFun := fun x => (TensorProduct.mk (Localization.Away (g₁ * a)) Qs Ω[(Localization.Away (g₁
          * a))⁄R] (σ x)).toAddMonoidHom
        map_zero' := by
          ext ω
          exact (congrArg (fun q => q ⊗ₜ[(Localization.Away (g₁ * a))] ω) (map_zero σ)).trans
            (TensorProduct.zero_tmul _ ω)
        map_add' := fun x y => by
          ext ω
          exact (congrArg (fun q => q ⊗ₜ[(Localization.Away (g₁ * a))] ω) (map_add σ x y)).trans
            (TensorProduct.add_tmul _ _ ω) }
    have hj0 : ∀ x ω, j0 x ω = σ x ⊗ₜ[(Localization.Away (g₁ * a))] ω := fun _ _ => rfl
    let j : Qc ⊗[(Localization.Away c)] Ω[(Localization.Away (g₁ * a))⁄R] →+ Qs ⊗[(Localization.Away
        (g₁ * a))] Ω[(Localization.Away (g₁ * a))⁄R] :=
      TensorProduct.liftAddHom j0 (fun r' x ω => by
        rw [hj0, hj0]
        obtain ⟨x0, rfl⟩ := Ideal.Quotient.mk_surjective x
        have e1 : r' • Ideal.Quotient.mk (Ideal.span (insert (algebraMap R (Localization.Away c) π)
            (Set.range z'))) x0 =
            Ideal.Quotient.mk _ (r' * x0) := rfl
        rw [e1, hσmk, hσmk, map_mul, ← algebraMap_smul (A := (Localization.Away (g₁ * a))) r' ω,
            TensorProduct.tmul_smul,
          TensorProduct.smul_tmul']
        rfl)
    have hjt : ∀ (x : Qc) (ω : Ω[(Localization.Away (g₁ * a))⁄R]), j (x ⊗ₜ ω) = σ x ⊗ₜ ω := fun x ω
        => by
      change j0 x ω = _; rw [hj0]
    have hj : ∀ (r' : Qc) (m : Qc ⊗[(Localization.Away c)] Ω[(Localization.Away (g₁ * a))⁄R]), j (r'
        • m) = σ r' • j m := by
      intro r' m
      induction m using TensorProduct.inductionOn with
      | tmul x ω =>
        rw [TensorProduct.smul_tmul', smul_eq_mul, hjt, hjt, map_mul, TensorProduct.smul_tmul',
            smul_eq_mul]
      | add m₁ m₂ h₁ h₂ => rw [smul_add, map_add, h₁, h₂, map_add, smul_add]
    refine linearIndependent_of_semilinear σ hσ j hj _ ?_
    have : (j ∘ fun j' : Fin n => (1 : Qc) ⊗ₜ[(Localization.Away c)] D R (Localization.Away (g₁ *
        a)) (algebraMap (Localization.Away c) (Localization.Away (g₁ * a)) (z' j'))) =
        fun j' : Fin n => (1 : (Localization.Away (g₁ * a)) ⧸ J.map (algebraMap A (Localization.Away
            (g₁ * a)))) ⊗ₜ[(Localization.Away (g₁ * a))] D R (Localization.Away (g₁ * a))
            (algebraMap A (Localization.Away (g₁ * a)) (zb j')) := by
      funext j'
      simp only [Function.comp_apply]
      rw [hjt, map_one, hz'S]
    rw [this]
    exact hlin0
  refine ⟨g₁ * a, fun h => (Ideal.IsPrime.mem_or_mem ‹𝔭.IsPrime› h).elim hg₁ ha, r, n,
      (Localization.Away c), inferInstance,
    inferInstance, iCSg, inferInstance, hCsm, hsurj, fun i => algebraMap C (Localization.Away c) (W
        (Sum.inl i)), z', b',
    fun i => hb' (Sum.inl i), fun j => hb' (Sum.inr j), hJC', hlin⟩

end ChartTransport

end SchemeTheory.SmoothCharts

namespace Algebra

open SchemeTheory.SmoothCharts
open _root_.KaehlerDifferential _root_.TensorProduct _root_.MvPolynomial
open scoped TensorProduct

universe u v

theorem exists_smooth_surjective_localizationAway_basis_kaehlerDifferential_comap_eq_span
    {R : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    (π : R) (hπ : IsLocalRing.maximalIdeal R = Ideal.span {π})
    {A : Type u} [CommRing A] [Algebra R A] [Algebra.FiniteType R A]
    (J : Ideal A) (hπJ : algebraMap R A π ∈ J)
    [Algebra (IsLocalRing.ResidueField R) (A ⧸ J)] [IsScalarTower R (IsLocalRing.ResidueField R) (A
        ⧸ J)]
    (𝔭 : Ideal A) [𝔭.IsPrime]
    (𝔮 : Ideal (A ⧸ J)) [𝔮.IsPrime] (h𝔮 : 𝔮.comap (Ideal.Quotient.mk J) = 𝔭)
    (hsmooth : Algebra.IsSmoothAt (IsLocalRing.ResidueField R) 𝔮)
    (hfree : (⟨𝔮, ‹_›⟩ : PrimeSpectrum (A ⧸ J)) ∈ Module.freeLocus (A ⧸ J) ((A ⧸ J) ⊗[A] Ω[A⁄R])) :
    ∃ (g : A) (_ : g ∉ 𝔭) (r n : ℕ) (C : Type u) (_ : CommRing C) (_ : Algebra R C)
      (_ : Algebra C (Localization.Away g)) (_ : IsScalarTower R C (Localization.Away g)),
      Algebra.Smooth R C ∧ Function.Surjective (algebraMap C (Localization.Away g)) ∧
      ∃ (y : Fin r → C) (z : Fin n → C) (b : Module.Basis (Fin r ⊕ Fin n) C Ω[C⁄R]),
        (∀ i, b (Sum.inl i) = D R C (y i)) ∧ (∀ j, b (Sum.inr j) = D R C (z j)) ∧
        Ideal.comap (algebraMap C (Localization.Away g)) (J.map (algebraMap A (Localization.Away
            g))) =
          Ideal.span (insert (algebraMap R C π) (Set.range z)) ∧
        LinearIndependent (C ⧸ Ideal.span (insert (algebraMap R C π) (Set.range z)))
          fun j : Fin n => (1 : C ⧸ Ideal.span (insert (algebraMap R C π) (Set.range z))) ⊗ₜ[C]
            D R (Localization.Away g) (algebraMap C (Localization.Away g) (z j)) := by
  classical
  set k : Type u := IsLocalRing.ResidueField R with hkdef
  have : IsNoetherianRing R := inferInstance
  have hAfp : Algebra.FinitePresentation R A := Algebra.FinitePresentation.of_finiteType.mp
      inferInstance
  have hk : Function.Surjective (algebraMap R k) := Ideal.Quotient.mk_surjective
  have hJ𝔭 : J ≤ 𝔭 := by
    intro x hx; rw [← h𝔮, Ideal.mem_comap]; rw [Ideal.Quotient.eq_zero_iff_mem.mpr hx]; exact
        Ideal.zero_mem _
  obtain ⟨r, n, yb, zb, hzb, ⟨b₀, hb₀⟩, ⟨b₁, hb₁⟩, hrank⟩ := ResidueBasis.fibreBasis k hk J 𝔭 𝔮 h𝔮
  obtain ⟨g₁, hg₁, C, iC, iRC, iCA, iT, hCstd, hθ, W, b, hW, hb⟩ :=
    MinimalAmbient.main
      𝔭 (Sum.elim yb zb) b₀ hb₀
  have : Module.FinitePresentation (A ⧸ J) ((A ⧸ J) ⊗[A] Ω[A⁄R]) := inferInstance
  obtain ⟨t, ht, bM, hbM⟩ :=
    Module.FinitePresentation.exists_notMem_basis_localizedModule_of_basis_residueField_tensor
      𝔮 hfree (fun i => (1 : A ⧸ J) ⊗ₜ[A] D R A (Sum.elim yb zb i)) b₁ hb₁
  obtain ⟨g₂, hg₂t⟩ := Ideal.Quotient.mk_surjective t
  have hg₂ : g₂ ∉ 𝔭 := by rw [← h𝔮, Ideal.mem_comap, hg₂t]; exact ht
  set A₁ : Type u := Localization.Away g₁ with hA₁
  set JC : Ideal C := Ideal.span (insert (algebraMap R C π) (Set.range (W ∘ Sum.inr))) with hJCdef
  set I₁ : Ideal C := Ideal.comap (algebraMap C A₁) (J.map (algebraMap A A₁)) with hI₁
  have hJCI : JC ≤ I₁ := by
    rw [hJCdef, Ideal.span_le]
    rintro x (rfl | ⟨j, rfl⟩)
    · change algebraMap R C π ∈ I₁
      rw [hI₁, Ideal.mem_comap, ← IsScalarTower.algebraMap_apply, IsScalarTower.algebraMap_apply R A
          A₁]
      exact Ideal.mem_map_of_mem _ hπJ
    · change W (Sum.inr j) ∈ I₁
      rw [hI₁, Ideal.mem_comap, hW]
      exact Ideal.mem_map_of_mem _ (hzb j)
  set B : Type u := C ⧸ JC with hB
  have hπB : ∀ x ∈ IsLocalRing.maximalIdeal R, algebraMap R B x = 0 := by
    intro x hx
    rw [hπ, Ideal.mem_span_singleton] at hx
    obtain ⟨y, rfl⟩ := hx
    change Ideal.Quotient.mk JC (algebraMap R C (π * y)) = 0
    have hπJC : algebraMap R C π ∈ JC := Ideal.subset_span (Set.mem_insert _ _)
    rw [map_mul, map_mul, Ideal.Quotient.eq_zero_iff_mem.mpr hπJC, zero_mul]
  let iKB : Algebra k B := (Ideal.Quotient.lift (IsLocalRing.maximalIdeal R) (algebraMap R B)
      hπB).toAlgebra
  have : IsScalarTower R k B := IsScalarTower.of_algebraMap_eq' (by
    ext x
    exact (Ideal.Quotient.lift_mk (IsLocalRing.maximalIdeal R) (algebraMap R B) hπB).symm)
  obtain ⟨hBft, hBsm, hBrank⟩ := ChartTransport.quot_smooth_and_rank π hπ hCstd W b hb JC hJCdef
  set gb₁ : A ⧸ J := Ideal.Quotient.mk J g₁ with hgb₁
  have hgb₁𝔮 : gb₁ ∉ 𝔮 := by rw [← h𝔮, Ideal.mem_comap] at hg₁; exact hg₁
  set L : Type u := Localization.Away gb₁ with hL
  have : Algebra.FiniteType R (A ⧸ J) := inferInstance
  have : Algebra.FiniteType k (A ⧸ J) := Algebra.FiniteType.of_restrictScalars_finiteType R k (A ⧸
      J)
  obtain ⟨𝔮', i𝔮', h𝔮', hsm', hrank'⟩ :=
    LocalizedCentre.centre_localized_smooth_and_rank k (A ⧸ J) 𝔮 hsmooth r hrank gb₁ hgb₁𝔮 L
  have hunit : IsUnit (((algebraMap (A ⧸ J) L).comp (Ideal.Quotient.mk J)) g₁) :=
    IsLocalization.Away.algebraMap_isUnit gb₁
  set lam₁ : A₁ →+* L := IsLocalization.Away.lift g₁ hunit with hlam₁
  have hlam₁ : ∀ x : A, lam₁ (algebraMap A A₁ x) = algebraMap (A ⧸ J) L (Ideal.Quotient.mk J x) :=
    fun x => IsLocalization.Away.lift_eq g₁ hunit x
  set ψ₀ : C →+* L := lam₁.comp (algebraMap C A₁) with hψ₀
  have hlamJ : ∀ x ∈ J, lam₁ (algebraMap A A₁ x) = 0 := fun x hx => by
    rw [hlam₁, Ideal.Quotient.eq_zero_iff_mem.mpr hx, map_zero]
  have hψ₀J : ∀ x ∈ JC, ψ₀ x = 0 := by
    have hle : JC ≤ RingHom.ker ψ₀ := by
      rw [hJCdef, Ideal.span_le]
      rintro x (rfl | ⟨j, rfl⟩)
      · simp only [SetLike.mem_coe, RingHom.mem_ker, hψ₀, RingHom.comp_apply]
        rw [← IsScalarTower.algebraMap_apply R C A₁, IsScalarTower.algebraMap_apply R A A₁]
        exact hlamJ _ hπJ
      · simp only [SetLike.mem_coe, RingHom.mem_ker, hψ₀, RingHom.comp_apply, Function.comp_apply]
        rw [hW, Sum.elim_inr]
        exact hlamJ _ (hzb j)
    exact fun x hx => hle hx
  set ψ₁ : B →+* L := Ideal.Quotient.lift JC ψ₀ hψ₀J with hψ₁
  have hψ₁k : ∀ x : k, ψ₁ (algebraMap k B x) = algebraMap k L x := by
    intro x
    obtain ⟨r', rfl⟩ := hk x
    rw [← IsScalarTower.algebraMap_apply R k B, IsScalarTower.algebraMap_apply R C B,
      Ideal.Quotient.algebraMap_eq, hψ₁, Ideal.Quotient.lift_mk, hψ₀, RingHom.comp_apply,
      ← IsScalarTower.algebraMap_apply R C A₁, IsScalarTower.algebraMap_apply R A A₁, hlam₁,
      IsScalarTower.algebraMap_apply k (A ⧸ J) L, ← IsScalarTower.algebraMap_apply R k (A ⧸ J),
      IsScalarTower.algebraMap_apply R A (A ⧸ J), Ideal.Quotient.algebraMap_eq]
  let ψ : B →ₐ[k] L := AlgHom.mk ψ₁ hψ₁k
  have e1 : lam₁ (algebraMap A A₁ g₁) = algebraMap (A ⧸ J) L gb₁ :=
    (hlam₁ g₁).trans (congrArg (algebraMap (A ⧸ J) L) hgb₁).symm
  have hlam₁surj : Function.Surjective lam₁ := by
    intro zL
    obtain ⟨m, ā, hm⟩ := IsLocalization.Away.surj gb₁ zL
    obtain ⟨a₀, rfl⟩ := Ideal.Quotient.mk_surjective ā
    refine ⟨IsLocalization.mk' A₁ a₀ (⟨g₁ ^ m, m, rfl⟩ : Submonoid.powers g₁), ?_⟩
    have hu : IsUnit (algebraMap (A ⧸ J) L gb₁ ^ m) := (IsLocalization.Away.algebraMap_isUnit
        gb₁).pow m
    apply hu.mul_left_injective
    change lam₁ _ * algebraMap (A ⧸ J) L gb₁ ^ m = zL * algebraMap (A ⧸ J) L gb₁ ^ m
    rw [hm, ← e1, ← map_pow, ← map_mul, ← map_pow]
    erw [IsLocalization.mk'_spec]
    rw [hlam₁]
  have hψ : Function.Surjective ψ := by
    intro zL
    obtain ⟨y, hy⟩ := hlam₁surj zL
    obtain ⟨c, rfl⟩ := hθ y
    refine ⟨Ideal.Quotient.mk JC c, ?_⟩
    change ψ₁ (Ideal.Quotient.mk JC c) = zL
    rw [hψ₁, Ideal.Quotient.lift_mk, hψ₀, RingHom.comp_apply, hy]
  set v : Ideal B := 𝔮'.comap ψ.toRingHom with hv
  have : v.IsPrime := Ideal.comap_isPrime _ _
  have : Algebra.FiniteType k B := hBft
  have : Algebra.Smooth k B := hBsm
  obtain ⟨t₃, ht₃, hker⟩ :=
    Algebra.exists_notMem_map_ker_eq_bot_of_surjective_of_isSmoothAt_of_finrank_le
      ψ hψ 𝔮' v rfl hsm' ((hBrank v).trans hrank'.symm.le)
  have : ∃ (c : C) (a : A), a ∉ 𝔭 ∧ g₂ ∣ a ∧ algebraMap C A₁ c = algebraMap A A₁ a ∧
      (I₁.map (algebraMap C (Localization.Away c)) = JC.map (algebraMap C (Localization.Away c)))
          := by
    obtain ⟨c₃, rfl⟩ := Ideal.Quotient.mk_surjective t₃
    obtain ⟨m, a₃, hm⟩ := IsLocalization.Away.surj g₁ (algebraMap C A₁ c₃)
    obtain ⟨u₁, hu₁⟩ := hθ (algebraMap A A₁ (g₁ ^ m))
    obtain ⟨u₂, hu₂⟩ := hθ (algebraMap A A₁ g₂)
    have ha₃ : a₃ ∉ 𝔭 := by
      intro ha₃
      have h1 : lam₁ (algebraMap A A₁ a₃) ∈ 𝔮' := by
        rw [hlam₁]
        have : Ideal.Quotient.mk J a₃ ∈ 𝔮 := by rw [← h𝔮, Ideal.mem_comap] at ha₃; exact ha₃
        rw [← h𝔮'] at this
        exact this
      rw [← hm, map_mul, map_pow] at h1
      rcases (Ideal.IsPrime.mem_or_mem i𝔮' h1) with h2 | h2
      · apply ht₃
        rw [hv, Ideal.mem_comap]
        change ψ₁ (Ideal.Quotient.mk JC c₃) ∈ 𝔮'
        rwa [hψ₁, Ideal.Quotient.lift_mk, hψ₀, RingHom.comp_apply]
      · have hu : IsUnit (lam₁ (algebraMap A A₁ g₁) ^ m) := by
          rw [e1]; exact (IsLocalization.Away.algebraMap_isUnit gb₁).pow m
        exact (Ideal.IsPrime.ne_top i𝔮') (Ideal.eq_top_of_isUnit_mem _ h2 hu)
    refine ⟨c₃ * u₁ * u₂, a₃ * g₂, ?_, dvd_mul_left _ _, ?_, ?_⟩
    · exact fun h => (Ideal.IsPrime.mem_or_mem ‹𝔭.IsPrime› h).elim ha₃ hg₂
    · rw [map_mul, map_mul, hu₁, hu₂, map_mul, ← hm, map_pow]
    · set Cc : Type u := Localization.Away (c₃ * u₁ * u₂) with hCc
      apply le_antisymm
      · rw [Ideal.map_le_iff_le_comap]
        intro x hx
        rw [Ideal.mem_comap]
        have hxker : Ideal.Quotient.mk JC x ∈ RingHom.ker ψ.toRingHom := by
          rw [RingHom.mem_ker]
          change ψ₁ (Ideal.Quotient.mk JC x) = 0
          rw [hψ₁, Ideal.Quotient.lift_mk, hψ₀, RingHom.comp_apply]
          rw [hI₁, Ideal.mem_comap] at hx
          have : J.map (algebraMap A A₁) ≤ RingHom.ker lam₁ := by
            rw [Ideal.map_le_iff_le_comap]; intro y hy; exact hlamJ y hy
          exact this hx
        have h0 : algebraMap B (Localization.Away (Ideal.Quotient.mk JC c₃)) (Ideal.Quotient.mk JC
            x) = 0 := by
          have := Ideal.mem_map_of_mem (algebraMap B (Localization.Away (Ideal.Quotient.mk JC c₃)))
              hxker
          rwa [hker, Ideal.mem_bot] at this
        rw [IsLocalization.map_eq_zero_iff (Submonoid.powers (Ideal.Quotient.mk JC c₃))] at h0
        obtain ⟨⟨_, ⟨m', rfl⟩⟩, hm'⟩ := h0
        have hmem : c₃ ^ m' * x ∈ JC := by
          rw [← Ideal.Quotient.eq_zero_iff_mem, map_mul, map_pow]; exact hm'
        have hc₃unit : IsUnit (algebraMap C Cc (c₃ ^ m')) := by
          rw [map_pow]; refine IsUnit.pow _ ?_
          exact IsLocalization.Away.isUnit_of_dvd (c₃ * u₁ * u₂) ⟨u₁ * u₂, by ring⟩
        have := Ideal.mem_map_of_mem (algebraMap C Cc) hmem
        rw [map_mul] at this
        exact (Ideal.unit_mul_mem_iff_mem _ hc₃unit).mp this
      · exact Ideal.map_mono hJCI
  obtain ⟨c, a, ha, hg₂a, hca, hIdeal⟩ := this
  exact ChartTransport.finalTransport π J 𝔭 yb zb g₁ hg₁ C hCstd hθ W b hW hb c a ha hca hIdeal g₂
      hg₂a
    (fun S _ _ _ _ M _ hu => LocalizedBasis.linIndep_of_basis_localizedModule J t (Sum.elim yb zb)
        bM hbM S M (by
        rw [← hg₂t]
        exact hu.map (algebraMap S (S ⧸ J.map (algebraMap A S)))) |>.comp Sum.inr Sum.inr_injective)

end Algebra

end
