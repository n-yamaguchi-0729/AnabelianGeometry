/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.AlgebraicCurves.Divisors.ClassGroup.ClassGroup
public import Nyll.AlgebraicCurves.Divisors.Maps.Maps
public import Nyll.AlgebraicCurves.Divisors.Maps.Semilinear
public import Nyll.AlgebraicCurves.Divisors.Norm.PushforwardDivSeparable
public import Nyll.AlgebraicCurves.FunctionFields.Transcendence.CurveOver
public import Nyll.AlgebraicCurves.Places.Restriction.AlgEquivSmulEqRestrictEq
public import Nyll.AlgebraicCurves.Places.Restriction.RestrictEq
public import Nyll.AlgebraicCurves.Places.Restriction.RestrictionComposition
public import Nyll.GaloisCohomology.Cyclic.PermutationCoboundary
public import Mathlib.Algebra.Algebra.Tower
public import Mathlib.Algebra.Group.Action.End
public import Mathlib.Data.Finsupp.Basic
public import Mathlib.FieldTheory.Galois.Basic
public import Mathlib.FieldTheory.Fixed
public import Mathlib.GroupTheory.OrderOfElement

/-!
# Actual divisor primitives in a cyclic function-field extension

Over algebraically closed constants all residue degrees are one, so
divisor pushforward is the actual map on places. Every base divisor has
an upstairs lift. A divisor with zero pushforward is a difference under
a generator of the cyclic Galois group: this follows from transitivity
on the actual place fibers and finite orbit telescoping.

The constructed primitive stays over the support of the original
divisor. Thus support conditions needed for Weil reciprocity survive
this construction, including at ramified fibers.
-/

@[expose] public section

noncomputable section

namespace AlgebraicCurve.Divisor

variable {K F L : Type*} [Field K] [IsAlgClosed K] [Field F] [Field L]
  [Algebra K F] [Algebra K L] [Algebra F L] [IsScalarTower K F L]
  [FiniteDimensional F L] [IsCurveOver K F] [IsCurveOver K L]

/-- Over algebraically closed constants the actual divisor pushforward
is the unweighted map of places, since every residue degree is one. -/
theorem pushforward_eq_mapDomain_restrict (D : Divisor K L) :
    pushforward F D = Finsupp.mapDomain (fun w : Place K L => w.restrict F) D := by
  have hdeg (w : Place K L) : w.inertiaDeg F = 1 := by
    have h := w.deg_restrict_mul_inertiaDeg (F := F)
    rw [IsCurveOver.deg_eq_one_of_isAlgClosed,
      IsCurveOver.deg_eq_one_of_isAlgClosed, one_mul] at h
    exact h
  induction D using Finsupp.induction with
  | zero => rw [map_zero, Finsupp.mapDomain_zero]
  | single_add w n D _ _ ih =>
    rw [map_add, pushforward_single, hdeg, Nat.cast_one, mul_one,
      Finsupp.mapDomain_add, Finsupp.mapDomain_single, ih]

/-- Actual place lifting supplies a divisor above every base divisor,
without introducing support over any new base place. -/
theorem exists_pushforward_eq_support_subset (D : Divisor K F) :
    ∃ B : Divisor K L, pushforward F B = D ∧
      (B.support : Set (Place K L)) ⊆
        (fun w : Place K L => w.restrict F) ⁻¹' (D.support : Set (Place K F)) := by
  classical
  have hr : Function.Surjective (fun w : Place K L => w.restrict F) :=
    fun v => Place.exists_restrict_eq (M := L) v
  let s := Function.surjInv hr
  have hs (v : Place K F) : (s v).restrict F = v := Function.rightInverse_surjInv hr v
  refine ⟨Finsupp.mapDomain s D, ?_, ?_⟩
  · rw [pushforward_eq_mapDomain_restrict, ← Finsupp.mapDomain_comp]
    have hcomp : (fun w : Place K L => w.restrict F) ∘ s = id := funext hs
    rw [hcomp, Finsupp.mapDomain_id]
  · intro w hw
    obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp (Finsupp.mapDomain_support hw)
    change (s v).restrict F ∈ D.support
    rw [hs]
    exact hv

/-- A zero-pushforward divisor in an actual cyclic Galois extension
has a generator primitive supported over the same base places. -/
theorem exists_cyclic_smul_sub_of_pushforward_zero [IsGalois F L]
    (σ : L ≃ₐ[F] L) (hσ : Subgroup.zpowers σ = ⊤)
    (D : Divisor K L) (hD : pushforward F D = 0) :
    ∃ C : Divisor K L,
      SemilinearAut.ofAlgAut (σ.restrictScalars K) • C - C = D ∧
      (C.support : Set (Place K L)) ⊆
        (fun w : Place K L => w.restrict F) ⁻¹'
          ((fun w : Place K L => w.restrict F) '' (D.support : Set (Place K L))) := by
  let action : (L ≃ₐ[F] L) →* Equiv.Perm (Place K L) :=
    (MulAction.toPermHom (SemilinearAut K L) (Place K L)).comp
      (SemilinearAut.ofAlgAut.comp (AlgEquiv.restrictScalarsHom K))
  have hr : Function.Surjective (fun w : Place K L => w.restrict F) :=
    fun v => Place.exists_restrict_eq (M := L) v
  have hrσ (w : Place K L) : (action σ w).restrict F = w.restrict F :=
    Place.restrict_ofAlgAut_smul σ w
  have horbit (w w' : Place K L) (h : w.restrict F = w'.restrict F) :
      ∃ n : ℕ, (action σ ^ n) w = w' := by
    obtain ⟨τ, hτ⟩ := Place.exists_algEquiv_smul_eq_of_restrict_eq w w' h.symm
    have hmem : τ ∈ Subgroup.zpowers σ := by
      rw [hσ]
      exact Subgroup.mem_top τ
    obtain ⟨n, hn⟩ := (isOfFinOrder_of_finite σ).mem_powers_iff_mem_zpowers.mpr hmem
    change σ ^ n = τ at hn
    refine ⟨n, ?_⟩
    rw [← map_pow action σ n, hn]
    exact hτ
  have hzero : Finsupp.mapDomain (fun w : Place K L => w.restrict F) D = 0 := by
    rw [← pushforward_eq_mapDomain_restrict, hD]
  obtain ⟨C, hC, hsupport⟩ :=
    CyclicAction.exists_permutation_coboundary_of_mapDomain_eq_zero
      (action σ) (fun w : Place K L => w.restrict F) hr hrσ horbit D hzero
  refine ⟨C, ?_, hsupport⟩
  rw [SemilinearAut.divisor_smul_def]
  exact hC

/-- A genuine norm preimage has a divisor of the cyclic descent form.
Both the lifted divisor and the generator primitive are constructed from
the original function and its norm divisor. -/
theorem exists_cyclic_norm_divisor [IsGalois F L]
    (σ : L ≃ₐ[F] L) (hσ : Subgroup.zpowers σ = ⊤)
    (N : ℕ) (E : Divisor K F) (u : L) (hu : u ≠ 0)
    (hnorm : ∀ v : Place K F, v.ord (Algebra.norm F u) = (N : ℤ) * E v) :
    ∃ B C : Divisor K L, pushforward F B = E ∧
      (B.support : Set (Place K L)) ⊆
        (fun w : Place K L => w.restrict F) ⁻¹' (E.support : Set (Place K F)) ∧
      ∀ w : Place K L, w.ord u =
        (SemilinearAut.ofAlgAut (σ.restrictScalars K) • C - C + (N : ℤ) • B) w := by
  obtain ⟨B, hB, hsupport⟩ := exists_pushforward_eq_support_subset (L := L) E
  obtain ⟨D, hD, _⟩ := HasPrincipalDivisors.exists_divisor (K := K) u hu
  have hpush : pushforward F D = (N : ℤ) • E :=
    pushforward_div_of_isSeparable hu hD (fun v => by
      rw [Finsupp.smul_apply, smul_eq_mul, hnorm])
  have hzero : pushforward F (D - (N : ℤ) • B) = 0 := by
    rw [map_sub, map_zsmul, hpush, hB, sub_self]
  obtain ⟨C, hC, _⟩ := exists_cyclic_smul_sub_of_pushforward_zero
    σ hσ (D - (N : ℤ) • B) hzero
  refine ⟨B, C, hB, hsupport, fun w => ?_⟩
  rw [hC, sub_add_cancel, hD]

end AlgebraicCurve.Divisor
